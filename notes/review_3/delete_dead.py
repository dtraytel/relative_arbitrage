#!/usr/bin/env python3
"""Delete the dead lemma blocks of chosen theories, using a fresh analysis.

  delete_dead.py OUTDIR REPO Session.Theory [Session.Theory ...] [--dry] [--keep=a,b]

1. A block runs from a top-level 'lemma|theorem|corollary|proposition' line to
   the next top-level command.  It is a candidate when no fact of the analysis
   that lies in it is USED and no USED fact of the theory is bound inside it.
2. Fixpoint: a candidate whose name still occurs in the remaining *code* of
   any theory (prose and cartouche contents ignored) is kept.
3. A text block directly before a deleted block goes too, when every fact
   name it mentions is deleted.  Headers left without content go.
4. Unused definitions whose constant is named nowhere else go.
5. @{thm ...} antiquotations naming deleted facts become \\<open>name\\<close>.
"""
import os, re, sys, collections

OUT, REPO = sys.argv[1], sys.argv[2]
args = [a for a in sys.argv[3:] if not a.startswith('--')]
DRY = '--dry' in sys.argv
KEEP = set()
for a in sys.argv[3:]:
    if a.startswith('--keep='):
        KEEP |= set(a[len('--keep='):].split(','))
DIRS = {"Symmetric_Matrix_Spectra": "Symmetric_Matrix_Spectra",
        "Semicontinuous_Analysis": "Semicontinuous_Analysis",
        "Second_Order_Viscosity_Analysis": "Second_Order_Viscosity_Analysis",
        "Wiener_Measure": "Wiener_Measure",
        "Continuous_Time_Martingales": "Continuous_Time_Martingales",
        "Continuous_Path_Spaces": "Continuous_Path_Spaces",
        "Relative_Arbitrage": "Relative_Arbitrage",
        "Relative_Arbitrage_Statement": "Statement"}
START = re.compile(r'^(lemma|theorem|corollary|proposition|definition|fun|primrec|function|'
                   r'abbreviation|locale|sublocale|interpretation|global_interpretation|lemmas|'
                   r'text|txt|section|subsection|subsubsection|paragraph|chapter|context|end|declare|'
                   r'notation|no_notation|type_synonym|typedef|datatype|record|inductive|inductive_set|'
                   r'ML|ML_file|setup|instance|instantiation|consts|named_theorems|bundle|'
                   r'unbundle|method|attribute_setup|method_setup|hide_const|hide_fact|lift_definition|'
                   r'experiment|schematic_goal|qualified|private)\b|^\(\*')
FACTKW = re.compile(r'^(lemma|theorem|corollary|proposition)\b')
HEAD = re.compile(r'^(chapter|section|subsection|subsubsection|paragraph)\b')
LEVEL = {'chapter': 0, 'section': 1, 'subsection': 2, 'subsubsection': 3, 'paragraph': 4}
PROSE = re.compile(r'^\s*(text|txt|section|subsection|subsubsection|paragraph|chapter)\b')
OPEN, CLOSE = '\\<open>', '\\<close>'


def code_only(text):
    """Drop prose commands with their cartouche, and the contents of all cartouches."""
    out, depth = [], 0
    for l in text.split('\n'):
        if depth == 0 and PROSE.match(l):
            k = l.find(OPEN)
            depth = (l[k:].count(OPEN) - l[k:].count(CLOSE)) if k >= 0 else 1
            continue
        if depth > 0:
            depth = max(0, depth + l.count(OPEN) - l.count(CLOSE))
            continue
        out.append(re.sub(r'\\<open>.*?\\<close>', ' ', l))
    return '\n'.join(out)


def word(nm):
    return re.compile(r'(?<![\w.\'])' + re.escape(nm) + r'(?![\w\'])')


rows = [l.rstrip('\n').split('\t') for l in open(os.path.join(OUT, 'facts.tsv'))]
by_thy = collections.defaultdict(list)
for r in rows:
    by_thy[r[1]].append((r[2].split('.')[-1], int(r[3]), r[5] == 'USED'))

# ---- 1. candidate blocks
plans = {}
for st in args:
    sess, thy = st.split('.', 1)
    path = os.path.join(REPO, DIRS[sess], thy + '.thy')
    L = open(path).read().split('\n')
    n = len(L)
    starts = [i for i, l in enumerate(L) if START.match(l)]
    facts = by_thy[st]
    used_names = {nm for nm, _, u in facts if u}
    blocks = []
    for k, s in enumerate(starts):
        e = starts[k + 1] if k + 1 < len(starts) else n
        if not FACTKW.match(L[s]):
            continue
        lines_in = [(nm, ln, u) for nm, ln, u in facts if s < ln <= e]
        if not lines_in or any(u for _, _, u in lines_in):
            continue
        names = sorted({nm for nm, _, _ in lines_in})
        if set(names) & KEEP:
            continue
        body = '\n'.join(L[s:e])
        if any(re.search(r'(^|\s)' + re.escape(nm) + r'\s*(\[[^\]]*\])?\s*:', body) for nm in used_names):
            continue
        blocks.append((s, e, names))
    plans[st] = dict(path=path, L=L, starts=starts, blocks=blocks, facts=facts)

all_files = []
for d in DIRS.values():
    dp = os.path.join(REPO, d)
    all_files += [os.path.join(dp, f) for f in os.listdir(dp) if f.endswith('.thy')]


def remaining_text(pl):
    dele = [False] * len(pl['L'])
    for s, e, _ in pl['blocks']:
        for t in range(s, e):
            dele[t] = True
    return '\n'.join(l for i, l in enumerate(pl['L']) if not dele[i])


# ---- 2. keep what remaining code still names
kept = []
changed = True
while changed:
    changed = False
    by_path = {pl['path']: pl for pl in plans.values()}
    code = '\n'.join(code_only(remaining_text(by_path[f]) if f in by_path else open(f).read())
                     for f in all_files)
    for st, pl in plans.items():
        for b in list(pl['blocks']):
            if any(word(nm).search(code) for nm in b[2]):
                pl['blocks'].remove(b)
                kept.append((st, b[2]))
                changed = True

deleted_names = {nm for pl in plans.values() for (_, _, ns) in pl['blocks'] for nm in ns}

# ---- 3. texts and headers, then write
report = []
for st, pl in plans.items():
    L, starts, blocks, facts = pl['L'], pl['starts'], pl['blocks'], pl['facts']
    n = len(L)
    dele = [False] * n
    for s, e, _ in blocks:
        for t in range(s, e):
            dele[t] = True
    allnames = {nm for nm, _, _ in facts}
    for s, e, names in blocks:
        k = starts.index(s)
        if k == 0:
            continue
        ps = starts[k - 1]
        if not re.match(r'^(text|txt)\b', L[ps]) or dele[ps]:
            continue
        txt = '\n'.join(L[ps:s])
        toks = set(re.findall(r'\\<open>(\w+)\\<close>', txt)) | \
            set(re.findall(r'@\{thm(?:\s*\[[^\]]*\])?\s+(\w+)', txt))
        ment = toks & allnames
        if ment and ment <= deleted_names:
            for t in range(ps, s):
                dele[t] = True
    changed = True
    while changed:
        changed = False
        live_starts = [i for i in starts if not dele[i]]
        for k, i in enumerate(live_starts):
            m = HEAD.match(L[i])
            if not m:
                continue
            nxt = live_starts[k + 1] if k + 1 < len(live_starts) else None
            empty = nxt is None
            if not empty:
                m2 = HEAD.match(L[nxt])
                if m2 and LEVEL[m2.group(1)] <= LEVEL[m.group(1)]:
                    empty = True
                elif L[nxt].startswith('(*<*)') and any(L[t].strip() == 'end' for t in range(nxt, min(nxt + 3, n))):
                    empty = True
            if empty:
                for t in range(i, nxt if nxt is not None else n):
                    dele[t] = True
                changed = True
                break
    out = []
    for i, l in enumerate(L):
        if dele[i]:
            continue
        if l.strip() == '' and len(out) >= 2 and out[-1].strip() == '' and out[-2].strip() == '':
            continue
        out.append(l)
    report.append((st, sum(dele), len(blocks), [nm for _, _, ns in blocks for nm in ns]))
    if not DRY:
        open(pl['path'], 'w').write('\n'.join(out))

# ---- 4. unused definitions named nowhere else
DEFKW = re.compile(r'^(definition|abbreviation|fun|primrec|function)\s+(?:\(in\s+\w+\)\s*)?"?(\w+)')
unused_consts = collections.defaultdict(set)
for l in open(os.path.join(OUT, 'user_consts.tsv')):
    c, t, u = l.rstrip('\n').split('\t')
    if u != 'USED':
        unused_consts[t].add(c.split('.')[-1])
def_report = collections.defaultdict(list)
if not DRY:
    changed = True
    while changed:
        changed = False
        texts = {p: open(p).read() for p in all_files}
        for st in args:
            path = plans[st]['path']
            L = texts[path].split('\n')
            n = len(L)
            starts = [i for i, l in enumerate(L) if START.match(l)]
            for k, i in enumerate(starts):
                m = DEFKW.match(L[i])
                if not m or m.group(2) not in unused_consts[st] or m.group(2) in KEEP:
                    continue
                c = m.group(2)
                e = starts[k + 1] if k + 1 < len(starts) else n
                w = word(c)
                rest_here = '\n'.join(L[:i] + L[e:])
                if w.search(rest_here) or any(w.search(t) for q, t in texts.items() if q != path):
                    continue
                open(path, 'w').write('\n'.join(L[:i] + L[e:]))
                def_report[st].append(c)
                deleted_names.add(c + '_def')
                changed = True
                break
            if changed:
                break

# ---- 5. antiquotations naming deleted facts, everywhere
live_elsewhere = {r[2].split('.')[-1] for r in rows if r[5] == 'USED'}
gone = deleted_names - live_elsewhere
pat = re.compile(r'@\{thm(?:\s*\[[^\]]*\])?\s+(\w+)\}')
fixed = 0
for p in all_files:
    s = open(p).read()
    s2 = pat.sub(lambda m: '\\<open>%s\\<close>' % m.group(1) if m.group(1) in gone else m.group(0), s)
    if s2 != s:
        fixed += len(pat.findall(s)) - len(pat.findall(s2))
        if not DRY:
            open(p, 'w').write(s2)
for st, names in kept:
    print(f'kept (still named in code): {st}: {" ".join(names)}')
for st, nl, nb, names in report:
    print(f'{st}: {nb} blocks, {nl} lines: {" ".join(names)}')
print('antiquotations rewritten:', fixed)
for st, cs in def_report.items():
    print(f'{st}: definitions deleted: {" ".join(cs)}')
