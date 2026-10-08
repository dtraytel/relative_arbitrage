"""minimize_imports.py OUT REPO [--write]  (OUT: the output directory of Review_Analysis.thy): give every user theory exactly the maximal theories it
needs (named facts and constants), computed in topological order so that every
theory keeps all it needs among its ancestors.  Non-user imports that a theory
lists today are kept (notation and syntax are invisible to the analysis)."""
import sys, os, re, glob, collections
OUT, REPO = sys.argv[1], sys.argv[2]
WRITE = '--write' in sys.argv
USER = {"Symmetric_Matrix_Spectra", "Semicontinuous_Analysis", "Second_Order_Viscosity_Analysis",
        "Wiener_Measure", "Continuous_Time_Martingales", "Continuous_Path_Spaces",
        "Relative_Arbitrage", "Relative_Arbitrage_Statement"}
DIRS = {"Relative_Arbitrage_Statement": "Statement"}
user = lambda t: t.split('.')[0] in USER
par = {}
for l in open(OUT + '/thy_parents.tsv'):
    a = l.rstrip('\n').split('\t'); par[a[0]] = a[1].split() if len(a) > 1 and a[1] else []
rows = [l.rstrip('\n').split('\t') for l in open(OUT + '/facts.tsv')]
dep_thy = dict(l.rstrip('\n').split('\t') for l in open(OUT + '/dep_thys.tsv') if l.count('\t') == 1)
const_thy = dict(l.rstrip('\n').split('\t') for l in open(OUT + '/const_thys.tsv') if l.count('\t') == 1)
fact_thy = {r[2]: r[1] for r in rows}
need = collections.defaultdict(set)
for r in rows:
    for d in (r[6].split() if len(r) > 6 and r[6] else []):
        need[r[1]].add(fact_thy.get(d, dep_thy.get(d, '?')))
    for c in (r[7].split() if len(r) > 7 and r[7] else []):
        need[r[1]].add(const_thy.get(c, '?'))
# locales used by name and @{theory} antiquotations are needs too
import json as _json
LOC = _json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'data', 'locales.json')))
for f in glob.glob(REPO + '/*/*.thy'):
    txt = open(f).read()
    m = re.search(r'\btheory\s+(\w+)\s+imports\b', txt)
    if not m: continue
    full = [t for t in par if t.endswith('.' + m.group(1)) and user(t)]
    if not full: continue
    t = full[0]
    used = set(re.findall(r'\(in\s+(\w+)\)', txt)) | set(re.findall(r'^\s*context\s+(\w+)\s+begin', txt, re.M)) \
        | set(re.findall(r'\binterpret(?:ation)?\s+(?:\w+\s*:\s*)?(\w+)', txt)) \
        | set(re.findall(r'^\s*sublocale\s+[^\n]*?(\w+)\s*$', txt, re.M)) \
        | set(re.findall(r'^locale\s+\w+\s*=\s*(\w+)', txt, re.M)) \
        | set(re.findall(r'^locale\s+\w+\s*=\s*\w+\s*\+\s*(\w+)', txt, re.M)) \
        | set(re.findall(r'^\s+(?:and\s+)?(\w+)\s*\+', txt, re.M))
    for L in used:
        if L in LOC and LOC[L] != t:
            need[t].add(LOC[L])
    for q in re.findall(r'@\{theory\s+([\w\-]+\.\w+)\}', txt):
        if q != t:
            need[t].add(q)
old_anc = {}
def anc(t):
    if t in old_anc: return old_anc[t]
    s = {t}
    for p in par.get(t, []): s |= anc(p)
    old_anc[t] = s; return s
# facts and constants named in antiquotations are needs too
fact_defs = collections.defaultdict(set)
for r in rows:
    fact_defs[r[2].split('.')[-1]].add(r[1])
const_defs = collections.defaultdict(set)
for c, th in const_thy.items():
    const_defs[c.split('.')[-1]].add(th)
for f in glob.glob(REPO + '/*/*.thy'):
    txt = open(f).read()
    m = re.search(r'\btheory\s+(\w+)\s+imports\b', txt)
    if not m: continue
    full = [t for t in par if t.endswith('.' + m.group(1)) and user(t)]
    if not full: continue
    t = full[0]
    A = anc(t)
    for q in re.findall(r'@\{thm(?:\s*\[[^\]]*\])?\s+([\w.\']+)', txt):
        for th in fact_defs.get(q.split('.')[-1], ()):
            if th in A and th != t: need[t].add(th)
    for q in re.findall(r'@\{const(?:\s*\[[^\]]*\])?\s+([\w.\']+)', txt):
        for th in const_defs.get(q.split('.')[-1], ()):
            if th in A and th != t: need[t].add(th)
# keep every current non-user ancestor (notation and syntax are invisible to the analysis)
for t in list(par):
    if user(t):
        need[t] |= {x for x in anc(t) if not user(x) and x != t}
# source import lists
src = {}
for f in glob.glob(REPO + '/*/*.thy'):
    s = open(f).read()
    m = re.search(r'\btheory\s+(\w+)\s+imports\b(.*?)\bbegin\b', s, re.S)
    if not m: continue
    thy = m.group(1)
    full = [t for t in par if t.endswith('.' + thy) and user(t)]
    if not full: continue
    toks = [x.strip('"') for x in re.findall(r'"[^"]+"|[\w.\-]+', re.sub(r'\(\*.*?\*\)', ' ', m.group(2), flags=re.S))]
    src[full[0]] = (f, toks, m.start(2), m.end(2))
def qual(tok, sess):
    if '.' in tok: return tok
    return sess + '.' + tok
# topological order over user theories
order, seen = [], set()
def visit(t):
    if t in seen: return
    seen.add(t)
    for p in par.get(t, []): visit(p)
    order.append(t)
for t in par: visit(t)
new_anc = {}
newpar = {}
def nanc(t):
    if t in new_anc: return new_anc[t]
    if not user(t): return anc(t)
    raise KeyError(t)
for t in order:
    if not user(t):
        continue
    if t not in src:
        new_anc[t] = anc(t); newpar[t] = par[t]; continue
    sess = t.split('.')[0]
    f, toks, _, _ = src[t]
    keep_nonuser = [qual(x, sess) for x in toks if not user(qual(x, sess))]
    nd = {x for x in need.get(t, set()) if x != t and x != '?' and x in old_anc or x in par} - {t}
    nd = {x for x in nd if x in par and (not user(x) or x in new_anc)}
    cand = set(nd) | set(keep_nonuser)
    A = {x: (new_anc[x] if user(x) else anc(x)) for x in cand}
    maximal = [x for x in cand if not any(x in A[y] and x != y for y in cand)]
    # keep the non-user imports the file lists even if implied
    ps = sorted(set(maximal) | set(keep_nonuser))
    newpar[t] = ps
    s = {t}
    for p in ps: s |= (new_anc[p] if user(p) else anc(p))
    new_anc[t] = s
changed = 0
for t, (f, toks, a, b) in sorted(src.items()):
    sess = t.split('.')[0]
    if sess == 'Relative_Arbitrage_Statement':
        continue
    old = [qual(x, sess) for x in toks]
    new = newpar[t]
    if set(old) == set(new):
        continue
    changed += 1
    shown = [(x.split('.', 1)[1] if x.split('.')[0] == sess else '"%s"' % x) for x in new if x != 'Pure']
    dropped = sorted(set(old) - set(new)); added = sorted(set(new) - set(old))
    print(f"{t}: -{len(dropped)} +{len(added)}  drop {[d.split('.',1)[-1] for d in dropped]} add {[x.split('.',1)[-1] for x in added]}")
    if WRITE:
        s = open(f).read()
        lines, cur = [], '   '
        for x in shown:
            if len(cur) + len(x) + 1 > 90:
                lines.append(cur); cur = '   '
            cur += ' ' + x
        lines.append(cur)
        s = s[:a] + '\n' + '\n'.join(lines) + '\n' + s[b:]
        open(f, 'w').write(s)
print("theories changed:", changed)
# The map data/locales.json (locale name -> defining theory) was generated by scanning
# `locale NAME` in the user theories, HOL(-Analysis, -Probability, -Library) and the AFP;
# regenerate it when a theory defines a new locale.
import os as _os
if _os.environ.get("SHOW"): print(_os.environ["SHOW"], newpar.get(_os.environ["SHOW"]), sorted(need.get(_os.environ["SHOW"],[]))[:60])
if _os.environ.get("CHECK"):
    for item in _os.environ["CHECK"].split(';'):
        t, fact = item.split(':')
        defs = fact_defs.get(fact, set())
        print('CHECK', t, fact, 'defined in', sorted(defs), 'reachable:', [d for d in defs if d in new_anc.get(t, set())])
