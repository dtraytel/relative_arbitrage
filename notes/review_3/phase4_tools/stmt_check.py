#!/usr/bin/env python3
"""stmt_check.py WORKTREE [BASE]  (BASE defaults to bc034d3)
For every .thy file changed against BASE, list the named facts (lemma, theorem,
corollary, proposition) that were removed, added, or whose statement text changed.
The statement is the text from the fact head to the first line that starts the
proof (proof, by, using, unfolding, apply, including, supply, .).  Whitespace is
normalised.  A changed statement must be identical in meaning or stronger, and every
removed fact must have had all its users re-pointed."""
import sys, subprocess, re
WT = sys.argv[1]; BASE = sys.argv[2] if len(sys.argv) > 2 else 'bc034d3'
files = subprocess.run(['git', '-C', WT, 'diff', '--name-only', BASE, '--', '*.thy'], capture_output=True, text=True).stdout.split()
HEAD = re.compile(r'^(lemma|theorem|corollary|proposition)\s+(?:\(in\s+\w+\)\s*)?(\w+)\s*(\[[^\]]*\])?\s*:')
STOP = re.compile(r'^\s*(proof\b|by\b|using\b|unfolding\b|apply\b|including\b|supply\b|\.\s*$|\.\.\s*$|sorry\b|oops\b)')
TOP = re.compile(r'^(lemma|theorem|corollary|proposition|definition|text|section|subsection|end|context|locale|lemmas|declare|\(\*)')
def facts(text):
    out = {}; L = text.split('\n'); i = 0
    while i < len(L):
        m = HEAD.match(L[i])
        if m:
            name = m.group(2); buf = [L[i]]; j = i + 1
            while j < len(L) and not STOP.match(L[j]) and not TOP.match(L[j]):
                buf.append(L[j]); j += 1
            out[name] = ' '.join(' '.join(buf).split()); i = j
        else:
            i += 1
    return out
tot_rm = tot_ch = 0
for f in files:
    old = subprocess.run(['git', '-C', WT, 'show', f'{BASE}:{f}'], capture_output=True, text=True).stdout
    try: new = open(f'{WT}/{f}').read()
    except FileNotFoundError: new = ''
    a, b = facts(old), facts(new)
    rm = sorted(set(a) - set(b)); ad = sorted(set(b) - set(a))
    ch = sorted(n for n in set(a) & set(b) if a[n] != b[n])
    if rm or ad or ch:
        print(f'== {f}')
        for n in rm: print(f'   removed: {n}')
        for n in ad: print(f'   added:   {n}')
        for n in ch: print(f'   CHANGED: {n}\n      old: {a[n][:300]}\n      new: {b[n][:300]}')
    tot_rm += len(rm); tot_ch += len(ch)
print(f'files changed: {len(files)}; facts removed: {tot_rm}; statements changed: {tot_ch}')
