"""simulate.py OUT CHANGES.json : check that after replacing the import lists given in
CHANGES (theory -> list of full theory names), every user theory still has every
theory it needs (named facts and constants) among its ancestors."""
import sys, json, collections
OUT = sys.argv[1]
changes = json.load(open(sys.argv[2]))
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
new = dict(par); new.update(changes)
def ancs(P, t, memo):
    if t in memo: return memo[t]
    s = {t}
    for p in P.get(t, []): s |= ancs(P, p, memo)
    memo[t] = s; return s
m_old, m_new = {}, {}
bad = 0
for t in sorted(par):
    lost = (ancs(par, t, m_old) - ancs(new, t, m_new))
    missing = {x for x in need.get(t, set()) if x in lost}
    if missing:
        bad += 1
        print('BROKEN', t, '<-', sorted(missing))
print('theories checked:', len(par), 'broken:', bad)
