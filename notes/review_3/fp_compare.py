#!/usr/bin/env python3
"""fp_compare.py OLD.tsv NEW.tsv [RENAMES]
Compare two fingerprints.tsv files written by Review_Analysis.thy.  Facts are keyed by
their name without the theory qualifier (so a theory move or rename keeps the key);
RENAMES is an optional file of 'old_key new_key' lines for renamed facts.  Reports
facts whose statement fingerprint changed, facts that disappeared and facts that
are new.  Phases 5, 6 and 8 must report no changed and no disappeared fact."""
import sys, collections
def load(p):
    d = collections.defaultdict(dict)
    for l in open(p):
        full, key, i, h = l.rstrip('\n').split('\t')
        d[key][int(i)] = (h, full)
    return d
old, new = load(sys.argv[1]), load(sys.argv[2])
ren = {}
if len(sys.argv) > 3:
    for l in open(sys.argv[3]):
        if l.strip() and not l.startswith('#'):
            a, b = l.split(); ren[a] = b
changed, gone = [], []
for k, v in old.items():
    k2 = ren.get(k, k)
    if k2 not in new: gone.append(k); continue
    if {i: h for i, (h, _) in v.items()} != {i: h for i, (h, _) in new[k2].items()}:
        changed.append(k)
added = [k for k in new if k not in {ren.get(x, x) for x in old}]
for k in sorted(changed): print('CHANGED', k)
for k in sorted(gone): print('GONE   ', k)
print(f'facts: {len(old)} -> {len(new)}; changed {len(changed)}, gone {len(gone)}, new {len(added)}')
sys.exit(1 if changed or gone else 0)
