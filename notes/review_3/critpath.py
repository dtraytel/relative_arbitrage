import re, sys, collections, glob, os
OUT=sys.argv[1]; BUILDLOG=sys.argv[2]; HERE=os.path.dirname(os.path.abspath(__file__))
exec(open(os.path.join(HERE,"actual_imports.py")).read().replace('print(','(lambda *a,**k:None)('))
# per-theory CPU seconds from build log (both sessions' logs mixed)
tm={}
for l in open(BUILDLOG):
    m=re.match(r'^[\w\-]+: theory ([\w\-\.]+) 100% \(([0-9.]+)s', l)
    if m: tm[m.group(1)]=float(m.group(2))
def critical(edges, nodes):
    memo={}
    def f(t):
        if t in memo: return memo[t]
        best=max([f(p) for p in edges.get(t,[]) if p in nodes], default=(0,[]))
        memo[t]=(best[0]+tm.get(t,0), best[1]+[t]); return memo[t]
    return max((f(t) for t in nodes), key=lambda x:x[0])
ra=[t for t in src_imp if t.startswith('Relative_Arbitrage.') or t.startswith('Relative_Arbitrage_Statement.')]
lib=[t for t in src_imp if not (t.startswith('Relative_Arbitrage.') or t.startswith('Relative_Arbitrage_Statement.'))]
nodes=set(src_imp)
cur_edges={t:[i for i in src_imp[t] if i in nodes] for t in src_imp}
need_edges={}
for t in src_imp:
    nd=need.get(t,set())-{t}
    need_edges[t]=[x for x in nd if x in nodes]
c1=critical(cur_edges, nodes); c2=critical(need_edges, nodes)
tot=sum(tm.get(t,0) for t in nodes)
print(f"total CPU of user theories: {tot:.0f}s")
print(f"critical path, current imports: {c1[0]:.0f}s over {len(c1[1])} theories")
print("   ", " -> ".join(x.split('.')[-1] for x in c1[1]))
print(f"critical path, needed deps only: {c2[0]:.0f}s over {len(c2[1])} theories")
print("   ", " -> ".join(x.split('.')[-1] for x in c2[1]))
