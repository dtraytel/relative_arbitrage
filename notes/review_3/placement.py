import collections, sys, json
OUT=sys.argv[1]
par={}
for l in open(OUT+'/thy_parents.tsv'):
    a=l.rstrip('\n').split('\t'); par[a[0]]=a[1].split() if len(a)>1 and a[1] else []
anc_memo={}
def anc(t):
    if t in anc_memo: return anc_memo[t]
    s={t}
    for p in par.get(t,[]): s|=anc(p)
    anc_memo[t]=s; return s
sess=lambda t: t.split('.')[0]
decl={
 "Symmetric_Matrix_Spectra":["HOL-Analysis"],
 "Semicontinuous_Analysis":["HOL-Probability","Standard_Borel_Spaces","Lower_Semicontinuous"],
 "Second_Order_Viscosity_Analysis":["HOL-Analysis","Symmetric_Matrix_Spectra"],
 "Continuous_Time_Martingales":["HOL-Probability","Martingales"],
 "Wiener_Measure":["HOL-Probability","Kolmogorov_Chentsov","Continuous_Time_Martingales"],
 "Continuous_Path_Spaces":["Continuous_Time_Martingales","Kolmogorov_Chentsov","Levy_Prokhorov_Metric","Standard_Borel_Spaces","Semicontinuous_Analysis","HOL-Complex_Analysis"],
}
def closure(s):
    out=set(); st=[s]
    while st:
        x=st.pop()
        if x in out: continue
        out.add(x); st+=decl.get(x,[])
    return out
def allowed_for_sessions(ss, extra_thys=()):
    tops=[t for t in par if sess(t) in ss]+list(extra_thys)
    A=set()
    for t in tops: A|=anc(t)
    return A
targets={s: allowed_for_sessions(closure(s)) for s in decl}
# hypothetical analytic base: SMS + SOVA + SemiC minus Semicontinuous_Selection (+ its HOL-Prob deps)
an=allowed_for_sessions({"Symmetric_Matrix_Spectra","Second_Order_Viscosity_Analysis","HOL-Analysis"},
   ["Semicontinuous_Analysis.Semicontinuity","Semicontinuous_Analysis.Semicontinuous_Envelopes","Semicontinuous_Analysis.Berge"])
targets["ANALYTIC(SMS+SOVA+SemiC\\Selection, no probability)"]=an
print("analytic base contains HOL-Probability theories?", any(sess(t)=="HOL-Probability" for t in an))
rows=[l.rstrip('\n').split('\t') for l in open(OUT+'/facts.tsv')]
facts={}
for r in rows:
    deps=r[6].split() if len(r)>6 and r[6] else []
    consts=r[7].split() if len(r)>7 and r[7] else []
    facts[r[2]]=dict(sess=r[0],thy=r[1],deps=deps,consts=consts,used=r[5],line=int(r[3]))
dep_thy={}
for l in open(OUT+'/dep_thys.tsv'):
    a=l.rstrip('\n').split('\t')
    if len(a)==2: dep_thy[a[0]]=a[1]
const_thy={}
for l in open(OUT+'/const_thys.tsv'):
    a=l.rstrip('\n').split('\t')
    if len(a)==2: const_thy[a[0]]=a[1]
def fthy(n): return facts[n]['thy'] if n in facts else dep_thy.get(n,'?')
def movable(A):
    cand={n for n,f in facts.items() if f['thy'] not in A}
    while True:
        def ok(n):
            f=facts[n]
            own = n[:-4] if n.endswith('_def') else None
            for c in f['consts']:
                if c==own: continue
                t=const_thy.get(c,'?')
                if t in A: continue
                d=c+'_def'
                if d in cand: continue
                return False
            for d in f['deps']:
                if fthy(d) in A or d in cand: continue
                return False
            return True
        new={n for n in cand if ok(n)}
        if new==cand: return cand
        cand=new
res={k: movable(A) for k,A in targets.items()}
# per RA theory summary
ra=[n for n,f in facts.items() if f['sess'] in ('Relative_Arbitrage',)]
order=["Symmetric_Matrix_Spectra","Semicontinuous_Analysis","Second_Order_Viscosity_Analysis","ANALYTIC(SMS+SOVA+SemiC\\Selection, no probability)","Continuous_Time_Martingales","Wiener_Measure","Continuous_Path_Spaces"]
bythy=collections.defaultdict(list)
for n in ra: bythy[facts[n]['thy']].append(n)
short={"Symmetric_Matrix_Spectra":"SMS","Semicontinuous_Analysis":"SemiC","Second_Order_Viscosity_Analysis":"SOVA","ANALYTIC(SMS+SOVA+SemiC\\Selection, no probability)":"ANLYT","Continuous_Time_Martingales":"CTM","Wiener_Measure":"WM","Continuous_Path_Spaces":"CPS"}
print(f"{'RA theory':42s} {'facts':>5} " + " ".join(f"{short[o]:>6}" for o in order) + "  (#facts movable to each target)")
tot=collections.Counter()
for t in sorted(bythy, key=lambda t: t):
    ns=bythy[t]
    cnt=[sum(1 for n in ns if n in res[o]) for o in order]
    for o,c in zip(order,cnt): tot[o]+=c
    print(f"{t.split('.')[-1]:42s} {len(ns):5d} " + " ".join(f"{c:6d}" for c in cnt))
print(f"{'TOTAL':42s} {len(ra):5d} " + " ".join(f"{tot[o]:6d}" for o in order))
# also: CPS facts movable to CTM, SOVA/SMS facts movable lower, etc.
for src,tgt in [("Continuous_Path_Spaces","Continuous_Time_Martingales"),("Second_Order_Viscosity_Analysis","Symmetric_Matrix_Spectra"),("Wiener_Measure","Continuous_Time_Martingales")]:
    ns=[n for n,f in facts.items() if f['sess']==src]
    m=[n for n in ns if n in res[tgt]]
    print(f"{src} facts movable to {tgt}: {len(m)}/{len(ns)}")
json.dump({k:sorted(v) for k,v in res.items()}, open(OUT+'/movable.json','w'))

print("\n==== strict modes: only Relative_Arbitrage facts may move ====")
RA_SESS={'Relative_Arbitrage'}
ra_consts={c for c,t in const_thy.items() if sess(t) in RA_SESS}
def movable2(A, library_ready):
    cand={n for n,f in facts.items() if f['sess'] in RA_SESS and f['thy'] not in A}
    if library_ready:
        cand={n for n in cand if not any(c in ra_consts for c in facts[n]['consts'])}
    while True:
        def ok(n):
            f=facts[n]
            own = n[:-4] if n.endswith('_def') else None
            for c in f['consts']:
                if c==own: continue
                t=const_thy.get(c,'?')
                if t in A: continue
                if (c+'_def') in cand: continue
                return False
            for d in f['deps']:
                if fthy(d) in A or d in cand: continue
                return False
            return True
        new={n for n in cand if ok(n)}
        if new==cand: return cand
        cand=new
for mode in (False, True):
    print("\n-- mode:", "LIBRARY-READY (statement names no paper-session constant)" if mode else "with co-moved definitions")
    r2={k: movable2(A, mode) for k,A in targets.items()}
    print(f"{'RA theory':42s} {'facts':>5} " + " ".join(f"{short[o]:>6}" for o in order))
    tot=collections.Counter()
    for t in sorted(bythy):
        ns=bythy[t]
        cnt=[sum(1 for n in ns if n in r2[o]) for o in order]
        for o,c in zip(order,cnt): tot[o]+=c
        if any(cnt): print(f"{t.split('.')[-1]:42s} {len(ns):5d} " + " ".join(f"{c:6d}" for c in cnt))
    print(f"{'TOTAL':42s} {len(ra):5d} " + " ".join(f"{tot[o]:6d}" for o in order))
    json.dump({k:sorted(v) for k,v in r2.items()}, open(OUT+('/movable_libready.json' if mode else '/movable_withdefs.json'),'w'))
