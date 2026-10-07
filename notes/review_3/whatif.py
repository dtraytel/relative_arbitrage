import json, sys, collections, os
src=open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'placement.py')).read().split('print("\\n==== strict')[0].replace('print(','(lambda *a,**k:None)(')
exec(src)
OUT=sys.argv[1]
key="ANALYTIC(SMS+SOVA+SemiC\\Selection, no probability)"
A=set(targets[key]) | {"Continuous_Time_Martingales.Integrability_Criteria__virtual"}
dep_thy["Integrability_Criteria.cInf_mult_pos"]="Continuous_Time_Martingales.Integrability_Criteria__virtual"
if "Integrability_Criteria.cInf_mult_pos" in facts: facts["Integrability_Criteria.cInf_mult_pos"]['thy']="Continuous_Time_Martingales.Integrability_Criteria__virtual"
RA_SESS={'Relative_Arbitrage'}
cand={n for n,f in facts.items() if f['sess'] in RA_SESS and f['thy'] not in A}
while True:
    def ok(n):
        f=facts[n]; own = n[:-4] if n.endswith('_def') else None
        for c in f['consts']:
            if c==own: continue
            if const_thy.get(c,'?') in A or (c+'_def') in cand: continue
            return False
        for d in f['deps']:
            if fthy(d) in A or d in cand: continue
            return False
        return True
    new={n for n in cand if ok(n)}
    if new==cand: break
    cand=new
bythy=collections.defaultdict(lambda:[0,0])
for n,f in facts.items():
    if f['sess'] in RA_SESS:
        bythy[f['thy'].split('.')[-1]][0]+=1
        if n in cand: bythy[f['thy'].split('.')[-1]][1]+=1
for t in ["Curvature_Operator","Viscosity_Definitions","Viscosity_Ball","Constraint_Set_Convexity","Viscosity_Comparison_Interface","Ball_Solution","Eigenvalue_Bound_Exact","Operator_Continuity","Operator_Formula","Operator_Envelopes","Operator_Envelope_Continuity","Comparison_Strictness","Comparison_Localisation","Comparison_Principle","Comparison_Two_Domain","Value_Function_Tangential_Field","Covariation_Density"]:
    print(f"{t:35s} {bythy[t][1]:3d}/{bythy[t][0]:3d}")
print("total RA facts placeable probability-free:", len(cand))
