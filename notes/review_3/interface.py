import sys, collections
OUT=sys.argv[1]
rows=[l.rstrip('\n').split('\t') for l in open(OUT+'/facts.tsv')]
F={r[2]:dict(thy=r[1], deps=(r[6].split() if len(r)>6 and r[6] else []), consts=(r[7].split() if len(r)>7 and r[7] else [])) for r in rows}
def closure(root, stop_thys):
    seen=set(); st=[root]
    while st:
        n=st.pop()
        if n in seen or n not in F: continue
        seen.add(n)
        if F[n]['thy'].split('.')[-1] in stop_thys: continue   # do not look inside the interface theories
        st+=F[n]['deps']
    return seen
op_thys={"Curvature_Operator","Viscosity_Definitions","Constraint_Set_Convexity","Eigenvalue_Bound_Exact","Operator_Continuity","Operator_Formula","Operator_Envelopes","Operator_Envelope_Continuity","Viscosity_Ball","Viscosity_Comparison_Interface","Ball_Solution"}
for root in ["Comparison_Two_Domain.uniqueness_expandable"]:
    c=closure(root, op_thys)
    iface=sorted(n for n in c if F[n]['thy'].split('.')[-1] in op_thys)
    print(f"{root}: closure {len(c)} facts; operator-layer facts consumed directly: {len(iface)}")
    for n in iface: print("   ", n)
cls_thys={"Exit_Class","Constraint_Set_Convexity","Curvature_Operator","Eigenvalue_Bound_Exact","Operator_Formula","Operator_Continuity","Operator_Envelopes"}
# which sconstraint-related facts are consumed by the class / DPP / tightness chain (outside the operator theories)
sc=[n for n,f in F.items() if any(c.endswith('.sconstraint') for c in f['consts']) and f['thy'].split('.')[-1]=='Exit_Class']
users=collections.defaultdict(set)
for n,f in F.items():
    for d in f['deps']:
        if d in sc and f['thy'].split('.')[-1] not in cls_thys: users[d].add(f['thy'].split('.')[-1])
print("\nExit_Class facts about sconstraint used outside the operator/class-definition theories:")
for d in sorted(users, key=lambda d:-len(users[d])): print(f"   {d}  <- {len(users[d])} theories: {', '.join(sorted(users[d]))[:150]}")
