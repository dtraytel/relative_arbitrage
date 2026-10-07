import collections, sys, re, os
OUT=sys.argv[1]; REPO='/home/user/relative_arbitrage'
par={}
for l in open(OUT+'/thy_parents.tsv'):
    a=l.rstrip('\n').split('\t'); par[a[0]]=a[1].split() if len(a)>1 and a[1] else []
anc_memo={}
def anc(t):
    if t in anc_memo: return anc_memo[t]
    s={t}
    for p in par.get(t,[]): s|=anc(p)
    anc_memo[t]=s; return s
rows=[l.rstrip('\n').split('\t') for l in open(OUT+'/facts.tsv')]
dep_thy={}
for l in open(OUT+'/dep_thys.tsv'):
    a=l.rstrip('\n').split('\t')
    if len(a)==2: dep_thy[a[0]]=a[1]
const_thy={}
for l in open(OUT+'/const_thys.tsv'):
    a=l.rstrip('\n').split('\t')
    if len(a)==2: const_thy[a[0]]=a[1]
fact_thy={r[2]:r[1] for r in rows}
need=collections.defaultdict(set)   # theory -> theories whose facts/consts it uses
for r in rows:
    t=r[1]
    for d in (r[6].split() if len(r)>6 and r[6] else []):
        need[t].add(fact_thy.get(d, dep_thy.get(d,'?')))
    for c in (r[7].split() if len(r)>7 and r[7] else []):
        need[t].add(const_thy.get(c,'?'))
user=lambda t: t.split('.')[0] in {"Symmetric_Matrix_Spectra","Semicontinuous_Analysis","Second_Order_Viscosity_Analysis","Wiener_Measure","Continuous_Time_Martingales","Continuous_Path_Spaces","Relative_Arbitrage","Relative_Arbitrage_Statement"}
# for each user theory: direct parents; which parents are "needed" = some needed theory is in anc(parent) and not reachable via other needed-parents? Simplify: parent p is redundant if no needed theory lies in anc(p) \ union(anc(q) for other parents q)... report parents whose anc contains no needed theory at all ("unused import") and parents subsumed by another parent ("transitively redundant").
report=[]
for t in sorted(par):
    if not user(t) or t.startswith('Draft') : continue
    ps=par[t]; nd=need.get(t,set())-{t}
    unused=[p for p in ps if not (anc(p) & nd)]
    subsumed=[p for p in ps if any(p in anc(q) and p!=q for q in ps)]
    # minimal necessary user-level parents: needed user theories not covered by others
    nd_user=sorted(x for x in nd if user(x) and x!=t)
    maximal=[x for x in nd_user if not any(x in anc(y) and x!=y for y in nd_user)]
    report.append((t, ps, unused, subsumed, maximal))
for t,ps,un,sub,mx in report:
    if un or sub:
        print(t)
        if un: print("   imports supplying nothing used:", ", ".join(un))
        if sub: print("   imports already implied by another import:", ", ".join(sub))
        print("   minimal user-theory deps actually used:", ", ".join(mx) if mx else "-")

print("\n===== source imports vs. latest needed theories =====")
import glob
src_imp={}
for f in glob.glob(REPO+'/*/*.thy'):
    s=open(f).read(); m=re.search(r'\bimports\b(.*?)\bbegin\b', s, re.S)
    body=re.sub(r'\(\*.*?\*\)',' ',m.group(1),flags=re.S)
    toks=[x.strip('"') for x in re.findall(r'"[^"]+"|[\w.\-]+', body)]
    base=os.path.basename(f)[:-4]
    full=[t for t in par if t.endswith('.'+base) and user(t)]
    if not full: continue
    t=full[0]
    res=[]
    for x in toks:
        cand=[y for y in par if y==x or y.endswith('.'+x.split('.')[-1])]
        res.append(cand[0] if cand else x)
    src_imp[t]=res
for t in sorted(src_imp):
    nd=need.get(t,set())-{t}
    nd_user=sorted(x for x in nd if user(x))
    maximal=[x for x in nd_user if not any(x in anc(y) and x!=y for y in nd_user)]
    imps=[i for i in src_imp[t] if user(i)]
    # an import is "late" if it is not an ancestor-or-equal of any maximal needed theory
    useless=[i for i in imps if not any(m in anc(i) for m in maximal) and not any(i in anc(m) for m in maximal)]
    over=[i for i in imps if not any(i==m or i in anc(m) for m in maximal) and any(m in anc(i) for m in maximal)]
    if over or useless:
        print(t.split('.',1)[1], "|", len(src_imp[t]), "imports")
        print("   needs at most:", ", ".join(m.split('.',1)[1] for m in maximal) or "-")
        if over: print("   imports later than needed:", ", ".join(i.split('.',1)[1] for i in over))
        if useless: print("   imports with nothing needed below them:", ", ".join(i.split('.',1)[1] for i in useless))
