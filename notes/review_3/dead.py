import csv, re, os, sys, collections, json
REPO=os.path.abspath(os.path.join(os.path.dirname(__file__),'..','..'))
OUT=sys.argv[1]
dirs={"Symmetric_Matrix_Spectra":"Symmetric_Matrix_Spectra","Semicontinuous_Analysis":"Semicontinuous_Analysis","Second_Order_Viscosity_Analysis":"Second_Order_Viscosity_Analysis","Wiener_Measure":"Wiener_Measure","Continuous_Time_Martingales":"Continuous_Time_Martingales","Continuous_Path_Spaces":"Continuous_Path_Spaces","Relative_Arbitrage":"Relative_Arbitrage","Relative_Arbitrage_Statement":"Statement"}
rows=[l.rstrip('\n').split('\t') for l in open(OUT+'/facts.tsv')]
START=re.compile(r'^(lemma|theorem|corollary|proposition|definition|fun|primrec|function|abbreviation|locale|sublocale|interpretation|lemmas|text|section|subsection|subsubsection|paragraph|context|end|declare|notation|type_synonym|inductive|ML|setup|instance|instantiation)\b')
NAMED=re.compile(r'^(?:lemma|theorem|corollary|proposition|lemmas|definition|abbreviation|fun|primrec)\s+(?:\(in\s+\w+\)\s*)?"?(\w+)')
fileinfo={}
def info(sess,thy):
    key=(sess,thy)
    if key in fileinfo: return fileinfo[key]
    p=os.path.join(REPO,dirs[sess],thy.split('.')[-1]+'.thy')
    L=open(p).read().split('\n')
    starts=[i+1 for i,l in enumerate(L) if START.match(l)]
    names={}
    for i,l in enumerate(L):
        m=NAMED.match(l)
        if m: names.setdefault(m.group(1),i+1)
    fileinfo[key]=(len(L),starts,names); return fileinfo[key]
def extent(sess,thy,line):
    n,starts,_=info(sess,thy)
    nxt=[s for s in starts if s>line]
    return (nxt[0] if nxt else n)-line
res=collections.defaultdict(lambda: {'facts':0,'used':0,'unused':[], 'unused_lines':0,'lines':0})
seen_lines=set()
for r in rows:
    sess,thy,name,line,kind,use=r[0],r[1],r[2],int(r[3]),r[4],r[5]
    base=name.split('.')[-1]
    if line==0:
        _,_,names=info(sess,thy); line=names.get(base,0)
    d=res[(sess,thy)]; d['facts']+=1
    if use=='USED': d['used']+=1
    else:
        if line and (thy,line) not in seen_lines:
            seen_lines.add((thy,line)); ext=extent(sess,thy,line); d['unused_lines']+=ext
        else: ext=0
        d['unused'].append((name,line,ext,kind))
# but a line block might contain both used and unused facts (e.g. lemma with several results): subtract blocks that contain a used fact
used_lines=set()
for r in rows:
    if r[5]=='USED':
        line=int(r[3])
        if line==0: line=info(r[0],r[1])[2].get(r[2].split('.')[-1],0)
        used_lines.add((r[1],line))
tot=collections.Counter(); totl=collections.Counter(); sesslines=collections.Counter()
out=[]
for (sess,thy),d in sorted(res.items()):
    n,_,_=info(sess,thy)
    ul=sum(e for (nm,l,e,k) in d['unused'] if (thy,l) not in used_lines)
    d['unused_lines']=ul
    tot[sess]+=d['facts']; totl[sess]+=ul; sesslines[sess]+=n
    out.append((sess,thy,n,d['facts'],d['used'],len(d['unused']),ul))
print(f"{'session/theory':60s} {'lines':>6} {'facts':>6} {'used':>5} {'unused':>6} {'dead lines':>10}")
cur=None
for sess,thy,n,f,u,un,ul in out:
    if sess!=cur:
        cur=sess; print(f"== {sess}: {sesslines[sess]} lines, ~{totl[sess]} dead lines ({100*totl[sess]/sesslines[sess]:.0f}%)")
    print(f"   {thy.split('.')[-1]:57s} {n:6d} {f:6d} {u:5d} {un:6d} {ul:10d}")
print("TOTAL dead lines ~", sum(totl.values()), "of", sum(sesslines.values()))
json.dump({f"{s}|{t}":d['unused'] for (s,t),d in res.items()}, open(OUT+'/unused_by_theory.json','w'))
