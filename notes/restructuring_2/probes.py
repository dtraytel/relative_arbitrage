#!/usr/bin/env python3
"""Probes for the second restructuring plan (notes/PLAN_RESTRUCTURING_2.md).

Run from this directory:  python3 probes.py [probe ...]
with no argument it runs all of them.  Every number quoted in the plan comes
from here.  `thy_parse.py` must sit next to this file.

WARNING, and the reason this file exists at all: a naive comment stripper
that counts `(*` depth goes unbalanced on the term `(*v)` -- the matrix-vector
product -- and silently blanks the rest of the file.  Before this was fixed,
`Doubling_Of_Variables` reported 1 lemma instead of 141 and `Matrix_Algebra`
93 instead of 147.  `thy_parse.scan` therefore tracks string literals and
cartouches and only starts a comment outside both.  `probe0` re-checks the
parse against a plain grep and must print 0 mismatches.
"""
import re, sys, collections
from thy_parse import all_entities, SESSIONS, ROOT
import os

ents = all_entities()
STMT = ('lemma','theorem','corollary','proposition','schematic_goal')
DEFK = ('definition','abbreviation','fun','primrec','locale','type_synonym','inductive','inductive_set','datatype','record')
ID   = re.compile(r"[A-Za-z][A-Za-z0-9_']*")

owner = {}
for e in ents:
    if e['name']: owner.setdefault(e['name'], e)

def stmt(e):
    return re.sub(r"^\w+\s*(\([^)]*\)\s*)?([A-Za-z_][A-Za-z0-9_']*)?\s*(\[[^\]]*\])?\s*:", '', e['header'], count=1)

# Constants of the paper: the statement of a lemma mentioning one of these is
# about this paper.  Constants of the path toolkit: generic, but declared in
# the paper session today.
PAPER = set("""sconstraint Pi_constraint Pi_proj suff_volatile feasible ell_op ell_op_s eigen_lb eigen_ub Mp eq36_rhs
 ball_v exit_class exit_val iexit_class iexit_val xclass xval pdelclass arb_V relative_arbitrage val_fn mkt_exit_vals
 mkt_law_witness mkt_path_laws mkt_law_closure stopped_market stopped_exit_vals stopped_val_fn visc_subsol visc_supersol
 visc_sol visc_subsol_env visc_supersol_env visc_sol_env visc_subsol_env2 visc_supersol_env2 visc_supersol_lsc supersol_jet
 max_principle_boundary max_principle_boundary_raw ell_op_pair ell_op_lsc ell_op_usc mgap rank1proj tanp tanpV tanpU tanSF
 rotSF uvec uvecV colm projmat bmX bm_paths cbmX Bcont ito_Z coord_Z sbmpair eulerp xiC euXi bmpair ibmpair ibm_law selker
 pball_exit iextend expandable test_fun_at test_fun_C2 sint""".split())
GENERIC = set("""pcut pglue padd pdel pfut pembed prebase pstopped pafter pshift pfst pcoord ploc iglue pexit iexit
 path_stopping_time pre_sigma_of ess_inf_time ess_inf_enn dyceil rclamp vshift confined_paths kglue kglue_law aglue_law
 pair_law_of pglue_law pshift_law outerp acont Yint pairX pairY pairpath pstep""".split())

def probe0():
    "parser self-check: parsed declarations vs grep"
    bad = 0
    cnt = collections.Counter((e['session'],e['theory']) for e in ents if e['kind'] in STMT)
    for s in SESSIONS:
        for f in sorted(os.listdir(os.path.join(ROOT,s))):
            if not f.endswith('.thy'): continue
            txt = open(os.path.join(ROOT,s,f), encoding='utf-8').read()
            g = len(re.findall(r'^(lemma|theorem|corollary|proposition)\b', txt, re.M))
            if g != cnt[(s,f[:-4])]:
                bad += 1; print("  MISMATCH", s, f, cnt[(s,f[:-4])], g)
    print("probe0: mismatched theories:", bad)

def probe1():
    "inventory"
    k = collections.Counter(e['kind'] for e in ents)
    print("probe1:", dict(k))
    for s in SESSIONS:
        n = sum(1 for e in ents if e['session']==s and e['kind'] in STMT)
        d = sum(1 for e in ents if e['session']==s and e['kind'] in DEFK)
        L = sum(len(open(os.path.join(ROOT,s,f),encoding='utf-8').read().split('\n'))
                for f in os.listdir(os.path.join(ROOT,s)) if f.endswith('.thy'))
        print(f"   {s:34s} {L:6d} lines  {n:5d} statements  {d:4d} definitions")

def probe2():
    "buckets: how paper-bound is each statement of Relative_Arbitrage"
    b = collections.Counter(); ln = collections.Counter()
    for e in ents:
        if e['session'] != 'Relative_Arbitrage' or e['kind'] not in STMT or not e['name']: continue
        ws = set(ID.findall(stmt(e))); n = e['endline']-e['line']+1
        if ws & PAPER: k='paper statement'
        elif ws & GENERIC: k='path toolkit only'
        elif any(w in owner and owner[w]['session']=='Relative_Arbitrage' for w in ws): k='other RA name'
        else: k='lower sessions only'
        b[k]+=1; ln[k]+=n
    for k in b: print(f"probe2: {b[k]:5d} statements {ln[k]:7d} lines   {k}")

def probe3():
    "statements that name nothing from their own session (can leave it)"
    below = {'Symmetric_Matrix_Spectra':set(),'Semicontinuous_Analysis':set(),
             'Second_Order_Viscosity_Analysis':{'Symmetric_Matrix_Spectra'},'Wiener_Measure':set(),
             'Continuous_Time_Martingales':set(),
             'Continuous_Path_Spaces':{'Continuous_Time_Martingales','Semicontinuous_Analysis'},
             'Relative_Arbitrage':{'Continuous_Path_Spaces','Symmetric_Matrix_Spectra','Semicontinuous_Analysis',
                                   'Second_Order_Viscosity_Analysis','Wiener_Measure','Continuous_Time_Martingales'},
             'Statement':{'Relative_Arbitrage','Continuous_Path_Spaces','Symmetric_Matrix_Spectra',
                          'Semicontinuous_Analysis','Second_Order_Viscosity_Analysis','Wiener_Measure',
                          'Continuous_Time_Martingales'}}
    c = collections.Counter()
    for e in ents:
        if e['kind'] not in STMT or not e['name']: continue
        ss = {owner[w]['session'] for w in set(ID.findall(e['body'])) if w in owner}
        if ss <= below[e['session']]: c[(e['session'],e['theory'])] += 1
    for k,v in sorted(c.items(), key=lambda kv:-kv[1])[:20]: print(f"probe3: {v:5d}  {k[0]}/{k[1]}")
    print("probe3: total", sum(c.values()))

def probe4():
    "duplicate statements, modulo renaming of short variables"
    known = {e['name'] for e in ents if e['name']}
    TOK = re.compile(r"\\<[A-Za-z0-9^_]+>|[A-Za-z][A-Za-z0-9_']*|[^\sA-Za-z]")
    def norm(s):
        out=[]; m={}
        for t in TOK.findall(s):
            if t.startswith('\\<') or not t[0].isalpha(): out.append(t); continue
            if t in known or '_' in t or len(t) > 6 or t in ('assumes','shows','fixes','and'): out.append(t)
            else:
                m.setdefault(t, 'v%d' % len(m)); out.append(m[t])
        return ''.join(out)
    g = collections.defaultdict(list)
    for e in ents:
        if e['kind'] in STMT and e['name']:
            n = norm(stmt(e))
            if len(n) > 30: g[n].append(e)
    for n, es in g.items():
        if len(es) > 1:
            print("probe4:", ", ".join(f"{x['name']} ({x['session']}/{x['theory']}:{x['line']})" for x in es))

def probe5():
    "statements named nowhere else (dead-code candidates; deliverables included)"
    uses = collections.Counter()
    for e in ents:
        for w in set(ID.findall(e['body'])):
            if w in owner and w != e['name']: uses[w] += 1
    by = collections.defaultdict(list)
    for e in ents:
        if e['kind'] in STMT and e['name'] and uses[e['name']] == 0:
            by[(e['session'],e['theory'])].append(e['name'])
    for k in sorted(by, key=lambda k: -len(by[k])):
        print(f"probe5: {len(by[k]):3d} {k[0]}/{k[1]}: {', '.join(by[k])}")
    print("probe5: total", sum(len(v) for v in by.values()))

def probe6():
    "direct imports from which nothing is named"
    imports = {}
    for s in SESSIONS:
        for f in sorted(os.listdir(os.path.join(ROOT,s))):
            if not f.endswith('.thy'): continue
            txt = open(os.path.join(ROOT,s,f), encoding='utf-8').read()
            m = re.search(r'\btheory\s+(\S+)\s+imports(.*?)\bbegin\b', txt, re.S)
            imports[(s,f[:-4])] = [a or b for a,b in re.findall(r'"([^"]+)"|([A-Za-z_][A-Za-z0-9_.\']*)', m.group(2))] if m else []
    used = collections.defaultdict(set)
    for e in ents:
        k = (e['session'],e['theory'])
        for w in set(ID.findall(e['body'])):
            if w in owner and (owner[w]['session'],owner[w]['theory']) != k:
                used[k].add((owner[w]['session'],owner[w]['theory']))
    proj = set(imports)
    def key(i, s): return tuple(i.split('.',1)) if '.' in i else (s,i)
    def closure(k, seen=None):
        seen = set() if seen is None else seen
        for i in imports.get(k,[]):
            kk = key(i,k[0])
            if kk in proj and kk not in seen: seen.add(kk); closure(kk,seen)
        return seen
    for k in sorted(imports):
        for d in [key(i,k[0]) for i in imports[k]]:
            if d in proj and not ((closure(d) | {d}) & used[k]):
                print(f"probe6: {k[0]}/{k[1]} imports {d[0]}/{d[1]} -- nothing below it is named")

if __name__ == '__main__':
    names = sys.argv[1:] or ['probe0','probe1','probe2','probe3','probe4','probe5','probe6']
    for n in names: globals()[n]()
