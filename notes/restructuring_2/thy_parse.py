import os, re, sys, json, collections

import os
ROOT = os.environ.get("REPO", os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
SESSIONS = ["Symmetric_Matrix_Spectra","Semicontinuous_Analysis","Second_Order_Viscosity_Analysis",
            "Wiener_Measure","Continuous_Time_Martingales","Continuous_Path_Spaces",
            "Relative_Arbitrage","Statement"]

OPEN, CLOSE = "‹", "›"   # cartouche delimiters

def scan(text):
    """Blank comment bodies. Comments do not start inside string literals
    or cartouches (so `(*v)` in a term is not a comment)."""
    out = list(text)
    n = len(text)
    i = 0
    comdepth = 0
    instr = False
    cart = 0
    while i < n:
        c = text[i]
        if comdepth > 0:
            if text.startswith("(*", i):
                comdepth += 1; out[i]=' '; out[i+1]=' '; i+=2; continue
            if text.startswith("*)", i):
                comdepth -= 1; out[i]=' '; out[i+1]=' '; i+=2; continue
            if c != '\n': out[i]=' '
            i += 1; continue
        if instr:
            if c == '\\': i += 2; continue
            if c == '"': instr = False
            i += 1; continue
        if cart > 0:
            if text.startswith("\\<open>", i): cart += 1; i += 7; continue
            if text.startswith("\\<close>", i): cart -= 1; i += 8; continue
            if c == OPEN: cart += 1; i += 1; continue
            if c == CLOSE: cart -= 1; i += 1; continue
            i += 1; continue
        if c == '"':
            instr = True; i += 1; continue
        if text.startswith("\\<open>", i): cart += 1; i += 7; continue
        if c == OPEN: cart += 1; i += 1; continue
        if text.startswith("(*", i):
            comdepth = 1; out[i]=' '; out[i+1]=' '; i+=2; continue
        i += 1
    return "".join(out)

def blank_doc_cartouches(text):
    """Blank the bodies of text/section/... cartouches, keeping newlines."""
    out = list(text)
    kw = re.compile(r'(?<![A-Za-z_.])(text|txt|section|subsection|subsubsection|paragraph|chapter|text_raw|abstract)\s*(\\<open>|'+OPEN+')')
    for m in kw.finditer(text):
        start = m.end()
        # find matching close by cartouche depth, handling both ascii \<open> and unicode
        i = start; depth = 1
        while i < len(text) and depth > 0:
            if text.startswith("\\<open>", i): depth+=1; i+=7; continue
            if text.startswith("\\<close>", i): depth-=1; i+=8; continue
            if text[i]==OPEN: depth+=1; i+=1; continue
            if text[i]==CLOSE: depth-=1; i+=1; continue
            i+=1
        for j in range(start, min(i,len(text))):
            if out[j] != '\n': out[j]=' '
    return "".join(out)

DECL_KWS = ["lemma","theorem","corollary","proposition","definition","abbreviation","fun","primrec",
            "locale","sublocale","interpretation","type_synonym","inductive","inductive_set",
            "instantiation","instance","context","end","declare","notation","no_notation",
            "lift_definition","setup_lifting","named_theorems","schematic_goal","method","ML",
            "datatype","record","typedef","axiomatization","syntax","translations","print_translation",
            "section","subsection","subsubsection","text","paragraph","chapter","theory","imports","begin",
            "proof","qed","next","by","apply","done","using","unfolding","have","show","obtain","fix","assume",
            "then","also","finally","moreover","ultimately","let","note","from","with","case","hence","thus","term","value","typ","thm"]

TOP_DECL = re.compile(r'^(lemma|theorem|corollary|proposition|definition|abbreviation|fun|primrec|locale|sublocale|type_synonym|inductive|inductive_set|schematic_goal|datatype|record|typedef|context|end|instantiation)\b')
PROOF_START = re.compile(r'^\s*(by|proof|apply|unfolding|using|\.\.|\.)\b')

def parse_theory(path):
    raw = open(path, encoding='utf-8').read()
    code = blank_doc_cartouches(scan(raw))
    lines = code.split('\n')
    rawlines = raw.split('\n')
    ents = []
    ctx = []  # context/locale stack
    i = 0
    while i < len(lines):
        line = lines[i]
        m = TOP_DECL.match(line)
        if m:
            kw = m.group(1)
            if kw == 'context':
                nm = re.match(r'context\s+([A-Za-z_][A-Za-z0-9_\'.]*)', line)
                ctx.append(nm.group(1) if nm else '?')
                i+=1; continue
            if kw == 'end':
                if ctx: ctx.pop()
                i+=1; continue
            if kw in ('instantiation',):
                i+=1; continue
            # gather header: from this line until proof start (for lemmas) or end of decl
            j = i+1
            body = [line]
            while j < len(lines):
                l = lines[j]
                if TOP_DECL.match(l): break
                if kw in ('lemma','theorem','corollary','proposition','schematic_goal') and PROOF_START.match(l):
                    break
                if re.match(r'^\s*(by|proof)\b', l) and kw in ('definition','abbreviation','fun','primrec','inductive','inductive_set','sublocale'):
                    break
                if l.strip() == '' and j>i and kw in ('definition','abbreviation','type_synonym'):
                    pass
                body.append(l)
                j += 1
                if j - i > 400: break
            header = "\n".join(body)
            # name extraction
            nm = None
            m2 = re.match(r'^(?:lemma|theorem|corollary|proposition|definition|abbreviation|fun|primrec|locale|sublocale|type_synonym|inductive|inductive_set|schematic_goal|datatype|record|typedef)\s*(?:\((?:in\s+)?[^)]*\)\s*)?([A-Za-z_][A-Za-z0-9_\']*)?', line)
            inloc = None
            mi = re.match(r'^\w+\s*\(\s*in\s+([A-Za-z_][A-Za-z0-9_\'.]*)\s*\)', line)
            if mi: inloc = mi.group(1)
            if m2 and m2.group(1): nm = m2.group(1)
            # find end of the whole command (next top decl)
            k = j
            while k < len(lines) and not TOP_DECL.match(lines[k]):
                k += 1
            ents.append(dict(kind=kw, name=nm, line=i+1, endline=k, header=header,
                             body="\n".join(lines[i:k]), ctx=list(ctx)+([inloc] if inloc else []),
                             path=path))
            i = j
            continue
        i += 1
    return ents

def all_entities():
    res = []
    for s in SESSIONS:
        d = os.path.join(ROOT, s)
        for f in sorted(os.listdir(d)):
            if f.endswith('.thy'):
                for e in parse_theory(os.path.join(d,f)):
                    e['session']=s; e['theory']=f[:-4]
                    res.append(e)
    return res

if __name__ == '__main__':
    ents = all_entities()
    print(len(ents))
    kinds = collections.Counter(e['kind'] for e in ents)
    print(kinds)
