import json,collections,re,bisect
exec(open("closure.py").read().split("roots=json.load")[0])
import os
SRC = os.environ.get("BORROW_LANG_SRC", os.path.abspath("../../../borrow_lang")) + "/"
rowsj=json.load(open("rows.json"))
# root map from def inventory col4
names=set(D)
suffix=collections.defaultdict(set)
for n in names:
    m=re.match(r"_private\.[\w.]+?\.\d+\.(.*)",n); base=m.group(1) if m else n
    p=base.split(".")
    for i in range(len(p)): suffix[".".join(p[i:])].add(n)
def resolve(t):
    if t in names: return {t}
    return suffix.get(t,set())
rootrow={}
for o in rowsj:
    if not o["doc"].startswith("def"): continue
    for t in re.findall(r"`([^`]*)`",o["cells"][4]):
        if not t.startswith("BoCa."): continue
        for n in resolve(t):
            if own[n]: rootrow.setdefault(own[n],(o["row"],o["cells"][6].strip("`") if len(o["cells"])>6 else ""))
# headers per file
hdr={}
def headers(mod):
    if mod in hdr: return hdr[mod]
    L=open(SRC+mod.replace(".","/")+".lean").read().split("\n")
    hs=[]
    for i,l in enumerate(L,1):
        m=re.match(r"/-! *(#+) *(.*)",l)
        if m and len(m.group(1))==2: hs.append((i,m.group(2)[:50]))
    hdr[mod]=hs; return hs
def hdrof(o):
    hs=headers(D[o]["mod"]); ln=int(D[o]["s"].split(":")[0])
    ks=[h[0] for h in hs]; k=bisect.bisect_right(ks,ln)-1
    return hs[k][1] if k>=0 else ""
