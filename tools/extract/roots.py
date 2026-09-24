import re, json, collections
import os
SRC = os.environ.get("BORROW_LANG_SRC", os.path.abspath("../../../borrow_lang")) + "/"
rows=[l.rstrip("\n").split("\t") for l in open("dump.tsv")]
D={}
for r in rows:
    n,mod,kind,priv,s,e,sel,deps=r
    D[n]=dict(mod=mod,kind=kind,priv=priv=="true",s=s,e=e,sel=sel,deps=[d for d in deps.split(",") if d])
names=set(D)
# namespace set
suffix=collections.defaultdict(set)
for n in names:
    if "_private" in n: 
        # private: strip mangling for lookup
        m=re.match(r"_private\.[\w.]+?\.\d+\.(.*)",n)
        base=m.group(1) if m else n
    else: base=n
    parts=base.split(".")
    for i in range(len(parts)):
        suffix[".".join(parts[i:])].add(n)
LEGACY={"BoCa."+m for m in "Resource ResourceTests Model BoLo BoLoTests Flatten FlattenTests Wp WpTests LogRel LogRelTests Compat Ledger DefectB Surgery SurgeryTests LifeTests TestCore Programs".split()}
TICK=re.compile(r"`([^`]*)`")
def resolve(t):
    t=t.strip()
    if t in names: return {t}
    if "BoCa."+t in names: return {"BoCa."+t}
    return suffix.get(t,set())
out=[]
for doc in ["docs/definition-inventory.md","docs/paper-inventory.md"]:
    sec=None
    for line in open(SRC+doc):
        if line.startswith("## "): sec=line.strip()
        m=re.match(r"^\| (\d+\.\d+) \|",line)
        if not m: continue
        rid=m.group(1)
        cs=[c.strip() for c in line.split("|")]
        res=[]
        for t in TICK.findall(line):
            if doc.startswith("docs/def") and not t.startswith("BoCa."): continue
            if "." not in t or not (t[0].isalpha() or t[0]=="_") or re.search(r"[\s()\[\]{},;:=<>|\\/*+@#$%^&~\"…⟦⟧]",t): continue
            if t.split(".")[-1] in ("lean","md","txt","pdf","sh","py"): continue
            for n in sorted(resolve(t)):
                if n not in res: res.append(n)
        out.append(dict(doc=doc.split("/")[1],sec=sec,row=rid,names=res,cells=cs))
json.dump(out,open("rows.json","w"),ensure_ascii=False,indent=0)
allroots=set(); leg=set(); amb=0
for o in out:
    for n in o["names"]:
        (leg if D[n]["mod"] in LEGACY else allroots).add(n)
print(len(out),"rows",len(allroots),"nonlegacy roots",len(leg),"legacy cited")
c=collections.Counter(D[n]["mod"] for n in allroots); print(c)
json.dump(sorted(allroots),open("roots.json","w"))

amb=collections.Counter()
for o in out:
  for n in o["names"]:
    pass
import itertools
unres=set()
for doc in ["docs/definition-inventory.md","docs/paper-inventory.md"]:
  for line in open(SRC+doc):
    if not re.match(r"^\| \d+\.\d+ \|",line): continue
    for t in TICK.findall(line):
      if doc.startswith("docs/def") and not t.startswith("BoCa."): continue
      if "." not in t or not (t[0].isalpha() or t[0]=="_") or re.search(r"[\s()\[\]{},;:=<>|\\/*+@#$%^&~\"…⟦⟧]",t): continue
      if t.split(".")[-1] in ("lean","md","txt","pdf","sh","py"): continue
      r=resolve(t)
      if len(r)==0: unres.add(t)
      if len(r)>1: amb[(t,tuple(sorted(r)))]+=1
print("unresolved",sorted(unres)[:40])
for k in amb: print(k)
