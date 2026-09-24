# Source scanning: units (blocks merged over mutual), contexts, prefixes.
exec(open("blocks.py").read())
SRCL={}
def lines(mod):
    if mod not in SRCL: SRCL[mod]=open(SRC+mod.replace(".","/")+".lean").read().split("\n")
    return SRCL[mod]
# all source namespaces
NS=set()
for n in D:
    if n.startswith("_private"): continue
    p=n.split(".")
    for i in range(1,len(p)): NS.add(".".join(p[:i]))
def strip_comments(L):
    """return list of (lineno, code) with comments removed; tracks nested block comments."""
    out=[]; depth=0
    for i,l in enumerate(L,1):
        res=""; j=0
        while j<len(l):
            if depth:
                a=l.find("/-",j); b=l.find("-/",j)
                if b<0 and a<0: j=len(l); break
                if a>=0 and (b<0 or a<b): depth+=1; j=a+2
                else: depth-=1; j=b+2
            else:
                a=l.find("/-",j); c=l.find("--",j)
                if c>=0 and (a<0 or c<a): res+=l[j:c]; break
                if a<0: res+=l[j:]; break
                res+=l[j:a]; depth+=1; j=a+2
        out.append((i,res.rstrip()))
    return out
UNITS={}   # uid -> dict
def resolve_ns(name, path):
    name=name.strip()
    if name.startswith("_root_."): name=name[7:]
    for k in range(len(path),-1,-1):
        c=".".join(path[:k]+[name])
        if c in NS: return c
    return None
def scan(mod):
    L=lines(mod)
    bl=sorted([b for b in blocks if b[0]==mod], key=lambda b:b[1])
    cover={}
    for b in bl:
        for i in range(blocks[b]["s"][0], blocks[b]["e"][0]+1): cover[i]=b
    code=strip_comments(L)
    # gap commands
    cmds=[]; cur=None
    for i,c in code:
        if i in cover:
            cur=None; continue
        if not c.strip(): continue
        if not c[0].isspace():
            cur=[i,c]; cmds.append(cur)
        elif cur is not None:
            cur[1]+="\n"+c
    scopes=[dict(kind="file",ns=[],opens=[],vars=[],opts=[])]
    pending=[]; mutual=None; units=[]; ci=0
    events=sorted([(c[0],"cmd",c[1]) for c in cmds]+[(b[1],"blk",b) for b in bl])
    for ln,kind,x in events:
        if kind=="blk":
            ctx=dict(ns=sum([s["ns"] for s in scopes],[]),
                     opens=[o for s in scopes for o in s["opens"]],
                     vars=[v for s in scopes for v in s["vars"]],
                     opts=[o for s in scopes for o in s["opts"]])
            if mutual is not None:
                mutual["blocks"].append(x)
                if mutual.get("ctx") is None: mutual["ctx"]=ctx; mutual["prefix"]=pending; pending=[]
            else:
                units.append(dict(mod=mod,blocks=[x],ctx=ctx,prefix=pending,s=blocks[x]["s"][0],e=blocks[x]["e"][0]))
                pending=[]
            continue
        c=x.strip()
        m=re.match(r"(noncomputable\s+)?section\b\s*(\S*)",c)
        if c=="mutual":
            mutual=dict(blocks=[],start=ln,ctx=None); continue
        if c=="end" and mutual is not None:
            units.append(dict(mod=mod,blocks=mutual["blocks"],ctx=mutual["ctx"],prefix=mutual["prefix"],s=mutual["start"],e=ln,mutual=True))
            mutual=None; continue
        if c.endswith(" in") or re.match(r"^(open|set_option)\b.*\bin$",c):
            pending.append((c, sum([s["ns"] for s in scopes],[]))); continue
        if c.startswith("namespace "):
            scopes.append(dict(kind="ns",ns=c.split()[1].split("."),opens=[],vars=[],opts=[])); continue
        if m and not c.startswith("sectionX"):
            if c.split()[0] in ("section","noncomputable"):
                scopes.append(dict(kind="sec",ns=[],opens=[],vars=[],opts=[],name=m.group(2))); continue
        if c=="end" or c.startswith("end "):
            if len(scopes)>1: scopes.pop()
            continue
        if c.startswith("open "):
            scopes[-1]["opens"].append((c, sum([s["ns"] for s in scopes],[]))); continue
        if c.startswith("variable"):
            scopes[-1]["vars"].append(c); continue
        if c.startswith("set_option"):
            scopes[-1]["opts"].append(c); continue
        if c.startswith("import") or c.startswith("example") or c.startswith("#"): continue
        if c.startswith("universe"): scopes[-1]["vars"].append(c); continue
        print("UNHANDLED",mod,ln,c[:80])
    return units
