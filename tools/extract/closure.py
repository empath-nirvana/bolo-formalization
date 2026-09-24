import json, re, collections
rows=[l.rstrip("\n").split("\t") for l in open("dump.tsv")]
D={}
for n,mod,kind,priv,s,e,sel,deps in rows:
    D[n]=dict(mod=mod,kind=kind,priv=priv=="true",s=s,e=e,deps=[d for d in deps.split(",") if d])
privby=collections.defaultdict(list)
for k in D:
    m=re.match(r"_private\.[\w.]+?\.\d+\.(.*)",k)
    if m: privby[m.group(1)].append(k)
def owner(n):
    if D[n]["s"]!="-": return n
    m=re.match(r"(_private\.[\w.]+?\.\d+\.)(.*)",n)
    pre,base=(m.group(1),m.group(2)) if m else ("",n)
    parts=base.split(".")
    for i in range(len(parts)-1,0,-1):
        c=".".join(parts[:i])
        for cand in ([pre+c] if pre else [])+[c]:
            if cand in D and D[cand]["s"]!="-": return cand
        # private owner of a public-looking aux
        for k in privby.get(c,[]):
            if D[k]["s"]!="-": return k
    return None
own={n:owner(n) for n in D}
noown=[n for n in D if own[n] is None]
print("no owner:",len(noown),noown[:20])
odeps=collections.defaultdict(set)
for n in D:
    o=own[n]
    if o is None: continue
    for d in D[n]["deps"]:
        if d in D and own[d] and own[d]!=o: odeps[o].add(own[d])
roots=json.load(open("roots.json"))
seen=set(); st=[own[r] for r in roots if own[r]]
while st:
    x=st.pop()
    if x in seen: continue
    seen.add(x); st.extend(odeps[x])
json.dump(sorted(seen),open("closure.json","w"))
json.dump({k:sorted(v) for k,v in odeps.items()},open("odeps.json","w"))
json.dump(own,open("own.json","w"))
bymod=collections.Counter(); lines=collections.Counter(); tot=collections.Counter(); totl=collections.Counter()
for o in set(own.values())-{None}:
    s=int(D[o]["s"].split(":")[0]); e=int(D[o]["e"].split(":")[0])
    tot[D[o]["mod"]]+=1; totl[D[o]["mod"]]+=e-s+1
    if o in seen: bymod[D[o]["mod"]]+=1; lines[D[o]["mod"]]+=e-s+1
print("closure owners",len(seen),"lines",sum(lines.values()))
for m in sorted(tot,key=lambda m:-lines[m]): print(f"{m:28s} {bymod[m]:5d}/{tot[m]:5d}  {lines[m]:6d}/{totl[m]:6d}")
