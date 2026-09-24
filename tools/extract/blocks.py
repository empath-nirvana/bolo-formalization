exec(open("info.py").read())
def rng(o):
    s=D[o]["s"].split(":"); e=D[o]["e"].split(":")
    return (int(s[0]),int(s[1])),(int(e[0]),int(e[1]))
owners=sorted(set(v for v in own.values() if v))
bymod=collections.defaultdict(list)
for o in owners: bymod[D[o]["mod"]].append(o)
block={}   # owner -> block id (mod, startline)
blocks={}  # id -> dict(mod,s,e,members)
for mod,oss in bymod.items():
    oss.sort(key=lambda o:(rng(o)[0], (-rng(o)[1][0],-rng(o)[1][1])))
    cur=None
    for o in oss:
        s,e=rng(o)
        if cur and s>=blocks[cur]["s"] and e<=blocks[cur]["e"]:
            block[o]=cur; blocks[cur]["members"].append(o)
        else:
            cur=(mod,s[0]); blocks[cur]=dict(mod=mod,s=s,e=e,members=[o]); block[o]=cur
bdeps=collections.defaultdict(set)
for o in owners:
    for d in odeps.get(o,()):
        if block[d]!=block[o]: bdeps[block[o]].add(block[d])
def bname(b): 
    m=blocks[b]["members"]; 
    return min(m,key=lambda o:rng(o)[0])
