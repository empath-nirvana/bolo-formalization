exec(open("gen.py").read())
skip=set(CFG["stage1_skip_rows"])
isthm=lambda u: D[owners_of(u)[0]]["kind"]=="thm"
roots=set(uid for uid,rs in unit_rows.items() if any(r not in skip for r in rs) and not isthm(uid))
sel=select(roots)
DEFERRED=[]
for u,rs in sorted(unit_rows.items()):
    if isthm(u) and u not in sel and any(r not in skip for r in rs):
        new=close(sel|{u})-sel
        if sum(UBY[x]["e"]-UBY[x]["s"]+1 for x in new) <= 60: sel=select(sel|{u})
        else: DEFERRED.append(u)
json.dump(["%s:%d"%u for u in DEFERRED],open("deferred.json","w"))
tgt,inline,probs=assign(sel)
for p in probs: print("PROB",p)
banners={}
exec(open("banners.py").read())
banners["__support__"]=SUPPORT_BANNER; banners["__what__"]=SUPPORT_WHAT
order,g,written,strip=emit(sel,tgt,banners)
json.dump(dict(order=order,tgt={"%s:%d"%u:t for u,t in tgt.items()},strip=["%s:%d"%u for u in strip]),open("stage1.json","w"),indent=0)
print("files",len(order)); print("\n".join(order))
rows=write_bridge(sel,tgt,strip,OUT+"/Bridge/Names.csv")
print("bridge rows",len(rows),"stripped privates",len(strip))
