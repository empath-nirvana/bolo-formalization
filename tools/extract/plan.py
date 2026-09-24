exec(open("stage1.py").read().split("tgt,inline,probs=assign(sel)")[0])
S1SEL=set(sel); S1TGT,_,_=assign(sel)
SUB={"6.1":(1,15),"6.2":(16,63),"6.3":(64,66),"6.4":(67,95),"6.5":(96,119),"6.6":(120,134),"6.7":(135,150),"6.8":(151,176)}
SUBDIR={"6.1":"Paper/S6_1_StandardLemmas","6.2":"Paper/S6_2_NonStandardLemmas","6.3":"Paper/S6_3_FrameAndAntiFrame",
 "6.4":"Paper/S6_4_StandardEntailments","6.5":"Paper/S6_5_NonStandardEntailments","6.6":"Paper/S6_6_ReborrowingEntailments",
 "6.7":"Paper/S6_7_WeakestPreconditionRules","6.8":"Paper/S6_8_FundamentalProperty"}
def subof(r):
    n=int(r.split(".")[1])
    for k,(a,b) in SUB.items():
        if a<=n<=b: return k
LIT=re.compile(r"refuted|_false\b|\bnot_|stuck_|ViewWitness|DefectB|unreachable|Gap|_blocked|WalkNeg|Example|residual|Residual|_fails|counterex",re.I)
NONVAC=re.compile(r"nonvacuous|_applies|_inhabited|_witness")
primary={}; cited={}
for o in ROWS:
    if not o["doc"].startswith("paper"): continue
    r=o["row"]; note=o["cells"][5] if len(o["cells"])>5 else ""
    names=[]
    for t in re.findall(r"`([^`]*)`", " ".join(o["cells"])):
        if "." not in t or not (t[:1].isalpha() or t[:1]=="_"): continue
        for n in sorted(resolve_full(t)):
            if own.get(n) and D[n]["mod"] not in LEGACY and D[n]["mod"]!="BoCa.Wp":
                names.append(n)
    first=True
    for n in names:
        u=unit_of_owner[own[n]]
        if first and not LIT.search(n): primary.setdefault(u,r); first=False
        else: cited.setdefault(u,r)
rootsF=set(S1SEL)|set(primary)|set(cited)|set(DEF2 for DEF2 in unit_rows if True)
selF=select(rootsF)
print("full selection units",len(selF),"lines",sum(UBY[u]["e"]-UBY[u]["s"]+1 for u in selF))
tgtF={}
for u in selF:
    if u in S1SEL: tgtF[u]=S1TGT[u]; continue
    if u in primary and u[0]!="BoCa.Wp":
        r=primary[u]
        if r.startswith("6."): tgtF[u]=SUBDIR[subof(r)]+"/Lemmas"
        else: tgtF[u]="Paper/CONF/Results"
        continue
    name=owners_of(u)[0]
    if LIT.search(name): tgtF[u]="Paper/LiteralReadings"; continue
    if u in cited and NONVAC.search(name):
        r=cited[u]; tgtF[u]=(SUBDIR[subof(r)]+"/Lemmas") if r.startswith("6.") else "Paper/CONF/Results"; continue
    if u in unit_rows:   # a definition-inventory theorem row deferred from Stage 1
        tgtF[u]="Paper/"+{"4":"S4_LogicalRelation","5":"S5_Model"}.get(sorted(unit_rows[u],key=rowkey)[0].split(".")[0],"X")+"/Remarks"; continue
    tgtF[u]="Support/"+support_topic(u)
# a literal-reading unit that a paper or support unit depends on is support
revF=collections.defaultdict(set)
for u in selF:
    for d in udeps[u]:
        if d in selF: revF[d].add(u)
changed=True
while changed:
    changed=False
    for u in selF:
        if tgtF[u].startswith("Paper/LiteralReadings") and any(not tgtF[x].startswith("Paper/LiteralReadings") for x in revF[u]):
            tgtF[u]="Support/"+support_topic(u); changed=True
for u in selF:
    if tgtF[u]=="Support/LiteralSupport" and all(tgtF[x].startswith("Paper/LiteralReadings") for x in revF[u]):
        tgtF[u]="Paper/LiteralReadings"
import csv
with open(OUT+"/Bridge/Plan.csv","w",newline="",encoding="utf-8") as f:
    w=csv.writer(f); w.writerow(["unit","source","lines","stage","target","inventory_rows"])
    for u in sorted(selF,key=lambda u:(tgtF[u],modidx(u[0]),u[1])):
        rs=sorted(set(unit_rows.get(u,[]))|({primary[u]} if u in primary else set())|({cited[u]} if u in cited else set()),key=lambda r:(r.split(".")[0],int(r.split(".")[1])))
        w.writerow([owners_of(u)[0], u[0].replace(".","/")+".lean:%d"%u[1], UBY[u]["e"]-UBY[u]["s"]+1, 1 if u in S1SEL else 2, tgtF[u], ";".join(rs)])
c=collections.Counter(); cl=collections.Counter()
for u in selF: c[tgtF[u].split("/")[0]+"/"+tgtF[u].split("/")[1] if "/" in tgtF[u] else tgtF[u]]+=1; cl[tgtF[u].split("/")[0]+"/"+tgtF[u].split("/")[1]]+=UBY[u]["e"]-UBY[u]["s"]+1
for k in sorted(c): print(f"{c[k]:5d} {cl[k]:6d} {k}")
# left behind
allu=[u for u in ALLU]
lb=collections.Counter(); lbl=collections.Counter()
for u in allu:
    if u["id"] not in selF: lb[u["mod"]]+=1; lbl[u["mod"]]+=u["e"]-u["s"]+1
print("LEFT BEHIND")
for m in sorted(lb,key=lambda m:-lbl[m]): print(f"{lb[m]:5d} {lbl[m]:6d} {m}")
json.dump(dict(selF=["%s:%d"%u for u in selF]),open("full.json","w"))
