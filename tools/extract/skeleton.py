import json,re,csv,os
OUT=os.path.abspath("../..")
rows=json.load(open("rows.json"))
plan={}
for r in csv.DictReader(open(OUT+"/Bridge/Plan.csv")):
    for x in r["inventory_rows"].split(";"):
        if x and r["target"].endswith("/Lemmas") or r["target"].endswith("CONF/Results"):
            plan.setdefault(x,[]).append(r["unit"])
SUBS=[("6.1","S6_1_StandardLemmas","Standard Lemmas","pp. 6–8",(1,15),
 "*\"There's no strict definition, but lemmas feel 'standard' when their statement doesn't unfold resources or definitions, and don't include any particularly unusual/custom operations.\"*"),
 ("6.2","S6_2_NonStandardLemmas","Non-standard Lemmas","pp. 8–22",(16,63),""),
 ("6.3","S6_3_FrameAndAntiFrame","Frame and Anti-Frame","pp. 22–27",(64,66),""),
 ("6.4","S6_4_StandardEntailments","Standard Entailments","pp. 27–29",(67,95),""),
 ("6.5","S6_5_NonStandardEntailments","Non-standard Entailments","pp. 29–32",(96,119),""),
 ("6.6","S6_6_ReborrowingEntailments","Reborrowing Entailments","pp. 32–35",(120,134),""),
 ("6.7","S6_7_WeakestPreconditionRules","Weakest Precondition Rules","pp. 35–40",(135,150),""),
 ("6.8","S6_8_FundamentalProperty","Fundamental Property","pp. 40–49",(151,176),"")]
prow={o["row"]:o for o in rows if o["doc"].startswith("paper")}
def ln(r):
    o=prow.get(r)
    if not o: return None
    c=o["cells"]; kind=c[2].strip(); name=c[3].strip(); st=c[4].strip()
    tgt=", ".join("`%s`"%u.replace("BoCa.","") for u in plan.get(r,[])[:3]) or "—"
    return "* **%s %s**%s — %s; planned: %s" % (kind, r, (" (%s)"%name) if name else "", st, tgt)
BUILT=set(json.load(open("cfg.json"))["stage2_sections"])
for key,d,title,pages,(a,b),intro in SUBS:
    if d.split("_")[0]+"_"+d.split("_")[1] in BUILT: continue
    items=[ln("6.%d"%n) for n in range(a,b+1)]
    items=[x for x in items if x]
    txt="/-!\n# [TR] §%s %s  (%s)\n\n%s%s\n\n**Stage 2.**  This file will hold the numbered results of the subsection, in printed order,\neach under its printed statement and proof, with the Lean declaration moved from the\nsource and a numbered alias.  The results, with the inventory's status and the\ndeclaration `Bridge/Plan.csv` assigns to each:\n\n%s\n-/\n" % (key,title,pages,intro,"\n" if intro else "", "\n".join(items))
    os.makedirs(OUT+"/Paper/"+d,exist_ok=True)
    open(OUT+"/Paper/%s/Lemmas.lean"%d,"w").write(txt)
conf=[o for o in rows if o["doc"].startswith("paper") and o["row"].startswith("3.")]
items=["* **%s %s** (%s) — %s" % (o["cells"][2].strip(),o["row"],o["cells"][3].strip(),o["cells"][4].strip()) for o in conf]
txt="""/-!
# [CONF] §3 — the conference paper's own numbered results

[CONF] numbers three results.  3.1 is [TR] 6.151 (the Fundamental Property,
`Paper/S6_8_FundamentalProperty/Lemmas.lean`).  3.2 and 3.3 are adequacy;
neither document prints a proof of either.  Stage 2 moves their Lean
statements and proofs here, with `Fig16.LogRel.Typed.adequacy` (6.151 composed
with 3.3).

%s
-/
""" % "\n".join(items)
os.makedirs(OUT+"/Paper/CONF",exist_ok=True)
open(OUT+"/Paper/CONF/Results.lean","w").write(txt)
print("ok")
