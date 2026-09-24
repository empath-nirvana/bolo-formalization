# Stage 2: stage 1, the deferred remarks of §§4–5, and the numbered results of the
# subsections listed in cfg.json's "stage2_sections", each with its record and alias.
exec(open("gen.py").read())

ORDER = CFG["order2"]
SHORT = {f: f.replace("Paper/", "").replace("/", "_") for f in ORDER}
SECFILE = {k: v["file"] for k, v in CFG["sections"].items()}

# ---------------------------------------------------------------- the results
RESULTS = {}      # row -> record
def is_conf(r): return r.startswith("3.")
def default_aliases(row, kind, name):
    """`TR.lemma_6_N` (`CONF.<kind>_3_N` for a [CONF] result), and the printed name `TR.«name»`"""
    if is_conf(row):
        return ["CONF.%s_%s" % (kind.lower(), row.replace(".", "_"))]
    out = ["TR.lemma_" + row.replace(".", "_")]
    if name: out.append("TR." + (name if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", name) else "«%s»" % name))
    return out
def parse_results(path, sec):
    cur = None
    for line in open(path, encoding="utf-8").read().split("\n"):
        if line.startswith("@@ "):
            parts = [x.strip() for x in line[3:].split("|")]
            row, kind, page, decls = parts[:4]
            name = parts[4] if len(parts) > 4 else ""
            ds = []
            for i, d in enumerate(x.strip() for x in decls.split(",") if x.strip()):
                if "=" in d:
                    n, *a = [x.strip() for x in d.split("=")]; ds.append((n, a))
                else:
                    ds.append((d, default_aliases(row, kind, name) if i == 0 else []))
            cur = dict(row=row, kind=kind, page=page, decls=ds, name=name, sec=sec,
                       file=SECFILE[sec], stmt=[], proof=[], remark=[], extra=[])
            RESULTS[row] = cur
        elif cur is None or not line.strip() and not cur["proof"]:
            continue
        elif line.startswith("+ "):
            k, n = line[2:].split(None, 1); cur["extra"].append((k, n.strip()))
        elif line.startswith("> "):
            cur["stmt"].append(line[2:])
        elif line.startswith("~ "):
            cur["remark"].append(line[2:])
        else:
            cur["proof"].append(line)
for sec in CFG["stage2_sections"]:
    parse_results("results/%s.txt" % sec, sec)
def nrow(r): return (is_conf(r),) + tuple(int(x) for x in r.split("."))

_seen = {}
for r, R0 in RESULTS.items():
    for n, al in R0["decls"]:
        for a in al:
            if a in _seen: raise Exception("alias %s given twice (%s, %s)" % (a, _seen[a], r))
            _seen[a] = r
PROWS = {}
for o in ROWS:
    if o["doc"].startswith("paper"):
        c = o["cells"]
        PROWS[o["row"]] = dict(kind=c[2], name=c[3], status=c[4].strip("`"), note=c[5] if len(c) > 5 else "")

# ---------------------------------------------------------------- selection
sel1, DEFERRED = stage1_selection()
ORDER1 = ORDER; ORDER = CFG["order"]
TGT1, _, _ = assign(sel1)          # stage 1's placement, kept
ORDER = ORDER1
RU = {}           # result unit -> row
DECL_UNIT = {}    # declaration name -> unit
for r in sorted(RESULTS, key=nrow):
    for n, a in RESULTS[r]["decls"]:
        if n not in D: raise Exception("no declaration %s for %s" % (n, r))
        u = unit_of_owner[own[n]]
        DECL_UNIT[n] = u
        RU.setdefault(u, r)
EXTRA = {}        # unit -> (row, "tw" | "lit" | "beside"): a declaration the record cites that is not the result
for r in sorted(RESULTS, key=nrow):
    for k, n in RESULTS[r]["extra"]:
        if n not in D: raise Exception("no declaration %s for %s" % (n, r))
        u = unit_of_owner[own[n]]
        DECL_UNIT[n] = u
        if u not in RU: EXTRA.setdefault(u, (r, k))
REMARK = {}       # remark unit -> definition row
for u in DEFERRED:
    REMARK[u] = sorted(unit_rows[u], key=rowkey)[0]
for r in CFG["remark_rows"]:
    for u, rs in unit_rows.items():
        if r in rs and u not in sel1 and u not in RU and D[owners_of(u)[0]]["kind"] == "thm":
            REMARK.setdefault(u, r)
sel = select(sel1 | set(RU) | set(REMARK) | set(EXTRA))

pre = {}
for u in sel:
    if u in RU: pre[u] = RESULTS[RU[u]]["file"]
    elif u in REMARK: pre[u] = CFG["remark_target"][REMARK[u]]
    elif u in EXTRA and EXTRA[u][1] == "lit": pre[u] = CFG["literal_target"][RESULTS[EXTRA[u][0]]["sec"]]
    elif u in EXTRA and EXTRA[u][1] in ("beside", "litbeside"): pre[u] = RESULTS[EXTRA[u][0]]["file"]
    elif u in sel1: pre[u] = TGT1[u] if TGT1[u].startswith("Paper") else None
    else: pre[u] = None
    for m, rx, f in CFG.get("literal_patterns", []):   # the configuration a literal reading builds
        if pre[u] is None and u[0] == m and any(re.fullmatch(rx, o) for o in owners_of(u)) and not any(
                u[0] == m2 and any(re.fullmatch(rx2, o) for o in owners_of(u)) for m2, rx2, t in CFG["topic_rules"]):
            pre[u] = f
    if pre[u] and pre[u].startswith("Paper") and pre[u] not in ORDER:
        raise Exception("no order for " + pre[u])

# A result (or remark) whose declaration an earlier paper file needs is declared in that
# file, ahead of its subsection; its record and alias stay in its own subsection's file.
HOME = dict(pre)
CLOSE = {}
def closure(u):
    if u not in CLOSE: CLOSE[u] = close({u}) & sel
    return CLOSE[u]
changed = True
while changed:
    changed = False
    for y in sel:
        f = pre[y]
        if not f or not f.startswith("Paper"): continue
        for x in closure(y):
            g = pre[x]
            if x != y and g and g.startswith("Paper") and pidx(g) > pidx(f):
                pre[x] = f; changed = True
HOISTED = {u: pre[u] for u in sel if pre[u] != HOME[u]}

STAGE2_TOPICS = True
tgt, inline, probs = assign(sel, pre, pin={u: TGT1[u] for u in sel1}, latest=True)
for p in probs: print("PROB", p)

# ---------------------------------------------------------------- records
def rel(f): return "`%s.lean`" % f
def label(r): return ("Lemma " + r) if r in RESULTS else ("row %s's theorem" % r)
def labels(rs):
    lem = [x for x in rs if x in RESULTS]; oth = [label(x) for x in rs if x not in RESULTS]
    out = []
    if lem:
        nums = lem[0] if len(lem) == 1 else ", ".join(lem[:-1]) + " and " + lem[-1]
        out.append(("Lemma " if len(lem) == 1 else "Lemmas ") + nums)
    return ", ".join(out + oth)
def lemma_title(r):
    R0 = RESULTS[r]
    t = "%s %s" % (R0["kind"], r)
    if R0["name"]: t += " (%s)" % R0["name"]
    return t
TAGRX = re.compile(r"`?\[(as printed[^\]]*|restricted:[^\]\n]*|variant[^\]]*|repair[^\]]*)\]`?")
def source_tags(n):
    u = DECL_UNIT[n]
    text = utext(u)
    head = text.split(":=")[0]
    return sorted(set("`[%s]`" % m.group(1).strip() for m in TAGRX.finditer(head)))
NOTE_DROP = re.compile(r"old carrier|`ResI`|ResI\b|`Model\.|`Resource\.|remains the|`BoLo\.(?!.*Fig16)", re.I)
def inventory_note(r):
    note = dehistory(PROWS[r]["note"])
    parts = re.split(r"(?<=[.;])\s+(?=[A-Z*(\[`])", note)
    return " ".join(p for p in parts if not NOTE_DROP.search(p)).strip()
def users_in(u, f):
    """rows of the results declared in file f (in their own file) whose Lean needs u"""
    out = set()
    for x in sel:
        if tgt[x] == f and x in RU and HOME[x] == f and x != u and u in closure(x): out.add(RU[x])
        if tgt[x] == f and x in REMARK and HOME[x] == f and x != u and u in closure(x): out.add(REMARK[x])
        if tgt[x] == f and x in EXTRA and x not in RU and x != u and u in closure(x): out.add(EXTRA[x][0])
    return sorted(out, key=nrow)
def al_txt(al):
    if not al: return ""
    return (", alias " if len(al) == 1 else ", aliases ") + ", ".join("`%s`" % a for a in al)
def lean_line(r, f):
    R0 = RESULTS[r]
    if not R0["decls"]:
        return "**Lean.** None in this repository."
    
    bits = []
    for n, a in R0["decls"]:
        u = DECL_UNIT[n]
        if tgt[u] != f and u in RU and RU[u] != r:
            tags = source_tags(n)
            bits.append("`%s`%s%s — the declaration of %s, in %s: the same statement, printed twice" % (
                n, al_txt(a), (", source tag " + " ".join(tags)) if tags else "",
                lemma_title(RU[u]), rel(tgt[u])))
            continue
        where = "" if tgt[u] == f else " — declared in %s, ahead of this subsection: the Lean of %s there needs it" % (
            rel(tgt[u]), labels(users_in(u, tgt[u])) or "a result")
        tags = source_tags(n)
        bits.append("`%s`%s%s%s" % (n, al_txt(a), (", source tag " + " ".join(tags)) if tags else "", where))
    out = "**Lean.** " + "; ".join(bits) + "."
    for k, head in (("beside", "Also here"), ("litbeside", "Literal reading, kept here"), ("tw", "Typed-world version"), ("lit", "Literal reading")):
        xs = [n for kk, n in R0["extra"] if kk == k and EXTRA.get(DECL_UNIT[n], (None,))[0] == r]
        if xs:
            out += "\n\n**%s.** %s." % (head, "; ".join("`%s`%s" % (n, "" if tgt[DECL_UNIT[n]] == f else ", in " + rel(tgt[DECL_UNIT[n]])) for n in xs))
    return out
def record(r, f):
    R0 = RESULTS[r]
    P = PROWS.get(r, {})
    out = ["## %s · `%s` %s · inventory `%s`" % (lemma_title(r), "[CONF]" if is_conf(r) else "[TR]", R0["page"], P.get("status", "—")), ""]
    out += ["> " + x for x in R0["stmt"]]
    out += ["", "**Printed proof, transcribed.** " + re.sub(r"^Proof\.\s*", "", "\n".join(R0["proof"]).strip())]
    if R0["remark"]: out += ["", "\n".join(R0["remark"])]
    out += ["", lean_line(r, f)]
    note = inventory_note(r) if r in PROWS else ""
    if note: out += ["", "**Inventory note** (source `docs/paper-inventory.md`, row %s). %s" % (r, note)]
    return "/-!\n" + "\n".join(out).rstrip() + "\n-/"
def def_record(r, f, units_elsewhere=()):
    info = DEFROWS[r]; tag = STATUS_TAG.get(info["status"], info["status"])
    out = ["### %s · %s · %s · `%s`" % (r, info["printed"], info["page"], tag), "", dehistory(info["note"])]
    for u in units_elsewhere:
        out += ["", "`%s` is declared in %s, ahead of this file: the Lean of %s there needs it." % (
            owners_of(u)[0], rel(tgt[u]), labels(users_in(u, tgt[u])) or "a result")]
    return "/-!\n" + "\n".join(out) + "\n-/"
def alias_lines(u):
    r = RU[u]
    ls = ["alias %s := %s" % (a, n) for n, al in RESULTS[r]["decls"] if DECL_UNIT[n] == u for a in al]
    return "\n".join(ls)

# rows homed in each paper file whose Lean is not there: records without a declaration
PSEUDO = collections.defaultdict(list)     # file -> [(key, text)]
for r, R0 in RESULTS.items():
    f = R0["file"]
    if not any(tgt[DECL_UNIT[n]] == f for n, a in R0["decls"]):
        txt = record(r, f)
        al = ["alias %s := %s" % (a, n) for n, als in R0["decls"] for a in als]
        if al: txt += "\n" + "\n".join(al)
        PSEUDO[f].append((rowkey(r), txt))
REMARK_ROWS = collections.defaultdict(list)
for u, r in REMARK.items(): REMARK_ROWS[r].append(u)
for r, us in REMARK_ROWS.items():
    f = CFG["remark_target"][r]
    if all(tgt[u] != f for u in us):
        PSEUDO[f].append((rowkey(r), def_record(r, f, [u for u in us])))
for f in PSEUDO: PSEUDO[f].sort()

STAGE2_FILES = (set(v["file"] for v in CFG["sections"].values()) | set(CFG["remark_target"].values())) - set(TGT1.values())
class Hook:
    def __init__(self):
        self.seen = collections.defaultdict(set); self.done = collections.defaultdict(set)
        self.inline_run = {}
        self.keys = {}
    def extra_edges(self):
        """an alias names its declaration, so a record's file imports the file declaring it"""
        e = collections.defaultdict(set)
        for r, R0 in RESULTS.items():
            for n, al in R0["decls"]:
                if al and tgt[DECL_UNIT[n]] != R0["file"]: e[R0["file"]].add(tgt[DECL_UNIT[n]])
        return e
    def passes_key(self, x):
        """a declaration a record cites does not pull the results it uses up to its record"""
        return not (x in EXTRA and x not in RU and x not in REMARK)
    def subkey(self, u):
        """a record's cited declarations follow the result, as far as Lean allows"""
        return 1 if (u in EXTRA and u not in RU and u not in REMARK) else 0
    def inherit_all(self, f):
        return f in STAGE2_FILES
    def row_of(self, u, f, default):
        if u in RU and HOME[u] == f: return RU[u]
        if u in EXTRA and not (u in RU or u in REMARK) and f.startswith("Paper"): return EXTRA[u][0]
        if u in REMARK and HOME[u] == f: return REMARK[u]
        if u in HOISTED and tgt[u] == f: return None
        if u not in sel1: return None
        return default(u)
    def pseudo_before(self, u, f):
        if not ((u in RU or u in REMARK) and HOME[u] == f): return []
        k = self.keys[u][0]
        out = []
        for i, (kk, txt) in enumerate(PSEUDO.get(f, [])):
            if kk < k and i not in self.done[f]:
                self.done[f].add(i); out.append(txt)
        if out: self.inline_run[f] = None
        return out
    def pseudo_end(self, f):
        out = [txt for i, (kk, txt) in enumerate(PSEUDO.get(f, [])) if i not in self.done[f]]
        return out
    def before(self, u, f):
        if u in sel1: return None
        if u in EXTRA and not (u in RU or u in REMARK):
            r, k = EXTRA[u]
            if k == "beside" and tgt[u] == RESULTS[r]["file"]:
                self.inline_run[f] = None
                return "/-! A declaration the record of %s cites. -/" % lemma_title(r)
            if k == "litbeside" and tgt[u] == RESULTS[r]["file"]:
                self.inline_run[f] = None
                if (r, k) in self.seen[f]: return "/-! %s, the literal reading, continued. -/" % lemma_title(r)
                self.seen[f].add((r, k))
                return ("/-!\n### %s — the literal reading, kept beside it\n\nThe same statement at the printed "
                        "definitions read literally, as the record above describes; `Paper/LiteralReadings/` holds what "
                        "measures it.  Nothing in the paper tree depends on it.\n-/") % lemma_title(r)
            what = {"tw": "typed-world version", "lit": "literal reading", "beside": "cited declaration"}[k]
            self.inline_run[f] = None
            if (r, k) in self.seen[f]: return "/-! %s, %s, continued. -/" % (lemma_title(r), what)
            self.seen[f].add((r, k))
            return ("/-!\n### %s — %s\n\nThe printed statement, the printed proof and the adjudication are in "
                    "%s, under the record of %s.\n-/") % (lemma_title(r), what, rel(RESULTS[r]["file"]), lemma_title(r))
        if u in RU and HOME[u] == f:
            self.inline_run[f] = None
            r = RU[u]
            if r in self.seen[f]: return "/-! %s, continued. -/" % lemma_title(r)
            self.seen[f].add(r); return record(r, f)
        if u in REMARK and HOME[u] == f:
            self.inline_run[f] = None
            r = REMARK[u]
            if r in self.seen[f] or any(tgt[x] == f and r in unit_rows.get(x, []) for x in sel1):
                self.seen[f].add(r); return "/-!\nRow %s, continued.\n-/" % r
            self.seen[f].add(r); return def_record(r, f)
        if u in HOISTED and tgt[u] == f:
            self.inline_run[f] = None
            users = users_in(u, f)
            if u in RU:
                r = RU[u]
                return ("/-!\n### %s's declaration, ahead of its subsection\n\n`[TR]` prints %s in %s (%s).  "
                        "The Lean of %s in this file needs it, so it is declared here; its statement, printed proof "
                        "and alias are in %s.\n-/") % (lemma_title(r), lemma_title(r), CFG["sections"][RESULTS[r]["sec"]]["title"].split(" ")[0],
                        RESULTS[r]["page"], labels(users) or "a result", rel(HOME[u]))
            r = REMARK[u]
            return ("/-!\n### Row %s's theorem `%s`, ahead of its file\n\nA remark on a printed definition of `[TR]` §%s; "
                    "its proof uses results of §6, and the Lean of %s in this file needs it, so it is declared here.  "
                    "The row is recorded in %s.\n-/") % (r, owners_of(u)[0], r.split(".")[0],
                    labels(users) or "a result", rel(HOME[u]))
        if f.startswith("Paper"):
            users = users_in(u, f)
            key = tuple(users[:1])
            if self.inline_run.get(f) == key: return ""
            self.inline_run[f] = key
            return "/-! `[about ours]` — what the Lean of %s needs; the paper prints nothing here. -/" % (
                label(users[0]) if users else "the results below")
        return None
    def after(self, u, f):
        if u in RU and HOME[u] == f: return alias_lines(u) or None
        return None

# ---------------------------------------------------------------- emission
banners = {}
exec(open("banners.py").read())
banners["__support__"] = SUPPORT_BANNER; banners["__what__"] = SUPPORT_WHAT
order, g, written, strip = emit(sel, tgt, banners, hook=Hook())
json.dump(dict(order=order, tgt={"%s:%d" % u: t for u, t in tgt.items()}, strip=["%s:%d" % u for u in strip],
               hoisted={"%s:%d" % u: t for u, t in HOISTED.items()}), open("stage2.json", "w"), indent=0)
extra = []
for r, R0 in sorted(RESULTS.items(), key=lambda t: nrow(t[0])):
    for n, als in R0["decls"]:
        for a in als:
            u = DECL_UNIT[n]
            extra.append(dict(name=a, source_name=n, private="no", kind=D[n]["kind"], target=R0["file"] + ".lean",
                              source=u[0].replace(".", "/") + ".lean:" + D[own[n]]["s"].split(":")[0], rows=r))
def rows_of(u):
    rs = set(unit_rows.get(u, []))
    rs |= {r for r, R0 in RESULTS.items() for n, a in R0["decls"] if DECL_UNIT[n] == u}
    if u in EXTRA: rs.add(EXTRA[u][0])
    return ";".join(sorted(rs, key=rowkey))
rows = write_bridge(sel, tgt, strip, OUT + "/Bridge/Names.csv", extra=extra, rows_of=rows_of)
print("files", len(order)); print("bridge rows", len(rows), "aliases", len(extra), "hoisted", len(HOISTED), "inline", len(inline))

# ---------------------------------------------------------------- Paper/INDEX.md
def short(n): return n[5:] if n.startswith("BoCa.") else n
def cell(s): return s.replace("|", "\\|").replace("\n", " ")
DEFNUM = {"5.61": "Definition 6.1", "5.65": "Definition 6.2", "5.66": "Definition 6.3"}
L = ["# Index of `[TR]` and `[CONF]`", "",
     "Generated by `tools/extract/stage2.py`; do not edit.  Every numbered result of `[TR]` §6 and "
     "`[CONF]` §3, and every row of the source's `docs/definition-inventory.md` (the printed "
     "definitions of `[TR]` §§1–5 and Definitions 6.1–6.3), with the file and the declarations "
     "that carry it.  Declaration names are the source's without the `BoCa.` prefix; paths are "
     "relative to the repository root.", "",
     "`[TR]` numbers Definitions and Lemmas in two sequences: Definitions 6.1, 6.2 and 6.3 are "
     "definition rows 5.61, 5.65 and 5.66, listed under *Definitions* below.", ""]
nodecl = []
L += ["## Numbered results", "",
      "| result | name | status | file | declaration | aliases |", "|---|---|---|---|---|---|"]
for r in sorted(RESULTS, key=nrow):
    R0 = RESULTS[r]; P = PROWS.get(r, {})
    title = ("`[CONF]` " if is_conf(r) else "") + "%s %s" % (R0["kind"], r)
    if not R0["decls"]:
        nodecl.append((title, "none on the printed carrier: untranscribed (see its record in `%s.lean`)" % R0["file"]))
        L.append("| %s | %s | `%s` | `%s.lean` | **none — untranscribed** | — |" % (title, cell(R0["name"]), P.get("status", "—"), R0["file"]))
        continue
    files = sorted(set(tgt[DECL_UNIT[n]] for n, a in R0["decls"]))
    decls = ", ".join("`%s`" % short(n) for n, a in R0["decls"])
    als = ", ".join("`%s`" % a for n, al in R0["decls"] for a in al)
    tws = [n for k, n in R0["extra"] if k == "tw"]
    if tws: decls += " (typed world: %s)" % ", ".join("`%s`" % short(n) for n in tws)
    L.append("| %s | %s | `%s` | %s | %s | %s |" % (title, cell(R0["name"]), P.get("status", "—"),
             ", ".join("`%s.lean`" % f for f in files), decls, als or "—"))
L += ["", "## Definitions", "",
      "| row | printed | tag | file | declarations |", "|---|---|---|---|---|"]
for r in sorted(DEFROWS, key=rowkey):
    info = DEFROWS[r]; tag = STATUS_TAG.get(info["status"], info["status"])
    us = [u for u in sel if r in unit_rows.get(u, [])]
    label = r + (" (%s)" % DEFNUM[r] if r in DEFNUM else "")
    if not us:
        nodecl.append(("row " + label, ("no printed counterpart; the row records what the source's legacy carrier added, "
                       "and this repository does not carry that carrier") if "no printed counterpart" in info["printed"]
                       else "its Lean is on the source's legacy carrier only, which this repository does not carry"))
        L.append("| %s | %s | `%s` | — | **none** |" % (label, cell(info["printed"]), tag)); continue
    files = sorted(set(tgt[u] for u in us))
    decls = sorted(set(short(owners_of(u)[0]) for u in us))
    L.append("| %s | %s | `%s` | %s | %s |" % (label, cell(info["printed"]), tag,
             ", ".join("`%s.lean`" % f for f in files), ", ".join("`%s`" % d for d in decls)))
L += ["", "## Repaired definitions", "",
      "Every definition row tagged `[repair]`: the library's reading departs from the print, and the "
      "row's comment in its file gives the adjudication and the sentences of the paper that ground it.  "
      "The headline results additionally hold at the typed world, the repair of rows 4.4–4.14 and 5.33 "
      "recorded in `Paper/S4_LogicalRelation/Definitions.lean` and `Paper/S5_Model/Definitions.lean` and "
      "declared in `Support/TypedWorld/`.", ""]
for r in sorted(DEFROWS, key=rowkey):
    info = DEFROWS[r]
    if info["status"] != "repair": continue
    us = [u for u in sel if r in unit_rows.get(u, [])]
    files = sorted(set(tgt[u] for u in us))
    L.append("* **%s** %s — %s" % (r, cell(info["printed"]), ", ".join("`%s.lean`" % f for f in files) or "no declaration here"))
L += ["", "## Rows with no declaration", ""]
L += ["* %s — %s." % (a, b) for a, b in nodecl] if nodecl else ["None."]
open(OUT + "/Paper/INDEX.md", "w").write("\n".join(L) + "\n")
print("index", len(RESULTS), "results", len(DEFROWS), "definition rows", len(nodecl), "without declaration")
