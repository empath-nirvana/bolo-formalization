# Stage 2: stage 1, the deferred remarks of §§4–5, and the numbered results of the
# subsections listed in cfg.json's "stage2_sections", each with its record and alias.
exec(open("gen.py").read())

ORDER = CFG["order2"]
SHORT = {f: f.replace("Paper/", "").replace("/", "_") for f in ORDER}
SECFILE = {k: v["file"] for k, v in CFG["sections"].items()}

# ---------------------------------------------------------------- the results
RESULTS = {}      # row -> record
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
                    n, a = d.split("=", 1); ds.append((n.strip(), a.strip()))
                else:
                    ds.append((d, "TR.lemma_" + row.replace(".", "_") if i == 0 else None))
            cur = dict(row=row, kind=kind, page=page, decls=ds, name=name, sec=sec,
                       file=SECFILE[sec], stmt=[], proof=[], remark=[])
            RESULTS[row] = cur
        elif cur is None or not line.strip() and not cur["proof"]:
            continue
        elif line.startswith("> "):
            cur["stmt"].append(line[2:])
        elif line.startswith("~ "):
            cur["remark"].append(line[2:])
        else:
            cur["proof"].append(line)
for sec in CFG["stage2_sections"]:
    parse_results("results/%s.txt" % sec, sec)
def nrow(r): return tuple(int(x) for x in r.split("."))

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
REMARK = {}       # remark unit -> definition row
for u in DEFERRED:
    REMARK[u] = sorted(unit_rows[u], key=rowkey)[0]
for r in CFG["remark_rows"]:
    for u, rs in unit_rows.items():
        if r in rs and u not in sel1 and u not in RU and D[owners_of(u)[0]]["kind"] == "thm":
            REMARK.setdefault(u, r)
sel = select(sel1 | set(RU) | set(REMARK))

pre = {}
for u in sel:
    if u in RU: pre[u] = RESULTS[RU[u]]["file"]
    elif u in REMARK: pre[u] = CFG["remark_target"][REMARK[u]]
    elif u in sel1: pre[u] = TGT1[u] if TGT1[u].startswith("Paper") else None
    else: pre[u] = None
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
def labels(rs): return ", ".join(label(x) for x in rs)
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
    return sorted(out, key=nrow)
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
                n, (", alias `%s`" % a) if a else "", (", source tag " + " ".join(tags)) if tags else "",
                lemma_title(RU[u]), rel(tgt[u])))
            continue
        where = "" if tgt[u] == f else " — declared in %s, ahead of this subsection: the Lean of %s there uses it" % (
            rel(tgt[u]), labels(users_in(u, tgt[u])) or "a result")
        tags = source_tags(n)
        bits.append("`%s`%s%s%s" % (n, (", alias `%s`" % a) if a else "", (", source tag " + " ".join(tags)) if tags else "", where))
    return "**Lean.** " + "; ".join(bits) + "."
def record(r, f):
    R0 = RESULTS[r]
    P = PROWS.get(r, {})
    out = ["## %s · `[TR]` %s · inventory `%s`" % (lemma_title(r), R0["page"], P.get("status", "—")), ""]
    out += ["> " + x for x in R0["stmt"]]
    out += ["", "**Printed proof, transcribed.** " + "\n".join(R0["proof"]).strip()]
    if R0["remark"]: out += ["", "\n".join(R0["remark"])]
    out += ["", lean_line(r, f)]
    note = inventory_note(r) if r in PROWS else ""
    if note: out += ["", "**Inventory note** (source `docs/paper-inventory.md`, row %s). %s" % (r, note)]
    return "/-!\n" + "\n".join(out).rstrip() + "\n-/"
def def_record(r, f, units_elsewhere=()):
    info = DEFROWS[r]; tag = STATUS_TAG.get(info["status"], info["status"])
    out = ["### %s · %s · %s · `%s`" % (r, info["printed"], info["page"], tag), "", dehistory(info["note"])]
    for u in units_elsewhere:
        out += ["", "`%s` is declared in %s, ahead of this file: the Lean of %s there uses it." % (
            owners_of(u)[0], rel(tgt[u]), labels(users_in(u, tgt[u])) or "a result")]
    return "/-!\n" + "\n".join(out) + "\n-/"
def alias_lines(u):
    r = RU[u]
    ls = ["alias %s := %s" % (a, n) for n, a in RESULTS[r]["decls"] if a and DECL_UNIT[n] == u]
    return "\n".join(ls)

# rows homed in each paper file whose Lean is not there: records without a declaration
PSEUDO = collections.defaultdict(list)     # file -> [(key, text)]
for r, R0 in RESULTS.items():
    f = R0["file"]
    if not any(tgt[DECL_UNIT[n]] == f for n, a in R0["decls"]):
        txt = record(r, f)
        al = ["alias %s := %s" % (a, n) for n, a in R0["decls"] if a]
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
    def inherit_all(self, f):
        return f in STAGE2_FILES
    def row_of(self, u, f, default):
        if u in RU and HOME[u] == f: return RU[u]
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
                        "The Lean of %s in this file uses it, so it is declared here; its statement, printed proof "
                        "and alias are in %s.\n-/") % (lemma_title(r), lemma_title(r), CFG["sections"][RESULTS[r]["sec"]]["title"].split(" ")[0],
                        RESULTS[r]["page"], labels(users) or "a result", rel(HOME[u]))
            r = REMARK[u]
            return ("/-!\n### Row %s's theorem `%s`, ahead of its file\n\nA remark on a printed definition of `[TR]` §%s; "
                    "its proof uses results of §6, and the Lean of %s in this file uses it, so it is declared here.  "
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
    for n, a in R0["decls"]:
        if a:
            u = DECL_UNIT[n]
            extra.append(dict(name=a, source_name=n, private="no", kind=D[n]["kind"], target=R0["file"] + ".lean",
                              source=u[0].replace(".", "/") + ".lean:" + D[own[n]]["s"].split(":")[0], rows=r))
def rows_of(u):
    rs = set(unit_rows.get(u, []))
    rs |= {r for r, R0 in RESULTS.items() for n, a in R0["decls"] if DECL_UNIT[n] == u}
    return ";".join(sorted(rs, key=rowkey))
rows = write_bridge(sel, tgt, strip, OUT + "/Bridge/Names.csv", extra=extra, rows_of=rows_of)
print("files", len(order)); print("bridge rows", len(rows), "aliases", len(extra), "hoisted", len(HOISTED), "inline", len(inline))
