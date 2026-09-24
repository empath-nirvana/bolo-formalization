# Generator: selects units, assigns them to target files, emits Lean.
import sys, os, json
exec(open("src.py").read())
OUT = os.path.abspath("../..")
CFG = json.load(open("cfg.json"))

# ---------------------------------------------------------------- units
ALLU = []
for mod in sorted(set(b[0] for b in blocks)):
    for u in scan(mod):
        u["id"] = (mod, u["s"])
        ALLU.append(u)
UBY = {u["id"]: u for u in ALLU}
unit_of_block = {}
for u in ALLU:
    for b in u["blocks"]:
        unit_of_block[b] = u["id"]
unit_of_owner = {o: unit_of_block[block[o]] for o in block}
def owners_of(uid):
    return [m for b in UBY[uid]["blocks"] for m in blocks[b]["members"]]
udeps = collections.defaultdict(set)
for u in ALLU:
    for o in owners_of(u["id"]):
        for d in odeps.get(o, ()):
            if d in unit_of_owner and unit_of_owner[d] != u["id"]:
                udeps[u["id"]].add(unit_of_owner[d])
def utext(uid):
    u = UBY[uid]; L = lines(u["mod"])
    return "\n".join(L[u["s"] - 1:u["e"]])

LEGACY = set("BoCa." + m for m in CFG["legacy"])

# ---------------------------------------------------------------- selection
def close(roots):
    seen = set(); st = list(roots)
    while st:
        x = st.pop()
        if x in seen: continue
        seen.add(x); st.extend(udeps[x])
    return seen

def notation_target(uid):
    """a notation unit's denoted function, resolved in its namespace"""
    t = utext(uid)
    m = re.search(r"=>\s*([\w.Ͱ-Ͽἀ-῿'₀-₉!?]+)", t)
    if not m: return None
    nm = m.group(1); ns = UBY[uid]["ctx"]["ns"]
    for k in range(len(ns), -1, -1):
        c = ".".join(ns[:k] + [nm])
        if c in unit_of_owner: return unit_of_owner[c]
    return None

NOTATION = {}
for u in ALLU:
    t = utext(u["id"])
    if re.match(r"\s*(@\[[^\]]*\]\s*)?(scoped |local )?(infix|infixl|infixr|prefix|postfix|notation)\b", t):
        tgt = notation_target(u["id"])
        if tgt: NOTATION[u["id"]] = tgt

def ucode(uid):
    u = UBY[uid]; L = lines(u["mod"])
    return "\n".join(c for i, c in strip_comments(L[u["s"] - 1:u["e"]]))
NOTSYM = {}
for n, t in NOTATION.items():
    udeps[n].add(t)
    syms = [x.strip() for x in re.findall(r'"([^"]+)"', utext(n))]
    syms = [x for x in syms if x]
    NOTSYM[n] = syms[0]
for u in ALLU:
    if u["mod"] in CFG["no_mathlib"] or u["id"] in NOTATION: continue
    code = ucode(u["id"])
    for n, sym in NOTSYM.items():
        if n[0] in LEGACY: continue
        if sym in code and n != u["id"] and NOTATION[n] != u["id"]:
            udeps[u["id"]].add(n)

# a tactic macro leaves no trace in the terms that use it: a unit whose text names it needs it
TACMACRO = {}
for u in ALLU:
    if u["mod"] in LEGACY: continue
    m = re.match(r'\s*(?:@\[[^\]]*\]\s*)?(?:local |scoped )?macro\s+"([^"]+)"[^\n]*:\s*tactic', ucode(u["id"]))
    if m: TACMACRO[u["id"]] = re.compile(r"(?<![\w.])" + re.escape(m.group(1)) + r"(?![\w'])")
for u in ALLU:
    if u["mod"] in LEGACY or u["id"] in TACMACRO: continue
    code = ucode(u["id"])
    for t, rx in TACMACRO.items():
        if rx.search(code): udeps[u["id"]].add(t)

SIMP = [u["id"] for u in ALLU if re.search(r"@\[[^\]]*\bsimp\b", ucode(u["id"]).split(":=")[0])
        and u["mod"] not in LEGACY]

# syntactic references: names a tactic mentions that need not survive into the term
TACLIST = re.compile(r"\b(?:simp|simp only|dsimp|dsimp only|simp_all|simp_all only|simpa|simpa only|rw|rewrite|rwa|erw|simp_rw|nth_rw \d+|nth_rewrite \d+|unfold|delta|conv)\b[^\[\n]*\[([^\]]*)\]")
UNFOLD = re.compile(r"\b(?:unfold|delta)\s+((?:[\w.'₀-₉]+\s*)+)")
IDENT = re.compile(r"[A-Za-z_\u0370-\u03ff\u1d00-\u1dbf\u2070-\u209f\u1f00-\u1fff][\w.'₀-₉!?\u0370-\u03ff\u2070-\u209f]*")
def open_nss(ctx):
    out = []
    for cmd, path in ctx["opens"]:
        try: items = parse_open(cmd)
        except Exception: continue
        for kind, nm, names in items:
            full = resolve_ns(nm, path)
            if full and kind == "plain": out.append(full)
    return out
def syn_resolve(tok, ctx):
    path = ctx["ns"]
    cands = [".".join(path[:k] + [tok]) for k in range(len(path), -1, -1)]
    cands += [o + "." + tok for o in open_nss(ctx)]
    for c in cands:
        if c in unit_of_owner: return unit_of_owner[c]
        if c in own and own[c]: return unit_of_owner[own[c]]
    return None
for u in ALLU:
    if u["mod"] in LEGACY: continue
    code = ucode(u["id"])
    toks = set()
    for m in TACLIST.finditer(code):
        for t in re.split(r"[,\s←]+", m.group(1)):
            t = t.strip().lstrip("←").strip()
            if IDENT.fullmatch(t or "-"): toks.add(t)
    for m in UNFOLD.finditer(code):
        for t in m.group(1).split(): toks.add(t)
    ctx = U_ctx = u["ctx"]
    for t in toks:
        d = syn_resolve(t, ctx)
        if d and d != u["id"]: udeps[u["id"]].add(d)


SIMPSET = set(SIMP)
def select(root_units):
    sel = close(root_units)
    while True:
        add = set()
        for n, tgt in NOTATION.items():
            if tgt in sel and n not in sel: add.add(n)
        for s in SIMP:
            if s not in sel and udeps[s] <= sel and UBY[s]["mod"] not in LEGACY:
                # only lemmas about selected objects
                add.add(s)
        for x in CFG.get("extra_units", []):
            pass
        if not add: return sel
        sel = close(sel | add)

# ---------------------------------------------------------------- rows
ROWS = json.load(open("rows.json"))
DEFROWS = {}
for o in ROWS:
    if not o["doc"].startswith("def"): continue
    c = o["cells"]
    DEFROWS[o["row"]] = dict(row=o["row"], printed=c[2], page=c[3], lean=c[4],
                            status=c[5].strip("`"), note=c[6])
def rowkey(r):
    a, b = r.split("."); return (int(a), int(b))
names_all = set(D)
def resolve_full(t):
    if t in names_all: return {t}
    return suffix.get(t, set())
unit_rows = collections.defaultdict(list)   # uid -> [row ids]
for r, info in DEFROWS.items():
    for t in re.findall(r"`([^`]*)`", info["lean"]):
        if not t.startswith("BoCa."): continue
        for n in resolve_full(t):
            if own.get(n) and D[n]["mod"] not in LEGACY:
                uid = unit_of_owner[own[n]]
                if r not in unit_rows[uid]: unit_rows[uid].append(r)

SECDIR = CFG["secdir"]
def paper_target(uid):
    """target for a unit that implements a printed row, or None"""
    if uid[0] in CFG.get("support_modules", []): return None
    rs = [r for r in unit_rows.get(uid, []) if DEFROWS[r]["status"] != "plumbing"]
    if not rs: return None
    rs.sort(key=rowkey)
    r = rs[0]
    ov = CFG["row_target"].get(r)
    if ov == "SUPPORT": return None
    if ov: return ov
    return SECDIR[r.split(".")[0]] + "/Definitions"

STAGE2_TOPICS = False
def support_topic(uid):
    if STAGE2_TOPICS:
        for m, a, b, t in CFG.get("stage2_topic_ranges", []):
            if uid[0] == m and a <= uid[1] <= b: return t
    for m, rx, t in CFG.get("topic_rules", []):
        if uid[0] == m and any(re.fullmatch(rx, o) for o in owners_of(uid)): return t
    for m, a, b, t in CFG.get("topic_ranges", []):
        if uid[0] == m and a <= uid[1] <= b: return t
    return CFG["topic"].get(uid[0], "Misc")

# ---------------------------------------------------------------- layering
MODORDER = [l.split()[1] for l in open(SRC + "BoCa.lean") if l.startswith("import ")]
def modidx(m):
    if m in CFG.get("mod_priority", {}): return CFG["mod_priority"][m]
    return MODORDER.index(m) if m in MODORDER else 999
ORDER = CFG["order"]
def pidx(f): return ORDER.index(f)
SHORT = {f: f.split("/")[1].split("_")[0] if f.startswith("Paper/S") else f.split("/")[-1] for f in ORDER}
SHORT["Paper/S6_2_NonStandardLemmas/Definitions"] = "S6_2"
SHORT["Paper/LiteralReadings/S4_LogicalRelation"] = "Literal"
for f in ORDER:
    if f.endswith("/Remarks"): SHORT[f] = SHORT.get(f, "") + "R"

def assign(sel, pre=None, pin=None, latest=False):
    """pin: units whose target is given and kept (stage 1's placement, when stage 2 runs)"""
    pinned = pin or {}
    tgt = {}
    for u in sel:
        tgt[u] = pre[u] if pre is not None else paper_target(u)
        if tgt[u] and tgt[u] not in ORDER and not tgt[u].startswith("Support/"):
            raise Exception("no order for " + tgt[u])
    # fixed support targets (e.g. Interpreter) are treated as support with a given file
    fixed = {u: t for u, t in tgt.items() if t and t.startswith("Support/")}
    for u in fixed: tgt[u] = None
    dep = {u: [d for d in udeps[u] if d in sel] for u in sel}
    rev = collections.defaultdict(list)
    for u in sel:
        for d in dep[u]: rev[d].append(u)
    sys.setrecursionlimit(100000)
    lo_c, hi_c = {}, {}
    def lo(u):
        if u in lo_c: return lo_c[u]
        lo_c[u] = -1
        r = -1
        for d in dep[u]:
            r = max(r, pidx(tgt[d]) if tgt[d] else lo(d))
        lo_c[u] = r; return r
    def hi(u):
        if u in hi_c: return hi_c[u]
        hi_c[u] = 99
        r = 99
        for x in rev[u]:
            r = min(r, pidx(tgt[x]) if tgt[x] else hi(x))
        hi_c[u] = r; return r
    inline = {}
    probs = []
    for u in sel:
        if tgt[u] is None and u not in pinned:
            l, h = lo(u), hi(u)
            if l >= h:
                if l > h: probs.append(("sandwich>", u, l, h))
                inline[u] = ORDER[h]
    for u, f in inline.items(): tgt[u] = f
    # paper-paper violations
    for u in sel:
        if tgt[u] and tgt[u] in ORDER:
            for d in dep[u]:
                x = pidx(tgt[d]) if tgt[d] in ORDER else (lo(d) if tgt[d] is None else -1)
                if x > pidx(tgt[u]): probs.append(("viol", u, tgt[u], d, tgt[d]))
    # support files
    bytopic = collections.defaultdict(list)
    for u in sel:
        if tgt[u] is None and u not in pinned: bytopic[support_topic(u)].append(u)
    for t, us in bytopic.items():
        if latest:
            # as few layers as the intervals allow, each unit in the latest layer it fits
            H = lambda u: min(hi(u), len(ORDER))   # nothing in the paper tree needs it: after the last file
            pts = []
            for u in sorted(us, key=H):
                if not any(lo(u) <= p < H(u) for p in pts): pts.append(H(u) - 1)
            layer = {u: max(p for p in pts if lo(u) <= p < H(u)) for u in us}
            for p in sorted(set(layer.values())):
                name = "Support/" + t if len(pts) == 1 else "Support/" + t + "@After:" + (
                    "END" if p == len(ORDER) - 1 else ORDER[p])
                name = CFG.get("support_names", {}).get(name, name)
                if "@" in name: probs.append(("unnamed support layer", name))
                for u in us:
                    if layer[u] == p: tgt[u] = name
            continue
        # greedy: group units (by increasing lo) while max lo < min hi
        us.sort(key=lambda u: (lo(u), hi(u)))
        groups = []; cur = []; clo = -1; chi = 99
        for u in us:
            nlo, nhi = max(clo, lo(u)), min(chi, hi(u))
            if cur and nlo >= nhi:
                groups.append((cur, clo)); cur = []; nlo, nhi = lo(u), hi(u)
            cur.append(u); clo, chi = nlo, nhi
        groups.append((cur, clo))
        for us2, L in groups:
            name = "Support/" + t if len(groups) == 1 else \
                "Support/" + t + "@" + ("Base" if L < 0 else "After:" + ORDER[L])
            name = CFG.get("support_names", {}).get(name, name)
            if "@" in name: probs.append(("unnamed support layer", name))
            for u in us2: tgt[u] = name
    for u, t in pinned.items(): tgt[u] = t
    # an attribute-only lemma (simp) goes with its latest dependency, emitted as early as it can be
    g = file_graph([u for u in sel if not (u in SIMPSET and not rev[u])], tgt)
    fo = topo_files(sorted(set(tgt[u] for u in sel)), g)
    for u in sel:
        if u in SIMPSET and not rev[u] and dep[u] and u not in pinned:
            tgt[u] = max((tgt[d] for d in dep[u]), key=fo.index)
    return tgt, inline, probs

def file_graph(sel, tgt):
    g = collections.defaultdict(set)
    for u in sel:
        for d in udeps[u]:
            if d in sel and tgt[d] != tgt[u]: g[tgt[u]].add(tgt[d])
    return g

def sccs(nodes, g):
    idx = {}; low = {}; st = []; on = set(); out = []; c = [0]
    def dfs(v):
        idx[v] = low[v] = c[0]; c[0] += 1; st.append(v); on.add(v)
        for w in g.get(v, ()):
            if w not in idx: dfs(w); low[v] = min(low[v], low[w])
            elif w in on: low[v] = min(low[v], idx[w])
        if low[v] == idx[v]:
            comp = []
            while True:
                w = st.pop(); on.discard(w); comp.append(w)
                if w == v: break
            out.append(comp)
    for v in nodes:
        if v not in idx: dfs(v)
    return out

# ---------------------------------------------------------------- emission
def topo_files(files, g):
    order = []; seen = set()
    def visit(f):
        if f in seen: return
        seen.add(f)
        for d in sorted(g.get(f, ())): visit(d)
        order.append(f)
    for f in sorted(files, key=lambda f: (ORDER.index(f) if f in ORDER else 50, f)): visit(f)
    return order

BINDER = re.compile(r"[({\[⦃]\s*([^:(){}\[\]⦃⦄]*?)\s*(?::|[)}\]⦄])")
def var_names(cmd):
    ns = set()
    for m in BINDER.finditer(cmd[len("variable"):]):
        for w in m.group(1).split():
            if re.match(r"^[\w'₀-₉]+$", w): ns.add(w)
    return ns

def unit_sort(sel_file, tgt, f, row_of, inherit_all=False, keys_out=None, passes=None, subkey=None):
    """topological order of the units of file f, printed rows first where possible"""
    us = [u for u in sel_file]
    S = set(us)
    dep = {u: [d for d in udeps[u] if d in S] for u in us}
    rev = collections.defaultdict(list)
    for u in us:
        for d in dep[u]: rev[d].append(u)
    base = {}
    for u in us:
        r = row_of(u)
        base[u] = (rowkey(r) if r else (999, 999), subkey(u) if subkey else 0, modidx(u[0]), u[1])
        if u in SIMPSET: base[u] = ((-1, -1), 0, modidx(u[0]), u[1])
    # a support unit inherits the smallest key among its dependents
    key = dict(base)
    changed = True
    while changed:
        changed = False
        for u in us:
            if inherit_all or row_of(u) is None:
                for x in rev[u]:
                    if key[x] < key[u] and (passes is None or passes(x)):
                        key[u] = key[x]; changed = True
    import heapq
    indeg = {u: len(dep[u]) for u in us}
    h = [(key[u], modidx(u[0]), u[1], u) for u in us if indeg[u] == 0]
    heapq.heapify(h); out = []
    while h:
        *_, u = heapq.heappop(h); out.append(u)
        for x in rev[u]:
            indeg[x] -= 1
            if indeg[x] == 0: heapq.heappush(h, (key[x], modidx(x[0]), x[1], x))
    assert len(out) == len(us), (f, len(out), len(us))
    if keys_out is not None: keys_out.update(key)
    return out

owned = collections.defaultdict(set)
for n in D:
    o = own.get(n)
    if o: owned[unit_of_owner[o]].add(n)

def modname(f): return f.replace("/", ".")

def parse_open(cmd):
    c = " ".join(cmd.split())
    assert c.startswith("open ")
    c = c[5:]
    if c.endswith(" in"): c = c[:-3]
    m = re.match(r"^(\S+)\s*\((.*)\)\s*$", c)
    if m: return [("explicit", m.group(1), m.group(2).split())]
    if " hiding " in c or " renaming " in c or "(" in c:
        raise Exception("unhandled open " + cmd)
    return [("plain", x, None) for x in c.split()]

def open_lines(opens, avail_ns, avail_c):
    out = []
    for cmd, path in opens:
        for kind, nm, names in parse_open(cmd):
            full = resolve_ns(nm, path)
            if full is None:
                if nm.startswith("BoCa") or nm in NS: continue
                if any(p + "." + nm in NS for p in [".".join(path[:k]) for k in range(1, len(path)+1)]): continue
                full = nm  # outside BoCa (Mathlib / core)
                if kind == "plain": out.append("open " + full); continue
                out.append("open %s (%s)" % (full, " ".join(names))); continue
            if not full.startswith("BoCa"):
                out.append(("open " + full) if kind == "plain" else "open %s (%s)" % (full, " ".join(names))); continue
            if full not in avail_ns: continue
            if kind == "plain": out.append("open " + full)
            else:
                keep = [x for x in names if full + "." + x in avail_c]
                if keep: out.append("open %s (%s)" % (full, " ".join(keep)))
    # dedupe preserving order
    seen = set(); res = []
    for o in out:
        if o not in seen: seen.add(o); res.append(o)
    return res

STATUS_TAG = {"exact": "[as printed]", "encoding": "[encoding]", "repair": "[repair]", "plumbing": "[about ours]"}
HIST = re.compile(r"\b(commit|deleted|migration|is gone|are gone|used to|no longer|retired|was scored|were scored|since been|Phase C|is now|are now|now reads|previously|formerly)\b", re.I)
def dehistory(note):
    parts = re.split(r"(?<=[.;])\s+(?=[A-Z*(\[`])", note)
    return " ".join(p for p in parts if not HIST.search(p)).strip()
def unit_comment(rs, seenrows):
    out = []
    cont = [r for r in rs if r in seenrows]
    if cont:
        out.append(("Row %s, continued." if len(cont) == 1 else "Rows %s, continued.") % ", ".join(cont))
    for r in rs:
        info = DEFROWS[r]
        tag = STATUS_TAG.get(info["status"], info["status"])
        if r in seenrows:
            continue
        out.append("### %s · %s · %s · `%s`\n\n%s" % (r, info["printed"], info["page"], tag, dehistory(info["note"])))
    return "/-!\n" + "\n\n".join(out) + "\n-/"

def support_row_comment(rs, sel, tgt, seenrows):
    """a Support declaration that implements a row: point to the paper file holding the row"""
    out = []
    for r in rs:
        homes = sorted(set(tgt[x] for x in sel if tgt[x].startswith("Paper") and r in unit_rows.get(x, [])))
        info = DEFROWS[r]; tag = STATUS_TAG.get(info["status"], info["status"])
        if r in seenrows:
            out.append("Row %s, continued." % r)
        elif homes:
            out.append("Row %s · %s · `%s` — %s are in %s." % (r, info["printed"], tag,
                       "the repaired reading; the printed row, its adjudication and the literal reading" if info["status"] == "repair" else "the printed row and its note", ", ".join("`%s.lean`" % h for h in homes)))
        else:
            out.append("### %s · %s · %s · `%s`\n\n%s" % (r, info["printed"], info["page"], tag, dehistory(info["note"])))
    return "/-!\n" + "\n\n".join(out) + "\n-/"

def emit(sel, tgt, banners, header_of=None, extra_files=(), hook=None):
    SUPPORT_BANNER = banners["__support__"]; SUPPORT_WHAT = banners["__what__"]
    files = sorted(set(tgt[u] for u in sel))
    g = file_graph(sel, tgt)
    if hook and hasattr(hook, "extra_edges"):
        for f, ds in hook.extra_edges().items():
            g[f] |= {d for d in ds if d != f}
    order = topo_files(files, g)
    # private stripping
    strip = set()
    for u in sel:
        for d in udeps[u]:
            if d in sel and tgt[d] != tgt[u]:
                if any(n.startswith("_private") for n in owners_of(d)): strip.add(d)
    for d in strip:
        for n in owners_of(d):
            if n.startswith("_private"):
                base = re.match(r"_private\.[\w.]+?\.\d+\.(.*)", n).group(1)
                if base in D: print("PRIVATE CLASH", n)
    MATH = {}
    provided = {}   # file -> (ns set, const set) including transitive imports
    written = {}
    for f in order:
        imps = sorted(g.get(f, ()))
        ans, ac = set(), set()
        for i in imps:
            ans |= provided[i][0]; ac |= provided[i][1]
        default_row_of = lambda u: (sorted([r for r in unit_rows.get(u, []) if DEFROWS[r]["status"] != "plumbing"], key=rowkey) or [None])[0] if tgt[u].startswith("Paper") and paper_target(u) == tgt[u] else None
        us = unit_sort([u for u in sel if tgt[u] == f], tgt, f,
                       (lambda u: hook.row_of(u, f, default_row_of)) if hook else default_row_of,
                       inherit_all=bool(hook and hook.inherit_all(f)), keys_out=hook.keys if hook else None,
                       passes=getattr(hook, "passes_key", None), subkey=getattr(hook, "subkey", None))
        body = []; curkey = None; seenrows = set(); prev_inline = False
        def close_group():
            if curkey is not None:
                body.append("end %s" % ".".join(curkey[0]) if curkey[0] else "end")
                body.append("")
        for u in us:
            if hook:
                for txt in hook.pseudo_before(u, f):
                    close_group(); curkey = None
                    body.append(txt); body.append("")
            U = UBY[u]; ctx = U["ctx"]
            text = utext(u)
            if u in strip:
                text = re.sub(r"(?m)^((?:@\[[^\]]*\]\s*)?)private (?=(theorem|def|lemma|abbrev|instance|structure|inductive|noncomputable|irreducible_def)\b)", r"\1", text)
            words = set(re.findall(r"[\w'₀-₉]+", text))
            vs = []
            for v in ctx["vars"]:
                nms = var_names(v)
                if (nms & words) if nms else (set(re.findall(r"[\w'₀-₉]+", v)) - {"variable", "Type", "Prop"}) & words:
                    vs.append(v)
            ol = open_lines(ctx["opens"], ans, ac)
            key = (tuple(ctx["ns"]), tuple(ol), tuple(vs), tuple(ctx["opts"]))
            if key != curkey:
                close_group()
                curkey = key
                body.append(("namespace " + ".".join(ctx["ns"])) if ctx["ns"] else "section")
                for p in range(1, len(ctx["ns"]) + 1): ans.add(".".join(ctx["ns"][:p]))
                body.extend(ol)
                body.extend(vs)
                body.extend(ctx["opts"])
                body.append("")
            # prefix commands
            pre = []
            for cmd, path in U["prefix"]:
                if cmd.startswith("open"):
                    ls = open_lines([(cmd, path)], ans, ac)
                    pre.extend(l + " in" for l in ls)
                else: pre.append(cmd)
            # comments
            hc = hook.before(u, f) if hook else None
            if hc is not None:
                if hc: body.append(hc)
                prev_inline = hc.startswith("/-! `[about ours]`")
            elif f.startswith("Paper") and paper_target(u) == f:
                rs = sorted([r for r in unit_rows.get(u, []) if DEFROWS[r]["status"] != "plumbing"], key=rowkey)
                if rs:
                    body.append(unit_comment(rs, seenrows)); seenrows.update(rs)
                prev_inline = False
            elif f.startswith("Support") and [r for r in unit_rows.get(u, []) if DEFROWS[r]["status"] != "plumbing"]:
                rs = sorted([r for r in unit_rows.get(u, []) if DEFROWS[r]["status"] != "plumbing"], key=rowkey)
                body.append(support_row_comment(rs, sel, tgt, seenrows)); seenrows.update(rs)
            elif f.startswith("Paper") and not prev_inline:
                body.append("/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/")
                prev_inline = True
            body.extend(pre)
            body.append(text)
            body.append("")
            for n in owned[u]:
                ac.add(n)
                p = n.split(".")
                for k in range(1, len(p)): ans.add(".".join(p[:k]))
            ha = hook.after(u, f) if hook else None
            if ha:
                close_group(); curkey = None
                body.append(ha); body.append("")
        if hook:
            for txt in hook.pseudo_end(f):
                close_group(); curkey = None
                body.append(txt); body.append("")
        close_group()
        provided[f] = (ans, ac)
        needs_mathlib = any(UBY[u]["mod"] not in CFG["no_mathlib"] for u in us)
        imports = [modname(i) for i in imps]
        MATH[f] = needs_mathlib or any(MATH[i] for i in imps)
        if needs_mathlib and not any(MATH[i] for i in imps):
            imports = ["Mathlib"] + imports
        banner = banners.get(f) or (SUPPORT_BANNER.format(topic=f[len("Support/"):].replace("/", " — "), what=SUPPORT_WHAT.get(f, "plumbing")) if f.startswith("Support/") else "")
        src = ("\n".join("import " + i for i in imports) + "\n\n" if imports else "") + banner + "\nnoncomputable section\n\n" + "\n".join(body) + "\nend\n"
        path = os.path.join(OUT, f + ".lean")
        os.makedirs(os.path.dirname(path), exist_ok=True)
        open(path, "w").write(src)
        written[f] = [u for u in us]
    return order, g, written, strip

AUXNAME = re.compile(r"(\.(match_\d+(_\d+)?|_sparseCasesOn_\d+|proof_\d+|_proof_\d+|_f|_sunfold|_unsafe_rec|splitter|eq_\d+|eq_def|below|brecOn|binductionOn|casesOn|recOn|rec|noConfusion|noConfusionType|ctorIdx|ctorElim|ctorElimType|sizeOf_spec|_sizeOf_\d+|_sizeOf_inst|inj|injEq)$)|_aux_|\.«|\._|^_h$")
def write_bridge(sel, tgt, strip, path, extra=(), rows_of=None):
    import csv
    rows = []
    for u in sel:
        for n in sorted(owned[u]):
            if AUXNAME.search(n): continue
            m = re.match(r"_private\.[\w.]+?\.\d+\.(.*)", n)
            base = m.group(1) if m else n
            newname = base
            priv = "yes" if (m and u not in strip) else "no"
            o = own[n]
            rs = rows_of(u) if rows_of else ";".join(sorted(unit_rows.get(u, []), key=rowkey))
            rows.append(dict(name=newname, source_name=base, private=priv, kind=D[n]["kind"],
                             target=tgt[u] + ".lean", source=u[0].replace(".", "/") + ".lean:" + D[o]["s"].split(":")[0],
                             rows=rs))
    rows.extend(extra)
    rows.sort(key=lambda r: (r["target"], r["name"]))
    with open(path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=["name", "source_name", "private", "kind", "target", "source", "rows"])
        w.writeheader(); w.writerows(rows)
    return rows


# ---------------------------------------------------------------- stage 1's selection
def stage1_selection():
    """the §§1–5 definitions and what they need; theorem-valued rows whose proofs cost
    more than 60 further lines are deferred"""
    skip = set(CFG["stage1_skip_rows"])
    isthm = lambda u: D[owners_of(u)[0]]["kind"] == "thm"
    roots = set(uid for uid, rs in unit_rows.items() if any(r not in skip for r in rs) and not isthm(uid))
    sel = select(roots)
    deferred = []
    for u, rs in sorted(unit_rows.items()):
        if isthm(u) and u not in sel and any(r not in skip for r in rs):
            new = close(sel | {u}) - sel
            if sum(UBY[x]["e"] - UBY[x]["s"] + 1 for x in new) <= 60: sel = select(sel | {u})
            else: deferred.append(u)
    return sel, deferred
