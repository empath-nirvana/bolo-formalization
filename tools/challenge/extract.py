"""Write comparator/Challenge/<source path> for each source file below: the
declarations of that file whose names the closure (tools/challenge/Closure.lean)
lists, or that own an auxiliary it lists (`f.match_1`, `f._f`, ...), copied
verbatim with their docstrings, under the same namespaces and `open`s.  Section
comments (`/-! ... -/`) are dropped.  The files are listed in an order consistent
with their imports.

    python3 tools/challenge/extract.py <repo root> <closure file> <output dir>
"""
import re, sys, pathlib
root = pathlib.Path(sys.argv[1]); closure_file = sys.argv[2]
FILES = ["Paper/S1_Syntax/Definitions.lean", "Support/Syntax/Terms.lean",
         "Support/Lifetimes/Terms.lean", "Support/Lifetimes/Substitution.lean",
         "Support/Statics/Contexts.lean", "Paper/S3_Dynamics/Definitions.lean",
         "Paper/S2_Statics/Definitions.lean", "Support/Statics/Presupposed.lean",
         "Support/Dynamics/Machine.lean", "Support/LogicalRelation/Adequacy.lean"]
closure = set()
for l in open(closure_file):
    parts = l.split()
    if len(parts) >= 2 and parts[-1].startswith("BoCa."): closure.add(parts[-1])
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*(def|abbrev|theorem|lemma|inductive|structure|instance|class)\s+([^\s(:{\[]+)?")
def wanted(full):
    return full in closure or any(c.startswith(full + ".") for c in closure)
outdir = pathlib.Path(sys.argv[3])
for f in FILES:
    out = []
    lines = (root / f).read_text().split("\n")
    ns = []; opens = {}; i = 0; doc = None; chunks = []
    while i < len(lines):
        L = lines[i]
        if not L.strip() or L.startswith("--") or L.startswith("import "): i += 1; continue
        if L.startswith("/-!") or (L.startswith("/-") and not L.startswith("/--")):
            depth = 0
            while True:
                depth += lines[i].count("/-") - lines[i].count("-/")
                i += 1
                if depth <= 0: break
            doc = None; continue
        if L.startswith("/--"):
            j = i
            while "-/" not in lines[j]: j += 1
            doc = lines[i:j+1]; i = j + 1; continue
        if L.startswith("namespace "): ns.append(L.split()[1]); opens[len(ns)] = []; i += 1; continue
        if L.startswith("end"):
            if L.strip() != "end": ns.pop()
            i += 1; continue
        if L.startswith("noncomputable section") or L.startswith("section"): i += 1; continue
        if L.startswith("open "): opens[len(ns)].append(L); i += 1; continue
        # declaration (possibly preceded by a bare attribute line)
        j = i + 1
        while j < len(lines) and (lines[j] == "" or lines[j][0] in " \t|") :
            j += 1
        # trim trailing blank lines
        k = j
        while lines[k-1].strip() == "": k -= 1
        body = lines[i:k]
        head = " ".join(body[:2])
        m = DECL.match(head.strip())
        if not m: i = j; doc = None; continue  # e.g. a bare `@[inherit_doc]` line
        name = m.group(2)
        full = (ns[-1] + "." + name) if (ns and name) else name
        if name and wanted(full):
            chunks.append((tuple(ns), tuple(opens.get(len(ns), [])), (doc or []) + body, full))
        doc = None; i = j
    # emit chunks, grouping by context
    mod = "Challenge." + f[:-5].replace("/", ".")
    imps = [l.split()[1] for l in lines if l.startswith("import ")]
    kept = ["Challenge." + m for m in imps if m.replace(".", "/") + ".lean" in FILES]
    dropped = [m for m in imps if m.replace(".", "/") + ".lean" not in FILES]
    out.extend("import " + m for m in kept)
    out.append(f"""
/-!
Verbatim from `{f}`: the declarations of that file the judged statement
reaches (see `comparator/Challenge.lean`), with their namespaces and `open`s.""" + (f"""
The source also imports {", ".join("`"+d+"`" for d in dropped)}; no declaration
copied here uses anything from {"it" if len(dropped)==1 else "them"}.""" if dropped else "") + """
-/

noncomputable section
""")
    ctx = None
    for nss, ops, text, full in chunks:
        if (nss, ops) != ctx:
            if ctx and ctx[0]: out.append(f"end {ctx[0][-1]}\n")
            if nss: out.append(f"namespace {nss[-1]}")
            out.extend(ops)
            if nss or ops: out.append("")
            ctx = (nss, ops)
        out.append("\n".join(text) + "\n")
    if ctx and ctx[0]: out.append(f"end {ctx[0][-1]}\n")
    out.append("end")
    p = outdir / ("Challenge/" + f)
    p.parent.mkdir(parents=True, exist_ok=True)
    text = "\n".join(out) + "\n"
    text = text.replace("namespace BoCa.Adequacy\nopen BoCa.Fig16\nopen BoCa.Fig16.BoLo (wp NoOwn WRes)\n", "namespace BoCa.Adequacy\n-- The source block also opens `BoCa.Fig16` and `BoCa.Fig16.BoLo (wp NoOwn WRes)`,\n-- the model, which is not replicated here; `emptyMem` uses neither.\n")
    assert "open BoCa.Fig16" not in text
    p.write_text(text)
    print(p)
