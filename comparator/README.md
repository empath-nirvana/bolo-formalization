# Independent verification via leanprover/comparator

**The judged theorem.**  `BoCa.Fig16.LogRel.Typed.adequacy`
(`Paper/CONF/Results.lean`):

```lean
theorem adequacy (e : Expr) (hD : DerivesWf LifeCtx.empty ([] : Ctx Ty) e Ty.unit) :
    BoCa.BoLo.Steps Adequacy.emptyMem e Adequacy.emptyMem (.val .unit)
```

A closed program that `[TR]` p. 2 types at `1` runs from the empty memory to `()`
and the empty memory: termination and memory reclamation.

**The trust base.**  The statement mentions only the syntax, the typing judgment
and the machine, so that is all a reader has to trust:

* `[TR]` §1, the syntax: `Expr`, `IsVal`, `Val`, `Prim`, `Loc`, `Life`, `LifeCtx`, `Ty`;
* `[TR]` §2, the typing judgment `DerivesWf` as the library reads it, with what it
  uses (`Ctx`, `Ctx.Split`, `Ctx.Solo`, `Ctx.Dead`, the axiom terms and their types,
  `Outlives`, `EntailsLt`/`EntailsLe`, `Ty.instLife`, `Ty.scopedB`, `Ty.bindsB`, …);
* `[TR]` §3, the machine: `BoLo.Kont`, `BoLo.Head`, `BoLo.Step1`, `BoLo.Steps`, the
  heap operations, and `Adequacy.emptyMem`.

Every definition here is written in core Lean; none uses Mathlib.  Nothing of the
model is in it: the logical relation, the resource algebra, `wp` and the typed
world of `[TR]` §§4–6, and the repairs recorded there, are used by the proof and
are not in the statement, so a pass does not ask anyone to trust them.  The
`[repair]` rows of `[TR]` §§1–3 that the statement does reach (the typing rules
and the two evaluation frames, README, *Which printed definitions are repaired*)
are in the trust base, and are read in `Challenge/`.

**The files.**  `Challenge.lean` states the theorem with a `sorry` body, which is
comparator's convention for a challenge; it is the only `sorry` in the repository,
and `scripts/check-hygiene.sh` permits exactly it.  `Challenge.lean` does NOT import
`Paper` or `Support`.  The modules under `Challenge/` replicate, verbatim, the
declarations the statement reaches, each copied from the source file its path names
(`Challenge/Paper/S1_Syntax/Definitions.lean` from `Paper/S1_Syntax/Definitions.lean`,
and so on), under the same namespaces, `open`s and names, one module per source
file.  The module split is not cosmetic: Lean reuses a pattern-matching auxiliary
(`f.match_1`) across definitions of the same shape, which ones are candidates
depends on module boundaries, and comparator compares those auxiliaries too.  For
the same reason `Lifetime.Life.depth` and `Ty.wfB`, which the statement does not
reach, are copied: `Life.mentions` and `Ty.scopedB` reuse the auxiliaries named
after them.

`config.json` names the theorem, lists no definition holes, and permits the three
standard axioms.  `definition_names` is empty on purpose: comparator compares a
listed definition by its type alone (it is a *hole* the solution may fill), while
a definition it reaches by crawling the theorem's statement is compared in full —
type and value — and so is every constant that value mentions.  Every definition
and inductive of the trust base is therefore compared structurally, declaration
for declaration.

**What a pass certifies.**  That `Paper` contains a theorem
`BoCa.Fig16.LogRel.Typed.adequacy` whose statement is exactly the one in
`Challenge.lean`, over declarations identical to the ones in `Challenge/`; that its
proof uses no axiom beyond `propext`, `Classical.choice` and `Quot.sound`; and
that both the Lean kernel and the independent nanoda kernel accept the exported
proof.  None of this trusts our build: comparator builds `Challenge` and `Paper`
itself in a `landrun` sandbox, reads them through `lean4export` rather than
loading `.olean` files, and replays the export in both kernels.

**Running it.**  CI runs the judge (`.github/workflows/comparator.yml`) on Linux,
where `landrun` sandboxes the build.  Locally, comparator's
`scripts/fake-landrun.sh` stands in for `landrun` on macOS; that runs the same
comparison and the same two kernels, without the sandbox:

```
git clone https://github.com/leanprover/comparator ../comparator-tool
git -C ../comparator-tool checkout c0c5a52
cp lean-toolchain ../comparator-tool/lean-toolchain   # and do not `lake update` there
(cd ../comparator-tool && lake build lean4export comparator)
COMPARATOR_LANDRUN=$PWD/../comparator-tool/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=$PWD/../comparator-tool/.lake/packages/lean4export/.lake/build/bin/lean4export \
COMPARATOR_NANODA=/path/to/nanoda_lib/target/release/nanoda_bin \
  lake env ../comparator-tool/.lake/build/bin/comparator comparator/config.json
```

`c0c5a52` is comparator's last commit on Lean v4.33.0; this repository is on
v4.33.1, and the judge is built with this repository's `lean-toolchain` so that
`lean4export` reads our `.olean` files.

**Keeping it in step.**  If a declaration of the trust base changes in `Paper/` or
`Support/`, the judge fails with `Const does not match between challenge and
target '<name>'` until the copy in `Challenge/` is updated to match.
