import Paper.S1_Syntax.Definitions
import Paper.S5_Model.Definitions
import Support.Model.Propositions

/-!
# [TR] §5 Model — remarks on the definitions

Row 5.62's `wp_eq_wpU` (the two printed readings of `↭` give the same `wp`),
row 5.56's `BigComp.perm` (`⨀` is order-independent), and row 5.67's theorems
(`[CONF]`'s prose characterisation of `✓`).

These are theorems about printed definitions — definition rows of
`Paper/INDEX.md` whose Lean is a theorem — whose proofs use results
of `[TR]` §6, so they cannot sit with the definitions.  Each carries the row's
number, printed form, page, tag and note.  A row's theorem that a §6 result's Lean
needs is declared in that result's file, and the row here says where.
-/

noncomputable section

/-!
### 5.56 · `⨀` — the iterated composition, with no printed empty case · [TR] p. 5, rows 11, 12, 19 · `[repair]`

The fold behind the printed large operator. The empty case is printed nowhere, and without it `ex(ρ)_◖` would have no value on any mut-free ρ — so `✓ρ` on the simplest resources depends on it; `BoCa.Fig16.BigComp.perm` makes the fold order irrelevant. Adjudicated here: the empty case is necessary and not convenient — neither document prints it, and without it `ex(ρ)_◖` has no value on any mut-free ρ — and `BoCa.Fig16.BigComp.perm` discharges the order-independence out of [TR] Lemmas 6.1–6.3 instead of assuming it

`BoCa.Fig16.BigComp.perm` is declared in `Paper/S6_1_StandardLemmas/Lemmas.lean`, ahead of this file: the Lean of Lemmas 6.7, 6.8, 6.10, 6.11 and 6.15 there needs it.
-/

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
### 5.62 · — [CONF] Fig. 18b's unguarded ↭, and the `wp` row read at it — · not in [TR] §5 · `[repair]`

The second printed reading of ↭ (`docs/adjudications.md` D3), kept alongside [TR]'s; `BoCa.Fig16.BoLo.wp_eq_wpU` proves the two readings give the same `SProp` inside the `wp` row, so nothing downstream has to choose. Adjudicated at `docs/adjudications.md` D3: both readings of ↭ are printed rows in the same documents, so both are carried and the choice is closed by proof rather than fiat — `BoCa.Fig16.BoLo.wp_eq_wpU` shows [TR]'s two guards follow from the `#`s that `wp` already quantifies over — and what survives away from `wp` is named. `BoCa.Fig16.ResU.Upd` is itself `[as printed]` against [CONF] Fig. 18b, so this row bundles a printed item with two declarations of ours
-/
/-- …and hence the two readings are the same `SProp`.
`[about ours: the equality of the two printed readings]` -/
theorem wp_eq_wpU (e : Expr) (Q : Val → WProp) : wp e Q = wpU e Q :=
  funext fun ρ => propext (wp_updV_iff_upd e Q ρ)

end BoCa.Fig16.BoLo

/-!
### 5.67 · — [CONF] §4.3's characterisation of `✓`: *"in a valid resource, every pair of aliases map to the same object and each has an immutable ancestor"*, and *"aliasing of exclusive locations … not guarded by immutable cells … violates the mutability-xor-aliasing restriction"* — · [CONF] p. 415:21, not in [TR] §5 · `[as printed]`

Prose, not a defining row, and it characterises an object that already has one — `✓ρ ≜ ⦇ρ⦈ defined` (row 5.59). [CONF] p. 415:21 says the enforcement is composition itself and nothing more: *"the advantage of reusing composition is that it already rules out all of the inconsistent aliasing cases"*, and names the mechanism — *"the conflict at `ℓ₁` causes `•` and therefore `E•` to be undefined, while the conflict at `ℓ₂` causes `◦` and therefore `A` to be undefined"*. So there is nothing extra to transcribe, and the three clauses are already theorems: *same object* is `CellU.compatR_iff`, proved as an **iff** (`▷◁ ⟺ a common value, and a common witness wherever there is one to share`), with `CellU.CompatS.imm_imm` at `●`; *an immutable ancestor* is `AgW.nonimm_beneath_imm` with `ExW.immFree` (6.36); *no cell both exclusive and aliasable* is `ResU.CompatS.disjoint_of_immFree` and `ResU.flat_eq_ag_at`. The row exists because the prose was uncited for the whole of `[TR]` §6's development; `docs/adjudications.md` §12.52 assembles it and records what it does **not** say

`BoCa.Fig16.CellU.compatR_iff` is declared in `Paper/S6_1_StandardLemmas/Lemmas.lean`, ahead of this file: the Lean of Lemmas 6.14 and 6.15 there needs it.

`BoCa.Fig16.AgW.nonimm_beneath_imm` is declared in `Paper/S6_2_NonStandardLemmas/Lemmas.lean`, ahead of this file: the Lean of Lemmas 6.38, 6.48 and 6.59 there needs it.

`BoCa.Fig16.ResU.CompatS.disjoint_of_immFree` is declared in `Paper/S6_1_StandardLemmas/Lemmas.lean`, ahead of this file: the Lean of Lemmas 6.7, 6.8, 6.10, 6.11 and 6.15 there needs it.

`BoCa.Fig16.ResU.flat_eq_ag_at` is declared in `Paper/S6_2_NonStandardLemmas/Lemmas.lean`, ahead of this file: the Lean of Lemmas 6.48 and 6.59 there needs it.
-/

end
