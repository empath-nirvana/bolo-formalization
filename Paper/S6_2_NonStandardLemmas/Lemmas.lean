import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_2_NonStandardLemmas.Definitions
import Paper.S6_2_NonStandardLemmas.Remarks
import Support.Lifetimes.Terms
import Support.LogicalRelation.Facts
import Support.Model.Algebra
import Support.Model.AlgebraInstances
import Support.Model.Ancestors
import Support.Model.CellFacts
import Support.Model.Cells
import Support.Model.ClosingSentence
import Support.Model.Compatibility
import Support.Model.Composition
import Support.Model.Flattening
import Support.Model.FlatteningCells
import Support.Model.Lifetimes
import Support.Model.Notation
import Support.Model.Outlives
import Support.Model.Prelude
import Support.Model.Propositions
import Support.Model.Reborrow
import Support.Model.ReborrowFrame
import Support.Model.ReborrowLowering
import Support.Model.RelaxedWalks
import Support.Model.Restriction
import Support.Model.Singletons
import Support.Model.Subtraction
import Support.Model.Surgery
import Support.Model.Update
import Support.Model.UpdateFrame
import Support.Model.WalkSplitting
import Support.Model.Walks
import Support.Statics.Contexts

/-!
# [TR] §6.2 Non-standard Lemmas  (physical pp. 8–22), Lemmas 6.16–6.63

The flattening `⦇ρ⦈` and its walks `ex`, `ag` (6.16–6.20, 6.30–6.37), the surgery
lemmas that trade a `mut` or `imm` cell for `ρ_v ● ℓ ↦ own(v)` (6.21–6.29, 6.34,
6.38, 6.39), cell-level facts (6.40–6.45), the update relation `↭` (6.46–6.51),
reborrowing (6.52–6.59, 6.61), and the logical relation's outlives lemmas (6.60,
6.62, 6.63).  Definitions 6.1–6.3, printed on pp. 9, 13 and 17, are in this
directory's `Definitions.lean`; the theorems about Definition 6.2's `∼` are in its
`Remarks.lean`.

**How this file reads.**  The numbered results of the subsection, in printed order as
far as Lean's definition-before-use allows.  Each opens with a record:

* the result's number, page and status (`proved`, `proved*`, `variant`; the
  legend is in `Paper/INDEX.md`);
* the printed statement, quoted, with the extraction's garbled symbols restored;
* the printed proof, transcribed compactly and in its own order, citing the lemmas it
  cites;
* the Lean declaration (its docstring carries the tag and its account of the
  proof),
  and the numbered alias `TR.lemma_6_N` declared after it;
* a note on how the declaration reads the printed statement.

A result whose declaration an earlier subsection's printed proof needs is declared
in that subsection's file, under a heading saying so; its record and alias stay
here.  A run of declarations the paper does not print, placed in this file only
because a result below needs it and it needs a result above, is marked
`[about ours]` and names the result it serves.  `§N` citations are to
`docs/adjudications.md`.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.16 · `[TR]` p. 8 · `proved`

> If ρ ● ⦇ρ′⦈ defined then ρ ● ρ′ defined.

**Printed proof, transcribed.** `ρ ● ⦇ρ′⦈` is defined iff `ρ` and `⦇ρ′⦈` have disjoint own-or-mut cells and `imm` cells that agree up to lifetimes.  Unravelling `⦇−⦈`, the cells of `ρ′` are a subset of those of `⦇ρ′⦈`, so the same condition holds of `ρ` and `ρ′`.

**Lean.** `BoCa.Fig16.ResU.CompatS.of_flat`, alias `TR.lemma_6_16`, tag `[as printed]`.

**Note.** `Fig16.ResU.CompatS.of_flat`, on the printed carrier. The print's whole proof is "the cells of `ρ′` are a subset of those of `⦇ρ′⦈`"; that is `Fig16.ResU.Flat.get`, **proved** rather than read off — a cell of `ρ` reappears in `⦇ρ⦈` at its own location with the same tag, value and witness. The inclusion is not literal, since `ag`'s `○`s may enlarge a lifetime set, but those three projections are all `▶◀` looks at
-/
/-- **`[TR]` Lemma 6.16** (p. 8): if `ρ ● ⦇ρ′⦈` is defined then so is `ρ ● ρ′`.
Definedness is `▸◂` by Lemma 6.9 (`ResU.compS_defined_iff`) at both ends,
and `⦇ρ′⦈` is named by its graph.  The proof is the print's: every cell of `ρ′`
sits at its own location in `⦇ρ′⦈` over the same value and witness
(`ResU.Flat.get`), and `▶◀` looks at nothing else (`CellU.compatS_iff`), so the
condition `ρ` satisfies against `⦇ρ′⦈` it satisfies against `ρ′`.
`[as printed]` (the printed `⦇ρ′⦈` appears as its graph — G4) -/
theorem ResU.CompatS.of_flat {ρ ρ' f : ResU Loc Val} (hf : ResU.Flat ρ' f)
    (h : ResU.CompatS ρ f) : ResU.CompatS ρ ρ' := by
  intro l ψ ψ' e e'
  obtain ⟨χ, hχ, hk, hv, hw⟩ := hf.get e'
  obtain ⟨k₁, k₂, m₁, m₂⟩ := CellU.compatS_iff.mp (h l ψ χ e hχ)
  exact CellU.compatS_iff.mpr ⟨k₁, hk.symm.trans k₂, m₁.trans hv, m₂.trans hw⟩

end BoCa.Fig16

alias TR.lemma_6_16 := BoCa.Fig16.ResU.CompatS.of_flat

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.42 · `[TR]` p. 15 · `proved`

> If ℓ ↦ mut(−, −, −, −) ▸◂ ρ, then ℓ ∉ ρ.

**Printed proof, transcribed.** By definition.

**Lean.** `BoCa.Fig16.ResU.compatS_single_mut`, alias `TR.lemma_6_42`, tag `[as printed]`.

**Note.** `Fig16.ResU.compatS_single_mut`, the `mut` instance of the same fused theorem.
-/
/-- **`[TR]` Lemma 6.42** (p. 15): if `ℓ ↦ mut(β,v,ρ′,P̂) ▶◀ ρ` then `ℓ ∉ ρ`.
`[as printed]` -/
theorem ResU.compatS_single_mut {l : Loc} {b : Life} {v : Val}
    {σ : ResU Loc Val} {hs : σ.InStratum b} {P : Val → SPropS Loc Val b}
    {hw : P v ⟨σ, hs⟩} {ρ : ResU Loc Val}
    (h : ResU.CompatS (ResU.single l (CellU.mutOf b v σ hs P hw)) ρ) :
    ρ.get l = none :=
  ResU.compatS_single_not_imm (by simp) h

end BoCa.Fig16

alias TR.lemma_6_42 := BoCa.Fig16.ResU.compatS_single_mut

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.17 · `[TR]` p. 8 · `proved`

> If ρ # ℓ ↦ mut(α, v, ρ_v, P̂) then ρ ▸◂ ρ_v ● ℓ ↦ own(v)

**Printed proof, transcribed.** Let `ρ_o = ℓ ↦ own(v)` and `ρ_m = ℓ ↦ mut(α, v, ρ_v, P̂)`.  By Lemma 6.9 it is enough that `ρ ● ρ_v ● ρ_o` is defined.  `✓(ρ ● ρ_m)` makes `⦇ρ ● ρ_m⦈ = ex(ρ)_● ● (ρ_m ● ex(ρ_v)_●) ● (ag(ρ) ○ ag(ρ_v))` defined; ignoring `ex(ρ)_●` and `ag(ρ)`, `ρ_m ● ⦇ρ_v⦈` is defined, so `ℓ ∉ dom⦇ρ_v⦈`, so `ρ_o ● ⦇ρ_v⦈` is defined, so `ρ_o ● ρ_v` is defined by Lemma 6.16.  Definedness of `ag(ρ) ○ ag(ρ_v)` makes `ρ` and `ρ_v` agree on `imm` cells up to lifetimes, hence `ρ` and `ρ_o ● ρ_v` (`ρ_o` has no `imm` cell); definedness of `ex(ρ)_● ● (ρ_m ● ex(ρ_v)_●)` makes `ρ` and `ρ_m ● ρ_v` have disjoint own-or-mut cells, hence `ρ` and `ρ_o ● ρ_v` (`ρ_o` and `ρ_m` have the same own-or-mut cells).  Together, `ρ` and `ρ_o ● ρ_v` are composable.

**Lean.** `BoCa.Fig16.ResU.compatS_of_hash_mut`, alias `TR.lemma_6_17`, tag `[as printed]`.

**Note.** `Fig16.ResU.compatS_of_hash_mut`, on the printed carrier, via 6.9 and 6.16 as the print does. `hs`, `P` and `hP` are `mut(α,v,ρᵥ,P̂)`'s own components, not added conditions.
-/
/-- **`[TR]` Lemma 6.17** (p. 8): if `ρ # ℓ ↦ mut(α, v, ρᵥ, P̂)` then
`ρ ▸◂ ρᵥ ● ℓ ↦ own(v)`.  The right-hand composite is named by its graph, which
carries its own `▸◂` and adds nothing, `●` being single-valued; `hs`, `P` and
`hP` are the printed `mut(α, v, ρᵥ, P̂)`'s own components, and `ℓ ↦ −` is
`ResU.single`, the notation neither document gives a defining row.

Two facts close it.  `ρ ▸◂ ρᵥ` is `ResU.CompatS.of_valid_mut`, which is the
printed proof from its display onward.  And `ℓ ∉ dom(ρ)` — `[TR]` Lemma 6.42
(`ResU.compatS_single_mut`) — so at `ℓ`, where the printed `ρₒ` sits, there
is nothing in `ρ` to test, and everywhere else `ρᵥ ● ℓ ↦ own(v)` is `ρᵥ`.  That
is the print's "since `ρₒ` contains no imm cells" and "since `ρₒ` and `ρₘ` have
the same own-or-mut cells", which on this carrier are the same observation about
the one location `ρₒ` occupies.
`[as printed]` (the printed `ρᵥ ● ℓ ↦ own(v)` appears as its graph — G4) -/
theorem ResU.compatS_of_hash_mut {ρ ρv w : ResU Loc Val} {l : Loc} {α : Life} {v : Val}
    {hs : ρv.InStratum α} {P : Val → SPropS Loc Val α} {hP : P v ⟨ρv, hs⟩}
    (h : ResU.Hash ρ (ResU.single l (CellU.mutOf α v ρv hs P hP)))
    (hw : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) w) : ResU.CompatS ρ w := by
  obtain ⟨hcompat, ρ', hρ', hval⟩ := h
  have hkey : ResU.CompatS ρ ρv :=
    ResU.CompatS.of_valid_mut (ResU.single_get_self _ _) (by simp) (by simp) hρ' hval
  have hnone : ρ.get l = none := ResU.compatS_single_mut hcompat.symm
  intro l' ψ χ e f
  rcases hw.get l' with ⟨-, -, g⟩ | ⟨χ', g₁, -, g⟩ | ⟨χ', -, g₂, g⟩ |
      ⟨u₁, u₂, u, -, g₂, -, -⟩
  · rw [g] at f; exact absurd f (by simp)
  · rw [g] at f; cases Option.some.inj f; exact hkey l' _ _ e g₁
  · obtain ⟨rfl, -⟩ := ResU.single_get_eq_some g₂
    rw [hnone] at e; exact absurd e (by simp)
  · obtain ⟨rfl, -⟩ := ResU.single_get_eq_some g₂
    rw [hnone] at e; exact absurd e (by simp)

end BoCa.Fig16

alias TR.lemma_6_17 := BoCa.Fig16.ResU.compatS_of_hash_mut

/-!
## Lemma 6.18 · `[TR]` p. 8 · `proved`

> If ρ₁ ▸◂ ρ₂ then ex(ρ₁ ● ρ₂)_● and ex(ρ₁)_● ● ex(ρ₂)_● are Kleene-equal (the left-hand side is defined iff the right-hand side is, and in case both are defined they are equal).

**Printed proof, transcribed.** `ρ₁ ▸◂ ρ₂` makes the own-or-mut cells of `ρ₁` and `ρ₂` disjoint.  Writing `ρ₁₂ = ρ₁ ● ρ₂`, the Kleene equalities
`ex(ρ₁₂)_● = ρ₁₂∣own ● ρ₁₂∣mut ● ⨀_{mut(_,_,ρ′,_)∈ρ₁₂} ex(ρ′)_●`
`= (ρ₁∣own ● ρ₂∣own) ● (ρ₁∣mut ● ρ₂∣mut) ● (⨀_{mut(_,_,ρ′,_)∈ρ₁} ex(ρ′)_●) ● (⨀_{mut(_,_,ρ′,_)∈ρ₂} ex(ρ′)_●)`
`= (ρ₁∣own ● ρ₁∣mut ● ⨀_{…∈ρ₁} ex(ρ′)_●) ● (ρ₂∣own ● ρ₂∣mut ● ⨀_{…∈ρ₂} ex(ρ′)_●) = ex(ρ₁)_● ● ex(ρ₂)_●`.

**Lean.** `BoCa.Fig16.ExS.split`, alias `TR.lemma_6_18`, tag `[as printed]` — declared in `Paper/S6_1_StandardLemmas/Lemmas.lean`, ahead of this subsection: the Lean of Lemmas 6.7, 6.8, 6.10, 6.11 and 6.15 there needs it.

**Note.** `Fig16.ExS.split`, on the printed carrier, as one Kleene equality rather than two halves: the `↔` between the two graphs at an arbitrary common result, which is the print's own gloss since `Fig16.ExS.functional` and `Fig16.ResU.Comp.functional` make both sides single-valued. The sole hypothesis is `Fig16.ResU.CompS ρ₁ ρ₂ ρ₁₂`, whose first conjunct is the printed `▸◂`; nothing constrains `ρ₁`, `ρ₂`, `ρ₁₂` or the result further.
-/
alias TR.lemma_6_18 := BoCa.Fig16.ExS.split

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.19 · `[TR]` p. 9 · `proved`

> If ⦇ρ⦈_○ defined then ⦇ρ⦈_○ and ⦇ρ⦈_○ ○ ⦇ρ⦈_○ are Kleene-equal.

**Printed proof, transcribed.** By induction on `ρ`, mutual with the statement that `ag(ρ)` and `ag(ρ) ○ ag(ρ)` are Kleene-equal.

**Lean.** `BoCa.Fig16.ResU.flatR_idem`, alias `TR.lemma_6_19`, tag `[as printed]`.

**Note.** `Fig16.ResU.flatR_idem`, on the printed carrier. The `FlatR` hypothesis is bound and unused — ours is the stronger theorem (convention 5) — so `Fig16.ResU.flatR_single_own` is supplied to show the hypothesis is satisfiable and the row is not vacuous
-/
/-- **`[TR]` Lemma 6.19** (p. 9): if `⦇ρ⦈_○` is defined then `⦇ρ⦈_○` and
`⦇ρ⦈_○ ○ ⦇ρ⦈_○` are Kleene-equal.  The two conjuncts are the two halves of
Kleene equality: the composite is defined, and every value of it is `⦇ρ⦈_○`.
`[as printed]` -/
theorem ResU.flatR_idem {ρ σ : ResU Loc Val} (_ : ResU.FlatR ρ σ) :
    ResU.CompR σ σ σ ∧ ∀ τ, ResU.CompR σ σ τ → τ = σ :=
  ⟨ResU.compR_self σ, fun _ hτ => ResU.CompR.functional hτ (ResU.compR_self σ)⟩

end BoCa.Fig16

alias TR.lemma_6_19 := BoCa.Fig16.ResU.flatR_idem

/-!
## Lemma 6.20 · `[TR]` p. 9 · `proved`

> If ρ₁ ▸◂ ρ₂ then ag(ρ₁ ● ρ₂) and ag(ρ₁) ○ ag(ρ₂) are Kleene-equal.

**Printed proof, transcribed.** `ρ₁ ▸◂ ρ₂` makes the `mut` cells disjoint and the `imm` cells agree up to lifetimes.  With `ρ₁₂ = ρ₁ ● ρ₂`, `ag(ρ₁₂) = ρ₁₂∣imm ○ ◯_{mut(_,_,ρ′,_)∈ρ₁₂} ag(ρ′) ○ ◯_{imm(_,_,ρ′)∈ρ₁₂} ⦇ρ′⦈_○ = (ρ₁∣imm ○ ρ₂∣imm) ○ (◯_{mut∈ρ₁} ag(ρ′) ○ ◯_{mut∈ρ₂} ag(ρ′)) ○ ρ_ag`.  The big composite `ρ_ag` has one component per `imm` cell of `ρ₁₂`, and those are the union up to lifetimes of the `imm` cells of `ρ₁` and of `ρ₂`, so by inclusion–exclusion `ρ_ag = ◯_{ρ₁∖ρ₂} ○ ◯_{ρ₂∖ρ₁} ○ ◯_{ρ₁∩ρ₂}`; by Lemma 6.19 the shared block equals itself composed with itself, so `ρ_ag = ◯_{imm∈ρ₁} ⦇ρ′⦈_○ ○ ◯_{imm∈ρ₂} ⦇ρ′⦈_○`.  Regrouping, `ag(ρ₁ ● ρ₂) = (ρ₁∣imm ○ ◯_{mut∈ρ₁} ag(ρ′) ○ ◯_{imm∈ρ₁} ⦇ρ′⦈_○) ○ (the same for ρ₂) = ag(ρ₁) ○ ag(ρ₂)`.

**Lean.** `BoCa.Fig16.AgW.split`, alias `TR.lemma_6_20`, tag `[as printed]` — declared in `Paper/S6_1_StandardLemmas/Lemmas.lean`, ahead of this subsection: the Lean of Lemmas 6.7, 6.8, 6.10, 6.11 and 6.15 there needs it.

**Note.** `Fig16.AgW.split`, on the printed carrier, the same shape as 6.18: hypothesis at `●`, conclusion composing at `○`, as printed. The print's inclusion-exclusion over `ρ₁∖ρ₂`, `ρ₂∖ρ₁`, `ρ₁∩ρ₂` is `Fig16.ResU.Sites.split_pairs_imm` forward and `Fig16.AgWitsI.assemble` backward; the appeal to 6.19 that duplicates the shared block is `Fig16.BigComp.dupR`, which at `○` needs only `Fig16.ResU.compR_self`. `Fig16.SplitExample.overlap` runs the lemma on two resources that genuinely share an `imm` location, so the row is not vacuous at the case the inclusion-exclusion exists for.
-/
alias TR.lemma_6_20 := BoCa.Fig16.AgW.split

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.41 · `[TR]` p. 15 · `proved`

> If ℓ ↦ own(−) ▸◂ ρ, then ℓ ∉ ρ.

**Printed proof, transcribed.** By definition.

**Lean.** `BoCa.Fig16.ResU.compatS_single_own`, alias `TR.lemma_6_41`, tag `[as printed]`.

**Note.** `Fig16.ResU.compatS_single_own`, on the printed carrier — the `own` instance of `Fig16.ResU.compatS_single_not_imm`, which states 6.41 and 6.42 once for any cell whose tag is not `imm`. The `[as printed]` tag sits on the instance, per the preamble's rule; the fused theorem carries `[variant]`.
-/
/-- **`[TR]` Lemma 6.41** (p. 15): if `ℓ ↦ own(v) ▶◀ ρ` then `ℓ ∉ ρ`.
`[as printed]` -/
theorem ResU.compatS_single_own {l : Loc} {v : Val} {ρ : ResU Loc Val}
    (h : ResU.CompatS (ResU.single l (CellU.ownOf v)) ρ) : ρ.get l = none :=
  ResU.compatS_single_not_imm (by simp) h

end BoCa.Fig16

alias TR.lemma_6_41 := BoCa.Fig16.ResU.compatS_single_own

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {Loc Val : Type}

/-!
## Lemma 6.21 · `[TR]` p. 10 · `proved`

> If ρ # ρ_v ● ℓ ↦ own(v) then ρ ▸◂ ℓ ↦ mut(α, v, ρ_v, P̂)

**Printed proof, transcribed.** The hypothesis makes `ρ ● ρ_v ● (ℓ ↦ own(v))` defined, which implies `ℓ ∉ dom(ρ)`, which implies `ρ ▸◂ ℓ ↦ mut(α, v, ρ_v, P̂)`.

**Lean.** `BoCa.Fig16.ResU.six21`, alias `TR.lemma_6_21`, tag `[as printed]`.

**Note.** `Fig16.ResU.six21`, on the printed carrier, `[as printed]`, with the printed `ρ_v ● ℓ ↦ own(v)` as its graph (G4). The printed proof's three steps are the three: `#`'s own `▸◂` puts the `own` cell at `ℓ` (`ResU.compatS_single_own`, then `ResU.Comp.get_of_left_none`), `●` admits no second cell beside an `own` one (`ResU.CompatS.right_eq_none`), and a location free in `ρ` makes the singleton disjoint.
-/
/-- **`[TR]` Lemma 6.21** (p. 10): if `ρ # ρ_v ● ℓ ↦ own(v)` then
`ρ ▸◂ ℓ ↦ mut(α, v, ρ_v, P̂)`.

The printed proof is one line: *"The hypothesis implies the composite
`ρ ● ρ_v ● (ℓ ↦ own(v))` is well-defined, which implies `ℓ ∉ dom(ρ)`, which
implies `ρ ▸◂ ℓ ↦ mut(α, v, ρ_v, P̂)` as needed."*  The three steps are the
three here: `#`'s own `▸◂` puts the `own` cell into `ρ_v ● ℓ ↦ own(v)` at `ℓ`
(`ResU.compatS_single_own` for `ρ_v(ℓ) = ⊥`, then `ResU.Comp.get_of_left_none`),
`●` admits no second cell beside an `own` one
(`ResU.CompatS.right_eq_none`), and a location free in `ρ` makes the singleton
disjoint from it.  The printed `ρ_v ● ℓ ↦ own(v)` is a partial term and appears
as its graph `hW` (G4).  `[as printed]` -/
theorem ResU.six21 {l : Loc} {b : Life} {v : Val} {ρ ρv W : ResU Loc Val}
    {hstr : ResU.InStratum b ρv} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρv, hstr⟩}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W) (h : ResU.Hash ρ W) :
    ResU.CompatS ρ (ResU.single l (CellU.mutOf b v ρv hstr P hw)) := by
  have hρvl : ρv.get l = none := ResU.compatS_single_own (ResU.CompatS.symm hW.1)
  have hWl : W.get l = some (CellU.ownOf v) := by
    rw [ResU.Comp.get_of_left_none hW hρvl]; exact ResU.single_get_self _ _
  have hρl : ρ.get l = none :=
    ResU.CompatS.right_eq_none (ResU.CompatS.symm h.1) hWl (by simp)
  refine ResU.Compat.of_disjoint (fun x => ?_)
  by_cases hx : x = l
  · exact Or.inl (hx ▸ hρl)
  · exact Or.inr (ResU.single_get_ne _ hx)

end BoCa.Fig16

alias TR.lemma_6_21 := BoCa.Fig16.ResU.six21

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {Loc Val : Type}

/-!
## Lemma 6.22 · `[TR]` p. 10 · `proved`

> If ρ # ℓ ↦ mut(α, v, ρ_v, P̂) then ρ # ρ_v ● ℓ ↦ own(v)

**Printed proof, transcribed.** Let `ρ_o = ℓ ↦ own(v)`, `ρ_m = ℓ ↦ mut(α, v, ρ_v, P̂)`.  The hypothesis gives `✓(ρ ● ρ_m)`, i.e. `ρ_hyp ≔ ex(ρ)_● ● ex(ρ_v)_● ● ρ_m ● (ag(ρ) ○ ag(ρ_v))` is defined.  `ρ ▸◂ ρ_v ● ρ_o` is Lemma 6.17, so it remains to show `✓(ρ ● ρ_v ● ρ_o)`, i.e. that `ρ_goal ≔ ex(ρ ● ρ_v)_● ● ρ_o ● ag(ρ ● ρ_v)` is defined.  By Lemma 6.17 `ρ ● ρ_v` is defined, so by Lemmas 6.18 and 6.20 `ρ_goal` is defined iff `(ex(ρ)_● ● ex(ρ_v)_●) ● ρ_o ● (ag(ρ) ○ ag(ρ_v))` is.  Since `ρ_o` contains a single `own` cell, that composite is defined iff the same composite with `ρ_m` for `ρ_o` is, which is `ρ_hyp`.

**Lean.** `BoCa.Fig16.ResU.six22`, alias `TR.lemma_6_22`, tag `[as printed]`.

**Note.** `Fig16.ResU.six22`, on the printed carrier, `[as printed]`, the printed proof in its own order: 6.17 (`Fig16.ResU.compatS_of_hash_mut`) for the `▸◂` and 6.9 (`Fig16.ResU.compS_defined_iff`) to turn it into the composite, then the two named composites read off by 6.18 (`Fig16.ExS.split`) and 6.20 (`Fig16.AgW.split`) with the `mut` cell's own rows (`Fig16.ExW.single_mut_inv`, `Fig16.AgW.single_mut_inv`). The closing sentence — *"since `ρ_o` contains a single `own` cell"* — is `Fig16.ResU.compatS_congr_of_excl`, spent at both compositions.
-/
/-- **`[TR]` Lemma 6.22** (p. 10): if `ρ # ℓ ↦ mut(α, v, ρ_v, P̂)` then
`ρ # ρ_v ● ℓ ↦ own(v)`.

The printed proof in its own order.  *"We have that `ρ ▸◂ ρ_v ● ρ_o` by theorem
6.17"* is `ResU.compatS_of_hash_mut`, and 6.9 (`ResU.compS_defined_iff`) turns
that `▸◂` into the composite, exactly as 6.17's own proof uses 6.9 in the other
direction.  *"so it only remains to show `✓(ρ ● ρ_v ● ρ_o)`"* is the remaining
goal.  The two composites the print names are read off by 6.18 (`ExS.split`)
and 6.20 (`AgW.split`): `ρ_hyp` is `ex(ρ)_● ● (ρ_m ● ex(ρ_v)_●)` against
`ag(ρ) ○ ag(ρ_v)`, the `mut` cell's own two rows supplying the inner factors
(`ExW.single_mut_inv`, `AgW.single_mut_inv`); `ρ_goal` is the same with
`ex(ρ_v)_● ● ρ_o` in place of `ρ_m ● ex(ρ_v)_●`, its `ag` side unchanged
because `ag(ℓ ↦ own(v)) = ∅`.  The closing sentence is
`ResU.compatS_congr_of_excl`, spent twice — once at the inner composition and
once at the outer one, `ResU.compS_agree_off_right` carrying the agreement off
`ℓ` between them.  `[as printed]` -/
theorem ResU.six22 {l : Loc} {b : Life} {v : Val} {ρ ρv W : ResU Loc Val}
    {hstr : ResU.InStratum b ρv} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρv, hstr⟩}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W)
    (h : ResU.Hash ρ (ResU.single l (CellU.mutOf b v ρv hstr P hw))) :
    ResU.Hash ρ W := by
  classical
  have hmk : (CellU.mutOf b v ρv hstr P hw).kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hcompat : ResU.CompatS ρ W := ResU.compatS_of_hash_mut h hW
  obtain ⟨σ, hσ⟩ := (ResU.compS_defined_iff ρ W).mpr hcompat
  refine ⟨hcompat, σ, hσ, ?_⟩
  obtain ⟨-, σm, hσm, hvm⟩ := h
  obtain ⟨F, hF⟩ := hvm
  obtain ⟨e₁, e₂, e, a₁, a₂, a, he₁, he₂, hec, ha₁, ha₂, hac, hF'⟩ :=
    (ResU.Flat.split hσm).mp hF
  obtain ⟨ev, hev, hcev⟩ := ExW.single_mut_inv he₂
  have havv : AgW ρv a₂ := AgW.single_mut_inv ha₂
  have hevl : ev.get l = none := ResU.compatS_single_mut hcev.1
  obtain ⟨eW, hceW⟩ := (ResU.compS_defined_iff ev (ResU.single l (CellU.ownOf v))).mpr
    (ResU.Compat.of_disjoint (fun x => by
      by_cases hx : x = l
      · exact Or.inl (hx ▸ hevl)
      · exact Or.inr (ResU.single_get_ne _ hx)))
  have hEW : ExS W eW := (ExS.split hW).mpr ⟨ev, _, hev, ExW.single_own l v, hceW⟩
  have hAW : AgW W a₂ :=
    (AgW.split hW).mpr ⟨a₂, _, havv, AgW.single_own l v, ResU.comp_empty_right a₂⟩
  have he₂l : e₂.get l = some (CellU.mutOf b v ρv hstr P hw) := by
    rw [ResU.Comp.get_of_right_none hcev hevl]; exact ResU.single_get_self _ _
  have hoff : ∀ x, x ≠ l → eW.get x = e₂.get x := by
    intro x hx
    rw [ResU.Comp.get_of_right_none hceW (ResU.single_get_ne _ hx),
      ResU.Comp.get_of_left_none hcev (ResU.single_get_ne _ hx)]
  obtain ⟨e', hce'⟩ := (ResU.compS_defined_iff e₁ eW).mpr
    (ResU.CompatS.symm (ResU.compatS_congr_of_excl hoff he₂l hmk
      (ResU.CompatS.symm hec.1)))
  have hoffe : ∀ x, x ≠ l → e'.get x = e.get x :=
    ResU.compS_agree_off_right hec hce' hoff
  have he₁l : e₁.get l = none :=
    ResU.CompatS.right_eq_none (ResU.CompatS.symm hec.1) he₂l hmk
  have hel : e.get l = some (CellU.mutOf b v ρv hstr P hw) := by
    rw [ResU.Comp.get_of_left_none hec he₁l]; exact he₂l
  obtain ⟨G, hG⟩ := (ResU.compS_defined_iff e' a).mpr
    (ResU.compatS_congr_of_excl hoffe hel hmk hF'.1)
  exact ⟨G, (ResU.Flat.split hσ).mpr
    ⟨e₁, eW, e', a₁, a₂, a, he₁, hEW, hce', ha₁, hAW, hac, hG⟩⟩

end BoCa.Fig16

alias TR.lemma_6_22 := BoCa.Fig16.ResU.six22

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {Loc Val : Type}

/-!
## Lemma 6.23 · `[TR]` p. 10 · `proved`

> If ρ # ρ_v ● ℓ ↦ own(v) then ρ # ℓ ↦ mut(α, v, ρ_v, P̂)

**Printed proof, transcribed.** Analogous to Lemma 6.22.  `ρ ▸◂ ρ_m` is Lemma 6.21, so it remains to show that `ρ_goal ≔ ex(ρ)_● ● ex(ρ_v)_● ● ρ_m ● (ag(ρ) ○ ag(ρ_v))` is defined given `ρ_hyp ≔ ex(ρ ● ρ_v)_● ● ρ_o ● ag(ρ ● ρ_v)`.  The assumption makes `ρ ● ρ_v` defined, so by Lemmas 6.18 and 6.20 `ρ_hyp`'s definedness is that of `ex(ρ)_● ● ex(ρ_v)_● ● ρ_o ● (ag(ρ) ○ ag(ρ_v))`; since `ρ_o` contains a single `own` cell, replacing it by `ρ_m` preserves definedness, which is `ρ_goal`.

**Lean.** `BoCa.Fig16.ResU.six23`, alias `TR.lemma_6_23`, tag `[as printed]`.

**Note.** `Fig16.ResU.six23`, on the printed carrier, `[as printed]`. *"Analogous to theorem 6.22"*: the same proof with the two composites exchanged and 6.21 in place of 6.17, closing on the same `Fig16.ResU.compatS_congr_of_excl` run the other way; the `mut` side's walks are built rather than taken apart (`Fig16.ExW.single_mut`, `Fig16.AgW.single_mut`).
-/
/-- **`[TR]` Lemma 6.23** (p. 10): if `ρ # ρ_v ● ℓ ↦ own(v)` then
`ρ # ℓ ↦ mut(α, v, ρ_v, P̂)`.

*"Analogous to theorem 6.22."*  The printed proof is 6.22's with the two
composites exchanged and 6.21 in place of 6.17 for the `▸◂`: `ρ_hyp` is now the
`own` side and `ρ_goal` the `mut` side, and the closing sentence is the same
one, `ResU.compatS_congr_of_excl`, run the other way.  The `mut` side's walks
are built rather than taken apart, by `ExW.single_mut` and `AgW.single_mut`.
`[as printed]` -/
theorem ResU.six23 {l : Loc} {b : Life} {v : Val} {ρ ρv W : ResU Loc Val}
    {hstr : ResU.InStratum b ρv} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρv, hstr⟩}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W) (h : ResU.Hash ρ W) :
    ResU.Hash ρ (ResU.single l (CellU.mutOf b v ρv hstr P hw)) := by
  classical
  have hok : (CellU.ownOf (Loc := Loc) v).kind ≠ Kind.imm := by simp
  have hcompat : ResU.CompatS ρ (ResU.single l (CellU.mutOf b v ρv hstr P hw)) :=
    ResU.six21 hW h
  obtain ⟨σ, hσ⟩ :=
    (ResU.compS_defined_iff ρ (ResU.single l (CellU.mutOf b v ρv hstr P hw))).mpr hcompat
  refine ⟨hcompat, σ, hσ, ?_⟩
  obtain ⟨-, σW, hσW, hvW⟩ := h
  obtain ⟨F, hF⟩ := hvW
  obtain ⟨e₁, eW, e, a₁, aW, a, he₁, heW, hec, ha₁, haW, hac, hF'⟩ :=
    (ResU.Flat.split hσW).mp hF
  obtain ⟨ev, eo, hev, heo, hceW⟩ := (ExS.split hW).mp heW
  obtain ⟨av, ao, hav, hao, hcaW⟩ := (AgW.split hW).mp haW
  rw [ExS.functional heo (ExW.single_own l v)] at hceW
  rw [AgW.functional hao (AgW.single_own l v)] at hcaW
  obtain rfl : aW = av := ResU.CompR.functional hcaW (ResU.comp_empty_right av)
  have hevl : ev.get l = none :=
    ResU.compatS_single_own (ResU.CompatS.symm hceW.1)
  obtain ⟨e₂, hce₂⟩ :=
    (ResU.compS_defined_iff (ResU.single l (CellU.mutOf b v ρv hstr P hw)) ev).mpr
      (ResU.Compat.of_disjoint (fun x => by
        by_cases hx : x = l
        · exact Or.inr (hx ▸ hevl)
        · exact Or.inl (ResU.single_get_ne _ hx)))
  have hE₂ : ExS (ResU.single l (CellU.mutOf b v ρv hstr P hw)) e₂ :=
    ExW.single_mut hev hce₂
  have hA₂ : AgW (ResU.single l (CellU.mutOf b v ρv hstr P hw)) aW :=
    AgW.single_mut hav
  have heWl : eW.get l = some (CellU.ownOf v) := by
    rw [ResU.Comp.get_of_left_none hceW hevl]; exact ResU.single_get_self _ _
  have hoff : ∀ x, x ≠ l → e₂.get x = eW.get x := by
    intro x hx
    rw [ResU.Comp.get_of_left_none hce₂ (ResU.single_get_ne _ hx),
      ResU.Comp.get_of_right_none hceW (ResU.single_get_ne _ hx)]
  obtain ⟨e', hce'⟩ := (ResU.compS_defined_iff e₁ e₂).mpr
    (ResU.CompatS.symm (ResU.compatS_congr_of_excl hoff heWl hok
      (ResU.CompatS.symm hec.1)))
  have hoffe : ∀ x, x ≠ l → e'.get x = e.get x :=
    ResU.compS_agree_off_right hec hce' hoff
  have he₁l : e₁.get l = none :=
    ResU.CompatS.right_eq_none (ResU.CompatS.symm hec.1) heWl hok
  have hel : e.get l = some (CellU.ownOf v) := by
    rw [ResU.Comp.get_of_left_none hec he₁l]; exact heWl
  obtain ⟨G, hG⟩ := (ResU.compS_defined_iff e' a).mpr
    (ResU.compatS_congr_of_excl hoffe hel hok hF'.1)
  exact ⟨G, (ResU.Flat.split hσ).mpr
    ⟨e₁, e₂, e', a₁, aW, a, he₁, hE₂, hce', ha₁, hA₂, hac, hG⟩⟩

end BoCa.Fig16

alias TR.lemma_6_23 := BoCa.Fig16.ResU.six23

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {Loc Val : Type}

/-!
## Lemma 6.24 · `[TR]` p. 10 · `proved`

> ρ # ℓ ↦ mut(α, v, ρ_v, P̂) iff ρ # ρ_v ● ℓ ↦ own(v)

**Printed proof, transcribed.** Combine Lemmas 6.22 and 6.23.

**Lean.** `BoCa.Fig16.ResU.six24`, alias `TR.lemma_6_24`, tag `[as printed]`.

**Note.** `Fig16.ResU.six24`, on the printed carrier, `[as printed]`; *"combine theorems 6.22 and 6.23"* is the two halves and nothing else. The printed `ρ_v ● ℓ ↦ own(v)` is a partial term and appears as its graph (G4), which is the print's presupposition that it is defined (convention F1). Not vacuous: `Fig16.ResU.hash_empty_single_mut` inhabits the left side.
-/
/-- **`[TR]` Lemma 6.24** (p. 10): `ρ # ℓ ↦ mut(α, v, ρ_v, P̂)` iff
`ρ # ρ_v ● ℓ ↦ own(v)`.  *"Combine theorems 6.22 and 6.23."*  `[as printed]` -/
theorem ResU.six24 {l : Loc} {b : Life} {v : Val} {ρ ρv W : ResU Loc Val}
    {hstr : ResU.InStratum b ρv} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρv, hstr⟩}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W) :
    ResU.Hash ρ (ResU.single l (CellU.mutOf b v ρv hstr P hw)) ↔ ResU.Hash ρ W :=
  ⟨fun h => ResU.six22 hW h, fun h => ResU.six23 hW h⟩

end BoCa.Fig16

alias TR.lemma_6_24 := BoCa.Fig16.ResU.six24

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {Loc Val : Type}

/-!
## Lemma 6.25 · `[TR]` p. 10 · `proved`

> Assuming all resources and composition are defined, ⟦ℓ ↦ mut(α, v, ρ_v, P̂)⟧ = ⟦ρ_v ● ℓ ↦ own(v)⟧

**Printed proof, transcribed.** By unfolding.

**Lean.** `BoCa.Fig16.ResU.six25`, alias `TR.lemma_6_25`, tag `[as printed]`.

**Note.** `Fig16.ResU.six25`, on the printed carrier, `[as printed]`, as one Kleene equality: both sides are partial terms, so the printed `=` is the `↔` between the two graphs at an arbitrary common memory, the shape of 6.18 and 6.20. *"By unfolding"* splits the other way from its `imm` twin 6.26: at a `mut` cell `ex` carries the cell (`ExW.single_mut_inv`) and `ag` is the witness's alone (`AgW.single_mut_inv`), both at `●`, so no 6.33 is spent where 6.26 must spend it. *"Assuming all resources and composition are defined"* is three hypotheses and each is spent.
-/
/-- **`[TR]` Lemma 6.25** (p. 10): assuming all resources and composition are
defined, `⟦ℓ ↦ mut(α, v, ρ_v, P̂)⟧ = ⟦ρ_v ● ℓ ↦ own(v)⟧`.

*"By unfolding."*  On the left, `ex` at the one `mut` cell is the cell composed
with `ex(ρ_v)_●` (`ExW.single_mut_inv`) and `ag` is `ag(ρ_v)`
(`AgW.single_mut_inv`), so `⦇ℓ ↦ mut(α, v, ρ_v, P̂)⦈` is
`ℓ ↦ mut(α, v, ρ_v, P̂) ● ⦇ρ_v⦈` after 6.3 (`ResU.CompS.assoc`).  On the right,
6.18 (`ExS.split`) and 6.20 (`AgW.split`) with `ExW.single_own` and
`AgW.single_own` give `ex(ρ_v)_● ● ℓ ↦ own(v) ● ag(ρ_v)`, and 6.3 with 6.2
(`ResU.CompS.comm`) moves the cell to the front, leaving `⦇ρ_v⦈` behind it.
`ℓ ∉ dom(⦇ρ_v⦈)` is the `own` cell's own `▸◂` (`ResU.compatS_single_own`,
6.41), so the two flattenings differ at `ℓ` and nowhere else, and there
`⟦mut(α, v, ρ_v, P̂)⟧ = v = ⟦own(v)⟧`.  Unlike its `imm` twin 6.26
this spends no 6.33: see the section note.

The printed `=` is Kleene equality between two partial terms, so it is the `↔`
between the two graphs at an arbitrary common memory — the shape of
6.18, 6.20 and 6.7.  *"Assuming all resources and composition are
defined"* is `hW`, `hvm` and `hvW`, and each is spent: the composition in both
directions, and one lowering's guard per direction.
`[as printed]` (the printed `●` and both `⟦−⟧` appear as their graphs — G4) -/
theorem ResU.six25 {l : Loc} {b : Life} {v : Val} {ρv W : ResU Loc Val}
    {hstr : ResU.InStratum b ρv} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρv, hstr⟩}
    {m : Loc → Option Val}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W)
    (hvm : ResU.Valid (ResU.single l (CellU.mutOf b v ρv hstr P hw)))
    (hvW : ResU.Valid W) :
    ResU.Lower (ResU.single l (CellU.mutOf b v ρv hstr P hw)) m ↔ ResU.Lower W m := by
  classical
  obtain ⟨hvv, -⟩ := ResU.Valid.split hW hvW
  obtain ⟨τ, eτ, aτ, heτ, haτ, hcτ⟩ := hvv
  obtain ⟨σW, hσW⟩ := hvW
  obtain ⟨E₁, E₂, E, A₁, A₂, A, hE₁, hE₂, hEc, hA₁, hA₂, hAc, hσ⟩ :=
    (ResU.Flat.split hW).mp hσW
  rw [ExS.functional hE₁ heτ, ExS.functional hE₂ (ExW.single_own l v)] at hEc
  rw [AgW.functional hA₁ haτ, AgW.functional hA₂ (AgW.single_own l v)] at hAc
  rw [ResU.CompR.functional hAc (ResU.comp_empty_right aτ)] at hσ
  obtain ⟨x, hx₁, hx₂⟩ :=
    (ResU.CompS.assoc eτ (ResU.single l (CellU.ownOf v)) aτ σW).mpr ⟨E, hEc, hσ⟩
  obtain ⟨z, hz₁, hz₂⟩ :=
    (ResU.CompS.assoc (ResU.single l (CellU.ownOf v)) aτ eτ σW).mpr
      ⟨x, hx₁, ResU.CompS.comm hx₂⟩
  rw [ResU.CompS.functional hz₁ (ResU.CompS.comm hcτ)] at hz₂
  have hτl : τ.get l = none := ResU.compatS_single_own hz₂.1
  obtain ⟨σM, hσM⟩ := hvm
  obtain ⟨EM, AM, hEM, hAM, hcM⟩ := id hσM
  obtain ⟨e, he, hce⟩ := ExW.single_mut_inv hEM
  rw [ExS.functional he heτ] at hce
  rw [AgW.functional (AgW.single_mut_inv hAM) haτ] at hcM
  obtain ⟨y, hy₁, hy₂⟩ :=
    (ResU.CompS.assoc (ResU.single l (CellU.mutOf b v ρv hstr P hw)) eτ aτ σM).mpr
      ⟨EM, hce, hcM⟩
  rw [ResU.CompS.functional hy₁ hcτ] at hy₂
  have hagree : ∀ l', (σM.get l').map CellU.erase = (σW.get l').map CellU.erase := by
    intro l'
    by_cases hl : l' = l
    · subst hl
      rw [ResU.Comp.get_of_right_none hy₂ hτl, ResU.Comp.get_of_right_none hz₂ hτl,
        ResU.single_get_self, ResU.single_get_self]
      rfl
    · rw [ResU.Comp.get_of_left_none hy₂ (ResU.single_get_ne _ hl),
        ResU.Comp.get_of_left_none hz₂ (ResU.single_get_ne _ hl)]
  constructor
  · rintro ⟨σ, hσ', hm⟩
    cases ResU.Flat.functional hσ' hσM
    exact ⟨σW, hσW, fun l' => (hm l').trans (hagree l')⟩
  · rintro ⟨σ, hσ', hm⟩
    cases ResU.Flat.functional hσ' hσW
    exact ⟨σM, hσM, fun l' => (hm l').trans (hagree l').symm⟩

end BoCa.Fig16

alias TR.lemma_6_25 := BoCa.Fig16.ResU.six25

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.32 · `[TR]` p. 11 · `proved`

> If ex(ρ)_● defined, then ex(ρ)_● = ex(ρ)_○.

**Printed proof, transcribed.** By induction on `ρ`, unfolding `ex`, and repeatedly applying Lemma 6.31.

**Lean.** `BoCa.Fig16.ExS.toExR`, alias `TR.lemma_6_32`, tag `[as printed]`.

**Note.** `Fig16.ExS.toExR`, on the printed carrier, `[as printed]`, both walks named by their graphs (G4): definedness of `ex(ρ)●` is the hypothesis `ExS ρ σ`, and the printed `=` is then `Fig16.ExR.functional` against any other value. The printed proof — *"by induction on `ρ`, unfolding `ex`, and repeatedly applying lemma 6.31"* — is the induction the walk is defined by (`ExW.rec`, three motives), with 6.31 as `Fig16.ResU.CompS.toCompR` at the two `◐`s and `Fig16.BigComp.toR` at the `⨀`: the index set, the family and the fold are the same objects and only the mode changes. Needed by 6.29, whose proof reasons about `⦇−⦈` while `ag`'s `imm` row calls `ex(−)_○`.
-/
/-- **`[TR]` Lemma 6.32** (p. 12): if `ex(ρ)●` is defined then
`ex(ρ)● = ex(ρ)_○`.

*"By induction on `ρ`, unfolding `ex`, and repeatedly applying lemma 6.31."*
Here the induction is the one the walk is defined by, and 6.31 is
`ResU.CompS.toCompR`: the derivation's index set, family and fold are the same
objects, and only the two `◐`s and the `⨀` change mode.  Definedness of
`ex(ρ)●` is the hypothesis `ExS ρ σ` (G4), and the printed `=` is then
`ExR.functional` against any other value.
`[as printed]` (both walks appear as their graphs — G4) -/
theorem ExS.toExR {ρ σ : ResU Loc Val} (h : ExS ρ σ) : ExR ρ σ := by
  refine ExW.rec (motive_1 := fun ρ σ _ => ExR ρ σ)
    (motive_2 := fun ρ w _ => ExWits CellU.CompatR CellU.CompR ρ w) ?mk ?nil ?cons h
  case mk =>
    intro ρ' σ' nm b w hs _ hb hnm hσ ihw
    exact ExW.mk hs ihw (BigComp.toR hb) (ResU.CompS.toCompR hnm)
      (ResU.CompS.toCompR hσ)
  case nil => intro ρ'; exact ExWits.nil
  case cons =>
    intro ρ' e l w ψ hψ hk _ _ ihe ihw
    exact ExWits.cons ψ hψ hk ihe ihw

end BoCa.Fig16

alias TR.lemma_6_32 := BoCa.Fig16.ExS.toExR

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.33 · `[TR]` p. 11 · `proved`

> If ⦇ρ⦈ defined, then ⦇ρ⦈ = ⦇ρ⦈_○.

**Printed proof, transcribed.** By unfolding `⦇−⦈` and `⦇−⦈_○`, and applying Lemmas 6.31 and 6.32.

**Lean.** `BoCa.Fig16.ResU.six33`, alias `TR.lemma_6_33`, tag `[as printed]`.

**Note.** `Fig16.ResU.six33`, on the printed carrier, `[as printed]` — three lines, as the printed proof is: *"By unfolding `⦇−⦈` and `⦇−⦈_○`, and applying lemmas 6.31 and 6.32."*  6.32 is `Fig16.ExS.toExR`, 6.31 is `Fig16.ResU.CompS.toCompR`, and the two definitions differ only in the order of the two walks, which `Fig16.ResU.CompR.comm` settles. Both flattenings are named by their graphs (G4), so "defined" is the hypothesis `Fig16.ResU.Flat ρ σ`. [TR] 6.39's normal-form display needs it: `ag`'s `imm` family hands back `⦇ρ_v⦈_○` and the display wants `⦇ρ_v⦈ = ex(ρ_v)● ● ag(ρ_v)` so the exclusive half can be split into the outer `●`
-/
/-- **`[TR]` Lemma 6.33** (p. 11): if `⦇ρ⦈` is defined then `⦇ρ⦈ = ⦇ρ⦈_○`.

The printed proof: *"By unfolding `⦇−⦈` and `⦇−⦈_○`, and applying lemmas 6.31
and 6.32."*  6.32 is `ExS.toExR` and 6.31 is `ResU.CompS.toCompR`, and the two
definitions differ only in the order of the two walks, which `ResU.CompR.comm`
settles.  Both flattenings are named by their graphs (G4), so "defined" is the
hypothesis `ResU.Flat ρ σ`.

`[TR]` 6.39's display needs it: `ag`'s `imm` family hands back `⦇ρ_v⦈_○`, and
the normal form wants `⦇ρ_v⦈ = ex(ρ_v)● ● ag(ρ_v)` so that the exclusive half
can be split off into the outer `●`.  `[as printed]` -/
theorem ResU.six33 {ρ σ : ResU Loc Val} (h : ResU.Flat ρ σ) : ResU.FlatR ρ σ := by
  obtain ⟨e, a, he, ha, hc⟩ := h
  exact ⟨a, e, ha, ExS.toExR he, ResU.CompR.comm (ResU.CompS.toCompR hc)⟩

end BoCa.Fig16

alias TR.lemma_6_33 := BoCa.Fig16.ResU.six33

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {Loc Val : Type}

/-!
## Lemma 6.26 · `[TR]` p. 10 · `proved`

> Assuming all resources and composition are defined, ⟦ℓ ↦ imm(α, v, ρ_v)⟧ = ⟦ρ_v ● ℓ ↦ own(v)⟧

**Printed proof, transcribed.** By unfolding.

**Lean.** `BoCa.Fig16.ResU.six26`, alias `TR.lemma_6_26`, tag `[as printed]`.

**Note.** `Fig16.ResU.six26`, on the printed carrier, `[as printed]`, as one Kleene equality: both sides are partial terms, so the printed `=` is the `↔` between the two graphs at an arbitrary common memory, the shape of 6.18, 6.20 and 6.7. *"Assuming all resources and composition are defined"* is the three hypotheses and nothing beyond them — the printed composition `ρ_v ● ℓ ↦ own(v)` named by its graph (G4), and each `⟦−⟧`'s own guard `✓`; both are spent, one per direction of the `↔`. *"By unfolding"* meets `ag`'s `imm` family, which hands back `ex(ρ_v)_○ ○ ag(ρ_v)`: `Fig16.ResU.six33` (6.33) identifies it with `⦇ρ_v⦈` and `Fig16.ResU.Valid.split` (6.35) is what makes `⦇ρ_v⦈` defined, the same pair 6.38's and 6.39's proofs spend at the same place. `Fig16.AgW.single_imm_inv` and `Fig16.ExW.empty_of_all_imm` evaluate the two walks at the one cell, `Fig16.ResU.compatS_single_own` (6.41) is `ℓ ∉ dom(⦇ρ_v⦈)`, and the two flattenings then differ at `ℓ` alone, where `⟦imm(ᾱ,v,ρ_v)⟧ = v = ⟦own(v)⟧`.
-/
/-- **`[TR]` Lemma 6.26** (p. 10): assuming all resources and composition are
defined, `⟦ℓ ↦ imm(ᾱ, v, ρ_v)⟧ = ⟦ρ_v ● ℓ ↦ own(v)⟧`.

*"By unfolding."*  On the left, `ex(ℓ ↦ imm(ᾱ, v, ρ_v))_● = ∅`
(`ExW.empty_of_all_imm`) and `ag` at the one cell is
`ℓ ↦ imm(ᾱ, v, ρ_v) ○ ⦇ρ_v⦈_○` (`AgW.single_imm_inv`).  On the right, 6.18
(`ExS.split`) and 6.20 (`AgW.split`) with `ExW.single_own` and `AgW.single_own`
give `ex(ρ_v)_● ● ℓ ↦ own(v) ● ag(ρ_v)`, and 6.3 (`ResU.CompS.assoc`) with 6.2
(`ResU.CompS.comm`) move the cell to the front.  The two remainders are
`⦇ρ_v⦈_○` and `⦇ρ_v⦈`, which 6.33 (`ResU.six33`) identifies, `⦇ρ_v⦈` being
defined by 6.35 (`ResU.Valid.split`) at the printed composition.
`ℓ ∉ dom(⦇ρ_v⦈)` is the `own` cell's own `▶◀` (`ResU.compatS_single_own`, 6.41),
so the two flattenings differ at `ℓ` and nowhere else, and there
`⟦imm(ᾱ, v, ρ_v)⟧ = v = ⟦own(v)⟧`.

The printed `=` is Kleene equality between two partial terms, so it is the `↔`
between the two graphs at an arbitrary common memory — the shape of
6.18, 6.20 and 6.7.  *"Assuming all resources and composition are
defined"* is `hW`, `hvi` and `hvW`, and each is spent: the composition in both
directions, and one lowering's guard per direction.
`[as printed]` (the printed `●` and both `⟦−⟧` appear as their graphs — G4) -/
theorem ResU.six26 {l : Loc} {s : LSet} {v : Val} {ρv W : ResU Loc Val}
    {hs : ρv.InStratum s.join} {m : Loc → Option Val}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W)
    (hvi : ResU.Valid (ResU.single l (CellU.immOf s v ρv hs)))
    (hvW : ResU.Valid W) :
    ResU.Lower (ResU.single l (CellU.immOf s v ρv hs)) m ↔ ResU.Lower W m := by
  classical
  -- `⦇ρ_v⦈` is defined, by 6.35 at the printed composition.
  obtain ⟨hvv, -⟩ := ResU.Valid.split hW hvW
  obtain ⟨τ, eτ, aτ, heτ, haτ, hcτ⟩ := hvv
  -- `⦇ρ_v ● ℓ ↦ own(v)⦈ = ℓ ↦ own(v) ● ⦇ρ_v⦈`, by 6.18 and 6.20.
  obtain ⟨σW, hσW⟩ := hvW
  obtain ⟨E₁, E₂, E, A₁, A₂, A, hE₁, hE₂, hEc, hA₁, hA₂, hAc, hσ⟩ :=
    (ResU.Flat.split hW).mp hσW
  rw [ExS.functional hE₁ heτ, ExS.functional hE₂ (ExW.single_own l v)] at hEc
  rw [AgW.functional hA₁ haτ, AgW.functional hA₂ (AgW.single_own l v)] at hAc
  rw [ResU.CompR.functional hAc (ResU.comp_empty_right aτ)] at hσ
  obtain ⟨x, hx₁, hx₂⟩ :=
    (ResU.CompS.assoc eτ (ResU.single l (CellU.ownOf v)) aτ σW).mpr ⟨E, hEc, hσ⟩
  obtain ⟨z, hz₁, hz₂⟩ :=
    (ResU.CompS.assoc (ResU.single l (CellU.ownOf v)) aτ eτ σW).mpr
      ⟨x, hx₁, ResU.CompS.comm hx₂⟩
  rw [ResU.CompS.functional hz₁ (ResU.CompS.comm hcτ)] at hz₂
  -- `ℓ ∉ dom(⦇ρ_v⦈)`, by 6.41 at the `own` cell.
  have hτl : τ.get l = none := ResU.compatS_single_own hz₂.1
  -- `⦇ℓ ↦ imm(ᾱ, v, ρ_v)⦈ = ℓ ↦ imm(ᾱ, v, ρ_v) ○ ⦇ρ_v⦈_○`.
  obtain ⟨σI, hσI⟩ := hvi
  obtain ⟨EI, AI, hEI, hAI, hcI⟩ := id hσI
  rw [ExS.functional hEI (ExW.empty_of_all_imm (fun m' ψ hg => by
      obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hg
      exact CellU.kind_immOf _ _ _ _))] at hcI
  rw [← ResU.CompS.functional hcI (ResU.comp_empty_left AI)] at hAI
  obtain ⟨ev, av, p, hev, hav, hp, hpA⟩ := AgW.single_imm_inv hAI
  rw [ExR.functional hev (ExS.toExR heτ), AgW.functional hav haτ] at hp
  -- 6.33 identifies `⦇ρ_v⦈_○` with `⦇ρ_v⦈`.
  obtain ⟨a', e', ha', he', hc'⟩ :=
    ResU.six33 (show ResU.Flat ρv τ from ⟨eτ, aτ, heτ, haτ, hcτ⟩)
  rw [AgW.functional ha' haτ, ExR.functional he' (ExS.toExR heτ)] at hc'
  rw [ResU.CompR.functional hp (ResU.CompR.comm hc')] at hpA
  -- The two flattenings agree after erasure: at `ℓ` both give `v`, and off `ℓ`
  -- both are `⦇ρ_v⦈`.
  have hagree : ∀ l', (σI.get l').map CellU.erase = (σW.get l').map CellU.erase := by
    intro l'
    by_cases hl : l' = l
    · subst hl
      rw [ResU.Comp.get_of_right_none hpA hτl, ResU.Comp.get_of_right_none hz₂ hτl,
        ResU.single_get_self, ResU.single_get_self]
      rfl
    · rw [ResU.Comp.get_of_left_none hpA (ResU.single_get_ne _ hl),
        ResU.Comp.get_of_left_none hz₂ (ResU.single_get_ne _ hl)]
  constructor
  · rintro ⟨σ, hσ', hm⟩
    cases ResU.Flat.functional hσ' hσI
    exact ⟨σW, hσW, fun l' => (hm l').trans (hagree l')⟩
  · rintro ⟨σ, hσ', hm⟩
    cases ResU.Flat.functional hσ' hσW
    exact ⟨σI, hσI, fun l' => (hm l').trans (hagree l').symm⟩

end BoCa.Fig16

alias TR.lemma_6_26 := BoCa.Fig16.ResU.six26

namespace BoCa.Fig16

/-!
## Lemma 6.63 · `[TR]` p. 22 · `proved`

> α ⊐ ↓α

**Printed proof, transcribed.** Unfolding `↓`, `↓α = α + 1`, and `α < α + 1`, so `α ⊐ α + 1`.

On the printed carrier the statement is `Fig16.Life.down_sqsubset`, `(↓a) ⊏ a`, which is `a ⊐ ↓a` read from the other side; `Life` is `ℕᵒᵈ`, so `↓a = a + 1` and `⊏` is `>` on `ℕ`.

**Lean.** `BoCa.Fig16.Life.down_sqsubset`, alias `TR.lemma_6_63`.

**Note.** `down α ≜ α + 1` and `SLife.Lt a b ≜ b < a`, i.e. `α ⊐ ↓α` as printed
-/
theorem Life.down_sqsubset (a : Life) : (↓a) ⊏ a := Nat.lt_succ_self _

end BoCa.Fig16

alias TR.lemma_6_63 := BoCa.Fig16.Life.down_sqsubset

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.27 · `[TR]` p. 10 · `proved`

> If @ρ ⊐ α and ρ ● ℓ ↦ mut(α, v, ρ_v, P̂) ↭ ρ′ then ρ′ = ρ′/ℓ ● ℓ ↦ mut(α, v′, ρ′_v, P̂)

**Printed proof, transcribed.** Let `ρ_m = ℓ ↦ mut(α, v, ρ_v, P̂)`.  `⦇ρ ● ρ_m⦈` and `⦇ρ′⦈` have the same borrows, so `⦇ρ′⦈` has a `mut` cell matching `ρ_m`: some `ℓ ↦ mut(α, v′, ρ′_v, P̂) ∈ ⦇ρ′⦈`.  Since `@ρ ⊐ α`, every other borrow in `⦇ρ′⦈` is disjoint from `α`, which by well-formedness of the resource `ρ′` means the cell cannot be in any `ρ″` of a `mut(_, _, ρ″, _)` or `imm(_, _, ρ″)` in `ρ′`.  So `ρ′(ℓ) = mut(α, v′, ρ′_v, P̂)` and `ρ′ = ρ′/ℓ ● ℓ ↦ mut(α, v′, ρ′_v, P̂)`.

**Lean.** `BoCa.Fig16.ResU.six27`, alias `TR.lemma_6_27`, tag `[as printed]`.

**Note.** `Fig16.ResU.six27`, on the printed carrier, `[as printed]`, with `@ρ ⊐ α` on the unprimed **pre**-resource as printed and the printed `ρ′ = ρ′/ℓ ● …` as its graph (G4). The printed hypothesis is the whole content: `↭` fixes a `mut` cell at `ℓ` in `⦇ρ′⦈` with the printed `α` and `P̂`, but not that it is `ρ′`'s own, and *"by well-formedness of the resource `ρ′` … the cell cannot be in any `ρ″`"* is the strata — a cell raised out of a witness strictly outlives the host that carries it, while `@ρ ⊐ α` makes every host strictly outlive `α`, and no cell at `α` does both. `Fig16.ResU.updV_inStratum` carries `Res_{↓α}` across `↭` and `Fig16.ResU.flat_inStratum_at` is the contradiction.
-/
/-- **`[TR]` Lemma 6.27** (p. 10): if `@ρ ⊐ α` and
`ρ ● ℓ ↦ mut(α, v, ρ_v, P̂) ↭ ρ′` then `ρ′ = ρ′/ℓ ● ℓ ↦ mut(α, v′, ρ′_v, P̂)`.

The printed proof, in its order.  *"`⦇ρ ● ρ_m⦈` and `⦇ρ′⦈` have the same
borrows"* is the hypothesis; *"there must be a `mut` cell in `⦇ρ′⦈` matching
`ℓ ↦ mut(α, v, ρ_v, P̂)`"* is `↭`'s clause (2) read forwards at `(ℓ, α, P̂)`,
the `mut` cell of `ρ ● ρ_m` sitting at `ℓ` in `⦇ρ ● ρ_m⦈` unchanged
(`ResU.flat_get_of_ne_imm`).

*"Furthermore, since `@ρ ⊐ α`, all borrows in `⦇ρ′⦈` other than … must be
disjoint from `α`, which by well-formedness of the resource `ρ′` implies that
the cell cannot be in any `ρ″`"* is the strata.  `ρ ● ρ_m ∈ Res_{↓α}`: the
frame is in `Res_α` by the printed hypothesis and the borrow is at `α` itself,
so both clear `↓α`.  `ResU.updV_inStratum` carries that across `↭` to
`ρ′ ∈ Res_{↓α}`, and then `ResU.flat_inStratum_at` says that at a location
where `ρ′` carries nothing the flattening carries nothing shorter than `↓α`'s
successor — that is, nothing at `α`.  The cell is at `α`, so `ρ′` carries a
cell at `ℓ`, and by `ResU.Flat.get` it is the `mut` cell itself.

*"Hence it must be that `ρ′(ℓ) = mut(α, v′, ρ′_v, P̂)`"* is the last step, and
`ResU.del_compS` is the printed `ρ′ = ρ′/ℓ ● …` as its graph (G4).
`[as printed]` -/
theorem ResU.six27 {l : BoCa.Loc} {α : Life} {v : BoCa.Val}
    {ρ ρv M ρ' : ResU BoCa.Loc BoCa.Val}
    {h : ResU.InStratum α ρv} {P : BoCa.Val → SPropS BoCa.Loc BoCa.Val α}
    {hw : P v ⟨ρv, h⟩}
    (hout : ResU.InStratum α ρ)
    (hM : ResU.CompS ρ (ResU.single l (CellU.mutOf α v ρv h P hw)) M)
    (hu : ResU.UpdV M ρ') :
    ∃ (v' : BoCa.Val) (χ : ResU BoCa.Loc BoCa.Val) (h' : ResU.InStratum α χ)
      (hw' : P v' ⟨χ, h'⟩),
      ResU.CompS (ρ'.del l) (ResU.single l (CellU.mutOf α v' χ h' P hw')) ρ' := by
  classical
  have hkm : (CellU.mutOf α v ρv h P hw).kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  obtain ⟨σ, hσ⟩ := hu.2.1
  obtain ⟨σ', hσ'⟩ := hu.2.2
  have hMl : M.get l = some (CellU.mutOf α v ρv h P hw) :=
    (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hM)
      (ResU.single_get_self _ _) hkm).2
  have hσl : σ.get l = some (CellU.mutOf α v ρv h P hw) :=
    ResU.flat_get_of_ne_imm hσ hMl hkm
  obtain ⟨v', χ, h', hw', hflat⟩ := (hu.1.2 l α P).mp ⟨v, ρv, h, hw, ⟨σ, hσ, hσl⟩⟩
  rw [ResU.flatAt_iff hσ'] at hflat
  have hdM : M.InStratum (↓α) :=
    BoLo.inStratum_comp (BoLo.compS_hC (↓α)) hM
      (fun m ψ e => CellU.InStratum.mono (le_of_lt (Life.down_sqsubset α)) (hout m ψ e))
      (ResU.inStratum_single l ((CellU.inStratum_mutOf (↓α) α v ρv h P hw).mpr
        (Life.down_sqsubset α)))
  have hd' : ρ'.InStratum (↓α) := ResU.updV_inStratum hdM hu
  have hρ'l : ρ'.get l ≠ none := by
    intro hnone
    have hcon := ResU.flat_inStratum_at hσ' hd'
      (fun φ e => absurd (hnone ▸ e) (by simp)) hflat
    rw [CellU.inStratum_mutOf] at hcon
    exact absurd hcon (lt_irrefl _)
  obtain ⟨φ, hφ⟩ : ∃ φ, ρ'.get l = some φ := by
    cases hg : ρ'.get l with
    | none => exact absurd hg hρ'l
    | some φ => exact ⟨φ, rfl⟩
  obtain ⟨χ₀, hχ₀, hk₀, -, -⟩ := ResU.Flat.get hσ' hφ
  rw [hflat] at hχ₀
  obtain rfl : χ₀ = CellU.mutOf α v' χ h' P hw' := (Option.some.inj hχ₀).symm
  have hkφ : φ.kind ≠ Kind.imm := by
    rw [← hk₀, CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hgg : σ'.get l = some φ := ResU.flat_get_of_ne_imm hσ' hφ hkφ
  rw [hflat] at hgg
  obtain rfl : φ = CellU.mutOf α v' χ h' P hw' := (Option.some.inj hgg).symm
  exact ⟨v', χ, h', hw', ResU.del_compS hφ⟩

end BoCa.Fig16

alias TR.lemma_6_27 := BoCa.Fig16.ResU.six27

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {Loc Val : Type}

/-! `[about ours]` — what the Lean of Lemma 6.28 needs; the paper prints nothing here. -/
/-- **The two flattenings of `[TR]` 6.28's string of iffs differ at `ℓ` alone.**
`⦇ρ ● ℓ ↦ mut(α, v, ρ_v, P̂)⦈` is
`ex(ρ)_● ● (ℓ ↦ mut(α, v, ρ_v, P̂) ● ex(ρ_v)_●) ● (ag(ρ) ○ ag(ρ_v))` and
`⦇ρ ● ρ_v ● ℓ ↦ own(v)⦈` is the same with `ex(ρ_v)_● ● ℓ ↦ own(v)` in the
middle — the printed proof's two displays.  The `ag` sides are literally the
same, because `ag(ℓ ↦ own(v)) = ∅` and `ag` at the `mut` cell is `ag(ρ_v)`, so
the two composites agree everywhere but `ℓ`, where one has the `mut` cell and
the other the `own` one.  `[about ours: the two displays of `[TR]` 6.28's
proof, compared]` -/
theorem ResU.flat_mut_own_agree_off {l : Loc} {b : Life} {v : Val}
    {ρ ρv W M O F G : ResU Loc Val} {hs : ResU.InStratum b ρv}
    {P : Val → SPropS Loc Val b} {hw : P v ⟨ρv, hs⟩}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W)
    (hM : ResU.CompS ρ (ResU.single l (CellU.mutOf b v ρv hs P hw)) M)
    (hO : ResU.CompS ρ W O)
    (hF : ResU.Flat M F) (hG : ResU.Flat O G) :
    (∀ x, x ≠ l → G.get x = F.get x) ∧
      F.get l = some (CellU.mutOf b v ρv hs P hw) ∧ G.get l = some (CellU.ownOf v) := by
  classical
  have hmk : (CellU.mutOf b v ρv hs P hw).kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hok : (CellU.ownOf (Loc := Loc) v).kind ≠ Kind.imm := by simp
  -- the `mut` side
  obtain ⟨e₁, e₂, e, a₁, a₂, a, he₁, he₂, hec, ha₁, ha₂, hac, hFc⟩ :=
    (ResU.Flat.split hM).mp hF
  obtain ⟨ev, hev, hcev⟩ := ExW.single_mut_inv he₂
  have havv : AgW ρv a₂ := AgW.single_mut_inv ha₂
  have hevl : ev.get l = none := ResU.compatS_single_mut hcev.1
  -- the `own` side
  obtain ⟨f₁, eW, f, b₁, aW, a', hf₁, heW, hfc, hb₁, haW, hbc, hGc⟩ :=
    (ResU.Flat.split hO).mp hG
  obtain ⟨ev', eo, hev', heo, hceW⟩ := (ExS.split hW).mp heW
  obtain ⟨av', ao, hav', hao, hcaW⟩ := (AgW.split hW).mp haW
  rw [ExS.functional heo (ExW.single_own l v)] at hceW
  rw [AgW.functional hao (AgW.single_own l v)] at hcaW
  obtain rfl : aW = av' := ResU.CompR.functional hcaW (ResU.comp_empty_right av')
  cases ExS.functional hev' hev
  cases AgW.functional hav' havv
  cases ExS.functional hf₁ he₁
  cases AgW.functional hb₁ ha₁
  cases ResU.CompR.functional hbc hac
  -- the two exclusive walks
  have he₂l : e₂.get l = some (CellU.mutOf b v ρv hs P hw) := by
    rw [ResU.Comp.get_of_right_none hcev hevl]; exact ResU.single_get_self _ _
  have heWl : eW.get l = some (CellU.ownOf v) := by
    rw [ResU.Comp.get_of_left_none hceW hevl]; exact ResU.single_get_self _ _
  have hoff : ∀ x, x ≠ l → eW.get x = e₂.get x := by
    intro x hx
    rw [ResU.Comp.get_of_right_none hceW (ResU.single_get_ne _ hx),
      ResU.Comp.get_of_left_none hcev (ResU.single_get_ne _ hx)]
  have hoffe : ∀ x, x ≠ l → f.get x = e.get x :=
    ResU.compS_agree_off_right hec hfc hoff
  have he₁l : e₁.get l = none :=
    ResU.CompatS.right_eq_none (ResU.CompatS.symm hec.1) he₂l hmk
  have hel : e.get l = some (CellU.mutOf b v ρv hs P hw) := by
    rw [ResU.Comp.get_of_left_none hec he₁l]; exact he₂l
  have hfl : f.get l = some (CellU.ownOf v) := by
    rw [ResU.Comp.get_of_left_none hfc he₁l]; exact heWl
  have hal : a.get l = none := ResU.CompatS.right_eq_none hFc.1 hel hmk
  refine ⟨fun x hx => ?_, ?_, ?_⟩
  · exact (ResU.compS_agree_off_right (ResU.CompS.comm hFc) (ResU.CompS.comm hGc)
      (fun y hy => hoffe y hy)) x hx
  · rw [ResU.Comp.get_of_right_none hFc hal]; exact hel
  · rw [ResU.Comp.get_of_right_none hGc hal]; exact hfl

/-!
## Lemma 6.28 · `[TR]` p. 11 · `proved`

> Assuming all compositions are defined and valid, ρ ● ℓ ↦ mut(α, v, ρ_v, P̂) ↭ ρ′ ● ℓ ↦ mut(α, v′, ρ′_v, P̂) iff ρ ● ℓ ↦ own(v) ● ρ_v ↭ ρ′ ● ℓ ↦ own(v′) ● ρ′_v

**Printed proof, transcribed.** A string of iffs.  The left side holds iff `ex(ρ)_● ● (ℓ ↦ mut(α, v, ρ_v, P̂)) ● ex(ρ_v)_● ● (ag(ρ) ○ ag(ρ_v))` and its primed counterpart have the same borrows (unravelling definitions), iff the same two composites with `ℓ ↦ own(v)` and `ℓ ↦ own(v′)` in place of the `mut` cells have the same borrows (by exclusivity of `ℓ`), iff the right side holds.

**Lean.** `BoCa.Fig16.ResU.six28`, alias `TR.lemma_6_28`, tag `[as printed]`.

**Note.** `Fig16.ResU.six28`, on the printed carrier, `[as printed]`. The printed string of three iffs: the outer two are *"by unravelling definitions"*, `Fig16.ResU.flat_mut_own_agree_off` each side once — the `ag` sides of the two displays are literally the same, since `ag(ℓ ↦ own(v)) = ∅` and `ag` at the `mut` cell is `ag(ρ_v)`, so the flattenings differ at `ℓ` alone. The middle is *"by exclusivity of `ℓ`"*, where `↭`'s two clauses come apart: the `imm` clause is false at `ℓ` on all four flattenings, and the `mut` clause is true on both sides in the `mut` configuration at the one class `(α, P̂)` the printed cells share and false on both in the `own` one. `Upd` is [CONF] Fig. 18b's unguarded `↭` (`docs/adjudications.md` D3); the print's *"assuming all compositions are defined and valid"* is the four compositions as graphs (G4) and the four `✓`s.
-/
/-- **`[TR]` Lemma 6.28** (p. 10): assuming all compositions are defined and
valid, `ρ ● ℓ ↦ mut(α, v, ρ_v, P̂) ↭ ρ′ ● ℓ ↦ mut(α, v′, ρ′_v, P̂)` iff
`ρ ● ℓ ↦ own(v) ● ρ_v ↭ ρ′ ● ℓ ↦ own(v′) ● ρ′_v`.

The printed proof is a string of three iffs.  The first and the third are
*"by unravelling definitions"*: `↭` compares the borrows of the two
flattenings, and `ResU.flat_mut_own_agree_off` is the unravelling, each side
once.  The middle one is *"by exclusivity of `ℓ`"*, and it is where the two
printed clauses of `↭` come apart.  At `ℓ` the `imm` clause is false on all
four flattenings — the cell there is `mut` or `own`, never `imm` — so it holds
either way.  The `mut` clause at `ℓ` is true on both sides in the `mut`
configuration, at the one class `(α, P̂)` the two cells share, and false on
both sides in the `own` configuration; the printed statement gives the two
`mut` cells the *same* `α` and `P̂`, which is exactly what makes the clause
hold in both.  Off `ℓ` the four flattenings agree in pairs, so every clause
there transfers unchanged.

`↭` is `ResU.Upd`, `[CONF]` Fig. 18b's unguarded reading (`docs/adjudications.md` D3); the
print's *"assuming all compositions are defined and valid"* is the four
compositions as graphs (G4) and the four `✓`s.  `[as printed]` -/
theorem ResU.six28 {l : Loc} {b : Life} {v v' : Val}
    {ρ ρ' ρv ρv' W W' M M' O O' : ResU Loc Val}
    {hs : ResU.InStratum b ρv} {hs' : ResU.InStratum b ρv'}
    {P : Val → SPropS Loc Val b} {hw : P v ⟨ρv, hs⟩} {hw' : P v' ⟨ρv', hs'⟩}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W)
    (hW' : ResU.CompS ρv' (ResU.single l (CellU.ownOf v')) W')
    (hM : ResU.CompS ρ (ResU.single l (CellU.mutOf b v ρv hs P hw)) M)
    (hM' : ResU.CompS ρ' (ResU.single l (CellU.mutOf b v' ρv' hs' P hw')) M')
    (hO : ResU.CompS ρ W O) (hO' : ResU.CompS ρ' W' O')
    (hvM : ResU.Valid M) (hvM' : ResU.Valid M')
    (hvO : ResU.Valid O) (hvO' : ResU.Valid O') :
    ResU.Upd M M' ↔ ResU.Upd O O' := by
  classical
  obtain ⟨F, hF⟩ := hvM
  obtain ⟨F', hF'⟩ := hvM'
  obtain ⟨G, hG⟩ := hvO
  obtain ⟨G', hG'⟩ := hvO'
  obtain ⟨hoff, hFl, hGl⟩ := ResU.flat_mut_own_agree_off hW hM hO hF hG
  obtain ⟨hoff', hFl', hGl'⟩ := ResU.flat_mut_own_agree_off hW' hM' hO' hF' hG'
  constructor
  · rintro ⟨hi, hm⟩
    refine ⟨fun x s w χ h => ?_, fun x c Q => ?_⟩
    · rw [ResU.flatAt_iff hG, ResU.flatAt_iff hG']
      by_cases hx : x = l
      · subst hx
        rw [hGl, hGl']
        exact ⟨fun hc => absurd (Option.some.inj hc) CellU.ownOf_ne_immOf,
               fun hc => absurd (Option.some.inj hc) CellU.ownOf_ne_immOf⟩
      · rw [hoff x hx, hoff' x hx]
        have hx' := hi x s w χ h
        rwa [ResU.flatAt_iff hF, ResU.flatAt_iff hF'] at hx'
    · by_cases hx : x = l
      · subst hx
        constructor
        · rintro ⟨w, χ, h, hw2, hfa⟩
          rw [ResU.flatAt_iff hG, hGl] at hfa
          exact absurd (Option.some.inj hfa) CellU.ownOf_ne_mutOf
        · rintro ⟨w, χ, h, hw2, hfa⟩
          rw [ResU.flatAt_iff hG', hGl'] at hfa
          exact absurd (Option.some.inj hfa) CellU.ownOf_ne_mutOf
      · have hx' := hm x c Q
        simp only [ResU.flatAt_iff hF, ResU.flatAt_iff hF'] at hx'
        simp only [ResU.flatAt_iff hG, ResU.flatAt_iff hG', hoff x hx, hoff' x hx]
        exact hx'
  · rintro ⟨hi, hm⟩
    refine ⟨fun x s w χ h => ?_, fun x c Q => ?_⟩
    · rw [ResU.flatAt_iff hF, ResU.flatAt_iff hF']
      by_cases hx : x = l
      · subst hx
        rw [hFl, hFl']
        exact ⟨fun hc => absurd (Option.some.inj hc).symm CellU.immOf_ne_mutOf,
               fun hc => absurd (Option.some.inj hc).symm CellU.immOf_ne_mutOf⟩
      · rw [← hoff x hx, ← hoff' x hx]
        have hx' := hi x s w χ h
        rwa [ResU.flatAt_iff hG, ResU.flatAt_iff hG'] at hx'
    · by_cases hx : x = l
      · subst hx
        constructor
        · rintro ⟨w, χ, h, hw2, hfa⟩
          rw [ResU.flatAt_iff hF, hFl] at hfa
          have heq := Option.some.inj hfa
          obtain rfl : b = c := CellU.mutOf_at heq
          obtain ⟨rfl, rfl, rfl⟩ := CellU.mutOf_inj heq
          exact ⟨v', ρv', hs', hw', (ResU.flatAt_iff hF' _ _).mpr hFl'⟩
        · rintro ⟨w, χ, h, hw2, hfa⟩
          rw [ResU.flatAt_iff hF', hFl'] at hfa
          have heq := Option.some.inj hfa
          obtain rfl : b = c := CellU.mutOf_at heq
          obtain ⟨rfl, rfl, rfl⟩ := CellU.mutOf_inj heq
          exact ⟨v, ρv, hs, hw, (ResU.flatAt_iff hF _ _).mpr hFl⟩
      · have hx' := hm x c Q
        simp only [ResU.flatAt_iff hG, ResU.flatAt_iff hG', hoff x hx, hoff' x hx] at hx'
        simp only [ResU.flatAt_iff hF, ResU.flatAt_iff hF']
        exact hx'

end BoCa.Fig16

alias TR.lemma_6_28 := BoCa.Fig16.ResU.six28

namespace BoCa.Fig16
variable {Loc Val : Type}

/-! `[about ours]` — what the Lean of Lemma 6.29 needs; the paper prints nothing here. -/
/-- **`[TR]` Lemma 6.29's proof through its second sentence.**  Its first two
sentences are about `⦇ρ′⦈` alone, and what they establish is a pair:
`⦇ρ′⦈(ℓ) = imm({α}, v, ρ_v)`, and *"all borrows in `⦇ρ′⦈` other than `ρᵢ` must
be disjoint from `α`"*.

*"By assumption, `⦇ρ ● ρᵢ⦈` and `⦇ρ′⦈` have the same borrows"* is `↭`'s two
clauses (`ResU.UpdImm`, `ResU.UpdMut`).  *"And by assumption,
`ρ # ρ_v ● ℓ ↦ own(v)`, so `ℓ ∉ dom(⦇ρ⦈)`"* is 6.18 and 6.20 at that `#`: the
`own` cell sits in `ex(−)●` at `ℓ`, and `●` there admits no second cell, so
`ex(ρ)●`, `ag(ρ)`, `ex(ρ_v)●` and `ag(ρ_v)` are all silent at `ℓ` — and by 6.32
(`ExS.toExR`) so is the `ex(ρ_v)_○` that `ag(ρᵢ)` calls.  *"This implies there
must be an imm cell in `⦇ρ′⦈` matching `ρᵢ` exactly"* is then `⦇ρ ● ρᵢ⦈(ℓ) = ρᵢ`
carried across `↭`, the first conjunct.

*"Furthermore, since `@ρ ⊐ α`, all borrows in `⦇ρ′⦈` other than `ρᵢ` must be
disjoint from `α`"* is the second: `ExW.inStratum` and `AgW.inStratum` on `ρ`
and on `ρ_v` — `imm({α}, v, ρ_v)` carries `ρ_v ∈ Res_α` as one of its own
arguments — carried across `↭`, which fixes an `imm` cell outright and a `mut`
cell's lifetime.

6.29 spends the pair on *"cannot be in any `ρ″`"* at `ℓ`; 6.38's closing
paragraph spends the second conjunct again, at `ρ′ ● ρ⁺/ℓ`, where the same
sentence is what keeps the borrow out of `ag(ρ′ ● ρ⁺/ℓ)`.

Stated at `BoCa.Loc`/`BoCa.Val`, as the `Res_α` lemmas it spends are.
`[about ours: the two facts `[TR]` Lemma 6.29's proof establishes about `⦇ρ′⦈`
before it descends to `ρ′`]` -/
theorem ResU.six29_borrows_off {α : Life} {ρ ρv ρ' W ρρi σ' : ResU BoCa.Loc BoCa.Val}
    {l : BoCa.Loc} {v : BoCa.Val} {hv : ρv.InStratum (LSet.singleton α).join}
    (hα : ρ.InStratum α)
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W)
    (hhash : ResU.Hash ρ W)
    (hρi : ResU.CompS ρ (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ρρi)
    (hupd : ResU.UpdV ρρi ρ') (hσ' : ResU.Flat ρ' σ') :
    σ'.get l = some (CellU.immOf (LSet.singleton α) v ρv hv) ∧
      ∀ m, m ≠ l → ∀ ψ, σ'.get m = some ψ → ψ.InStratum α := by
  have hcellk : (CellU.immOf (LSet.singleton α) v ρv hv).kind = Kind.imm :=
    CellU.kind_immOf _ _ _ _
  have himmi : ∀ m ψ,
      (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)).get m = some ψ →
      ψ.kind = Kind.imm := by
    intro m ψ h
    obtain ⟨-, rfl⟩ := ResU.single_get_eq_some h
    exact hcellk
  -- `ℓ ∉ dom(⦇ρ⦈)` and `ℓ ∉ dom(⦇ρ_v⦈)`, from the printed `#`.
  obtain ⟨-, T, hT, hvT⟩ := hhash
  obtain ⟨σT, eT, aT, hexT, hagT, hcT⟩ := hvT
  obtain ⟨e₁, e₂, he₁, he₂, hec⟩ := (ExS.split hT).mp hexT
  obtain ⟨a₁, a₂, ha₁, ha₂, hac⟩ := (AgW.split hT).mp hagT
  obtain ⟨f₁, f₂, hf₁, hf₂, hfc⟩ := (ExS.split hW).mp he₂
  obtain ⟨b₁, b₂, hb₁, hb₂, hbc⟩ := (AgW.split hW).mp ha₂
  have hownk : (CellU.ownOf (Loc := BoCa.Loc) v).kind ≠ Kind.imm := by simp
  have hf₂l : f₂.get l = some (CellU.ownOf v) := by
    rw [ExS.functional hf₂ (ExW.single_own l v)]
    exact ResU.single_get_self _ _
  have hf₁l : f₁.get l = none :=
    ResU.CompatS.right_eq_none (ResU.CompatS.symm hfc.1) hf₂l hownk
  have he₂l : e₂.get l = some (CellU.ownOf v) := by
    have := hfc.2 l; rw [hf₁l, hf₂l] at this; exact this
  have he₁l : e₁.get l = none :=
    ResU.CompatS.right_eq_none (ResU.CompatS.symm hec.1) he₂l hownk
  have heTl : eT.get l = some (CellU.ownOf v) := by
    have := hec.2 l; rw [he₁l, he₂l] at this; exact this
  have haTl : aT.get l = none :=
    ResU.CompatS.right_eq_none hcT.1 heTl hownk
  have ha₁l : a₁.get l = none := ((ResU.Comp.eq_none_iff hac l).mp haTl).1
  have ha₂l : a₂.get l = none := ((ResU.Comp.eq_none_iff hac l).mp haTl).2
  have hb₁l : b₁.get l = none := ((ResU.Comp.eq_none_iff hbc l).mp ha₂l).1
  -- `⦇ρ ● ρᵢ⦈(ℓ) = ρᵢ`, and everywhere else `⦇ρ ● ρᵢ⦈ ∈ Res_α`.
  obtain ⟨σ, hσ⟩ := hupd.2.1
  obtain ⟨E, A, hE, hA, hEA⟩ := hσ
  obtain ⟨E₁, E₂, hE₁, hE₂, hEc⟩ := (ExS.split hρi).mp hE
  obtain ⟨A₁, A₂, hA₁, hA₂, hAc⟩ := (AgW.split hρi).mp hA
  rw [ExS.functional hE₂ (ExW.empty_of_all_imm himmi)] at hEc
  rw [ResU.CompS.functional hEc (ResU.comp_empty_right E₁)] at hE hEA
  rw [ExS.functional hE₁ he₁] at hE hEA
  rw [AgW.functional hA₁ ha₁] at hAc
  obtain ⟨ev, av, p, hev, hav, hcp, hagi⟩ := AgW.single_imm_inv hA₂
  rw [ExR.functional hev (ExS.toExR hf₁)] at hcp
  rw [AgW.functional hav hb₁] at hcp
  have hpl : p.get l = none := by
    refine (ResU.Comp.eq_none_iff hcp l).mpr ⟨hf₁l, hb₁l⟩
  have hA₂l : A₂.get l = some (CellU.immOf (LSet.singleton α) v ρv hv) := by
    have := hagi.2 l; rw [ResU.single_get_self, hpl] at this; exact this
  have hAl : A.get l = some (CellU.immOf (LSet.singleton α) v ρv hv) := by
    have := hAc.2 l; rw [ha₁l, hA₂l] at this; exact this
  have hσl : σ.get l = some (CellU.immOf (LSet.singleton α) v ρv hv) := by
    have := hEA.2 l; rw [he₁l, hAl] at this; exact this
  -- `Res_α` off `ℓ`.
  have hstratσ : ∀ m, m ≠ l → ∀ ψ, σ.get m = some ψ → ψ.InStratum α := by
    intro m hm ψ hg
    have hEs : e₁.InStratum α := BoLo.ExW.inStratum BoLo.compS_hC he₁ α hα
    have hA₁s : a₁.InStratum α := BoLo.AgW.inStratum ha₁ α hα
    have hps : p.InStratum α :=
      BoLo.inStratum_comp (BoLo.compR_hC α) hcp
        (BoLo.ExW.inStratum BoLo.compR_hC (ExS.toExR hf₁) α hv)
        (BoLo.AgW.inStratum hb₁ α hv)
    have hA₂s : ∀ ζ, A₂.get m = some ζ → ζ.InStratum α := by
      intro ζ hζ
      have := hagi.2 m
      rw [ResU.single_get_ne _ hm] at this
      cases hpm : p.get m with
      | none => rw [hpm] at this; rw [this] at hζ; exact absurd hζ (by simp)
      | some π => rw [hpm] at this; rw [this] at hζ
                  exact hps m ζ (by rw [hpm]; exact hζ)
    have hAs : ∀ ζ, A.get m = some ζ → ζ.InStratum α := by
      intro ζ hζ
      rcases hAc.get m with ⟨-, -, e⟩ | ⟨ξ, g₁, -, e⟩ | ⟨ξ, -, g₂, e⟩ |
          ⟨ξ₁, ξ₂, ξ, g₁, g₂, e, hC⟩
      · rw [e] at hζ; exact absurd hζ (by simp)
      · rw [show ζ = ξ from Option.some.inj (hζ.symm.trans e)]; exact hA₁s m ξ g₁
      · rw [show ζ = ξ from Option.some.inj (hζ.symm.trans e)]; exact hA₂s ξ g₂
      · rw [show ζ = ξ from Option.some.inj (hζ.symm.trans e)]
        exact BoLo.compR_hC α _ _ _ hC (hA₁s m ξ₁ g₁) (hA₂s ξ₂ g₂)
    rcases hEA.get m with ⟨-, -, e⟩ | ⟨ξ, g₁, -, e⟩ | ⟨ξ, -, g₂, e⟩ |
        ⟨ξ₁, ξ₂, ξ, g₁, g₂, e, hC⟩
    · rw [e] at hg; exact absurd hg (by simp)
    · rw [show ψ = ξ from Option.some.inj (hg.symm.trans e)]; exact hEs m ξ g₁
    · rw [show ψ = ξ from Option.some.inj (hg.symm.trans e)]; exact hAs ξ g₂
    · rw [show ψ = ξ from Option.some.inj (hg.symm.trans e)]
      exact BoLo.compS_hC α _ _ _ hC (hEs m ξ₁ g₁) (hAs ξ₂ g₂)
  -- Across `↭`.
  have hσ'l : σ'.get l = some (CellU.immOf (LSet.singleton α) v ρv hv) :=
    (ResU.flatAt_iff hσ' l _).mp
      ((hupd.1.1 l (LSet.singleton α) v ρv hv).mp ⟨σ, ⟨e₁, A, hE, hA, hEA⟩, hσl⟩)
  have hstratσ' : ∀ m, m ≠ l → ∀ ψ, σ'.get m = some ψ → ψ.InStratum α := by
    intro m hm ψ hg
    rcases CellU.rep ψ with ⟨w, rfl⟩ | ⟨t, w, χ, hh, rfl⟩ | ⟨b, w, χ, hh, P, hw, rfl⟩
    · exact trivial
    · have : σ.get m = some (CellU.immOf t w χ hh) :=
        (ResU.flatAt_iff ⟨e₁, A, hE, hA, hEA⟩ m _).mp
          ((hupd.1.1 m t w χ hh).mpr ⟨σ', hσ', hg⟩)
      exact hstratσ m hm _ this
    · obtain ⟨w', χ', h', hw', hflat⟩ :=
        (hupd.1.2 m b P).mpr ⟨w, χ, hh, hw, ⟨σ', hσ', hg⟩⟩
      have hmm : σ.get m = some (CellU.mutOf b w' χ' h' P hw') :=
        (ResU.flatAt_iff ⟨e₁, A, hE, hA, hEA⟩ m _).mp hflat
      have hbb : (CellU.mutOf b w' χ' h' P hw').InStratum α := hstratσ m hm _ hmm
      exact hbb
  exact ⟨hσ'l, hstratσ'⟩

/-!
## Lemma 6.29 · `[TR]` p. 11 · `proved`

> If @ρ ⊐ α and ρ # ρ_v ● ℓ ↦ own(v) and ρ ● ℓ ↦ imm({α}, v, ρ_v) ↭ ρ′ then ρ′ = ρ′/ℓ ● ℓ ↦ imm({α}, v, ρ_v).

**Printed proof, transcribed.** Let `ρᵢ = ℓ ↦ imm({α}, v, ρ_v)`.  `⦇ρ ● ρᵢ⦈` and `⦇ρ′⦈` have the same borrows, and `ρ # ρ_v ● ℓ ↦ own(v)` gives `ℓ ∉ dom(⦇ρ⦈)`, so an `imm` cell of `⦇ρ′⦈` matches `ρᵢ` exactly: `⦇ρ′⦈(ℓ) = imm({α}, v, ρ_v)`.  Since `@ρ ⊐ α`, every other borrow in `⦇ρ′⦈` is disjoint from `α`, which by well-formedness of `ρ′` means the cell cannot be in any `ρ″` of a `mut(_, _, ρ″, _)` or `imm(_, _, ρ″)` in `ρ′`.  So `ρ′(ℓ) = imm({α}, v, ρ_v)` and `ρ′ = ρ′/ℓ ● ℓ ↦ imm({α}, v, ρ_v)`.

**Lean.** `BoCa.Fig16.ResU.six29`, alias `TR.lemma_6_29`, tag `[as printed]`.

**Note.** `Fig16.ResU.six29`, on the printed carrier, `[as printed]` — all three printed hypotheses verbatim, **nothing added**, the conclusion exactly as printed, and `ρ ● ρ_v ● ℓ ↦ own(v)`, `ρ ● ρᵢ` and `ρ′/ℓ ● ρᵢ` named by their graphs (G4). Stated at `BoCa.Loc`/`BoCa.Val`, as the `Res_α` lemmas it spends are. *"By well-formedness of the resource `ρ′`"* is **Fig. 16's own typing of the two borrow cells and nothing else**: `imm(ᾱ, v, ρ)` carries `ρ : Res_{⊔ᾱ}` and `mut(β, v, ρ, P̂)` carries `ρ : Res_β`, which on this carrier are arguments of `Fig16.CellU.immOf` and `Fig16.CellU.mutOf` and so are present at every cell by construction; `Fig16.BoLo.cell_wit_inStratum` is that sentence read off them. No predicate is added. *"`ℓ ∉ dom(⦇ρ⦈)`"* is 6.18 and 6.20 at the printed `#`, the `own` cell admitting no second cell under `●` at `ℓ`; 6.32 (`Fig16.ExS.toExR`) is what lets `ag(ρᵢ)`'s `ex(ρ_v)_○` be compared with it. *"All borrows … other than `ρᵢ` must be disjoint from `α`"* is `Fig16.BoLo.ExW.inStratum` and `Fig16.BoLo.AgW.inStratum` on `ρ` and on `ρ_v` — `imm({α}, v, ρ_v)` carries `ρ_v ∈ Res_α` itself — carried across `↭`. *"Cannot be in any `ρ″`"* needs **no descent into the nesting**: `Fig16.BoLo.flat_inStratum_inv` is pointwise, so were `ρ′(ℓ)` undefined it would ask nothing at `ℓ` and give `ρ′ ∈ Res_α`, whence `⦇ρ′⦈ ∈ Res_α` and at `ℓ` the false `α ⊐ α`. The cell is then pinned by `Fig16.ResU.Flat.get` (tag, value, witness) and the new `Fig16.ResU.Flat.get_ls_imm` (the lifetime set, `ag`'s `○`s being able only to enlarge it), and `Fig16.ResU.del_compS` is the conclusion. The proof's first two sentences are `Fig16.ResU.six29_borrows_off`, which returns the pair they establish about `⦇ρ′⦈` — the cell at `ℓ`, and *"all borrows … other than `ρᵢ` must be disjoint from `α`"* — because 6.38's closing paragraph spends the second again, at `ρ′ ● ρ⁺/ℓ`, where it is what keeps the borrow out of `ag(ρ′ ● ρ⁺/ℓ)`; 6.29 itself stated only the `●`-decomposition its last sentence gives.
-/
/-- **`[TR]` Lemma 6.29** (p. 11): if `@ρ ⊐ α` and `ρ # ρ_v ● ℓ ↦ own(v)` and
`ρ ● ℓ ↦ imm({α}, v, ρ_v) ↭ ρ′` then `ρ′ = ρ′/ℓ ● ℓ ↦ imm({α}, v, ρ_v)`.

*"Hence it must be that `ρ′(ℓ) = imm({α}, v, ρ_v, _)"*: the two facts
`ResU.six29_borrows_off` returns are the printed sentence before it, and
`ResU.flat_imm_at_top` is *"cannot be in any `ρ″`"*.  `ResU.Flat.get` then fixes
the tag, the value and the witness, and `ResU.Flat.get_ls_imm` fixes the
lifetime set, `ag`'s `○`s being able only to enlarge it.  The conclusion is
`ResU.del_compS`.

Stated at `BoCa.Loc`/`BoCa.Val`, as the `Res_α` lemmas it spends are.
`[as printed]` (`ρ ● ρ_v ● ℓ ↦ own(v)`, `ρ ● ρᵢ` and `ρ′/ℓ ● ρᵢ` appear as their
graphs — G4) -/
theorem ResU.six29 {α : Life} {ρ ρv ρ' W ρρi : ResU BoCa.Loc BoCa.Val}
    {l : BoCa.Loc} {v : BoCa.Val} {hv : ρv.InStratum (LSet.singleton α).join}
    (hα : ρ.InStratum α)
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W)
    (hhash : ResU.Hash ρ W)
    (hρi : ResU.CompS ρ (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ρρi)
    (hupd : ResU.UpdV ρρi ρ') :
    ResU.CompS (ρ'.del l)
      (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ρ' := by
  have hcellk : (CellU.immOf (LSet.singleton α) v ρv hv).kind = Kind.imm :=
    CellU.kind_immOf _ _ _ _
  obtain ⟨σ', hσ'⟩ := hupd.2.2
  obtain ⟨hσ'l, hstratσ'⟩ := ResU.six29_borrows_off hα hW hhash hρi hupd hσ'
  -- `ρ′(ℓ)` is defined.
  obtain ⟨ex', ag', hex', hag', hc'⟩ := hσ'
  have hdef : ∃ φ, ρ'.get l = some φ :=
    ResU.flat_imm_at_top ⟨ex', ag', hex', hag', hc'⟩ hσ'l rfl hstratσ'
  -- …and is the printed cell.
  obtain ⟨φ, hφ⟩ := hdef
  obtain ⟨χ, hχ, hkχ, heχ, hwχ⟩ := ResU.Flat.get ⟨ex', ag', hex', hag', hc'⟩ hφ
  obtain rfl : χ = CellU.immOf (LSet.singleton α) v ρv hv :=
    Option.some.inj (hχ.symm.trans hσ'l)
  have hkφ : φ.kind = Kind.imm := hkχ ▸ hcellk
  obtain ⟨s', hs', heta⟩ := CellU.imm_eta hkφ
  have hsub : ∀ x, s'.mem x → (LSet.singleton α).mem x :=
    fun x hx => ResU.Flat.get_ls_imm ⟨ex', ag', hex', hag', hc'⟩
      (hφ.trans (congrArg some heta)) hσ'l hx
  obtain ⟨y, hy⟩ := LSet.nonempty s'
  have hyα : y = α := hsub y hy
  have hseq : s' = LSet.singleton α := by
    refine LSet.ext (fun x => ⟨fun hx => hsub x hx, fun hx => ?_⟩)
    show s'.mem x
    have : x = α := hx
    rw [this, ← hyα]
    exact hy
  have heφ : φ.erase = v := by rw [← heχ, CellU.erase_immOf]
  have hwφ : φ.wit = ρv := by rw [← hwχ, CellU.wit_immOf]
  have hφ' : ρ'.get l = some (CellU.immOf (LSet.singleton α) v ρv hv) :=
    hφ.trans (congrArg some
      (heta.trans (CellU.immOf_congr hseq heφ hwφ hs' hv)))
  exact ResU.del_compS hφ'

end BoCa.Fig16

alias TR.lemma_6_29 := BoCa.Fig16.ResU.six29

/-!
## Lemma 6.30 · `[TR]` p. 11 · `proved`

> If ρ ▸◂ (ρ₁ ○ ρ₂) and ρ∣imm = ∅ then ρ ▸◂ ρ₁ and ρ ▸◂ ρ₂

**Printed proof, transcribed.** Since `ρ∣imm = ∅`, `ρ ▸◂ (ρ₁ ○ ρ₂)` implies `dom(ρ) ∩ dom(ρ₁ ○ ρ₂) = ∅`.  Unfolding `○`, `dom(ρ₁ ○ ρ₂) = dom(ρ₁) ∪ dom(ρ₂)`, so `dom(ρ)` is disjoint from each, and by definition `ρ ▸◂ ρ₁` and `ρ ▸◂ ρ₂`.

**Lean.** `BoCa.Fig16.ResU.CompatS.of_compR_left`, alias `TR.lemma_6_30`, tag `[as printed]` — declared in `Paper/S6_1_StandardLemmas/Lemmas.lean`, ahead of this subsection: the Lean of Lemmas 6.7, 6.8, 6.10, 6.11 and 6.15 there needs it.

**Note.** `Fig16.ResU.CompatS.of_compR_left`, on the printed carrier, `[as printed]`. The bowtie is the **filled** `▸◂` of p. 5's cell-level row, not the half-filled metavariable, and the composition inside it is `○`; both stand in the one statement. `ρ
-/
alias TR.lemma_6_30 := BoCa.Fig16.ResU.CompatS.of_compR_left

/-!
## Lemma 6.31 · `[TR]` p. 11 · `proved`

> If ρ ▸◂ ρ′ then ρ ○ ρ′ = ρ ● ρ′.

**Printed proof, transcribed.** It suffices that for cells `ψ ▸◂ ψ′`, `ψ ○ ψ′ = ψ ● ψ′`.  Unfolding `ψ ○ ψ′`: either `ψ = ψ′` and `ψ ○ ψ′ = ψ`, or `ψ ≠ ψ′` and, as `ψ ▸◂ ψ′`, `ψ ○ ψ′ = ψ ● ψ′`; the last case is unreachable.  `ψ ○ ψ′` disagrees with `●` only when `ψ = ψ′ = own(_)` or `mut(_, _, _, _)`, which `ψ ▸◂ ψ′` excludes.

**Lean.** `BoCa.Fig16.ResU.compR_iff_compS`, alias `TR.lemma_6_31`, tag `[as printed]` — declared in `Paper/S6_1_StandardLemmas/Lemmas.lean`, ahead of this subsection: the Lean of Lemmas 6.7, 6.8, 6.10, 6.11 and 6.15 there needs it.

**Note.** `Fig16.ResU.compR_iff_compS`, on the printed carrier: under the printed hypothesis `ρ ▶◀ ρ′` the two graphs coincide, which is definedness and value together.
-/
alias TR.lemma_6_31 := BoCa.Fig16.ResU.compR_iff_compS

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {Loc Val : Type}

/-!
## Lemma 6.34 · `[TR]` p. 11 · `proved`

> If ρ # ρ_v ● ℓ ↦ own(v) and @ρ_v ⊐ α then ρ # ℓ ↦ imm(α, v, ρ_v)

**Printed proof, transcribed.** By Lemma 6.11, `ρ # ρ_v` and `ρ # ℓ ↦ own(v)`.  Unfolding these, `ℓ ∉ dom(⦇ρ ● ρ_v⦈)`, and by Lemmas 6.20, 6.18, 6.31 and 6.32 the following are all defined and equal: `⦇ρ ● ρ_v⦈ = ex(ρ ● ρ_v)_● ● ag(ρ ● ρ_v) = ex(ρ)_● ● ex(ρ_v)_● ● (ag(ρ) ○ ag(ρ_v)) = ex(ρ)_● ● (ex(ρ_v)_● ○ ag(ρ) ○ ag(ρ_v)) = ex(ρ)_● ● (ex(ρ_v)_○ ○ ag(ρ) ○ ag(ρ_v)) = ex(ρ)_● ● (⦇ρ_v⦈_○ ○ ag(ρ))`.  The last equality, with `ℓ` outside the domain, completes the proof.

**Lean.** `BoCa.Fig16.ResU.six34`, alias `TR.lemma_6_34`, tag `[as printed]`.

**Note.** `Fig16.ResU.six34`, on the printed carrier, `[as printed]` — both printed hypotheses, **nothing added**, and the conclusion exactly as printed, with `ρ_v ● ℓ ↦ own(v)` named by its graph (G4). `@ρ_v ⊐ ᾱ` is `CellU.immOf`'s own typing argument `ρ_v : Res_{⊔ᾱ}`, which is where Fig. 16 puts it and where the printed proof leaves it — it is never used again. The printed proof is carried step for step: 6.11 (`Fig16.ResU.Hash.split`) with 6.2 at `#` (`Fig16.ResU.hash_symm`); *"unfolding these, `ℓ ∉ dom(⦇ρ ● ρ_v⦈)`"* as `Fig16.ResU.walks_none_of_hash_own`, the four walks silenced by the `own` cell that `●` admits no second cell beside; then the display's four lines — 6.18 and 6.20 (`Fig16.ResU.Flat.split`), 6.3 (`Fig16.ResU.CompS.assoc`) with 6.31 (`Fig16.ResU.compR_iff_compS`), 6.32 (`Fig16.ExS.toExR`), and Definition 6.1 naming the last line's `⦇ρ_v⦈_○` (`Fig16.ResU.FlatR`). The closing sentence is `Fig16.AgW.single_imm` inserting the one cell where the last line has room for it, and 6.41 (`Fig16.ResU.compatS_single_own`) for the `▸◂`.
-/
/-- **`[TR]` Lemma 6.34** (p. 11): if `ρ # ρ_v ● ℓ ↦ own(v)` and `@ρ_v ⊐ ᾱ`
then `ρ # ℓ ↦ imm(ᾱ, v, ρ_v)`.

Step for step.  *"By lemma 6.11, we have `ρ # ρ_v` and `ρ # ℓ ↦ own(v)`"* is
`ResU.Hash.split` at the printed composition, with `ResU.hash_symm` (6.2 at `#`)
putting the operands in the print's order.  *"Unfolding these, we have
`ℓ ∉ dom(⦇ρ ● ρ_v⦈)`"* is `ResU.walks_none_of_hash_own`, at the four walks the
display names.

The display then runs: line 2 is Lemmas 6.18 and 6.20 (`ResU.Flat.split`);
line 3 regroups by Lemma 6.3 (`ResU.CompS.assoc`) and reads the freed `●` at `○`
by Lemma 6.31 (`ResU.compR_iff_compS`); line 4 is Lemma 6.32 (`ExS.toExR`),
which is what lets `ex(ρ_v)_●` be the `ex(ρ_v)_○` that `ag`'s `imm` family calls
for; and line 5 regroups the three `○` factors as `⦇ρ_v⦈_○ ○ ag(ρ)`, which is
Definition 6.1 and is named here as `ResU.FlatR ρ_v P`.

*"The last equality, with the fact that `ℓ` is not in the domain, is sufficient
to complete the proof."*  `ex(ρ ● ℓ ↦ imm(ᾱ, v, ρ_v))_●` is `ex(ρ)_●` (6.18 and
`ExW.empty_of_all_imm`) and `ag(ρ ● ℓ ↦ imm(ᾱ, v, ρ_v))` is
`ag(ρ) ○ (ℓ ↦ imm(ᾱ, v, ρ_v) ○ ⦇ρ_v⦈_○)` (6.20 and `AgW.single_imm`), so the
flattening of the conclusion's composite is the last line with the one cell
inserted at `ℓ` — which composes because `ℓ` is in the domain of none of the
factors.  `ρ ▸◂ ℓ ↦ imm(ᾱ, v, ρ_v)` is the same absence at `ρ` itself, by
Lemma 6.41 (`ResU.compatS_single_own`) on the `#` that 6.11 returned.

`@ρ_v ⊐ ᾱ` is `hs`, `CellU.immOf`'s own typing argument; the printed proof does
not use it again.
`[as printed]` (the printed `●`s appear as their graphs — G4) -/
theorem ResU.six34 {l : Loc} {s : LSet} {v : Val} {ρ ρv W : ResU Loc Val}
    {hs : ρv.InStratum s.join}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W)
    (hh : ResU.Hash ρ W) :
    ResU.Hash ρ (ResU.single l (CellU.immOf s v ρv hs)) := by
  classical
  -- By 6.11, `ρ # ρ_v` and `ρ # ℓ ↦ own(v)`.
  obtain ⟨hhv, hho⟩ := ResU.Hash.split hW (ResU.hash_symm hh)
  have hρl : ρ.get l = none := ResU.compatS_single_own hho.1
  -- The printed display, at `ρ ● ρ_v`.
  obtain ⟨-, T₀, hT₀, σ₀, Ee, Aa, hEe, hAa, hσ₀⟩ := ResU.hash_symm hhv
  obtain ⟨e₁, f₁, he₁, hf₁, hEc⟩ := (ExS.split hT₀).mp hEe
  obtain ⟨a₁, b₁, ha₁, hb₁, hAc⟩ := (AgW.split hT₀).mp hAa
  obtain ⟨he₁l, ha₁l, hf₁l, hb₁l⟩ :=
    ResU.walks_none_of_hash_own hW hh he₁ ha₁ hf₁ hb₁
  have hEel : Ee.get l = none := (ResU.Comp.eq_none_iff hEc l).mpr ⟨he₁l, hf₁l⟩
  have hAal : Aa.get l = none := (ResU.Comp.eq_none_iff hAc l).mpr ⟨ha₁l, hb₁l⟩
  have hσ₀l : σ₀.get l = none := (ResU.Comp.eq_none_iff hσ₀ l).mpr ⟨hEel, hAal⟩
  -- Line 3: regroup, and read the freed `●` at `○` by 6.31.
  obtain ⟨X, hX₁, hX₂⟩ := (ResU.CompS.assoc e₁ f₁ Aa σ₀).mpr ⟨Ee, hEc, hσ₀⟩
  have hXR : ResU.CompR f₁ Aa X := (ResU.compR_iff_compS hX₁.1 X).mpr hX₁
  -- Lines 4 and 5: 6.32 names `ex(ρ_v)_●` at `○`, and the three `○` factors
  -- regroup as `⦇ρ_v⦈_○ ○ ag(ρ)`.
  obtain ⟨P, hP₁, hP₂⟩ :=
    (ResU.CompR.assoc a₁ b₁ f₁ X).mpr ⟨Aa, hAc, ResU.CompR.comm hXR⟩
  have hflatR : ResU.FlatR ρv P := ⟨b₁, f₁, hb₁, ExS.toExR hf₁, hP₁⟩
  have hXl : X.get l = none := ((ResU.Comp.eq_none_iff hX₂ l).mp hσ₀l).2
  -- `ρ ▸◂ ℓ ↦ imm(ᾱ, v, ρ_v)`, `ℓ` being absent from `ρ`.
  have hcompat : ResU.CompatS ρ (ResU.single l (CellU.immOf s v ρv hs)) :=
    ResU.Compat.of_disjoint (fun l' => by
      by_cases hl : l' = l
      · exact Or.inl (hl ▸ hρl)
      · exact Or.inr (ResU.single_get_ne _ hl))
  obtain ⟨ρρi, hρρi⟩ :=
    (ResU.compS_defined_iff ρ (ResU.single l (CellU.immOf s v ρv hs))).mpr hcompat
  refine ⟨hcompat, ρρi, hρρi, ?_⟩
  have hexρi : ExS ρρi e₁ :=
    (ExS.split hρρi).mpr ⟨e₁, PMap.empty, he₁,
      ExW.empty_of_all_imm (fun m' ψ hg => by
        obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hg
        exact CellU.kind_immOf _ _ _ _),
      ResU.comp_empty_right e₁⟩
  -- The one cell, inserted where the last line has room for it.
  have hcsA : ResU.CompatS (ResU.single l (CellU.immOf s v ρv hs)) X :=
    ResU.Compat.of_disjoint (fun l' => by
      by_cases hl : l' = l
      · exact Or.inr (hl ▸ hXl)
      · exact Or.inl (ResU.single_get_ne _ hl))
  obtain ⟨A, hA⟩ :=
    (ResU.compS_defined_iff (ResU.single l (CellU.immOf s v ρv hs)) X).mpr hcsA
  have hAR : ResU.CompR (ResU.single l (CellU.immOf s v ρv hs)) X A :=
    (ResU.compR_iff_compS hcsA A).mpr hA
  obtain ⟨A₂, hA₂a, hA₂b⟩ :=
    (ResU.CompR.assoc a₁ P (ResU.single l (CellU.immOf s v ρv hs)) A).mpr
      ⟨X, hP₂, ResU.CompR.comm hAR⟩
  have hagρi : AgW (ResU.single l (CellU.immOf s v ρv hs)) A₂ :=
    AgW.single_imm hflatR (ResU.CompR.comm hA₂a)
  have hagA : AgW ρρi A := (AgW.split hρρi).mpr ⟨a₁, A₂, ha₁, hagρi, hA₂b⟩
  have hcsσ : ResU.CompatS (ResU.single l (CellU.immOf s v ρv hs)) σ₀ :=
    ResU.Compat.of_disjoint (fun l' => by
      by_cases hl : l' = l
      · exact Or.inr (hl ▸ hσ₀l)
      · exact Or.inl (ResU.single_get_ne _ hl))
  obtain ⟨σ, hσ⟩ :=
    (ResU.compS_defined_iff (ResU.single l (CellU.immOf s v ρv hs)) σ₀).mpr hcsσ
  obtain ⟨y, hy₁, hy₂⟩ :=
    (ResU.CompS.assoc (ResU.single l (CellU.immOf s v ρv hs)) e₁ X σ).mp
      ⟨σ₀, hX₂, hσ⟩
  obtain ⟨x, hx₁, hx₂⟩ :=
    (ResU.CompS.assoc e₁ (ResU.single l (CellU.immOf s v ρv hs)) X σ).mpr
      ⟨y, ResU.CompS.comm hy₁, hy₂⟩
  rw [ResU.CompS.functional hx₁ hA] at hx₂
  exact ⟨σ, e₁, A, hexρi, hagA, hx₂⟩

end BoCa.Fig16

alias TR.lemma_6_34 := BoCa.Fig16.ResU.six34

/-!
## Lemma 6.35 · `[TR]` p. 12 · `proved`

> If ⦇ρ ● ρ′⦈ is defined then ⦇ρ⦈ and ⦇ρ′⦈ are defined.

**Printed proof, transcribed.** Unfolding `⦇−⦈` and applying Lemmas 6.20 and 6.18, `⦇ρ ● ρ′⦈ = ex(ρ ● ρ′)_● ● ag(ρ ● ρ′) = ex(ρ)_● ● ex(ρ′)_● ● (ag(ρ) ○ ag(ρ′))`, all defined.  Then: `ex(ρ)_● ● ex(ρ′)_● ▸◂ ag(ρ)` by Lemmas 6.30 and 6.36; hence `ex(ρ)_● ▸◂ ag(ρ)`, so `⦇ρ⦈` is defined; `ex(ρ)_● ● ex(ρ′)_● ▸◂ ag(ρ′)` by Lemmas 6.30 and 6.36; hence `ex(ρ′)_● ▸◂ ag(ρ′)`, so `⦇ρ′⦈` is defined.

**Lean.** `BoCa.Fig16.ResU.Valid.split`, alias `TR.lemma_6_35`, tag `[as printed]` — the declaration of Lemma 6.10, in `Paper/S6_1_StandardLemmas/Lemmas.lean`: the same statement, printed twice.

**Note.** `Fig16.ResU.Valid.split` — the **same declaration as 6.10**, 6.10 (p. 7) and 6.35 (p. 12) being the same statement printed twice: p. 5 defines `✓ρ ≜ ⦇ρ⦈ defined`, so "if `✓(ρ₁ ● ρ₂)` then `✓ρ₁` and `✓ρ₂`" and "if `⦇ρ ● ρ′⦈` is defined then `⦇ρ⦈` and `⦇ρ′⦈` are defined" differ only in whether the abbreviation is spelled out. The proof written is this one, the longer printed one: `Fig16.ResU.Flat.split_factors` is its display and its four composability constraints, taking 6.18 and 6.20 through `Fig16.ResU.Flat.split`, then 6.30 and 6.36 (`Fig16.ExS.immFree`) for the first and third bullets and `Fig16.ResU.CompatS.of_compS_left_immFree` for the second and fourth, and 6.9 to turn `▸◂` back into definedness.
-/
alias TR.lemma_6_35 := BoCa.Fig16.ResU.Valid.split

/-!
## Lemma 6.36 · `[TR]` p. 12 · `proved`

> If ex(ρ)_◐ is defined then ex(ρ)_◐∣imm = ∅.

**Printed proof, transcribed.** By induction on `ρ` and unfolding `ex`, noting that at each level only `mut` and `own` are kept.

**Lean.** `BoCa.Fig16.ExW.immFree`, alias `TR.lemma_6_36`, tag `[as printed]` — declared in `Paper/S6_1_StandardLemmas/Lemmas.lean`, ahead of this subsection: the Lean of Lemmas 6.7, 6.8, 6.10, 6.11 and 6.15 there needs it.

**Note.** `Fig16.ExW.immFree`, on the printed carrier, by induction on the walk. Generic in `C` under `hC`, and the discharge is **performed**, not merely available: `Fig16.ExS.immFree` at `●` (via `Fig16.CellU.compS_ne_imm`) and `Fig16.ExR.immFree` at `○` (via `Fig16.CellU.compR_ne_imm`), which are the two values the print's schematic `◐` takes; `Fig16.ResU.restrict_imm_empty_iff` is `ρ
-/
alias TR.lemma_6_36 := BoCa.Fig16.ExW.immFree

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.37 · `[TR]` p. 12 · `proved`

> If ρ ▸◂ ρ₁ and ρ ▸◂ ρ₂ and ρ₁ ▷◁ ρ₂ then ρ ▸◂ ρ₁ ○ ρ₂.

**Printed proof, transcribed.** Unfolding `▸◂`, at a location of `dom(ρ) ∩ dom(ρ₁)` both cells are `imm` over one witness and one value, and similarly for `ρ₂`.  By the definition of `○`, at a location of `dom(ρ) ∩ dom(ρ₁) ∩ dom(ρ₂)` the composite `(ρ₁ ○ ρ₂)(ℓ)` is `imm` over that witness and value, which suffices.

**Lean.** `BoCa.Fig16.ResU.six37`, alias `TR.lemma_6_37`, tag `[as printed]`.

**Note.** `Fig16.ResU.six37`, on the printed carrier, `[as printed]`, with `ρ₁ ○ ρ₂` named by its graph (G4) whose own first conjunct is the printed `ρ₁ ▷◁ ρ₂`. It is the **same statement as 6.12** (p. 7), printed twice in two notations: 6.12's "`ρ₁ ● ρ₂` … defined" is `▸◂` by Lemma 6.9 (`Fig16.ResU.compS_defined_iff`) and its "`ρ₂ ○ ρ₃` … defined" is `▷◁` by that lemma's `○` twin (`Fig16.ResU.compR_defined_iff`), so the rows agree hypothesis for hypothesis.  6.37's own printed proof — the overlap is `imm` on both sides over one value and one witness, and `○` returns a cell over that same value and witness — is `Fig16.CellU.CompatS.of_compR_left`, which is what `Fig16.ResU.compatS_of_compR` already carries for 6.12. [TR]'s proofs of 6.38 (p. 13), 6.39 (p. 15) and 6.55 (p. 18) cite it; 6.35's does not, it closes on 6.20/6.18/6.30/6.36
-/
/-- **`[TR]` Lemma 6.37** (p. 13): if `ρ ▸◂ ρ₁` and `ρ ▸◂ ρ₂` and `ρ₁ ▷◁ ρ₂`
then `ρ ▸◂ ρ₁ ○ ρ₂`.

`[TR]`'s proof: *"Unfolding the definition of `▸◂`, we have for any
`ℓ ∈ dom(ρ) ∩ dom(ρ₁)`, `ρ(ℓ) = imm(_, ρ, v)` and `ρ₁(ℓ) = imm(_, ρ, v)`, and
similarly for `ρ₂`.  By the definition of `○`, if
`ℓ′ ∈ dom(ρ) ∩ dom(ρ₁) ∩ dom(ρ₂)`, then `(ρ₁ ○ ρ₂)(ℓ) = imm(_, ρ, v)`, which is
sufficient to complete the proof."*  That is `CellU.CompatS.of_compR_left` at
the overlap and the two hypotheses off it, which is exactly the proof
`ResU.compatS_of_compR` carries for 6.12.

`ρ₁ ○ ρ₂` is named by its graph (G4), and `ResU.CompR`'s own first conjunct is
the printed `ρ₁ ▷◁ ρ₂`, so the three printed hypotheses are all present.
`[as printed]` (the printed `ρ₁ ○ ρ₂` appears as its graph — G4) -/
theorem ResU.six37 {ρ ρ₁ ρ₂ r : ResU Loc Val} (h₁ : ResU.CompatS ρ ρ₁)
    (h₂ : ResU.CompatS ρ ρ₂) (h₁₂ : ResU.CompR ρ₁ ρ₂ r) : ResU.CompatS ρ r :=
  ResU.compatS_of_compR h₁ h₂ h₁₂

end BoCa.Fig16

alias TR.lemma_6_37 := BoCa.Fig16.ResU.six37

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### Row 5.67's theorem `BoCa.Fig16.AgW.nonimm_beneath_imm`, ahead of its file

A remark on a printed definition of `[TR]` §5; its proof uses results of §6, and the Lean of Lemmas 6.38, 6.48 and 6.59 in this file needs it, so it is declared here.  The row is recorded in `Paper/S5_Model/Remarks.lean`.
-/
/-- **Every non-`imm` cell of `ag(ρ)` sits beneath an `imm` cell of `ag(ρ)`.**
`ag(ρ) = (ρ|imm ○ ⨀ ag(ρᵥ)) ○ ⨀ (ex(ρ′)_○ ○ ag(ρ′))`; the first group carries no
`own` or `mut` cell of its own and the second carries none either, by the same
argument one level down — so such a cell enters only through `ex(−)_○` inside
the `imm` family,
and the `imm` cell it entered beneath is carried to the top at its own location
by the same chain of `ag`s.

This is why `[TR]` 6.59's closing step lands on `↭`'s **first** clause, which
pins an `imm` cell together with its witness, rather than on the second, which
leaves a `mut` cell's value and witness free.
`[about ours: where `ag(ρ)`'s `mut` cells come from]` -/
theorem AgW.nonimm_beneath_imm {ρ σ : ResU Loc Val} (h : AgW ρ σ) :
    ∀ (n : Loc) (φ : CellU Loc Val), σ.get n = some φ → φ.kind ≠ Kind.imm →
      ∃ (m : Loc) (s : LSet) (u : Val) (χ : ResU Loc Val)
        (hh : χ.InStratum s.join) (ev av p : ResU Loc Val) (ξ : CellU Loc Val),
        σ.get m = some (CellU.immOf s u χ hh) ∧
        ExR χ ev ∧ AgW χ av ∧ ResU.CompR ev av p ∧
        p.get n = some ξ ∧ ξ.kind ≠ Kind.imm ∧
        ξ.wit = φ.wit ∧ ξ.erase = φ.erase := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  refine AgW.rec
    (motive_1 := fun ρ σ _ => ∀ (n : Loc) (φ : CellU Loc Val),
      σ.get n = some φ → φ.kind ≠ Kind.imm →
      ∃ (m : Loc) (s : LSet) (u : Val) (χ : ResU Loc Val)
        (hh : χ.InStratum s.join) (ev av p : ResU Loc Val) (ξ : CellU Loc Val),
        σ.get m = some (CellU.immOf s u χ hh) ∧
        ExR χ ev ∧ AgW χ av ∧ ResU.CompR ev av p ∧
        p.get n = some ξ ∧ ξ.kind ≠ Kind.imm ∧
        ξ.wit = φ.wit ∧ ξ.erase = φ.erase)
    (motive_2 := fun ρ w _ => ∀ q ∈ w, ∀ (n : Loc) (φ : CellU Loc Val),
      q.2.get n = some φ → φ.kind ≠ Kind.imm →
      ∃ (m : Loc) (s : LSet) (u : Val) (χ : ResU Loc Val)
        (hh : χ.InStratum s.join) (ev av p : ResU Loc Val) (ξ : CellU Loc Val),
        q.2.get m = some (CellU.immOf s u χ hh) ∧
        ExR χ ev ∧ AgW χ av ∧ ResU.CompR ev av p ∧
        p.get n = some ξ ∧ ξ.kind ≠ Kind.imm ∧
        ξ.wit = φ.wit ∧ ξ.erase = φ.erase)
    (motive_3 := fun ρ w _ => ∀ q ∈ w, ∀ (n : Loc) (φ : CellU Loc Val),
      q.2.get n = some φ → φ.kind ≠ Kind.imm →
      ∃ (s : LSet) (u : Val) (χ : ResU Loc Val)
        (hh : χ.InStratum s.join) (ev av p : ResU Loc Val) (ξ : CellU Loc Val),
        ExR χ ev ∧ AgW χ av ∧ ResU.CompR ev av p ∧
        p.get n = some ξ ∧ ξ.kind ≠ Kind.imm ∧
        ξ.wit = φ.wit ∧ ξ.erase = φ.erase ∧
        ((∃ m, q.2.get m = some (CellU.immOf s u χ hh)) ∨
          ρ.get q.1 = some (CellU.immOf s u χ hh)))
    ?mk ?nilM ?consM ?nilI ?consI h
  case mk =>
    intro ρ' σ' a bm bi wm wi hsm hsi hwm hwi hbm hbi ha hσ ihm ihi n φ hg hk
    rcases ResU.CompR.nonimm_source hσ hg hk with
      ⟨ξa, ea, ka, wa, era⟩ | ⟨ξb, eb, kb, wb, erb⟩
    · rcases ResU.CompR.nonimm_source ha ea ka with
        ⟨ξr, er, kr, wr, err⟩ | ⟨ξm, em, km, wm2, erm⟩
      · exact absurd (ResU.restrict_eq_some.mp er).2 kr
      · obtain ⟨τ, hmem, ξ', e', k', w', er'⟩ := BigComp.nonimm_source hbm em km
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmem
        obtain ⟨m, s, u, χ, hh, ev, av, pp, ξ, hqm, hex, hag, hc, hpn, hkξ, hwξ, heξ⟩ :=
          ihm q hq n ξ' e' k'
        obtain ⟨z, hz⟩ := BigComp.mem_factor hR ResU.compLawsR hbm q.2
          (List.mem_map.mpr ⟨q, hq, rfl⟩)
        obtain ⟨y₁, hy₁⟩ :=
          ResU.Comp.factor_trans hR ResU.compLawsR hz (ResU.CompR.comm ha)
        obtain ⟨y₂, hy₂⟩ := ResU.Comp.factor_trans hR ResU.compLawsR hy₁ hσ
        obtain ⟨s'', h'', hσm⟩ := ResU.CompR.imm_left_get hy₂ hqm
        exact ⟨m, s'', u, χ, h'', ev, av, pp, ξ, hσm, hex, hag, hc, hpn, hkξ,
          hwξ.trans (w'.trans (wm2.trans wa)),
          heξ.trans (er'.trans (erm.trans era))⟩
    · obtain ⟨τ, hmem, ξ', e', k', w', er'⟩ := BigComp.nonimm_source hbi eb kb
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmem
      obtain ⟨s, u, χ, hh, ev, av, pp, ξ, hex, hag, hc, hpn, hkξ, hwξ, heξ, hdisj⟩ :=
        ihi q hq n ξ' e' k'
      obtain ⟨z, hz⟩ := BigComp.mem_factor hR ResU.compLawsR hbi q.2
        (List.mem_map.mpr ⟨q, hq, rfl⟩)
      obtain ⟨y₁, hy₁⟩ := ResU.Comp.factor_trans hR ResU.compLawsR hz (ResU.CompR.comm hσ)
      rcases hdisj with ⟨m, hqm⟩ | hρm
      · obtain ⟨s'', h'', hσm⟩ := ResU.CompR.imm_left_get hy₁ hqm
        exact ⟨m, s'', u, χ, h'', ev, av, pp, ξ, hσm, hex, hag, hc, hpn, hkξ,
          hwξ.trans (w'.trans wb), heξ.trans (er'.trans erb)⟩
      · have hri : (ρ'.restrict Kind.imm).get q.1 = some (CellU.immOf s u χ hh) :=
          ResU.restrict_get_some hρm (CellU.kind_immOf _ _ _ _)
        obtain ⟨s₁, h₁, ham⟩ := ResU.CompR.imm_left_get ha hri
        obtain ⟨s'', h'', hσm⟩ := ResU.CompR.imm_left_get hσ ham
        exact ⟨q.1, s'', u, χ, h'', ev, av, pp, ξ, hσm, hex, hag, hc, hpn, hkξ,
          hwξ.trans (w'.trans wb), heξ.trans (er'.trans erb)⟩
  case nilM => intro ρ' q hq; exact absurd hq (by simp)
  case consM =>
    intro ρ' e l w ψ hψ hk he hw ihe ihw q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact ihe
    · exact ihw q hq'
  case nilI => intro ρ' q hq; exact absurd hq (by simp)
  case consI =>
    intro ρ' pe l w ψ hψ hk e a hex hag hc hw iha ihw q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · intro n φ hg hkφ
      obtain ⟨s, hs, heta⟩ := CellU.imm_eta hk
      rcases ResU.CompR.nonimm_source hc hg hkφ with
        ⟨ξe, ee, ke, we, ere⟩ | ⟨ξa, ea, ka, wa, era⟩
      · exact ⟨s, ψ.erase, ψ.wit, hs, e, a, pe, φ, hex, hag, hc, hg, hkφ, rfl, rfl,
          Or.inr (hψ.trans (congrArg some heta))⟩
      · obtain ⟨m, s', u, χ, hh, ev, av, pp, ξ, ham, hex', hag', hc', hpn,
          hkξ, hwξ, heξ⟩ := iha n ξa ea ka
        obtain ⟨s'', h'', hpm⟩ :=
          ResU.CompR.imm_left_get (ResU.CompR.comm hc) ham
        exact ⟨s'', u, χ, h'', ev, av, pp, ξ, hex', hag', hc', hpn, hkξ,
          hwξ.trans wa, heξ.trans era, Or.inl ⟨m, hpm⟩⟩
    · exact ihw q hq'

/-! `[about ours]` — what the Lean of Lemma 6.38 needs; the paper prints nothing here. -/
/-- **`[TR]` Lemma 6.38's first two sentences.**  6.29 with H3, H1 and H6 gives
H7, `ResU.six38_no_borrow_in_frame` moves the deletion past `ρ′`, and what the
two together deliver is `ρ′ ● ρ⁺/ℓ # ℓ ↦ imm({α}, v, ρ_v)` — the `#` the rest of
the printed proof works from.
`[about ours: `[TR]` Lemma 6.38's proof through its second sentence]` -/
theorem ResU.six38_steps_one_two {α : Life} {l : BoCa.Loc} {v : BoCa.Val}
    {ρ ρv ρ' ρp W ρρi ρ'ρp : ResU BoCa.Loc BoCa.Val}
    {hv : ρv.InStratum (LSet.singleton α).join}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W)
    (h1 : ResU.Hash ρ W) (h2 : ResU.Hash ρ' ρp)
    (h3 : ρ.InStratum α) (h4 : ρ'.InStratum α)
    (hρi : ResU.CompS ρ (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ρρi)
    (hpp : ResU.CompS ρ' ρp ρ'ρp) (h6 : ResU.UpdV ρρi ρ'ρp) :
    ResU.CompS ρ' (ρp.del l) (ρ'ρp.del l) ∧
      ResU.Hash (ρ'ρp.del l)
        (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ∧
      ResU.CompS (ρ'ρp.del l)
        (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ρ'ρp := by
  classical
  have h7 : ResU.CompS (ρ'ρp.del l)
      (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ρ'ρp :=
    ResU.six29 h3 hW h1 hρi h6
  have hcl : ρ'ρp.get l = some (CellU.immOf (LSet.singleton α) v ρv hv) :=
    ResU.compS_single_get_self (ResU.CompS.comm h7) (ResU.del_get_self _ _)
  have hρ'l : ρ'.get l = none := ResU.six38_no_borrow_in_frame h4 hpp hcl
  obtain ⟨-, x, hx, hvx⟩ := h2
  rw [ResU.CompS.functional hx hpp] at hvx
  refine ⟨⟨fun m ψ₁ ψ₂ e₁ e₂ => ?_, fun m => ?_⟩, ⟨h7.1, ρ'ρp, h7, hvx⟩, h7⟩
  · by_cases hm : m = l
    · subst hm; rw [ResU.del_get_self] at e₂; exact absurd e₂ (by simp)
    · exact hpp.1 m ψ₁ ψ₂ e₁ (by rwa [ResU.del_get_ne ρp hm] at e₂)
  · by_cases hm : m = l
    · subst hm
      show OptComp CellU.CompS (ρ'.get m) ((ρp.del m).get m) ((ρ'ρp.del m).get m)
      rw [hρ'l, ResU.del_get_self, ResU.del_get_self]
      rfl
    · show OptComp CellU.CompS (ρ'.get m) ((ρp.del l).get m) ((ρ'ρp.del l).get m)
      rw [ResU.del_get_ne ρp hm, ResU.del_get_ne ρ'ρp hm]
      exact hpp.2 m

end BoCa.Fig16

namespace BoCa.Fig16

/-- The reduction, so that the residual above is measured and not asserted:
`[TR]` Lemma 6.38 follows from it by its own first two sentences.
`[about ours: `[TR]` Lemma 6.38 reduced to `ResU.SixThirtyEightResidual`]` -/
theorem ResU.sixThirtyEight_of_residual
    (h : ResU.SixThirtyEightResidual) : ResU.SixThirtyEight := by
  intro α l v ρ ρv ρ' ρp W ρρi ρ'ρp hv hW h1 h2 h3 h4 h5 hρi hpp h6
  obtain ⟨hG, hGi, hGc⟩ := ResU.six38_steps_one_two hW h1 h2 h3 h4 hρi hpp h6
  exact ⟨ρ'ρp.del l, hG, h hW h1 h3 h4 h5 hρi hpp h6 hG hGi hGc⟩

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- **`[TR]` 6.38's step-10 sentence, at the reading its next clause fixes.**

*"By the definition of `ag`, `ℓ′ ∈ dom(ρ′|imm)`, `ℓ′ ∈ dom(ρ⁺/ℓ|imm)`, or
there are some `ℓ″`, `ρ″_v` such that `(ag(ρ′) ○ ag(ρ⁺/ℓ))(ℓ″) = imm(_,_,ρ″_v)`
and `ℓ′ ∈ dom(⦇ρ″_v⦈_○)`."*

The first cases are read at `⦇ρ⦈|imm`, not at `ρ|imm`: the clause the sentence
continues with is *"by H6, `ℓ′ ∈ ⦇ρ⦈|imm`"*, and H6 is an update, which
compares flattenings.  At that reading the split is exhaustive and holds at one
walk, which `AgSplitExample.not_agDomSplit` shows the `ρ|imm` reading does not.

An `imm` cell of the walk sits in `⦇ρ⦈` unchanged, `ex(ρ)_●` being `imm`-free
(6.36), which is the first case.  A non-`imm` one is in the walk only because
some `imm` cell's witness carried it there — `ex(ρ″)_○ ○ ag(ρ″)` is the only
factor of p. 5's `ag` that is not `imm`-valued — and that is
`AgW.nonimm_beneath_imm`, whose `ex(χ)_○ ○ ag(χ)` is Definition 6.1's
`⦇χ⦈_○` once commuted.  The sentence composes two walks; `dom` of a composite
is contained in the union of the operands' domains, so the two-operand form is
this one twice.
`[about ours: `[TR]` Lemma 6.38's step-10 sentence, at one walk]` -/
theorem AgW.dom_split {ρ A σ : ResU BoCa.Loc BoCa.Val}
    (h : AgW ρ A) (hf : ResU.Flat ρ σ)
    {m : BoCa.Loc} {ψ : CellU BoCa.Loc BoCa.Val} (hg : A.get m = some ψ) :
    (∃ φ, σ.get m = some φ ∧ φ.kind = Kind.imm) ∨
    (∃ (m' : BoCa.Loc) (χ : CellU BoCa.Loc BoCa.Val) (f : ResU BoCa.Loc BoCa.Val),
      A.get m' = some χ ∧ χ.kind = Kind.imm ∧ ResU.FlatR χ.wit f ∧ (f.get m).isSome) := by
  classical
  by_cases hk : ψ.kind = Kind.imm
  · obtain ⟨e, a, he, ha, hc⟩ := hf
    cases AgW.functional ha h
    exact Or.inl ⟨ψ, ResU.CompS.get_right_of_immFree hc (ExS.immFree he) hg, hk⟩
  · obtain ⟨m', s, u, χ, hh, ev, av, p, ξ, hAm', hex, hag, hp, hpm, -, -, -⟩ :=
      AgW.nonimm_beneath_imm h m ψ hg hk
    refine Or.inr ⟨m', CellU.immOf s u χ hh, p, hAm', CellU.kind_immOf _ _ _ _, ?_, ?_⟩
    · rw [CellU.wit_immOf]
      exact ⟨av, ev, hag, hex, ResU.CompR.comm hp⟩
    · rw [hpm]; rfl

/-- **`[TR]` Lemma 6.38 from its third sentence on** — `ResU.SixThirtyEightResidual`
discharged.

Step for step.  The first display is 6.18 and 6.20 through `ResU.Flat.split` at
`ρ′ ● ρ⁺/ℓ ● ℓ ↦ imm({α}, v, ρ_v)`, with `ExW.empty_of_all_imm` killing the
borrow's exclusive walk and `AgW.single_imm_inv` opening its aliasable one into
`ℓ ↦ imm({α}, v, ρ_v) ○ ex(ρ_v)_○ ○ ag(ρ_v)`; 6.35 (`ResU.Valid.split`) with H1
makes `⦇ρ_v⦈` defined and 6.33 (`ResU.six33`) turns `⦇ρ_v⦈_○` into
`ex(ρ_v)_● ● ag(ρ_v)`, which 6.31 (`ResU.CompS.toCompR`) puts back at `○`.  The
second display is the same at `ρ_v ● ℓ ↦ own(v)`, where `ex` keeps the `own`
cell and `ag(ℓ ↦ own(v)) = ∅`.

*"Applying lemmas 6.30 and 6.36 multiple times"*: 6.3 at `○`
(`ResU.CompR.assoc`) regroups the chain as
`(ag(ρ′) ○ ag(ρ⁺/ℓ) ○ ag(ρ_v)) ○ (ℓ ↦ imm({α}, v, ρ_v) ○ ex(ρ_v)_●)`, and 6.30
(`ResU.CompatS.of_compR_left`) with 6.36 (`ExS.immFree`) peels the three printed
bullets off it, the third giving `▸◂ ℓ ↦ own(v)` because an `imm`-free resource
`▸◂` a cell is disjoint from it.

*"By lemma 6.37 with `⦇ρ_v ● ℓ ↦ own(v)⦈` defined from lemma 6.35 with H1"* is
`ResU.six37` on `ex(W)_● ▸◂ ag(ρ_v)` — the second display's own outer `●` — and
the closing paragraph; and *"by lemma 6.36, `(ex(ρ_v)_● ● ℓ ↦ own(v))|imm = ∅`"*
is what turns the remaining `▸◂` into the disjointness the contradiction refutes.

H5 (`ρ⁺|own = ∅`) is unspent, as it is in the printed proof, and the printed
`ρ′ ● ρ⁺/ℓ # ℓ ↦ imm({α}, v, ρ_v)` is unspent too: `ResU.CompS G ρᵢ (ρ′ ● ρ⁺)`
and `✓(ρ′ ● ρ⁺)` from H6 already carry the first display.
`[about ours: `[TR]` Lemma 6.38's proof from "Then in order to show G1" on]` -/
theorem ResU.sixThirtyEightResidual : ResU.SixThirtyEightResidual := by
  classical
  intro α l v ρ ρv ρ' ρp W ρρi ρ'ρp G hv hW h1 h3 h4 h5 hρi hpp h6 hG hGi hGc
  -- the borrow cell
  set ι : CellU BoCa.Loc BoCa.Val := CellU.immOf (LSet.singleton α) v ρv hv with hιdef
  have hιk : ι.kind = Kind.imm := CellU.kind_immOf _ _ _ _
  have himmi : ∀ m ψ, (ResU.single l ι).get m = some ψ → ψ.kind = Kind.imm := by
    intro m ψ h
    obtain ⟨-, rfl⟩ := ResU.single_get_eq_some h
    exact hιk
  -- `⦇ρ′ ● ρ⁺⦈`, and the first display for `ρ′ ● ρ⁺/ℓ ● ℓ ↦ imm({α}, v, ρ_v)`
  obtain ⟨σρρ, hσρρ⟩ := h6.2.2
  obtain ⟨eG, eI, e, aG, aI, a, heG, heI, hec, haG, haI, hac, hc⟩ :=
    (ResU.Flat.split hGc).mp hσρρ
  obtain rfl : eI = (PMap.empty : ResU BoCa.Loc BoCa.Val) :=
    ExS.functional heI (ExW.empty_of_all_imm himmi)
  obtain rfl : eG = e := ResU.eq_of_comp_empty_right hec
  -- `ag(ℓ ↦ imm({α}, v, ρ_v)) = ℓ ↦ imm({α}, v, ρ_v) ○ ex(ρ_v)_○ ○ ag(ρ_v)`
  obtain ⟨ev, av, p, hev, hav, hcp, hagi⟩ := AgW.single_imm_inv (χ := ρv) haI
  -- 6.35 with H1: `⦇ρ_v⦈` and `⦇ρ_v ● ℓ ↦ own(v)⦈` are defined
  obtain ⟨-, T, hT, hvT⟩ := id h1
  obtain ⟨hvρ, hvW⟩ := ResU.Valid.split hT hvT
  obtain ⟨hvρv, -⟩ := ResU.Valid.split hW hvW
  obtain ⟨σv, hσv⟩ := hvρv
  obtain ⟨exv, agv, hexv, hagv, hcv⟩ := hσv
  obtain rfl : av = agv := AgW.functional hav hagv
  -- 6.33: `⦇ρ_v⦈_○ = ⦇ρ_v⦈`, so `p = ex(ρ_v)_● ● ag(ρ_v)`
  obtain rfl : p = σv :=
    ResU.FlatR.functional ⟨av, ev, hav, hev, ResU.CompR.comm hcp⟩
      (ResU.six33 ⟨exv, av, hexv, hav, hcv⟩)
  -- The second display: `ex(W)_● = ex(ρ_v)_● ● ℓ ↦ own(v)` and `ag(W) = ag(ρ_v)`
  obtain ⟨σW, hσW⟩ := hvW
  obtain ⟨f₁, f₂, eW, b₁, b₂, aW, hf₁, hf₂, hfc, hb₁, hb₂, hbc, hWc⟩ :=
    (ResU.Flat.split hW).mp hσW
  obtain rfl : exv = f₁ := ExS.functional hexv hf₁
  obtain rfl : ResU.single l (CellU.ownOf v) = f₂ :=
    ExS.functional (ExW.single_own l v) hf₂
  obtain rfl : av = b₁ := AgW.functional hav hb₁
  obtain rfl : (PMap.empty : ResU BoCa.Loc BoCa.Val) = b₂ :=
    AgW.functional (AgW.single_own l v) hb₂
  obtain rfl : av = aW := ResU.eq_of_comp_empty_right hbc
  have heW : ExS W eW :=
    (ExS.split hW).mpr ⟨exv, _, hexv, ExW.single_own l v, hfc⟩
  have haW : AgW W av := (AgW.split hW).mpr ⟨av, _, hav, AgW.single_own l v, hbc⟩
  -- `ag(ρ′) ○ ag(ρ⁺/ℓ) ○ ℓ ↦ imm({α},v,ρ_v) ○ ex(ρ_v)_● ○ ag(ρ_v)` regrouped so
  -- that `ag(ρ′) ○ ag(ρ⁺/ℓ) ○ ag(ρ_v)` is one factor: `[TR]` 6.3 at `○`.
  have hcvR : ResU.CompR exv av p := ResU.CompS.toCompR hcv
  obtain ⟨y, hy₁, hy₂⟩ :=
    (ResU.CompR.assoc aG (ResU.single l ι) p a).mp ⟨aI, hagi, hac⟩
  obtain ⟨z, hz₁, hz₂⟩ := (ResU.CompR.assoc y exv av a).mp ⟨p, hcvR, hy₂⟩
  obtain ⟨Z, hZ, hZ₂⟩ :=
    (ResU.CompR.assoc aG (ResU.single l ι) exv z).mpr ⟨y, hy₁, hz₁⟩
  obtain ⟨A, hA₀, hAZ⟩ :=
    (ResU.CompR.assoc av aG Z a).mp ⟨z, hZ₂, ResU.CompR.comm hz₂⟩
  have hA : ResU.CompR aG av A := ResU.CompR.comm hA₀
  -- The three printed bullets: 6.30 and 6.36 at each `○`.
  have himmE : eG.ImmFree := ExS.immFree heG
  have himmE' : eG.restrict Kind.imm = PMap.empty :=
    (ResU.restrict_imm_empty_iff eG).mpr himmE
  obtain ⟨hcA, hcZ⟩ := ResU.CompatS.of_compR_left himmE' hAZ hc.1
  obtain ⟨hcι, hcexv⟩ := ResU.CompatS.of_compR_left himmE' hZ hcZ
  obtain ⟨hcaG, hcav⟩ := ResU.CompatS.of_compR_left himmE' hA hcA
  -- `⦇ρ⦈`, `⦇W⦈` and the disjointness H1 supplies
  obtain ⟨σT, hσT⟩ := hvT
  obtain ⟨e₁, e₂, eT, a₁, a₂, aT, he₁, he₂, hecT, ha₁, ha₂, hacT, hcT⟩ :=
    (ResU.Flat.split hT).mp hσT
  obtain rfl : eW = e₂ := ExS.functional heW he₂
  obtain rfl : av = a₂ := AgW.functional haW ha₂
  have himmW : eW.ImmFree := ExS.immFree heW
  have himmT : eT.ImmFree := ResU.ImmFree.compS hecT (ExS.immFree he₁) himmW
  obtain ⟨hcTa₁, -⟩ :=
    ResU.CompatS.of_compR_left ((ResU.restrict_imm_empty_iff eT).mpr himmT) hacT hcT.1
  obtain ⟨-, hcWa₁⟩ := ResU.CompatS.of_compS_left_immFree himmT hecT hcTa₁
  have hF1 : ∀ m, eW.get m = none ∨ a₁.get m = none :=
    ResU.CompatS.disjoint_of_immFree himmW hcWa₁
  have hF2 : ∀ m, eW.get m = none ∨ av.get m = none :=
    ResU.CompatS.disjoint_of_immFree himmW hWc.1
  -- `⦇G⦈` itself
  obtain ⟨σG, hσGc⟩ := (ResU.compS_defined_iff eG aG).mpr hcaG
  have hσG : ResU.Flat G σG := ⟨eG, aG, heG, haG, hσGc⟩
  -- `[TR]` 6.29's second sentence, at `ρ′ ● ρ⁺`
  obtain ⟨hσρρl, hstrat⟩ :=
    ResU.six29_borrows_off (hv := hv) h3 hW h1 hρi h6 hσρρ
  have h7 : ResU.CompS (ρ'ρp.del l)
      (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ρ'ρp :=
    ResU.six29 h3 hW h1 hρi h6
  have hcl : ρ'ρp.get l = some (CellU.immOf (LSet.singleton α) v ρv hv) :=
    ResU.compS_single_get_self (ResU.CompS.comm h7) (ResU.del_get_self _ _)
  have hρ'l : ρ'.get l = none := ResU.six38_no_borrow_in_frame h4 hpp hcl
  have hGl : G.get l = none :=
    (ResU.Comp.eq_none_iff hG l).mpr ⟨hρ'l, ResU.del_get_self _ _⟩
  -- `ρ′ ● ρ⁺/ℓ ∈ Res_α`, hence so is `⦇ρ′ ● ρ⁺/ℓ⦈`
  have hGstrat : G.InStratum α := by
    intro m φ hφ
    by_cases hm : m = l
    · subst hm; rw [hGl] at hφ; simp at hφ
    · refine ResU.flat_inStratum_inv_at hσρρ (hstrat m hm) ?_
      exact (ResU.Comp.get_of_right_none hGc
        (ResU.single_get_ne _ hm)).trans hφ
  have hσGstrat : σG.InStratum α := BoLo.flat_inStratum hσG hGstrat
  -- `⦇ρ′ ● ρ⁺/ℓ⦈ = ⦇ρ′ ● ρ⁺⦈ ○ ⦇ℓ ↦ imm({α},v,ρ_v)⦈` read backwards at `ℓ`:
  -- the borrow is at the top level of `ρ′ ● ρ⁺` and nowhere else
  obtain ⟨σG', σI, hσG', hσI, hCompRG⟩ := BoLo.flat_compR hGc hσρρ
  obtain rfl : σG = σG' := ResU.Flat.functional hσG hσG'
  have hF3 : ∀ ψ, σG.get l = some ψ → ψ.kind ≠ Kind.imm := by
    intro ψ hψ hk
    obtain ⟨s₁, hs₁, heta⟩ := CellU.imm_eta hk
    have hψ' : σG.get l = some (CellU.immOf s₁ ψ.erase ψ.wit hs₁) :=
      hψ.trans (congrArg some heta)
    have hsub : ∀ x, s₁.mem x → (LSet.singleton α).mem x := fun x hx =>
      ResU.CompR.get_ls_imm hCompRG hψ' hσρρl hx
    obtain ⟨y, hy⟩ := LSet.nonempty s₁
    have hmem : s₁.mem α := by
      have hyα : y = α := hsub y hy
      exact hyα ▸ hy
    have hstr := hσGstrat l _ hψ'
    rw [CellU.inStratum_immOf] at hstr
    exact absurd (s₁.meet_least α hmem) (not_le_of_gt hstr)
  -- *"by H6"*: an `imm` cell of `⦇ρ′ ● ρ⁺/ℓ⦈` is one of `ag(ρ)`, one of
  -- `ag(ρ_v)`, or the borrow at `ℓ`
  obtain ⟨σρρi, hσρρi⟩ := h6.2.1
  obtain ⟨τρ, τI, hτρ, hτI, hCompRρ⟩ := BoLo.flat_compR hρi hσρρi
  obtain ⟨eρ, aρ, heρ, haρ, hcρ⟩ := hτρ
  obtain rfl : a₁ = aρ := AgW.functional ha₁ haρ
  obtain ⟨eI', aI', heI', haI', hcI'⟩ := hτI
  obtain rfl : (PMap.empty : ResU BoCa.Loc BoCa.Val) = eI' :=
    ExS.functional (ExW.empty_of_all_imm himmi) heI'
  obtain rfl : aI' = τI := ResU.eq_of_comp_empty_left hcI'
  obtain ⟨ev', av', p', hev', hav', hcp', hagi'⟩ := AgW.single_imm_inv (χ := ρv) haI'
  obtain rfl : p = p' :=
    ResU.FlatR.functional (ResU.six33 ⟨exv, av, hexv, hav, hcv⟩)
      ⟨av', ev', hav', hev', ResU.CompR.comm hcp'⟩
  have hF4 : ∀ m ψ, σG.get m = some ψ → ψ.kind = Kind.imm →
      m = l ∨ (∃ φ, a₁.get m = some φ ∧ φ.kind = Kind.imm ∧ φ.wit = ψ.wit) ∨
        (∃ φ, av.get m = some φ ∧ φ.kind = Kind.imm ∧ φ.wit = ψ.wit) := by
    intro m ψ hψ hk
    obtain ⟨χ₀, hχ₀, hkχ₀, heχ₀, hwχ₀⟩ := ResU.CompR.get_imm_left hCompRG hψ hk
    obtain ⟨s₀, hs₀, heta₀⟩ := CellU.imm_eta hkχ₀
    have hχ₀' : σρρ.get m = some (CellU.immOf s₀ χ₀.erase χ₀.wit hs₀) :=
      hχ₀.trans (congrArg some heta₀)
    have hupd : σρρi.get m = some (CellU.immOf s₀ χ₀.erase χ₀.wit hs₀) :=
      (ResU.flatAt_iff hσρρi m _).mp
        ((h6.1.1 m s₀ χ₀.erase χ₀.wit hs₀).mpr ⟨σρρ, hσρρ, hχ₀'⟩)
    rcases ResU.CompR.imm_source hCompRρ hupd with ⟨s₂, h₂, hg₂⟩ | ⟨s₃, h₃, hg₃⟩
    · refine Or.inr (Or.inl ⟨_, ResU.ag_eq_flat_at_imm heρ hcρ hg₂
        (CellU.kind_immOf _ _ _ _), CellU.kind_immOf _ _ _ _, ?_⟩)
      rw [CellU.wit_immOf]; exact hwχ₀
    · rcases ResU.CompR.imm_source hagi' hg₃ with ⟨s₄, h₄, hg₄⟩ | ⟨s₅, h₅, hg₅⟩
      · exact Or.inl (ResU.single_get_eq_some hg₄).1
      · refine Or.inr (Or.inr ⟨_, ResU.ag_eq_flat_at_imm hexv hcv hg₅
          (CellU.kind_immOf _ _ _ _), CellU.kind_immOf _ _ _ _, ?_⟩)
        rw [CellU.wit_immOf]; exact hwχ₀
  -- *"Assume for sake of contradiction that `ℓ′ ∈ dom(ex(ρ_v)_● ● ℓ ↦ own(v))`
  -- and `ℓ′ ∈ dom(ag(ρ′) ○ ag(ρ⁺/ℓ))`"*
  have hkey : ∀ m, eW.get m = none ∨ aG.get m = none := by
    intro m
    cases hmW : eW.get m with
    | none => exact Or.inl rfl
    | some ψW =>
      cases hmG : aG.get m with
      | none => exact Or.inr rfl
      | some ψG =>
        exfalso
        rcases AgW.dom_split haG hσG hmG with
          ⟨φ, hφ, hkφ⟩ | ⟨m', χc, f, hm', hkχ, hf, hsf⟩
        · rcases hF4 m φ hφ hkφ with rfl | ⟨φ', hφ', -, -⟩ | ⟨φ', hφ', -, -⟩
          · exact hF3 φ hφ hkφ
          · rcases hF1 m with h | h
            · rw [h] at hmW; simp at hmW
            · rw [h] at hφ'; simp at hφ'
          · rcases hF2 m with h | h
            · rw [h] at hmW; simp at hmW
            · rw [h] at hφ'; simp at hφ'
        · have hσGm' : σG.get m' = some χc :=
            ResU.CompS.get_right_of_immFree hσGc himmE hm'
          rcases hF4 m' χc hσGm' hkχ with
            rfl | ⟨φ', hφ', hkφ', hwφ'⟩ | ⟨φ', hφ', hkφ', hwφ'⟩
          · exact hF3 χc hσGm' hkχ
          · obtain ⟨s', hs', heta'⟩ := CellU.imm_eta hkφ'
            obtain ⟨ev₀, av₀, p₀, z₀, hev₀, hav₀, hcp₀, hz₀⟩ :=
              AgW.flat_imm_wit_le haρ m' s' φ'.erase φ'.wit hs'
                (hφ'.trans (congrArg some heta'))
            obtain rfl : f = p₀ :=
              ResU.FlatR.functional (by rw [hwφ']; exact hf)
                ⟨av₀, ev₀, hav₀, hev₀, ResU.CompR.comm hcp₀⟩
            rcases hF1 m with h | h
            · rw [h] at hmW; simp at hmW
            · rw [((ResU.Comp.eq_none_iff hz₀ m).mp h).1] at hsf; simp at hsf
          · obtain ⟨s', hs', heta'⟩ := CellU.imm_eta hkφ'
            obtain ⟨ev₀, av₀, p₀, z₀, hev₀, hav₀, hcp₀, hz₀⟩ :=
              AgW.flat_imm_wit_le hav m' s' φ'.erase φ'.wit hs'
                (hφ'.trans (congrArg some heta'))
            obtain rfl : f = p₀ :=
              ResU.FlatR.functional (by rw [hwφ']; exact hf)
                ⟨av₀, ev₀, hav₀, hev₀, ResU.CompR.comm hcp₀⟩
            rcases hF2 m with h | h
            · rw [h] at hmW; simp at hmW
            · rw [((ResU.Comp.eq_none_iff hz₀ m).mp h).1] at hsf; simp at hsf
  -- 6.37 with `⦇ρ_v ● ℓ ↦ own(v)⦈` defined
  have hceWaG : ResU.CompatS eW aG := ResU.Compat.of_disjoint hkey
  have hceWA : ResU.CompatS eW A := ResU.six37 hceWaG hWc.1 hA
  -- the third bullet's *"which implies … ▸◂ ℓ ↦ own(v)"*, and then `▸◂ ex(W)_●`
  have hEl : eG.get l = none := by
    rcases ResU.CompatS.disjoint_of_immFree himmE hcι l with h | h
    · exact h
    · rw [ResU.single_get_self] at h; simp at h
  have hceW : ResU.CompatS eG eW := ResU.Compat.of_disjoint (fun m => by
    by_cases hm : m = l
    · subst hm; exact Or.inl hEl
    · rcases ResU.CompatS.disjoint_of_immFree himmE hcexv m with h | h
      · exact Or.inl h
      · exact Or.inr ((ResU.Comp.eq_none_iff hfc m).mpr ⟨h, ResU.single_get_ne _ hm⟩))
  obtain ⟨E, hE⟩ := (ResU.compS_defined_iff eG eW).mpr hceW
  have hcEA : ResU.CompatS E A := ResU.Compat.of_disjoint (fun m => by
    rcases ResU.CompatS.disjoint_of_immFree himmE hcA m with h' | h'
    · rcases ResU.CompatS.disjoint_of_immFree himmW hceWA m with h'' | h''
      · exact Or.inl ((ResU.Comp.eq_none_iff hE m).mpr ⟨h', h''⟩)
      · exact Or.inr h''
    · exact Or.inr h')
  obtain ⟨σ, hσ⟩ := (ResU.compS_defined_iff E A).mpr hcEA
  -- the step-3 presupposition: `ρ′ ● ρ⁺/ℓ ▸◂ ρ_v ● ℓ ↦ own(v)`
  have hWm : ∀ m, m ≠ l → W.get m = ρv.get m := fun m hm =>
    ResU.Comp.get_of_right_none hW (ResU.single_get_ne _ hm)
  have hGW : ResU.CompatS G W := by
    intro m ψ₁ ψ₂ hg₁ hg₂
    by_cases hm : m = l
    · subst hm; rw [hGl] at hg₁; simp at hg₁
    · rw [hWm m hm] at hg₂
      by_cases hk₂ : ψ₂.kind = Kind.imm
      · obtain ⟨χ₂, hχ₂, hkχ₂, heχ₂, hwχ₂⟩ := AgW.get_imm hav hg₂ hk₂
        by_cases hk₁ : ψ₁.kind = Kind.imm
        · obtain ⟨χ₁, hχ₁, hkχ₁, heχ₁, hwχ₁⟩ := AgW.get_imm haG hg₁ hk₁
          obtain ⟨ξ, hξ⟩ := hA.1 m χ₁ χ₂ hχ₁ hχ₂
          obtain ⟨-, he₁', hw₁'⟩ := CellU.CompR.imm_left hξ hkχ₁
          obtain ⟨-, he₂', hw₂'⟩ := CellU.CompR.imm_left (CellU.CompR.comm hξ) hkχ₂
          exact CellU.compatS_iff.mpr ⟨hk₁, hk₂,
            heχ₁.symm.trans (he₁'.symm.trans (he₂'.trans heχ₂)),
            hwχ₁.symm.trans (hw₁'.symm.trans (hw₂'.trans hwχ₂))⟩
        · exfalso
          have hex₁ := ExS.get_of_ne_imm heG hg₁ hk₁
          rcases ResU.CompatS.disjoint_of_immFree himmE hcav m with h | h
          · rw [h] at hex₁; simp at hex₁
          · rw [h] at hχ₂; simp at hχ₂
      · exfalso
        have hex : exv.get m = some ψ₂ := ExS.get_of_ne_imm hexv hg₂ hk₂
        have heWm : eW.get m = some ψ₂ :=
          (ResU.Comp.get_of_right_none hfc (ResU.single_get_ne _ hm)).trans hex
        obtain ⟨χ₁, hχ₁, -, -, -⟩ := ResU.Flat.get hσG hg₁
        rcases ResU.CompatS.disjoint_of_immFree himmE hceW m with h | h
        · rcases hkey m with h' | h'
          · rw [h'] at heWm; simp at heWm
          · rw [(ResU.Comp.eq_none_iff hσGc m).mpr ⟨h, h'⟩] at hχ₁; simp at hχ₁
        · rw [h] at heWm; simp at heWm
  obtain ⟨X, hX⟩ := (ResU.compS_defined_iff G W).mpr hGW
  exact ⟨hGW, X, hX, σ, (ResU.Flat.split hX).mpr
    ⟨eG, eW, E, aG, av, A, heG, heW, hE, haG, haW, hA, hσ⟩⟩

end BoCa.Fig16

namespace BoCa.Fig16

/-!
## Lemma 6.38 · `[TR]` p. 12 · `proved`

> If (H1) ρ # ρ_v ● ℓ ↦ own(v), (H2) ρ′ # ρ⁺, (H3) @ρ ⊐ α, (H4) @ρ′ ⊐ α, (H5) ρ⁺∣own = ∅, (H6) ρ ● ℓ ↦ imm({α}, v, ρ_v) ↭ ρ′ ● ρ⁺, then (G1) ρ′ ● ρ⁺/ℓ # ρ_v ● ℓ ↦ own(v)

**Printed proof, transcribed.** By Lemma 6.29 with H3, H1 and H6, (H7) `ρ′ ● ρ⁺ = (ρ′ ● ρ⁺)/ℓ ● ℓ ↦ imm({α}, v, ρ_v)`; by H4 and H7, `ρ′ ● ρ⁺ = ρ′ ● ρ⁺/ℓ ● ℓ ↦ imm({α}, v, ρ_v)`.  For G1 it suffices that `⦇ρ′ ● ρ⁺/ℓ ● ρ_v ● ℓ ↦ own(v)⦈` is defined, which by Lemmas 6.18 and 6.20 is Kleene-equal to `ex(ρ′)_● ● ex(ρ⁺/ℓ)_● ● ex(ρ_v)_● ● ℓ ↦ own(v) ● (ag(ρ′) ○ ag(ρ⁺/ℓ) ○ ag(ρ_v))`.  The same reasoning with H2 gives `⦇ρ′ ● ρ⁺/ℓ ● ℓ ↦ imm({α}, v, ρ_v)⦈ = ex(ρ′)_● ● ex(ρ⁺/ℓ)_● ● (ag(ρ′) ○ ag(ρ⁺/ℓ) ○ ℓ ↦ imm({α}, v, ρ_v) ○ ⦇ρ_v⦈_○)`, defined; Lemma 6.35 with H1 makes `⦇ρ_v⦈` defined, Lemma 6.33 gives `⦇ρ_v⦈ = ⦇ρ_v⦈_○`, and Lemma 6.31 rewrites the last factor as `… ○ ex(ρ_v)_● ○ ag(ρ_v)`.  Lemmas 6.30 and 6.36, applied repeatedly, make `ex(ρ′)_● ● ex(ρ⁺/ℓ)_●` compatible with `ag(ρ′) ○ ag(ρ⁺/ℓ) ○ ag(ρ_v)`, with `ex(ρ_v)_●`, and with `ℓ ↦ imm({α}, v, ρ_v)`, hence with `ℓ ↦ own(v)`.  So it suffices that `ex(ρ_v)_● ● ℓ ↦ own(v) ▸◂ (ag(ρ′) ○ ag(ρ⁺/ℓ) ○ ag(ρ_v))`; by Lemma 6.37, with `⦇ρ_v ● ℓ ↦ own(v)⦈` defined by Lemma 6.35 and H1, that `ex(ρ_v)_● ● ℓ ↦ own(v) ▸◂ (ag(ρ′) ○ ag(ρ⁺/ℓ))`; and by Lemma 6.36, whose `imm` part is empty, that the two domains are disjoint.  Suppose `ℓ′` is in both.  By the definition of `ag`, `ℓ′ ∈ dom(ρ′∣imm)`, `ℓ′ ∈ dom(ρ⁺/ℓ∣imm)`, or `ℓ′ ∈ dom(⦇ρ″_v⦈_○)` for an `imm(_, _, ρ″_v)` at some `ℓ″` of `ag(ρ′) ○ ag(ρ⁺/ℓ)`.  In the first two cases H6 gives `ℓ′ ∈ ⦇ρ⦈∣imm`, contradicting H1; in the third, by the same reasoning about update `ℓ″ ∈ dom(⦇ρ⦈∣imm)`, so `ℓ′ ∈ dom(ag(ρ))`, again contradicting H1.

**Lean.** `BoCa.Fig16.ResU.six38`, alias `TR.lemma_6_38`, tag `[as printed]`.

**Note.** `Fig16.ResU.six38`, on the printed carrier, `[as printed]` — the six printed hypotheses in the printed order and the printed conclusion (`Fig16.ResU.SixThirtyEight`), with the `●`s named by their graphs (G4); stated at `BoCa.Loc`/`BoCa.Val`, as 6.29 is. **The printed proof, step for step.**  Sentences 1–2 are `Fig16.ResU.six38_steps_one_two`: 6.29 (`Fig16.ResU.six29`) with H3, H1 and H6 gives H7, and `Fig16.ResU.six38_no_borrow_in_frame` is *"by H4 and H7"* — `@ρ′ ⊐ α` puts `ℓ` outside `ρ′`, the cell H7 leaves there being `imm({α},−,−)`, whose `@` is `⊓{α} = α`. They deliver `ρ′ ● ρ⁺/ℓ # ℓ ↦ imm({α}, v, ρ_v)` **and** the composite `ρ′ ● ρ⁺ = ρ′ ● ρ⁺/ℓ ● ℓ ↦ imm(…)` the second sentence names, which is what lets the closing paragraph appeal to H6. From the third sentence on is `Fig16.ResU.SixThirtyEightResidual`, reduced by `Fig16.ResU.sixThirtyEight_of_residual` and discharged by `Fig16.ResU.sixThirtyEightResidual`: the two displays are 6.18 and 6.20 through `Fig16.ResU.Flat.split` at each composite, with `Fig16.ExW.empty_of_all_imm` and `Fig16.AgW.single_imm_inv` evaluating the borrow's two walks, 6.35 (`Fig16.ResU.Valid.split`) with H1 making `⦇ρ_v⦈` defined and 6.33 (`Fig16.ResU.six33`) with 6.31 (`Fig16.ResU.CompS.toCompR`) putting `⦇ρ_v⦈_○` back at `○`; the three bullets are 6.30 (`Fig16.ResU.CompatS.of_compR_left`) with 6.36 (`Fig16.ExS.immFree`) after 6.3 at `○` (`Fig16.ResU.CompR.assoc`) regroups the chain so that `ag(ρ′) ○ ag(ρ⁺/ℓ) ○ ag(ρ_v)` is one factor; and the reduction is 6.37 (`Fig16.ResU.six37`) on `ex(W)_● ▸◂ ag(ρ_v)` and 6.36 again. **The closing paragraph** reads its split at the flattening — `Fig16.AgW.dom_split`, the step-10 sentence at the reading its next clause *"by H6, `ℓ′ ∈ ⦇ρ⦈
-/
/-- **`[TR]` Lemma 6.38** (p. 12), proved: `ResU.sixThirtyEight_of_residual`
is the printed proof's first two sentences and
`ResU.sixThirtyEightResidual` is the rest of it.
`[as printed]` (the printed `●`s appear as their graphs — G4; the conclusion's
`ρ′ ● ρ⁺/ℓ` is asserted to exist rather than presupposed) -/
theorem ResU.six38 : ResU.SixThirtyEight :=
  ResU.sixThirtyEight_of_residual ResU.sixThirtyEightResidual

end BoCa.Fig16

alias TR.lemma_6_38 := BoCa.Fig16.ResU.six38

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {Loc Val : Type}

/-! `[about ours]` — what the Lean of Lemma 6.39 needs; the paper prints nothing here. -/
/-- **The `imm` normal form, over the same remainder.**  `[TR]` 6.39's second,
third and fourth displays: the walks of `ρ ● ℓ↦imm(α, v, ρ_v)` are cut by 6.18
and 6.20, `ag` at the singleton is `AgW.single_imm_inv`, 6.33
(`ResU.six33`) turns the `⦇ρ_v⦈_○` it returns into `⦇ρ_v⦈ = ex(ρ_v)_● ● ag(ρ_v)`
so that the exclusive half can be moved out to the `●`, and 6.31
(`ResU.compR_iff_compS`) with 6.37 (`ResU.six37`) and 6.3 do the moving:

```
⦇ρ ● ℓ↦imm(α,v,ρ_v)⦈ = ex(ρ)_● ● (ex(ρ_v)_● ○ (ℓ↦imm(α,v,ρ_v) ○ (ag(ρ) ○ ag(ρ_v))))
                     = ex(ρ)_● ● ex(ρ_v)_● ● (ℓ↦imm(α,v,ρ_v) ○ (ag(ρ) ○ ag(ρ_v)))
                     = ℓ↦imm(α,v,ρ_v) ● ex(ρ)_● ● ex(ρ_v)_● ● (ag(ρ) ○ ag(ρ_v))
```

The last line is the **silencing** step: `ℓ ∉ dom(K)` — carried in as `hnone`,
where `ResU.flat_own_normal` and `ResU.compatS_silences` produce it — gives
`ℓ ∉ dom(ag(ρ) ○ ag(ρ_v))` and hence `ℓ↦imm(α,v,ρ_v) ▸◂ ag(ρ) ○ ag(ρ_v)`.
`[about ours: `[TR]` 6.39's second through fourth displays, as a graph — G4]` -/
theorem ResU.flat_imm_normal {l : Loc} {s : LSet} {v : Val}
    {ρ ρv e₁ e₂ EX a₁ a₂ AG K iw σ' : ResU Loc Val} {hstr : ρv.InStratum s.join}
    (hiw : ResU.CompS ρ (ResU.single l (CellU.immOf s v ρv hstr)) iw)
    (hflat : ResU.Flat iw σ')
    (he₁ : ExS ρ e₁) (he₂ : ExS ρv e₂) (hEX : ResU.CompS e₁ e₂ EX)
    (ha₁ : AgW ρ a₁) (ha₂ : AgW ρv a₂) (hAG : ResU.CompR a₁ a₂ AG)
    (hK : ResU.CompS EX AG K) (hnone : K.get l = none) (hvv : ResU.Valid ρv) :
    ResU.CompS (ResU.single l (CellU.immOf s v ρv hstr)) K σ' := by
  classical
  obtain ⟨E₁, E₂, E, A₁, A₂, A, hE₁, hE₂, hEc, hA₁, hA₂, hAc, hσ'⟩ :=
    (ResU.Flat.split hiw).mp hflat
  rw [ExS.functional hE₁ he₁] at hEc
  rw [ExS.functional hE₂ (ExW.empty_of_all_imm (fun m ψ hg => by
      obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hg
      exact CellU.kind_immOf _ _ _ _))] at hEc
  rw [ResU.CompS.functional hEc (ResU.comp_empty_right e₁)] at hσ'
  rw [AgW.functional hA₁ ha₁] at hAc
  obtain ⟨ev, av, p, hev, hav, hp, hpA⟩ := AgW.single_imm_inv hA₂
  rw [AgW.functional hav ha₂] at hp
  -- 6.10 gave `✓ρ_v`; 6.33 identifies `⦇ρ_v⦈_○` with `⦇ρ_v⦈`.
  obtain ⟨τ, hτ⟩ := hvv
  obtain ⟨aτ, eτ, haτ, heτ, hcτ⟩ := ResU.six33 hτ
  rw [AgW.functional haτ ha₂, ExR.functional heτ hev] at hcτ
  rw [ResU.CompR.functional hp (ResU.CompR.comm hcτ)] at hpA
  obtain ⟨eF, aF, heF, haF, hcF⟩ := hτ
  rw [ExS.functional heF he₂, AgW.functional haF ha₂] at hcF
  -- `⦇ρ_v⦈ = ex(ρ_v)_● ● ag(ρ_v)`, read at `○` by 6.31.
  have hτR : ResU.CompR e₂ a₂ τ := ResU.CompS.toCompR hcF
  -- Rearrange `ag(ρ) ○ (ℓ↦imm ○ (ex(ρ_v)_○ ○ ag(ρ_v)))` to
  -- `ex(ρ_v)_● ○ (ℓ↦imm ○ (ag(ρ) ○ ag(ρ_v)))`.
  obtain ⟨q, hq₁, hq₂⟩ :=
    (ResU.CompR.assoc a₁ (ResU.single l (CellU.immOf s v ρv hstr)) τ A).mp
      ⟨A₂, hpA, hAc⟩
  obtain ⟨S₁, S₂, hS₁, hS₂, hS⟩ :=
    (ResU.CompR.exchange₄ e₂ a₂ (ResU.single l (CellU.immOf s v ρv hstr)) a₁ A).mp
      ⟨τ, q, hτR, ResU.CompR.comm hq₁, ResU.CompR.comm hq₂⟩
  rw [ResU.CompR.functional (ResU.CompR.comm hS₂) hAG] at hS
  obtain ⟨M, hM₁, hM₂⟩ :=
    (ResU.CompR.assoc e₂ (ResU.single l (CellU.immOf s v ρv hstr)) AG A).mpr
      ⟨S₁, hS₁, hS⟩
  -- The two silencings, both out of `ℓ ∉ dom(K)`.
  have hEXl : EX.get l = none := ((ResU.Comp.eq_none_iff hK l).mp hnone).1
  have he₂l : e₂.get l = none := ((ResU.Comp.eq_none_iff hEX l).mp hEXl).2
  have hAGl : AG.get l = none := ((ResU.Comp.eq_none_iff hK l).mp hnone).2
  have hcsAG : ResU.CompatS (ResU.single l (CellU.immOf s v ρv hstr)) AG :=
    ResU.Compat.of_disjoint (fun l' => by
      by_cases hl : l' = l
      · exact Or.inr (hl ▸ hAGl)
      · exact Or.inl (ResU.single_get_ne _ hl))
  have hcse₂ : ResU.CompatS e₂ (ResU.single l (CellU.immOf s v ρv hstr)) :=
    ResU.Compat.of_disjoint (fun l' => by
      by_cases hl : l' = l
      · exact Or.inl (hl ▸ he₂l)
      · exact Or.inr (ResU.single_get_ne _ hl))
  have hcse₂AG : ResU.CompatS e₂ AG :=
    (ResU.CompatS.of_compS_left_immFree
      (ResU.ImmFree.compS hEX (ExS.immFree he₁) (ExS.immFree he₂)) hEX hK.1).2
  -- 6.37 lifts the two to `ex(ρ_v)_● ▸◂ (ℓ↦imm ○ (ag(ρ) ○ ag(ρ_v)))`.
  have hcsM : ResU.CompatS e₂ M := ResU.six37 hcse₂ hcse₂AG hM₁
  have hMS : ResU.CompS e₂ M A := (ResU.compR_iff_compS hcsM A).mp hM₂
  obtain ⟨z, hz₁, hz₂⟩ := (ResU.CompS.assoc e₁ e₂ M σ').mp ⟨A, hMS, hσ'⟩
  rw [ResU.CompS.functional hz₁ hEX] at hz₂
  have hMS' : ResU.CompS (ResU.single l (CellU.immOf s v ρv hstr)) AG M :=
    (ResU.compR_iff_compS hcsAG M).mp hM₁
  obtain ⟨u, hu₁, hu₂⟩ :=
    (ResU.CompS.assoc EX (ResU.single l (CellU.immOf s v ρv hstr)) AG σ').mp
      ⟨M, hMS', hz₂⟩
  obtain ⟨K', hK', hK'σ⟩ :=
    (ResU.CompS.assoc (ResU.single l (CellU.immOf s v ρv hstr)) EX AG σ').mpr
      ⟨u, ResU.CompS.comm hu₁, hu₂⟩
  rwa [ResU.CompS.functional hK' hK] at hK'σ

/-!
## Lemma 6.39 · `[TR]` p. 13 · `proved`

> If (H1) ρ # ℓ ↦ own(v) ● ρ_v, (H2) ρ′ # ℓ ↦ own(v) ● ρ_v, (H3) ρ ● ℓ ↦ imm(α, v, ρ_v) ↭ ρ′ ● ℓ ↦ imm(α, v, ρ_v) then ρ ● ℓ ↦ own(v) ● ρ_v ↭ ρ′ ● ℓ ↦ own(v) ● ρ_v

**Printed proof, transcribed.** By H1 and H2, `ρ_of = ⦇ρ ● ℓ ↦ own(v) ● ρ_v⦈` and `ρ′_of` are defined; the goals are (G1) `dom(ρ_of∣imm,mut) = dom(ρ′_of∣imm,mut)` and (G2) `ρ_of(ℓ) ∼ ρ′_of(ℓ)` on that domain.  By Lemmas 6.18 and 6.20, `ρ_of = ℓ ↦ own(v) ● ex(ρ)_● ● ex(ρ_v)_● ● (ag(ρ) ○ ag(ρ_v))`, and likewise `ρ′_of`.  By H3, `ρ_if = ⦇ρ ● ℓ ↦ imm(α, v, ρ_v)⦈` and `ρ′_if` are defined with (H4) the same `imm`/`mut` domain, and `ρ_if = ex(ρ)_● ● (ℓ ↦ imm(α, v, ρ_v) ○ ag(ρ) ○ ⦇ρ_v⦈_○)`.  By Lemma 6.10 with H1, `✓ρ_v`; then by Lemma 6.35, `⦇ρ_v⦈ = ⦇ρ_v⦈_○`; rewriting, unfolding `⦇−⦈` and using Lemma 6.31, `ρ_if = ex(ρ)_● ● (ex(ρ_v)_● ○ (ℓ ↦ imm(α, v, ρ_v) ○ (ag(ρ) ○ ag(ρ_v))))`.  `ex(ρ_v)_●` is compatible with `ag(ρ_v)` (from `✓ρ_v`), with `ag(ρ)` and `ag(ρ′)` (from the forms of `ρ_of`, `ρ′_of` with Lemmas 6.30 and 6.36), and with `ℓ ↦ imm(α, v, ρ_v)` (Lemma 6.36); with Lemmas 6.37 and 6.31, `ρ_if = ex(ρ)_● ● ex(ρ_v)_● ● (ℓ ↦ imm(α, v, ρ_v) ○ (ag(ρ) ○ ag(ρ_v)))`.  From `ρ_of`, `ℓ ↦ own(v) ▸◂ ag(ρ) ○ ag(ρ_v)`, so `ℓ ∉ dom(ag(ρ) ○ ag(ρ_v))` (likewise primed), so `ℓ ↦ imm(α, v, ρ_v)` is compatible with it and by Lemma 6.31 `ρ_if = ℓ ↦ imm(α, v, ρ_v) ● ex(ρ)_● ● ex(ρ_v)_● ● (ag(ρ) ○ ag(ρ_v))`, likewise `ρ′_if`.  So `ρ_of` and `ρ_if` differ only by `ℓ ↦ own(v)` against `ℓ ↦ imm(α, v, ρ_v)`, with `ℓ` outside both `ag` parts, and G1 and G2 follow from H4: `dom(ρ_of)∣imm,mut = dom(ρ′_of)∣imm,mut = dom(ρ_if∣imm,mut)/ℓ = dom(ρ′_if∣imm,mut)/ℓ`, `ρ_of∣imm,mut = ρ_if∣imm,mut/ℓ`, `ρ′_of∣imm,mut = ρ′_if∣imm,mut/ℓ`.

**Lean.** `BoCa.Fig16.ResU.six39`, alias `TR.lemma_6_39`, tag `[as printed]`.

**Note.** `Fig16.ResU.six39`, on the printed carrier, `[as printed]`, with the printed `●`s named by their graphs (G4). The printed proof is transcribed in full: `Fig16.ResU.flat_own_normal` is its first display (6.18 and 6.20 cut the walks, `Fig16.ExW.single_own` and `Fig16.AgW.single_own` evaluate them at `ℓ ↦ own(v)`, 6.3 and 6.2 move the cell to the front) and `Fig16.ResU.flat_imm_normal` is its second through fourth (`Fig16.AgW.single_imm_inv` for `ag` at the singleton, 6.33 for `⦇ρ_v⦈_○ = ⦇ρ_v⦈`, then 6.31, 6.37 and 6.3 to move `ex(ρ_v)_●` out to the `●`), both over **one** remainder `K = ex(ρ)_● ● ex(ρ_v)_● ● (ag(ρ) ○ ag(ρ_v))`. The silencing step *"therefore `ℓ ∉ dom(ag(ρ) ○ ag(ρ_v))`"* is 6.41 (`Fig16.ResU.compatS_single_own`); the closing paragraph is `Fig16.ResU.compS_single_get_ne` and `Fig16.ResU.compS_single_get_self` off the two normal forms, and `↭` transfers through `Fig16.ResU.upd_iff_sim`. `↭` is `Fig16.ResU.UpdV`: the print reads H3 as carrying the definedness of `ρ_if` and `ρ′_if`, and the conclusion's comes from H1 and H2
-/
/-- **`[TR]` Lemma 6.39** (p. 13): if `ρ # ℓ↦own(v) ● ρ_v` and
`ρ′ # ℓ↦own(v) ● ρ_v` and `ρ ● ℓ↦imm(α, v, ρ_v) ↭ ρ′ ● ℓ↦imm(α, v, ρ_v)`, then
`ρ ● ℓ↦own(v) ● ρ_v ↭ ρ′ ● ℓ↦own(v) ● ρ_v`.

The print's closing paragraph — *"now the only difference between `ρ_of` and
`ρ_if`, as well as `ρ′_of` and `ρ′_if`, is `ℓ↦own(v)` vs `ℓ↦imm(α, v, ρ_v)`, and
we additionally know `ℓ ∉ dom(ag(ρ) ○ ag(ρ_v))`"* — is
`ResU.compS_single_get_ne` and `ResU.compS_single_get_self` read off the two
normal forms over the one remainder `K`.  The two printed equations
`ρ_of|imm,mut = ρ_if|imm,mut/ℓ` are then the `own` cell's absence from
`−|imm,mut`, and `↭` transfers because `ResU.upd_iff_sim` puts both sides in the
printed `dom + ∼` form.

`↭` is `ResU.UpdV`, not `ResU.Upd`: the print reads H3 as carrying the
definedness of `ρ_if` and `ρ′_if` (*"By H3, we also have … are defined"*), which
is exactly `UpdV`'s two extra conjuncts, and the conclusion's definedness comes
from H1 and H2.
`[as printed]` (the printed `●`s appear as their graphs — G4) -/
theorem ResU.six39 {l : Loc} {s : LSet} {v : Val}
    {ρ ρ' ρv ov iw iw' : ResU Loc Val} {hstr : ρv.InStratum s.join}
    (hov : ResU.CompS (ResU.single l (CellU.ownOf v)) ρv ov)
    (h1 : ResU.Hash ρ ov) (h2 : ResU.Hash ρ' ov)
    (hi : ResU.CompS ρ (ResU.single l (CellU.immOf s v ρv hstr)) iw)
    (hi' : ResU.CompS ρ' (ResU.single l (CellU.immOf s v ρv hstr)) iw')
    (h3 : ResU.UpdV iw iw') :
    ∃ w w', ResU.CompS ρ ov w ∧ ResU.CompS ρ' ov w' ∧ ResU.UpdV w w' := by
  classical
  obtain ⟨-, w, hw, hvw⟩ := h1
  obtain ⟨-, w', hw', hvw'⟩ := h2
  obtain ⟨σof, hfof⟩ := hvw
  obtain ⟨σof', hfof'⟩ := hvw'
  obtain ⟨e₁, e₂, EX, a₁, a₂, AG, K, he₁, he₂, hEX, ha₁, ha₂, hAG, hK, hKσ⟩ :=
    ResU.flat_own_normal hov hw hfof
  obtain ⟨e₁', e₂', EX', a₁', a₂', AG', K', he₁', he₂', hEX', ha₁', ha₂', hAG',
    hK', hK'σ⟩ := ResU.flat_own_normal hov hw' hfof'
  rw [ExS.functional he₂' he₂] at hEX'
  rw [AgW.functional ha₂' ha₂] at hAG'
  -- The silencing step, on each side: `ℓ ↦ own(v) ▸◂ K` gives `ℓ ∉ dom(K)`.
  have hnone : K.get l = none := ResU.compatS_single_own hKσ.1
  have hnone' : K'.get l = none := ResU.compatS_single_own hK'σ.1
  -- *"By lemma 6.10 with H1, `✓ρ_v`."*
  have hvv : ResU.Valid ρv :=
    (ResU.Valid.split hov (ResU.Valid.split hw ⟨σof, hfof⟩).2).2
  obtain ⟨σif, hfif⟩ := h3.2.1
  obtain ⟨σif', hfif'⟩ := h3.2.2
  have hiσ : ResU.CompS (ResU.single l (CellU.immOf s v ρv hstr)) K σif :=
    ResU.flat_imm_normal hi hfif he₁ he₂ hEX ha₁ ha₂ hAG hK hnone hvv
  have hiσ' : ResU.CompS (ResU.single l (CellU.immOf s v ρv hstr)) K' σif' :=
    ResU.flat_imm_normal hi' hfif' he₁' he₂ hEX' ha₁' ha₂ hAG' hK' hnone' hvv
  -- Off `ℓ`, the `own` flattening and the `imm` flattening are the same resource.
  have hoff : ∀ x : Loc, x ≠ l → σof.get x = σif.get x := fun x hx =>
    (ResU.compS_single_get_ne hKσ hx).trans (ResU.compS_single_get_ne hiσ hx).symm
  have hoff' : ∀ x : Loc, x ≠ l → σof'.get x = σif'.get x := fun x hx =>
    (ResU.compS_single_get_ne hK'σ hx).trans (ResU.compS_single_get_ne hiσ' hx).symm
  -- At `ℓ` the `own` flattening carries `own(v)`, which `−|imm,mut` drops.
  have hatl : ∀ ψ : CellU Loc Val, σof.borrowPart.get l ≠ some ψ := by
    intro ψ hb
    obtain ⟨hg, hk⟩ := ResU.borrowPart_eq_some.mp hb
    rw [ResU.compS_single_get_self hKσ hnone] at hg
    exact hk (by rw [← Option.some.inj hg]; exact CellU.kind_ownOf v)
  have hatl' : ∀ ψ : CellU Loc Val, σof'.borrowPart.get l ≠ some ψ := by
    intro ψ hb
    obtain ⟨hg, hk⟩ := ResU.borrowPart_eq_some.mp hb
    rw [ResU.compS_single_get_self hK'σ hnone'] at hg
    exact hk (by rw [← Option.some.inj hg]; exact CellU.kind_ownOf v)
  have hsim : ResU.SimForm σif σif' := (ResU.upd_iff_sim hfif hfif').mp h3.1
  refine ⟨w, w', hw, hw', (ResU.upd_iff_sim hfof hfof').mpr ⟨fun x => ?_, fun x ψ hb => ?_⟩,
    ⟨σof, hfof⟩, ⟨σof', hfof'⟩⟩
  · by_cases hx : x = l
    · subst hx
      exact ⟨fun ⟨ψ, hψ⟩ => absurd hψ (hatl ψ), fun ⟨ψ, hψ⟩ => absurd hψ (hatl' ψ)⟩
    · have hb : ∀ ζ : CellU Loc Val, σof.borrowPart.get x = some ζ ↔
          σif.borrowPart.get x = some ζ := fun ζ => by
        rw [ResU.borrowPart_eq_some, ResU.borrowPart_eq_some, hoff x hx]
      have hb' : ∀ ζ : CellU Loc Val, σof'.borrowPart.get x = some ζ ↔
          σif'.borrowPart.get x = some ζ := fun ζ => by
        rw [ResU.borrowPart_eq_some, ResU.borrowPart_eq_some, hoff' x hx]
      exact ⟨fun ⟨ζ, hζ⟩ => ((hsim.1 x).mp ⟨ζ, (hb ζ).mp hζ⟩).imp (fun ζ' h => (hb' ζ').mpr h),
        fun ⟨ζ, hζ⟩ => ((hsim.1 x).mpr ⟨ζ, (hb' ζ).mp hζ⟩).imp (fun ζ' h => (hb ζ').mpr h)⟩
  · by_cases hx : x = l
    · exact absurd hb (hx ▸ hatl ψ)
    · have hbi : σif.borrowPart.get x = some ψ := by
        rw [ResU.borrowPart_eq_some, ← hoff x hx, ← ResU.borrowPart_eq_some]; exact hb
      obtain ⟨ψ', hψ', hs⟩ := hsim.2 x ψ hbi
      exact ⟨ψ', (hoff' x hx).trans hψ', hs⟩

end BoCa.Fig16

alias TR.lemma_6_39 := BoCa.Fig16.ResU.six39

/-!
## Lemma 6.40 · `[TR]` p. 15 · `variant`

> ℓ ↦ own(v₁) # ρ if and only if ℓ ↦ own(v₂) # ρ

**Printed proof, transcribed.** By the definition of `#`, `ℓ ∉ ⦇ρ⦈`, so the condition follows immediately.

**Untranscribed on the printed carrier.**  This repository carries no declaration for it and no `TR.lemma_6_40`.

**Lean.** None in this repository.

**Note.** No single declaration states 6.40's `#`-iff
-/

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.43 · `[TR]` p. 15 · `proved`

> ℓ ↦ imm(α ∪ β, v, ρ′) = ℓ ↦ imm(α, v, ρ′) ● ℓ ↦ imm(β, v, ρ′)

**Printed proof, transcribed.** By definition.

**Lean.** `BoCa.Fig16.ResU.compS_single_imm`, alias `TR.lemma_6_43`, tag `[as printed]`.

**Note.** `Fig16.ResU.compS_single_imm`, on the printed carrier, at `ℓ ↦ −`. The graph carries definedness and value together, which is the print's equation between partial expressions.
-/
/-- **`[TR]` Lemma 6.43** (p. 15):
`ℓ ↦ imm(ᾱ ∪ β̄, v, ρ′) = ℓ ↦ imm(ᾱ, v, ρ′) ● ℓ ↦ imm(β̄, v, ρ′)`.  As a graph:
definedness and value together.  `[as printed]` -/
theorem ResU.compS_single_imm (l : Loc) (s t : LSet) (v : Val) (ρ' : ResU Loc Val)
    (h : ρ'.InStratum s.join) (h' : ρ'.InStratum t.join)
    (h'' : ρ'.InStratum (s ∪ t).join) :
    ResU.CompS (ResU.single l (CellU.immOf s v ρ' h))
      (ResU.single l (CellU.immOf t v ρ' h'))
      (ResU.single l (CellU.immOf (s ∪ t) v ρ' h'')) := by
  classical
  constructor
  · intro l' ψ₁ ψ₂ e₁ e₂
    obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some e₁
    obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e₂
    exact ⟨s, t, v, ρ', h, h', rfl, rfl⟩
  · intro l'
    by_cases e : l' = l
    · subst e
      rw [ResU.single_get_self, ResU.single_get_self, ResU.single_get_self]
      exact ⟨_, rfl, ⟨s, t, v, ρ', h, h', h'', rfl, rfl, rfl⟩⟩
    · rw [ResU.single_get_ne _ e, ResU.single_get_ne _ e, ResU.single_get_ne _ e]
      rfl

end BoCa.Fig16

alias TR.lemma_6_43 := BoCa.Fig16.ResU.compS_single_imm

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.44 · `[TR]` p. 16 · `proved`

> If ℓ ↦ imm(α, v₁, ρ′₁) ▸◂ ℓ ↦ imm(β, v₂, ρ′₂), then v₁ = v₂ and ρ′₁ = ρ′₂.

**Printed proof, transcribed.** By definition.

**Lean.** `BoCa.Fig16.ResU.compatS_single_imm_inv`, alias `TR.lemma_6_44`, tag `[as printed]`.

**Note.** `Fig16.ResU.compatS_single_imm_inv`, on the printed carrier.
-/
/-- **`[TR]` Lemma 6.44** (p. 16): if
`ℓ ↦ imm(ᾱ, v₁, ρ′₁) ▶◀ ℓ ↦ imm(β̄, v₂, ρ′₂)` then `v₁ = v₂` and `ρ′₁ = ρ′₂`.
The witnesses are compared by plain equality in `Res`, which is what the
stratified constructors buy.  `[as printed]` -/
theorem ResU.compatS_single_imm_inv {l : Loc} {s t : LSet} {v₁ v₂ : Val}
    {ρ₁ ρ₂ : ResU Loc Val} {h₁ : ρ₁.InStratum s.join} {h₂ : ρ₂.InStratum t.join}
    (h : ResU.CompatS (ResU.single l (CellU.immOf s v₁ ρ₁ h₁))
      (ResU.single l (CellU.immOf t v₂ ρ₂ h₂))) : v₁ = v₂ ∧ ρ₁ = ρ₂ := by
  obtain ⟨s₁, s₂, v, ρ, k₁, k₂, e₁, e₂⟩ :=
    h l _ _ (ResU.single_get_self _ _) (ResU.single_get_self _ _)
  obtain ⟨-, hv₁, hρ₁⟩ := CellU.immOf_inj e₁
  obtain ⟨-, hv₂, hρ₂⟩ := CellU.immOf_inj e₂
  exact ⟨hv₁.trans hv₂.symm, hρ₁.trans hρ₂.symm⟩

end BoCa.Fig16

alias TR.lemma_6_44 := BoCa.Fig16.ResU.compatS_single_imm_inv

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.45 · `[TR]` p. 16 · `proved`

> @(ρ₁ ● ρ₂) ⊐ α if and only if @ρ₁ ⊐ α and ρ₂ ⊐ α.

**Printed proof, transcribed.** In either direction: if `ℓ ∈ dom(ρ₁) ∩ dom(ρ₂)` then `ρ₁(ℓ) = imm(α, v, ρ)` and `ρ₂(ℓ) = imm(β, v, ρ)`, and `α ∪ β ⊐ α` iff `α ⊐ α` and `β ⊐ α`.

**Lean.** `BoCa.Fig16.ResU.atLife_comp_sqsupset`, alias `TR.lemma_6_45`, tag `[as printed]`.

**Note.** `Fig16.ResU.atLife_comp_sqsupset`, on the printed carrier, as one iff. `@` is the **graph**, so the three values are hypotheses rather than applications of a function, which is what keeps the statement free of `Classical.choice`. (The print drops the `@` on `ρ₂` at 600 dpi;
-/
/-- **`[TR]` Lemma 6.45** (p. 16): `@(ρ₁ ● ρ₂) ⊐ α` if and only if `@ρ₁ ⊐ α`
and `@ρ₂ ⊐ α`.  `@` is the graph, so the three values are hypotheses rather
than applications of a function — which is what keeps the statement free of
`Classical.choice`.

The print writes the second conjunct `ρ₂ ⊐ α`, dropping the `@` (600 dpi).
`⊐` relates lifetimes, so the printed form does not type; its own proof treats
the two operands symmetrically and the `@` is read.  `[as printed]` -/
theorem ResU.atLife_comp_sqsupset {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {a a₁ a₂ α : Life} (ha : ρ.AtLife a) (ha₁ : ρ₁.AtLife a₁) (ha₂ : ρ₂.AtLife a₂) :
    a ⊐ α ↔ (a₁ ⊐ α ∧ a₂ ⊐ α) := by
  have h₁ : a ≤ a₁ := by
    refine ha₁.2 a (fun l ψ e => ?_)
    rcases h.get l with ⟨e₁, -, -⟩ | ⟨χ, e₁, -, e'⟩ | ⟨χ, e₁, -, -⟩ |
        ⟨χ₁, χ₂, χ, e₁, -, e', hC⟩
    · rw [e₁] at e; exact absurd e (by simp)
    · rw [e₁] at e; cases Option.some.inj e; exact ha.1 l ψ e'
    · rw [e₁] at e; exact absurd e (by simp)
    · rw [e₁] at e
      cases Option.some.inj e
      refine le_trans (ha.1 l χ e') ?_
      rw [hC.at]; exact inf_le_left
  have h₂ : a ≤ a₂ := by
    refine ha₂.2 a (fun l ψ e => ?_)
    rcases h.get l with ⟨-, e₂, -⟩ | ⟨χ, -, e₂, -⟩ | ⟨χ, -, e₂, e'⟩ |
        ⟨χ₁, χ₂, χ, -, e₂, e', hC⟩
    · rw [e₂] at e; exact absurd e (by simp)
    · rw [e₂] at e; exact absurd e (by simp)
    · rw [e₂] at e; cases Option.some.inj e; exact ha.1 l ψ e'
    · rw [e₂] at e
      cases Option.some.inj e
      refine le_trans (ha.1 l χ e') ?_
      rw [hC.at]; exact inf_le_right
  have h₃ : a₁ ⊓ a₂ ≤ a := by
    refine ha.2 (a₁ ⊓ a₂) (fun l ψ e => ?_)
    rcases h.get l with ⟨-, -, e'⟩ | ⟨χ, e₁, -, e'⟩ | ⟨χ, -, e₂, e'⟩ |
        ⟨χ₁, χ₂, χ, e₁, e₂, e', hC⟩
    · rw [e'] at e; exact absurd e (by simp)
    · rw [e'] at e; cases Option.some.inj e
      exact le_trans inf_le_left (ha₁.1 l _ e₁)
    · rw [e'] at e; cases Option.some.inj e
      exact le_trans inf_le_right (ha₂.1 l _ e₂)
    · rw [e'] at e; cases Option.some.inj e
      rw [hC.at]
      exact le_inf
        (le_trans inf_le_left (ha₁.1 l χ₁ e₁))
        (le_trans inf_le_right (ha₂.1 l χ₂ e₂))
  constructor
  · intro hlt
    exact ⟨lt_of_lt_of_le hlt h₁, lt_of_lt_of_le hlt h₂⟩
  · intro hlt
    exact lt_of_lt_of_le (lt_inf_iff.mpr ⟨hlt.1, hlt.2⟩) h₃

end BoCa.Fig16

alias TR.lemma_6_45 := BoCa.Fig16.ResU.atLife_comp_sqsupset

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
## Lemma 6.46 · `[TR]` p. 16 · `proved`

> ρ₁ # ρ₂ ● ρ₃ if and only if ρ₁ ● ρ₂ # ρ₃.

**Printed proof, transcribed.** By unfolding `#` and Lemma 6.3.

**Lean.** `BoCa.Fig16.BoLo.hash_shift`, alias `TR.lemma_6_46`, tag `[as printed]`.

**Note.** `Fig16.BoLo.hash_shift`, on the printed carrier — the printed "if and only if", both composites named by their graphs (G4), and the print's own proof ("by unfolding `#` and lemma 6.3") is `Fig16.ResU.CompS.assoc` and nothing else.
-/
/-- **`[TR]` Lemma 6.46** (p. 16): `ρ₁ # ρ₂ ● ρ₃` if and only if
`ρ₁ ● ρ₂ # ρ₃`.  Both sides name a partial composite, so each is written as its
graph (G4); the print's own proof is "by unfolding `#` and lemma 6.3", and that
is `ResU.CompS.assoc`, whose two sides are exactly the two composites.
`[as printed]` (the printed composites appear as their graphs — G4) -/
theorem hash_shift (ρ₁ ρ₂ ρ₃ : WRes) :
    (∃ x, ResU.CompS ρ₂ ρ₃ x ∧ ResU.Hash ρ₁ x) ↔
    (∃ y, ResU.CompS ρ₁ ρ₂ y ∧ ResU.Hash y ρ₃) := by
  constructor
  · rintro ⟨x, hx, -, w, hw, hv⟩
    obtain ⟨y, hy, hyw⟩ := (ResU.CompS.assoc ρ₁ ρ₂ ρ₃ w).mp ⟨x, hx, hw⟩
    exact ⟨y, hy, hyw.1, w, hyw, hv⟩
  · rintro ⟨y, hy, -, w, hw, hv⟩
    obtain ⟨x, hx, hxw⟩ := (ResU.CompS.assoc ρ₁ ρ₂ ρ₃ w).mpr ⟨y, hy, hw⟩
    exact ⟨x, hx, hxw.1, w, hxw, hv⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_46 := BoCa.Fig16.BoLo.hash_shift

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.47 · `[TR]` p. 16 · `proved`

> ρ ↭ ρ

**Printed proof, transcribed.** By definition.

**Lean.** `BoCa.Fig16.ResU.Upd.refl`, alias `TR.lemma_6_47`, tag `[as printed]`; `BoCa.Fig16.ResU.UpdV.refl`, tag `[as printed]`.

**Note.** `Fig16.ResU.Upd.refl`, on the printed carrier at `[CONF]` Fig. 18b's unguarded `↭` — literally the printed statement, no hypothesis, and the print's proof is "by definition". `Fig16.ResU.UpdV.refl` is the same at `[TR]` p. 5's guarded reading, where `✓ρ` is part of the relation and so is a hypothesis (`docs/adjudications.md` D3).
-/
/-- **`[TR]` Lemma 6.47** — `ρ ↭ ρ` (p. 16, proved there "by definition"), at
`[CONF]` Fig. 18b's unguarded `↭`: literally the printed statement, with no
hypothesis.  `[as printed]` -/
theorem ResU.Upd.refl (ρ : ResU Loc Val) : ρ.Upd ρ :=
  ⟨fun _ _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩

end BoCa.Fig16

alias TR.lemma_6_47 := BoCa.Fig16.ResU.Upd.refl

namespace BoCa.Fig16
variable {Loc Val : Type}

/-! Lemma 6.47, continued. -/
/-- **`[TR]` Lemma 6.47** at `[TR]` p. 5's guarded `↭`.  `ResU.Valid ρ` is that
row's own `✓ρ₁ ∧ ✓ρ₂` at `ρ₁ = ρ₂ = ρ`, not a condition added here.
`[as printed]` -/
theorem ResU.UpdV.refl {ρ : ResU Loc Val} (h : ρ.Valid) : ρ.UpdV ρ :=
  ⟨ResU.Upd.refl ρ, h, h⟩

/-!
### Row 5.67's theorem `BoCa.Fig16.ResU.flat_eq_ag_at`, ahead of its file

A remark on a printed definition of `[TR]` §5; its proof uses results of §6, and the Lean of Lemmas 6.48 and 6.59 in this file needs it, so it is declared here.  The row is recorded in `Paper/S5_Model/Remarks.lean`.
-/
/-- **Where `ag(ρ)` carries a cell that is not `imm`, `⦇ρ⦈` carries that very
cell.**  `⦇ρ⦈ ≜ ex(ρ)● ● ag(ρ)` and `▶◀` holds only between two `imm` cells, so
the exclusive walk is silent there and the outer `●` returns the aliasable
walk's cell unchanged (`ResU.ex_none_of_ag_ne_imm` says the first half on its
own, further down).
`[about ours: `⦇ρ⦈` at a non-`imm` cell of `ag(ρ)`]` -/
theorem ResU.flat_eq_ag_at {ρ e a σ : ResU Loc Val} (_he : ExS ρ e)
    (hc : ResU.CompS e a σ) {n : Loc} {ψ : CellU Loc Val} (hg : a.get n = some ψ)
    (hk : ψ.kind ≠ Kind.imm) : σ.get n = some ψ := by
  have hen : e.get n = none := by
    cases f : e.get n with
    | none => rfl
    | some ξ => exact absurd (CellU.CompatS.kinds (hc.1 n ξ ψ f hg)).2 hk
  rcases ResU.Comp.get hc n with ⟨-, f₂, -⟩ | ⟨ξ, f₁, -, -⟩ | ⟨ξ, -, f₂, f⟩ |
      ⟨ξ₁, ξ₂, ξ, f₁, -, -, -⟩
  · rw [hg] at f₂; exact absurd f₂ (by simp)
  · rw [hen] at f₁; exact absurd f₁ (by simp)
  · rw [hg] at f₂; rw [f, Option.some.inj f₂]
  · rw [hen] at f₁; exact absurd f₁ (by simp)

/-! `[about ours]` — what the Lean of Lemma 6.48 needs; the paper prints nothing here. -/
/-- **…and therefore the raised subtree comes across whole.**  A cell of
`ag(ρ₂)` that is not `imm` sits beneath an `imm` cell of `ag(ρ₂)`
(`AgW.nonimm_beneath_imm`); that ancestor's witness `χ` is pinned by `↭`, so
`⦇χ⦈_○` is a `○`-factor of `ag(ρ₃)` as well, and it carries at `n` a cell with
the **same value and the same witness**.

Those are precisely the two components `↭`'s second clause wildcards, which is
why `[TR]` 6.48's proof runs this step alongside clause (2) rather than instead
of it.
`[about ours: `[TR]` 6.48's proof, *"by the definition of `ag`, there must exist
`ℓ′, ρ′` …, which implies `ag(ρ₃)(ℓ) = mut(β, v, ρᵢ, Q̂)`"*]` -/
theorem ResU.upd_ag_nonimm_transfer {ρ₂ ρ₃ e₂ a₂ σ₂ e₃ a₃ σ₃ : ResU Loc Val}
    (h : ResU.Upd ρ₂ ρ₃)
    (he₂ : ExS ρ₂ e₂) (ha₂ : AgW ρ₂ a₂) (hc₂ : ResU.CompS e₂ a₂ σ₂)
    (he₃ : ExS ρ₃ e₃) (ha₃ : AgW ρ₃ a₃) (hc₃ : ResU.CompS e₃ a₃ σ₃)
    {n : Loc} {φ : CellU Loc Val} (hg : a₂.get n = some φ)
    (hk : φ.kind ≠ Kind.imm) :
    ∃ (χ ev av p z : ResU Loc Val) (ξ : CellU Loc Val),
      ExR χ ev ∧ AgW χ av ∧ ResU.CompR ev av p ∧ ResU.CompR p z a₃ ∧
      p.get n = some ξ ∧ ξ.kind ≠ Kind.imm ∧
      ξ.wit = φ.wit ∧ ξ.erase = φ.erase := by
  obtain ⟨m, s, u, χ, hh, ev, av, p, ξ, hm, hev, hav, hp, hpn, hξk, hξw, hξe⟩ :=
    AgW.nonimm_beneath_imm ha₂ n φ hg hk
  obtain ⟨ev', av', p', z, hev', hav', hp', hz⟩ :=
    ResU.upd_ag_imm_wit_factor h he₂ ha₂ hc₂ he₃ ha₃ hc₃ hm
  rw [ExR.functional hev' hev, AgW.functional hav' hav] at hp'
  rw [ResU.CompR.functional hp' hp] at hz
  exact ⟨χ, ev, av, p, z, ξ, hev, hav, hp, hz, hpn, hξk, hξw, hξe⟩

/-- **`[TR]` 6.48's ancestor step, at its printed conclusion.**  p. 16 draws
`ag(ρ₃)(ℓ) = mut(β, v, ρᵢ, Q̂)` — cell **equality**, not `∼`.  Clause (2) of `↭`
fixes the lifetime `β` and the invariant `Q̂`; the ancestor step supplies the
value and the witness, which clause (2) wildcards.  Between them the cell is
pinned.

The witness needs the trace run on **both** sides.  `AgW.nonimm_beneath_imm`
returns the raised cell with the target's value and witness, and a `○` composite
takes its witness from an operand that is not `own` — so the trace pins the
witness unless the raised cell is itself an `own`, and when it is, `own`'s
witness is `∅` and the *other* side's trace pins it instead.  `↭` is symmetric
(`ResU.Upd.symm`), which is what lets the same step run both ways.

This is the conclusion `[TR]` 6.48's `mut ○ mut` bullet and its `own` bullet
both reach, and the one `[TR]` 6.59's closing sentence reaches for.
`[about ours: `[TR]` 6.48's proof, *"which implies `ag(ρ₃)(ℓ) = mut(β, v, ρᵢ,
Q̂)`"*]` -/
theorem ResU.upd_ag_mut_eq {ρ₂ ρ₃ e₂ a₂ σ₂ e₃ a₃ σ₃ : ResU Loc Val}
    (h : ResU.Upd ρ₂ ρ₃)
    (he₂ : ExS ρ₂ e₂) (ha₂ : AgW ρ₂ a₂) (hc₂ : ResU.CompS e₂ a₂ σ₂)
    (he₃ : ExS ρ₃ e₃) (ha₃ : AgW ρ₃ a₃) (hc₃ : ResU.CompS e₃ a₃ σ₃)
    {n : Loc} {b : Life} {v : Val} {χ : ResU Loc Val} {hb : χ.InStratum b}
    {P : Val → SPropS Loc Val b} {hw : P v ⟨χ, hb⟩}
    (hg : a₂.get n = some (CellU.mutOf b v χ hb P hw)) :
    a₃.get n = some (CellU.mutOf b v χ hb P hw) := by
  classical
  -- An `own` cell has the empty witness.
  have witOwn : ∀ ψ : CellU Loc Val, ψ.kind = Kind.own →
      ψ.wit = (PMap.empty : ResU Loc Val) := by
    intro ψ hk
    rcases CellU.rep ψ with ⟨u, rfl⟩ | ⟨s, u, τ, m, rfl⟩ | ⟨c, u, τ, m, Q, k, rfl⟩
    · simp
    · simp at hk
    · simp at hk
  -- What a `○`-factorisation carries over: the value always, the witness
  -- whenever the factor's own cell is not `own`.
  have key : ∀ (p z a : ResU Loc Val) (ξ ζ : CellU Loc Val),
      ResU.CompR p z a → p.get n = some ξ → a.get n = some ζ →
      ζ.kind ≠ Kind.own →
      ζ.erase = ξ.erase ∧ (ξ.kind ≠ Kind.own → ζ.wit = ξ.wit) := by
    intro p z a ξ ζ hC hp ha hζo
    rcases ResU.Comp.get hC n with ⟨f₁, -, -⟩ | ⟨ψ, f₁, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
        ⟨ψ₁, ψ₂, ψ, f₁, -, f, hcc⟩
    · rw [hp] at f₁
      exact absurd f₁ (by simp)
    · have e₁ : ξ = ψ := Option.some.inj (hp.symm.trans f₁)
      have e₂ : ζ = ψ := Option.some.inj (ha.symm.trans f)
      rw [e₁, e₂]
      exact ⟨rfl, fun _ => rfl⟩
    · rw [hp] at f₁
      exact absurd f₁ (by simp)
    · have e₁ : ξ = ψ₁ := Option.some.inj (hp.symm.trans f₁)
      have e₂ : ζ = ψ := Option.some.inj (ha.symm.trans f)
      subst e₁
      subst e₂
      refine ⟨(CellU.CompR.erase hcc).2, fun hξo => ?_⟩
      rcases CellU.CompR.wit_of_ne_own hcc hζo with ⟨-, e⟩ | ⟨k₂, e⟩
      · exact e
      · exact e.trans (CellU.CompR.wit hcc hξo k₂).symm
  have hφk : (CellU.mutOf b v χ hb P hw).kind ≠ Kind.imm := by simp
  have hφo : (CellU.mutOf b v χ hb P hw).kind ≠ Kind.own := by simp
  have hσ₂ : σ₂.get n = some (CellU.mutOf b v χ hb P hw) :=
    ResU.flat_eq_ag_at he₂ hc₂ hg hφk
  -- Clause (2) of `↭`: the lifetime and the invariant.
  obtain ⟨v', χ', hb', hw', hfa⟩ :=
    (h.2 n b P).mp ⟨v, χ, hb, hw, ⟨σ₂, ⟨e₂, a₂, he₂, ha₂, hc₂⟩, hσ₂⟩⟩
  have hσ₃ : σ₃.get n = some (CellU.mutOf b v' χ' hb' P hw') :=
    (ResU.flatAt_iff ⟨e₃, a₃, he₃, ha₃, hc₃⟩ n _).mp hfa
  -- The ancestor step, left to right.
  obtain ⟨κ, ev, av, p, z, ξ, -, -, -, hz, hpn, hξk, hξw, hξe⟩ :=
    ResU.upd_ag_nonimm_transfer h he₂ ha₂ hc₂ he₃ ha₃ hc₃ hg hφk
  have hocc : ∃ ζ, a₃.get n = some ζ := by
    rcases ResU.Comp.get hz n with ⟨f₁, -, -⟩ | ⟨ψ, -, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
        ⟨ψ₁, ψ₂, ψ, -, -, f, -⟩
    · rw [hpn] at f₁
      exact absurd f₁ (by simp)
    · exact ⟨ψ, f⟩
    · rw [hpn] at f₁
      exact absurd f₁ (by simp)
    · exact ⟨ψ, f⟩
  obtain ⟨ζ, hζ⟩ := hocc
  -- `ag(ρ₃)(n)` is `⦇ρ₃⦈(n)`: `ex(ρ₃)_●` is `imm`-free and `ag(ρ₃)` is occupied.
  have he₃n : e₃.get n = none := by
    cases f : e₃.get n with
    | none => rfl
    | some ξ' =>
        have hk := (CellU.CompatS.kinds (hc₃.1 n ξ' ζ f hζ)).1
        exact absurd hk (ExS.immFree he₃ n ξ' f)
  have ha₃n : a₃.get n = σ₃.get n := by
    rcases ResU.Comp.get hc₃ n with ⟨-, f₂, -⟩ | ⟨ψ, f₁, -, -⟩ | ⟨ψ, -, f₂, f⟩ |
        ⟨ψ₁, ψ₂, ψ, f₁, -, -, -⟩
    · rw [hζ] at f₂
      exact absurd f₂ (by simp)
    · rw [he₃n] at f₁
      exact absurd f₁ (by simp)
    · rw [f₂, f]
    · rw [he₃n] at f₁
      exact absurd f₁ (by simp)
  have hgt : a₃.get n = some (CellU.mutOf b v' χ' hb' P hw') := ha₃n.trans hσ₃
  have hζo : (CellU.mutOf b v' χ' hb' P hw').kind ≠ Kind.own := by simp
  obtain ⟨heL, hwL⟩ := key p z a₃ ξ _ hz hpn hgt hζo
  -- The value.
  have hv : v' = v := by
    have e := heL.trans hξe
    simpa using e
  subst hv
  -- The witness, from whichever side's trace has a cell that is not `own`.
  have hχ : χ' = χ := by
    by_cases hξo : ξ.kind = Kind.own
    · have hχe : χ = (PMap.empty : ResU Loc Val) := by
        have e := hξw.symm
        rw [witOwn ξ hξo] at e
        simpa using e
      obtain ⟨κ', ev', av', p', z', ξ', -, -, -, hz', hpn', hξk', hξw', hξe'⟩ :=
        ResU.upd_ag_nonimm_transfer h.symm he₃ ha₃ hc₃ he₂ ha₂ hc₂ hgt (by simp)
      obtain ⟨-, hwR⟩ := key p' z' a₂ ξ' _ hz' hpn' hg hφo
      by_cases hξo' : ξ'.kind = Kind.own
      · have e := hξw'.symm
        rw [witOwn ξ' hξo'] at e
        have : χ' = (PMap.empty : ResU Loc Val) := by simpa using e
        rw [this, hχe]
      · have e := (hwR hξo').trans hξw'
        simpa using e.symm
    · have e := (hwL hξo).trans hξw
      simpa using e
  subst hχ
  exact hgt

/-- **`ag(ρ₂)` and `ag(ρ₃)` agree wherever the cell is not `own`.**  This is
`[TR]` p. 16's two hard bullets as one statement: at an `imm` cell it is clause
(1), which pins the cell outright; at a `mut` cell it is the ancestor step
(`ResU.upd_ag_mut_eq`), clause (2) supplying the lifetime and the invariant and
the ancestor the value and the witness.

`own` is the one tag `↭` says nothing about directly, and `[TR]` p. 16 handles it
in its own bullet, by noting that an `own` cell contributes nothing to a `○`.
`[about ours: `[TR]` 6.48's proof at the aliasable walk, its `imm`, `mut ○ mut`
and `own` bullets together]` -/
theorem ResU.upd_ag_eq_of_ne_own {ρ₂ ρ₃ e₂ a₂ σ₂ e₃ a₃ σ₃ : ResU Loc Val}
    (h : ResU.Upd ρ₂ ρ₃)
    (he₂ : ExS ρ₂ e₂) (ha₂ : AgW ρ₂ a₂) (hc₂ : ResU.CompS e₂ a₂ σ₂)
    (he₃ : ExS ρ₃ e₃) (ha₃ : AgW ρ₃ a₃) (hc₃ : ResU.CompS e₃ a₃ σ₃)
    {n : Loc} {ψ : CellU Loc Val} (hg : a₂.get n = some ψ)
    (hk : ψ.kind ≠ Kind.own) : a₃.get n = some ψ := by
  rcases CellU.rep ψ with ⟨u, rfl⟩ | ⟨s, u, χ, hh, rfl⟩ | ⟨c, u, χ, hh, Q, kQ, rfl⟩
  · simp at hk
  · -- clause (1): an `imm` cell of `ag` is the flattening's cell, and `↭` pins it
    have hex : e₂.get n = none := by
      cases f : e₂.get n with
      | none => rfl
      | some ξ =>
          exact absurd (CellU.CompatS.kinds (hc₂.1 n ξ _ f hg)).1 (ExS.immFree he₂ n ξ f)
    have hσ₂ : σ₂.get n = some (CellU.immOf s u χ hh) := by
      rcases ResU.Comp.get hc₂ n with ⟨-, f₂, -⟩ | ⟨ζ, f₁, -, -⟩ | ⟨ζ, -, f₂, f⟩ |
          ⟨ζ₁, ζ₂, ζ, f₁, -, -, -⟩
      · rw [hg] at f₂; exact absurd f₂ (by simp)
      · rw [hex] at f₁; exact absurd f₁ (by simp)
      · exact f.trans (congrArg some (Option.some.inj (f₂.symm.trans hg)))
      · rw [hex] at f₁; exact absurd f₁ (by simp)
    have hσ₃ : σ₃.get n = some (CellU.immOf s u χ hh) :=
      (ResU.flatAt_iff ⟨e₃, a₃, he₃, ha₃, hc₃⟩ n _).mp
        ((h.1 n s u χ hh).mp ((ResU.flatAt_iff ⟨e₂, a₂, he₂, ha₂, hc₂⟩ n _).mpr hσ₂))
    exact ResU.ag_eq_flat_at_imm he₃ hc₃ hσ₃ (CellU.kind_immOf _ _ _ _)
  · exact ResU.upd_ag_mut_eq h he₂ ha₂ hc₂ he₃ ha₃ hc₃ hg

/-- **…and at an `own` cell the other walk carries an `own` or nothing.**  `↭`
says nothing about `own` directly; this is `ResU.upd_ag_eq_of_ne_own` read
backwards, which is `[TR]` p. 16's own move in its `own` bullet — the trace runs
in both directions because `↭` is symmetric. -/
theorem ResU.upd_ag_own_or_none {ρ₂ ρ₃ e₂ a₂ σ₂ e₃ a₃ σ₃ : ResU Loc Val}
    (h : ResU.Upd ρ₂ ρ₃)
    (he₂ : ExS ρ₂ e₂) (ha₂ : AgW ρ₂ a₂) (hc₂ : ResU.CompS e₂ a₂ σ₂)
    (he₃ : ExS ρ₃ e₃) (ha₃ : AgW ρ₃ a₃) (hc₃ : ResU.CompS e₃ a₃ σ₃)
    {n : Loc}
    (hg : ∀ ψ, a₂.get n = some ψ → ψ.kind = Kind.own) :
    ∀ φ, a₃.get n = some φ → φ.kind = Kind.own := by
  intro φ hφ
  by_contra hk
  have := ResU.upd_ag_eq_of_ne_own h.symm he₃ ha₃ hc₃ he₂ ha₂ hc₂ hφ hk
  exact hk (hg φ this)

end BoCa.Fig16

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
## Lemma 6.48 · `[TR]` p. 16 · `proved`

> If ρ₁ # ρ₂ and ρ₁ # ρ₃ and ρ₂ ↭ ρ₃, then ρ₁ ● ρ₂ ↭ ρ₁ ● ρ₃.

**Printed proof, transcribed.** The compatibilities give `✓(ρ₁ ● ρ₂)` and `✓(ρ₁ ● ρ₃)`; it suffices that `dom(⦇ρ₁ ● ρ₂⦈∣mut,imm) = dom(⦇ρ₁ ● ρ₃⦈∣mut,imm)` and `⦇ρ₁ ● ρ₂⦈(ℓ) ∼ ⦇ρ₁ ● ρ₃⦈(ℓ)` on it.  By Lemmas 6.20 and 6.18, `⦇ρ₁ ● ρⱼ⦈ = ex(ρ₁)_● ● ex(ρⱼ)_● ● (ag(ρ₁) ○ ag(ρⱼ))`.  `ρ₂ ↭ ρ₃` gives `dom(⦇ρ₂⦈∣mut,imm) = dom(⦇ρ₃⦈∣mut,imm)`, and the domain constraint follows.  At `ℓ`: by Lemma 6.36 the `ex` parts contain no `imm`, so `ex(ρ₁)`, `ex(ρ₂)` and `ag(ρ₁) ○ ag(ρ₂)` are disjoint, and there are three cases.  `ℓ ∈ dom(ex(ρ₁))`: both sides are `ex(ρ₁)(ℓ)`.  `ℓ ∈ dom(ex(ρ₂))`: the update gives `⦇ρ₂⦈(ℓ) ∼ ⦇ρ₃⦈(ℓ)`, which suffices.  `ℓ ∈ dom(ag(ρ₁) ○ ag(ρ₂))`: if `ℓ` is not in both `ag` domains, as before; otherwise, by the definition of `ag`, each side's cell is in `ρᵢ∣imm` or sits beneath an `imm` cell `ag(ρᵢ)(ℓ′) = imm(_, _, ρ′)` with `ℓ ∈ dom(⦇ρ′⦈_○)`, and unfolding `○` there are four cases: equal cells; two `imm` cells over one value and witness, where the update gives `ag(ρ₂)(ℓ) = ag(ρ₃)(ℓ)`; two `mut` cells `mut(α, v, ρᵢ, P̂)`, `mut(β, v, ρᵢ, Q̂)`, where the update gives `ag(ρ₃)(ℓ) = mut(β, _, _, Q̂)`, the cell sits beneath `ag(ρ₂)(ℓ′) = imm(_, _, ρ′)`, which the update carries to `ag(ρ₃)(ℓ′)`, so `ag(ρ₃)(ℓ) = mut(β, v, ρᵢ, Q̂)` and both composites are `mut(α ⊓ β, v, ρᵢ, P̂ ∧ Q̂)`; a `mut` against an `own`, done when the `mut` is `ρ₁`'s and otherwise carried by the update through the `imm` ancestor at `ℓ′`; and an `imm` against an own-or-mut, done when the `imm` is `ρ₁`'s and otherwise given by the update.

**Lean.** `BoCa.Fig16.BoLo.updV_frame`, alias `TR.lemma_6_48`, tag `[as printed]`.

**Note.** `Fig16.BoLo.updV_frame`, on the printed carrier, at [TR] p. 5's guarded `↭` as printed; the two printed `#`s are what supply its validity conjuncts on both sides. **The proof is p. 16's, step for step.**  6.18 and 6.20 (`Fig16.ResU.Flat.split`) cut both flattenings into `ex(ρ₁)_● ● ex(ρ_i)_● ● (ag(ρ₁) ○ ag(ρ_i))`, 6.36 (`Fig16.ExS.immFree`) with `Fig16.ResU.CompatS.disjoint_of_immFree` makes the three domains disjoint, and that is the print's three cases at a location. The aliasable case is the one that carries the technique: p. 16 accounts for a `mut` cell of the aliasable walk **by the `imm` cell it sits beneath**, carrying the ancestor across by `↭`'s first clause, which pins an `imm` cell together with its witness. That is `Fig16.ResU.upd_ag_eq_of_ne_own` — clause (1) at an `imm` cell, `Fig16.ResU.upd_ag_mut_eq` at a `mut` one, `Fig16.ResU.upd_ag_own_or_none` at an `own` one — in `Support/Model/Ancestors.lean`, upstream of this file so that 6.48 can use it. `Fig16.BoLo.flat_compR` with `Fig16.BoLo.cellUpd_compR` is a **second, pointwise route** to the same conclusion, kept and labelled as such; it was once this proof, and `docs/adjudications.md` §12.53 records what leaving p. 16's step unbuilt cost at 6.59.
-/
/-- **`[TR]` Lemma 6.48** (p. 16): if `ρ₁ # ρ₂` and `ρ₁ # ρ₃` and `ρ₂ ↭ ρ₃` then
`ρ₁ ● ρ₂ ↭ ρ₁ ● ρ₃`.  `↭` is `[TR]` p. 5's guarded row, and the two printed `#`s
are what supply its validity conjuncts on both sides.

The proof is the print's.  6.18 and 6.20 cut both flattenings into
`ex(ρ₁)_● ● ex(ρ_i)_● ● (ag(ρ₁) ○ ag(ρ_i))`, and 6.36 makes the three domains
disjoint, which gives the print's three cases at a location:

* `ℓ ∈ dom(ex(ρ₁))` — both composites are `ex(ρ₁)(ℓ)`;
* `ℓ ∈ dom(ag(ρ₁))` — both are `ag(ρ₁)(ℓ) ○ ag(ρ_i)(ℓ)`, and the two aliasable
  walks agree there: at an `imm` cell by clause (1), at a `mut` cell by the
  **ancestor step** (`Fig16.ResU.upd_ag_eq_of_ne_own`, off
  `Fig16.ResU.upd_ag_mut_eq`), and at an `own` cell by
  `Fig16.ResU.upd_ag_own_or_none`, an `own` contributing nothing to a `○`;
* neither — both composites are `⦇ρ_i⦈(ℓ)` itself, and `↭` is the hypothesis.

The second case is where p. 16 accounts for a `mut` cell of the aliasable walk
**by the `imm` cell it sits beneath**, carrying that ancestor across by `↭`'s
first clause.  `[as printed]` (the printed composites appear as their graphs — G4) -/
theorem updV_frame {ρ₁ ρ₂ ρ₃ ρ₁₂ ρ₁₃ : WRes} (h₁₂ : ResU.CompS ρ₁ ρ₂ ρ₁₂)
    (h₁₃ : ResU.CompS ρ₁ ρ₃ ρ₁₃) (hh₂ : ResU.Hash ρ₁ ρ₂) (hh₃ : ResU.Hash ρ₁ ρ₃)
    (h : ResU.UpdV ρ₂ ρ₃) : ResU.UpdV ρ₁₂ ρ₁₃ := by
  classical
  obtain ⟨τ₁₂, hτ₁₂⟩ := hash_valid_comp hh₂ h₁₂
  obtain ⟨τ₁₃, hτ₁₃⟩ := hash_valid_comp hh₃ h₁₃
  obtain ⟨e₁, e₂, e, a₁, a₂, a, he₁, he₂, hec, ha₁, ha₂, hac, hτ⟩ :=
    (ResU.Flat.split h₁₂).mp hτ₁₂
  obtain ⟨e₁', e₃, e', a₁', a₃, a', he₁', he₃, hec', ha₁', ha₃, hac', hτ'⟩ :=
    (ResU.Flat.split h₁₃).mp hτ₁₃
  rw [ExS.functional he₁' he₁] at hec'
  rw [AgW.functional ha₁' ha₁] at hac'
  obtain ⟨σ₂, x₂, y₂, hx₂, hy₂, hc₂⟩ := h.2.1
  rw [ExS.functional hx₂ he₂, AgW.functional hy₂ ha₂] at hc₂
  obtain ⟨σ₃, x₃, y₃, hx₃, hy₃, hc₃⟩ := h.2.2
  rw [ExS.functional hx₃ he₃, AgW.functional hy₃ ha₃] at hc₃
  have hfS : ∀ ψ₁ ψ₂ ψ ψ' : CellU BoCa.Loc BoCa.Val,
      CellU.CompS ψ₁ ψ₂ ψ → CellU.CompS ψ₁ ψ₂ ψ' → ψ = ψ' :=
    fun _ _ _ _ p q => CellU.CompS.functional p q
  have hfR : ∀ ψ₁ ψ₂ ψ ψ' : CellU BoCa.Loc BoCa.Val,
      CellU.CompR ψ₁ ψ₂ ψ → CellU.CompR ψ₁ ψ₂ ψ' → ψ = ψ' :=
    fun _ _ _ _ p q => CellU.CompR.functional p q
  -- 6.36: the exclusive walks are `imm`-free, so the three domains are disjoint
  have hdE : ∀ n, e₁.get n = none ∨ e₂.get n = none :=
    ResU.CompatS.disjoint_of_immFree (ExS.immFree he₁) hec.1
  have hdE' : ∀ n, e₁.get n = none ∨ e₃.get n = none :=
    ResU.CompatS.disjoint_of_immFree (ExS.immFree he₁) hec'.1
  have hdA : ∀ n, e.get n = none ∨ a.get n = none :=
    ResU.CompatS.disjoint_of_immFree
      (ResU.ImmFree.compS hec (ExS.immFree he₁) (ExS.immFree he₂)) hτ.1
  have hdA' : ∀ n, e'.get n = none ∨ a'.get n = none :=
    ResU.CompatS.disjoint_of_immFree
      (ResU.ImmFree.compS hec' (ExS.immFree he₁) (ExS.immFree he₃)) hτ'.1
  have hcell : ∀ n, CellUpd (τ₁₂.get n) (τ₁₃.get n) := by
    intro n
    by_cases hE1 : e₁.get n = none
    · by_cases hA1 : a₁.get n = none
      · -- `ρ₁` is silent in both walks: each composite is the operand's own flattening
        have hEn : e.get n = e₂.get n := by
          rcases ResU.Comp.get hec n with ⟨-, f₂, f⟩ | ⟨ψ, f₁, -, -⟩ | ⟨ψ, -, f₂, f⟩ |
              ⟨ψ₁, ψ₂, ψ, f₁, -, -, -⟩
          · rw [f, f₂]
          · rw [hE1] at f₁; exact absurd f₁ (by simp)
          · rw [f, f₂]
          · rw [hE1] at f₁; exact absurd f₁ (by simp)
        have hAn : a.get n = a₂.get n := by
          rcases ResU.Comp.get hac n with ⟨-, f₂, f⟩ | ⟨ψ, f₁, -, -⟩ | ⟨ψ, -, f₂, f⟩ |
              ⟨ψ₁, ψ₂, ψ, f₁, -, -, -⟩
          · rw [f, f₂]
          · rw [hA1] at f₁; exact absurd f₁ (by simp)
          · rw [f, f₂]
          · rw [hA1] at f₁; exact absurd f₁ (by simp)
        have hEn' : e'.get n = e₃.get n := by
          rcases ResU.Comp.get hec' n with ⟨-, f₂, f⟩ | ⟨ψ, f₁, -, -⟩ | ⟨ψ, -, f₂, f⟩ |
              ⟨ψ₁, ψ₂, ψ, f₁, -, -, -⟩
          · rw [f, f₂]
          · rw [hE1] at f₁; exact absurd f₁ (by simp)
          · rw [f, f₂]
          · rw [hE1] at f₁; exact absurd f₁ (by simp)
        have hAn' : a'.get n = a₃.get n := by
          rcases ResU.Comp.get hac' n with ⟨-, f₂, f⟩ | ⟨ψ, f₁, -, -⟩ | ⟨ψ, -, f₂, f⟩ |
              ⟨ψ₁, ψ₂, ψ, f₁, -, -, -⟩
          · rw [f, f₂]
          · rw [hA1] at f₁; exact absurd f₁ (by simp)
          · rw [f, f₂]
          · rw [hA1] at f₁; exact absurd f₁ (by simp)
        have hL : τ₁₂.get n = σ₂.get n := by
          refine OptComp.functional hfS ?_ (hc₂.2 n)
          rw [← hEn, ← hAn]; exact hτ.2 n
        have hR : τ₁₃.get n = σ₃.get n := by
          refine OptComp.functional hfS ?_ (hc₃.2 n)
          rw [← hEn', ← hAn']; exact hτ'.2 n
        rw [hL, hR]
        exact cellUpd_of_upd h.1 ⟨e₂, a₂, he₂, ha₂, hc₂⟩ ⟨e₃, a₃, he₃, ha₃, hc₃⟩ n
      · -- `ag(ρ₁)` is occupied: both composites are the aliasable ones
        have hAne : a.get n ≠ none := by
          rcases ResU.Comp.get hac n with ⟨f₁, -, -⟩ | ⟨ψ, -, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
              ⟨ψ₁, ψ₂, ψ, -, -, f, -⟩
          · exact absurd f₁ hA1
          · rw [f]; exact (by simp)
          · exact absurd f₁ hA1
          · rw [f]; exact (by simp)
        have hAne' : a'.get n ≠ none := by
          rcases ResU.Comp.get hac' n with ⟨f₁, -, -⟩ | ⟨ψ, -, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
              ⟨ψ₁, ψ₂, ψ, -, -, f, -⟩
          · exact absurd f₁ hA1
          · rw [f]; exact (by simp)
          · exact absurd f₁ hA1
          · rw [f]; exact (by simp)
        have hEnone : e.get n = none := (hdA n).resolve_right hAne
        have hEnone' : e'.get n = none := (hdA' n).resolve_right hAne'
        have hL : τ₁₂.get n = a.get n := by
          have h0 := hτ.2 n
          rw [hEnone] at h0
          cases hh : a.get n with
          | none => rw [hh] at h0; exact h0
          | some ψ => rw [hh] at h0; exact h0
        have hR : τ₁₃.get n = a'.get n := by
          have h0 := hτ'.2 n
          rw [hEnone'] at h0
          cases hh : a'.get n with
          | none => rw [hh] at h0; exact h0
          | some ψ => rw [hh] at h0; exact h0
        rw [hL, hR]
        -- the two aliasable walks agree at `n`, or both carry an `own`
        by_cases hk : ∀ ψ, a₂.get n = some ψ → ψ.kind = Kind.own
        · have hk' := ResU.upd_ag_own_or_none h.1 he₂ ha₂ hc₂ he₃ ha₃ hc₃ hk
          -- an `own` contributes nothing, so both composites are `ag(ρ₁)(n)`
          obtain ⟨ζ, hζ⟩ : ∃ ζ, a₁.get n = some ζ := by
            cases f : a₁.get n with
            | none => exact absurd f hA1
            | some ζ => exact ⟨ζ, rfl⟩
          have hone : ∀ (b c : ResU BoCa.Loc BoCa.Val),
              ResU.CompR a₁ b c → (∀ ψ, b.get n = some ψ → ψ.kind = Kind.own) →
              c.get n = some ζ := by
            intro b c hcc hb
            rcases ResU.Comp.get hcc n with ⟨f₁, -, -⟩ | ⟨ψ, f₁, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
                ⟨ψ₁, ψ₂, ψ, f₁, f₂, f, hC⟩
            · rw [hζ] at f₁; exact absurd f₁ (by simp)
            · rw [f, ← hζ, f₁]
            · rw [hζ] at f₁; exact absurd f₁ (by simp)
            · rw [f, show ψ = ψ₁ from CellU.compR_own_kind_right hC (hb ψ₂ f₂),
                ← hζ, f₁]
          rw [hone a₂ a hac hk, hone a₃ a' hac' hk']
          exact CellUpd.refl _
        · -- a cell that is not `own`: the ancestor step gives the same cell
          obtain ⟨ψ, hψ, hψk⟩ : ∃ ψ, a₂.get n = some ψ ∧ ψ.kind ≠ Kind.own := by
            by_contra hcon
            exact hk (fun ψ e => by
              by_contra hko
              exact hcon ⟨ψ, e, hko⟩)
          have := ResU.upd_ag_eq_of_ne_own h.1 he₂ ha₂ hc₂ he₃ ha₃ hc₃ hψ hψk
          have heq : a.get n = a'.get n := by
            refine OptComp.functional hfR (hac.2 n) ?_
            rw [hψ, ← this]; exact hac'.2 n
          rw [heq]
          exact CellUpd.refl _
    · -- `ex(ρ₁)` is occupied: both composites are `ex(ρ₁)(n)`
      obtain ⟨ζ, hζ⟩ : ∃ ζ, e₁.get n = some ζ := by
        cases f : e₁.get n with
        | none => exact absurd f hE1
        | some ζ => exact ⟨ζ, rfl⟩
      have hstep : ∀ (x ex ax cx tx : ResU BoCa.Loc BoCa.Val),
          ResU.CompS e₁ x ex → ResU.CompR a₁ ax cx → ResU.CompS ex cx tx →
          (∀ m, ex.get m = none ∨ cx.get m = none) →
          (∀ m, e₁.get m = none ∨ x.get m = none) → tx.get n = some ζ := by
        intro x ex ax cx tx hxe hxa hxt hdd hde
        have hexn : ex.get n = some ζ := by
          rcases ResU.Comp.get hxe n with ⟨f₁, -, -⟩ | ⟨ψ, f₁, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
              ⟨ψ₁, ψ₂, ψ, -, f₂, -, -⟩
          · rw [hζ] at f₁; exact absurd f₁ (by simp)
          · rw [f, ← hζ, f₁]
          · rw [hζ] at f₁; exact absurd f₁ (by simp)
          · rcases hde n with c | c
            · rw [hζ] at c; exact absurd c (by simp)
            · rw [c] at f₂; exact absurd f₂ (by simp)
        have hcxn : cx.get n = none := (hdd n).resolve_left (by rw [hexn]; simp)
        rcases ResU.Comp.get hxt n with ⟨f₁, -, -⟩ | ⟨ψ, f₁, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
            ⟨ψ₁, ψ₂, ψ, -, f₂, -, -⟩
        · rw [hexn] at f₁; exact absurd f₁ (by simp)
        · rw [f, ← hexn, f₁]
        · rw [hexn] at f₁; exact absurd f₁ (by simp)
        · rw [hcxn] at f₂; exact absurd f₂ (by simp)
      rw [hstep e₂ e a₂ a τ₁₂ hec hac hτ hdA hdE,
        hstep e₃ e' a₃ a' τ₁₃ hec' hac' hτ' hdA' hdE']
      exact CellUpd.refl _
  refine ⟨ResU.upd_of_flat hτ₁₂ hτ₁₃ (fun l s v χ hh => (hcell l).1 s v χ hh)
    (fun l b P => ?_), ⟨τ₁₂, hτ₁₂⟩, ⟨τ₁₃, hτ₁₃⟩⟩
  constructor
  · rintro ⟨v, χ, hh, hw, hg⟩
    obtain ⟨ψ, hψ, v', χ', hh', hw', rfl⟩ := ((hcell l).2 b P).mp ⟨_, hg, v, χ, hh, hw, rfl⟩
    exact ⟨v', χ', hh', hw', hψ⟩
  · rintro ⟨v, χ, hh, hw, hg⟩
    obtain ⟨ψ, hψ, v', χ', hh', hw', rfl⟩ :=
      ((hcell l).2 b P).mpr ⟨_, hg, v, χ, hh, hw, rfl⟩
    exact ⟨v', χ', hh', hw', hψ⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_48 := BoCa.Fig16.BoLo.updV_frame

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.49 · `[TR]` p. 17 · `proved`

> If ρ₁ ↭ ρ₂ and ρ₂ ↭ ρ₃, then ρ₁ ↭ ρ₃.

**Printed proof, transcribed.** `∼` is transitive, since `imm`s are required to be equal and `mut`s to have the same lifetime and predicate.

**Lean.** `BoCa.Fig16.ResU.UpdV.trans`, alias `TR.lemma_6_49`, tag `[as printed]`; `BoCa.Fig16.ResU.Upd.trans`, tag `[as printed]`.

**Note.** `Fig16.ResU.UpdV.trans`, at `[TR]` p. 5's guarded relation as printed, with `Fig16.ResU.Upd.trans` the same at `[CONF]` Fig. 18b's unguarded one.
-/
/-- **`[TR]` Lemma 6.49** — `↭` is transitive (p. 17) — at `[CONF]` Fig. 18b's
unguarded `↭`.  `ResU.UpdV.trans` is the same lemma at `[TR]`'s row.
`[as printed]` -/
theorem ResU.Upd.trans {ρ₁ ρ₂ ρ₃ : ResU Loc Val} (h₁ : ρ₁.Upd ρ₂) (h₂ : ρ₂.Upd ρ₃) :
    ρ₁.Upd ρ₃ :=
  ⟨fun l s v χ hs => (h₁.1 l s v χ hs).trans (h₂.1 l s v χ hs),
   fun l b P => (h₁.2 l b P).trans (h₂.2 l b P)⟩

/-! Lemma 6.49, continued. -/
/-- **`[TR]` Lemma 6.49** at `[TR]` p. 5's guarded `↭`: the guard rides along
with the hypotheses, so no extra premise is needed.  `[as printed]` -/
theorem ResU.UpdV.trans {ρ₁ ρ₂ ρ₃ : ResU Loc Val} (h₁ : ρ₁.UpdV ρ₂)
    (h₂ : ρ₂.UpdV ρ₃) : ρ₁.UpdV ρ₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.1, h₂.2.2⟩

end BoCa.Fig16

alias TR.lemma_6_49 := BoCa.Fig16.ResU.UpdV.trans

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
## Lemma 6.50 · `[TR]` p. 17 · `proved`

> If @ρ ⊐ α and ρ ↭ ρ′, then @ρ′ ⊐ α.

**Printed proof, transcribed.** Unfolding the update relation: all borrows have the same lifetime before and after updating.

**Lean.** `BoCa.Fig16.BoLo.updV_outlives`, alias `TR.lemma_6_50`, tag `[as printed]`.

**Note.** `Fig16.BoLo.updV_outlives`, on the printed carrier, `[as printed]` — `@ρ ⊐ α` is `Fig16.BoLo.Outlives`, the printed strict relation at the graph of `@ρ`, and `↭` is [TR] p. 5's guarded row. The printed proof is one sentence and elides two steps, both about `⦇−⦈` rather than about `↭`: `Fig16.BoLo.flat_inStratum` (`@ρ ⊐ α ⇒ @⦇ρ⦈ ⊐ α`, by the mutual induction the walks are defined by) and `Fig16.BoLo.flat_inStratum_inv` (its converse, where `ag`'s `○`s may only *lengthen* an `imm` cell's lifetime set).
-/
/-- **`[TR]` Lemma 6.50** (p. 16): if `@ρ ⊐ α` and `ρ ↭ ρ′` then `@ρ′ ⊐ α`.
`↭` is `[TR]` p. 5's guarded row, whose two validity conjuncts are what name the
flattenings the relation is about.  The print's own sentence — "all borrows must
have the same lifetime before and after updating" — is the middle step here:
clause (1) fixes an `imm` cell of `⦇ρ′⦈` outright and clause (2) fixes a `mut`
cell's lifetime, while an `own` cell's `@ψ` is `⊤` and `Res_α` asks nothing of
it at any `α`.  `[as printed]` -/
theorem updV_outlives {ρ ρ' : WRes} {α : Life} (h : Outlives ρ α)
    (hu : ResU.UpdV ρ ρ') : Outlives ρ' α := by
  have hρ : ρ.InStratum α := h
  obtain ⟨σ, hσ⟩ := hu.2.1
  obtain ⟨σ', hσ'⟩ := hu.2.2
  have hsσ : σ.InStratum α := flat_inStratum hσ hρ
  refine flat_inStratum_inv hσ' (fun l χ hl => ?_)
  rcases CellU.rep χ with ⟨w, rfl⟩ | ⟨s, w, ξ, hξ, rfl⟩ | ⟨b, w, ξ, hξ, P, hP, rfl⟩
  · exact trivial
  · obtain ⟨τ, hτ, hg⟩ := (hu.1.1 l s w ξ hξ).mpr ⟨σ', hσ', hl⟩
    cases ResU.Flat.functional hτ hσ
    exact hsσ l _ hg
  · obtain ⟨w₀, ξ₀, hξ₀, hP₀, τ, hτ, hg⟩ :=
      (hu.1.2 l b P).mpr ⟨w, ξ, hξ, hP, ⟨σ', hσ', hl⟩⟩
    cases ResU.Flat.functional hτ hσ
    exact (hsσ l _ hg : b ⊐ α)

end BoCa.Fig16.BoLo

alias TR.lemma_6_50 := BoCa.Fig16.BoLo.updV_outlives

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.51 · `[TR]` p. 17 · `proved`

> If ⦇ρ⦈(ℓ) = imm(α, ρᵢ, v) and ⦇ρ′⦈(ℓ) = imm(β, ρᵢ, v) and ρ # ρ′ then ⦇ρ ● ρ′⦈(ℓ) = imm(α ∪ β, ρᵢ, v)

**Printed proof, transcribed.** By Lemma 6.20, noting that by the definitions of `○` and `●`, `imm(α, ρᵢ, v) ○ imm(β, ρᵢ, v) = imm(α, ρᵢ, v) ● imm(β, ρᵢ, v)`, the `imm` cell over `ρᵢ` and `v` at the two lifetime sets joined.

**Lean.** `BoCa.Fig16.ResU.six51`, alias `TR.lemma_6_51`, tag `[as printed]`.

**Note.** `Fig16.ResU.six51`, on the printed carrier, `[as printed]` — the first printed lemma in this run that says what the flattening of a composite **is** at one location, and it is printed immediately before 6.52. The printed proof in full: *"Follows by lemma 6.20, noting that by the definition of `○` and `●`, `imm(ᾱ, ρᵢ, v) ○ imm(β̄, ρᵢ, v) = imm(ᾱ, ρᵢ, v) ● imm(β̄, ρᵢ, v) = imm(ᾱ ∪ β̄, ρᵢ, v)`."*  6.30 (`Fig16.BoLo.flat_compR`) splits the composite's flattening, `Fig16.ResU.Flat.functional` identifies the two halves with the given ones, and `Fig16.CellU.CompR.imm_union` is the cell step — clause (1) when the two cells coincide, clause (2) otherwise. Every flattening is named by its graph (G4), which is what carries the printed `#`'s definedness
-/
/-- **`[TR]` Lemma 6.51** (p. 17): if `⦇ρ⦈(ℓ) = imm(ᾱ, ρᵢ, v)` and
`⦇ρ′⦈(ℓ) = imm(β̄, ρᵢ, v)` and `ρ # ρ′` then `⦇ρ ● ρ′⦈(ℓ) = imm(ᾱ ∪ β̄, ρᵢ, v)`.

The printed proof, in full: *"Follows by lemma 6.20, noting that by the
definition of `○` and `●`, `imm(ᾱ, ρᵢ, v) ○ imm(β̄, ρᵢ, v) = imm(ᾱ, ρᵢ, v) ●
imm(β̄, ρᵢ, v) = imm(ᾱ ∪ β̄, ρᵢ, v)`."*  6.30 (`BoLo.flat_compR`) splits the
composite's flattening, `ResU.Flat.functional` identifies the two halves with
the given ones, and `CellU.CompR.imm_union` is the cell step.

Every flattening is named by its graph (G4), which is also what carries the
printed `#`'s definedness: `ρ # ρ′` gives the composite and its flattening, and
those are the hypotheses `hc` and `hσ₁₂`.
`[as printed]` -/
theorem ResU.six51 {ρ ρ' ρ₁₂ σ σ' σ₁₂ : ResU BoCa.Loc BoCa.Val}
    (hc : ResU.CompS ρ ρ' ρ₁₂) (hσ : ResU.Flat ρ σ) (hσ' : ResU.Flat ρ' σ')
    (hσ₁₂ : ResU.Flat ρ₁₂ σ₁₂)
    {l : BoCa.Loc} {a b : LSet} {v : BoCa.Val} {χ : ResU BoCa.Loc BoCa.Val}
    {ha : χ.InStratum a.join} {hb : χ.InStratum b.join}
    (hg : σ.get l = some (CellU.immOf a v χ ha))
    (hg' : σ'.get l = some (CellU.immOf b v χ hb)) :
    ∃ h : χ.InStratum (a ∪ b).join,
      σ₁₂.get l = some (CellU.immOf (a ∪ b) v χ h) := by
  obtain ⟨σ₁, σ₂, hf₁, hf₂, hcσ⟩ := BoLo.flat_compR hc hσ₁₂
  rw [ResU.Flat.functional hf₁ hσ, ResU.Flat.functional hf₂ hσ'] at hcσ
  rcases ResU.Comp.get hcσ l with ⟨f₁, -, -⟩ | ⟨ξ, f₁, f₂, -⟩ | ⟨ξ, f₁, -, -⟩ |
      ⟨ξ₁, ξ₂, ξ, f₁, f₂, f, hC⟩
  · rw [hg] at f₁; exact absurd f₁ (by simp)
  · rw [hg'] at f₂; exact absurd f₂ (by simp)
  · rw [hg] at f₁; exact absurd f₁ (by simp)
  · obtain ⟨h', he⟩ := CellU.CompR.imm_union hC
      (Option.some.inj (f₁.symm.trans hg)) (Option.some.inj (f₂.symm.trans hg'))
    exact ⟨h', f.trans (congrArg some he)⟩

end BoCa.Fig16

alias TR.lemma_6_51 := BoCa.Fig16.ResU.six51

namespace BoCa.Fig16
variable {Loc Val : Type}

/-! `[about ours]` — what the Lean of Lemma 6.52 needs; the paper prints nothing here. -/
/-- **The image of `reb_α` lies in `Res_{↓α}`**: its cells are the source's `imm`
cells, which lie in `Res_α`, or fresh `imm` cells at `{α}` exactly. -/
theorem ResU.reb_inStratum_down {α : Life} {ρ' ρ : ResU Loc Val}
    (h : ResU.Reb α ρ' ρ) : ρ.InStratum (↓α) := by
  intro l ψ hg
  obtain ⟨φ, hφ⟩ := ResU.reb_dom_subset h hg
  by_cases hk : φ.kind = Kind.imm
  · exact (ResU.reb_imm_cell_kw h hg hφ hk).2.2.2 _
      (CellU.InStratum.mono (le_of_lt (Life.down_sqsubset α)) (h.1 l φ hφ))
  · obtain ⟨v, χ, hχ, hψ, -, -⟩ := ResU.reb_src h hg hφ hk
    rw [hψ]
    exact Life.down_sqsubset α

/-- **`[TR]` 6.52's H1** (p. 17): at every location the reborrow covers, `ρ⁺`
carries an `imm` cell over the same value and witness as `ρ_reb`'s, and over a
lifetime set containing `ρ_reb`'s.

This is the step 6.52's proof takes before it builds `ρ⁺ ⊟ ρ_reb`, and `[TR]`
6.59's own statement names the result of that construction rather than the
construction, so the step is stated on its own here.
`[about ours: the display inside `[TR]` 6.52's proof, named]` -/
theorem ResU.six52_H1 {α : Life}
    {ρ'i ρ ρe ρ'' ρp ρρe ρ'p : ResU BoCa.Loc BoCa.Val}
    (hreb : ResU.Reb α ρ'i ρ)
    (hce : ResU.CompS ρ ρe ρρe)
    (hcp : ResU.CompS ρ'' ρp ρ'p)
    (hupd : ResU.UpdV ρρe ρ'p)
    (hse : ρe.InStratum α)
    (hs' : ρ''.InStratum α) :
    ∀ (l : BoCa.Loc) (s' : LSet) (v : BoCa.Val)
      (χ : ResU BoCa.Loc BoCa.Val) (h' : χ.InStratum s'.join),
      (ρ.restrictDom ρ'i.exclPart).get l = some (CellU.immOf s' v χ h') →
      ∃ (s : LSet) (h : χ.InStratum s.join),
        ρp.get l = some (CellU.immOf s v χ h) ∧ ∀ x, s'.mem x → s.mem x := by
  classical
  -- `ρ⁺` carries no borrow strictly shorter than `α`.
  have hdle : (↓α) ≤ α := le_of_lt (Life.down_sqsubset α)
  have hρρe : ρρe.InStratum (↓α) :=
    ResU.CompS.inStratum hce (ResU.reb_inStratum_down hreb)
      (ResU.InStratum.mono hdle hse)
  have hpdown : ρp.InStratum (↓α) :=
    ResU.CompS.inStratum_right hcp (BoLo.updV_outlives hρρe hupd)
  have hnb : ∀ m φ, ρp.get m = some φ → ¬ (φ.at < α) :=
    fun m φ e => CellU.not_at_lt_of_inStratum_down (hpdown m φ e)
  obtain ⟨σ, hσ⟩ := hupd.2.1
  obtain ⟨σ', hσ'⟩ := hupd.2.2
  obtain ⟨σ'', σp, hσ'', hσp, hcσ⟩ := BoLo.flat_compR hcp hσ'
  have hσ''s : σ''.InStratum α := BoLo.flat_inStratum hσ'' hs'
  have hexcl : (ρ.restrictDom ρ'i.exclPart).exclPart = PMap.empty := by
    -- the image of `reb_α` carries `imm` cells only
    refine PMap.ext fun m => ?_
    have hnone : (ρ.restrictDom ρ'i.exclPart).exclPart.get m = none := by
      cases f : (ρ.restrictDom ρ'i.exclPart).exclPart.get m with
      | none => rfl
      | some ξ =>
          obtain ⟨g1, g2⟩ := ResU.exclPart_eq_some.mp f
          exact absurd (ResU.reb_imm_image hreb (ResU.restrictDom_get_inv g1)) g2
    rw [hnone]; rfl
  have hle : ∀ (l : BoCa.Loc) (s' : LSet) (v : BoCa.Val)
      (χ : ResU BoCa.Loc BoCa.Val) (h' : χ.InStratum s'.join),
      (ρ.restrictDom ρ'i.exclPart).get l = some (CellU.immOf s' v χ h') →
      ∃ (s : LSet) (h : χ.InStratum s.join),
        ρp.get l = some (CellU.immOf s v χ h) ∧ ∀ x, s'.mem x → s.mem x := by
    intro l s' v χ h' he
    -- the reborrowed cell at `ℓ`, and `α ∈ s'`
    have hρl : ρ.get l = some (CellU.immOf s' v χ h') := ResU.restrictDom_get_inv he
    obtain ⟨φ', hφ'⟩ := ResU.restrictDom_dom he
    obtain ⟨hφ'g, hφ'k⟩ := ResU.exclPart_eq_some.mp hφ'
    obtain ⟨vv, χw, hχs, hψeq, -, -⟩ := ResU.reb_src hreb hρl hφ'g hφ'k
    obtain ⟨hs'eq, -, -⟩ := CellU.immOf_inj hψeq
    have hmem : s'.mem α := by rw [hs'eq]; rfl
    -- `⦇ρ ● ρₑ⦈(ℓ)` carries `α`, over the same value and witness
    obtain ⟨ζ, hζ, hζk, hζw⟩ := ResU.CompS.get_left hce hρl
    have hζe : ζ.erase = v := by
      rw [ResU.CompS.erase_left hce hρl hζ, CellU.erase_immOf]
    obtain ⟨tζ, htζ, hζeta⟩ := CellU.imm_eta (hζk.trans (CellU.kind_immOf _ _ _ _))
    have hζget : ρρe.get l = some (CellU.immOf tζ ζ.erase ζ.wit htζ) :=
      hζ.trans (congrArg some hζeta)
    have hmemζ : tζ.mem α :=
      ResU.CompR.get_ls_imm (ResU.CompS.toCompR hce) hρl hζget hmem
    obtain ⟨π, hπ, hπk, hπe, hπw⟩ := ResU.Flat.get hσ hζget
    obtain ⟨tπ, htπ, hπeta⟩ := CellU.imm_eta (hπk.trans (CellU.kind_immOf _ _ _ _))
    have hπget : σ.get l = some (CellU.immOf tπ π.erase π.wit htπ) :=
      hπ.trans (congrArg some hπeta)
    have hmemπ : tπ.mem α := ResU.Flat.get_ls_imm hσ hζget hπget hmemζ
    -- across `↭`
    have hπ' : σ'.get l = some (CellU.immOf tπ π.erase π.wit htπ) :=
      (ResU.flatAt_iff hσ' l _).mp
        ((hupd.1.1 l tπ π.erase π.wit htπ).mp ⟨σ, hσ, hπget⟩)
    -- `α` cannot come from `⦇ρ′⦈`
    have hmemp : ∃ ξ t, σp.get l = some ξ ∧ ξ.lsOf = some t ∧ t.mem α := by
      rcases ResU.CompR.lsOf_inv hcσ hπ' rfl hmemπ with ⟨ξ, t, e, ht, hxt⟩ | h
      · exact absurd (t.meet_least α hxt)
          (not_le_of_gt (CellU.sqsupset_of_lsOf ht (hσ''s l ξ e)))
      · exact h
    obtain ⟨ξp, tp, hξp, htp, hxtp⟩ := hmemp
    -- so `ρ⁺` carries it at the top level
    obtain ⟨ω, tω, hω, htω, hxtω⟩ :=
      ResU.flat_imm_at_top_of_no_shorter hσp hξp htp hxtp hnb
    -- and it is over the same value and witness
    have hξpe : ξp.erase = π.erase ∧ ξp.wit = π.wit := by
      have hc2 := hcσ.2 l
      rw [hξp, hπ'] at hc2
      cases hσ''l : σ''.get l with
      | none =>
          rw [hσ''l] at hc2
          exact ⟨by rw [← Option.some.inj hc2, CellU.erase_immOf],
            by rw [← Option.some.inj hc2, CellU.wit_immOf]⟩
      | some ξ'' =>
          rw [hσ''l] at hc2
          obtain ⟨ω', hω', hCω⟩ := hc2
          have hω'eq : ω' = CellU.immOf tπ π.erase π.wit htπ := (Option.some.inj hω').symm
          have hkξp : ξp.kind ≠ Kind.own := by
            rw [CellU.kind_of_lsOf htp]; exact fun c => Kind.noConfusion c
          refine ⟨?_, ?_⟩
          · rw [← CellU.CompR.erase_right hCω, hω'eq, CellU.erase_immOf]
          · rw [← (CellU.CompR.nonown_right hCω hkξp).2, hω'eq, CellU.wit_immOf]
    obtain ⟨tω', htω', hωeta⟩ := CellU.imm_eta (CellU.kind_of_lsOf htω)
    obtain ⟨κ, hκ, -, hκe, hκw⟩ := ResU.Flat.get hσp hω
    obtain rfl : κ = ξp := Option.some.inj (hκ.symm.trans hξp)
    have hωe : ω.erase = v := by
      rw [← hκe, hξpe.1, hπe, CellU.erase_immOf, hζe]
    have hωw : ω.wit = χ := by
      rw [← hκw, hξpe.2, hπw, CellU.wit_immOf, hζw, CellU.wit_immOf]
    have htωeq : tω = tω' := by
      have hlsω : CellU.lsOf ω = some tω' := by rw [hωeta]; rfl
      exact Option.some.inj (htω.symm.trans hlsω)
    refine ⟨tω', hωw ▸ htω', ?_, ?_⟩
    · exact hω.trans (congrArg some
        (hωeta.trans (CellU.immOf_congr rfl hωe hωw htω' _)))
    · intro x hx
      rw [hs'eq] at hx
      rw [show x = α from hx, ← htωeq]
      exact hxtω
  exact hle

/-- **`[TR]` 6.52's second conclusion**, at any `χ` the definition admits.
`ResU.Sub.inStratum`'s two side conditions are the printed *"all parts of the
resource outlive `α`"* and its exception *"except for the locations in `ρ` that
are mut or own in `ρ′ᵢ`"*, and neither mentions which `χ` Definition 6.3's
bullets picked, so the conclusion holds of every one of them.
`[about ours: `[TR]` 6.52's second conclusion at a `χ` given rather than
constructed]` -/
theorem ResU.six52_sub_inStratum {α : Life}
    {ρ'i ρ ρe ρ'' ρp ρρe ρ'p : ResU BoCa.Loc BoCa.Val}
    (hreb : ResU.Reb α ρ'i ρ)
    (hce : ResU.CompS ρ ρe ρρe)
    (hcp : ResU.CompS ρ'' ρp ρ'p)
    (hupd : ResU.UpdV ρρe ρ'p)
    (hse : ρe.InStratum α)
    (hs' : ρ''.InStratum α) :
    ∀ χ, ResU.Sub ρp (ρ.restrictDom ρ'i.exclPart) χ → χ.InStratum α := by
  classical
  have hdle : (↓α) ≤ α := le_of_lt (Life.down_sqsubset α)
  have hρρe : ρρe.InStratum (↓α) :=
    ResU.CompS.inStratum hce (ResU.reb_inStratum_down hreb)
      (ResU.InStratum.mono hdle hse)
  have hpdown : ρp.InStratum (↓α) :=
    ResU.CompS.inStratum_right hcp (BoLo.updV_outlives hρρe hupd)
  have hle := ResU.six52_H1 hreb hce hcp hupd hse hs'
  intro ψ hsub
  refine ResU.Sub.inStratum hsub hpdown ?_ ?_
  · -- off `dom(ρ_reb)`: `ρ ∈ Res_α`, and 6.50 at `ℓ` carries that to `ρ⁺`
    intro l φ hnone hφ
    have hρl : ∀ ξ, ρ.get l = some ξ → ξ.InStratum α := by
      intro ξ hξ
      have hexl : ρ'i.exclPart.get l = none := by
        cases f : ρ'i.exclPart.get l with
        | none => rfl
        | some φ' =>
            rw [ResU.restrictDom_get_of_some f, hξ] at hnone
            exact absurd hnone (by simp)
      obtain ⟨φ', hφ'⟩ := ResU.reb_dom_subset hreb hξ
      have hk : φ'.kind = Kind.imm := by
        by_contra hk
        rw [ResU.exclPart_eq_some.mpr ⟨hφ', hk⟩] at hexl
        exact absurd hexl (by simp)
      exact (ResU.reb_imm_cell_kw hreb hξ hφ' hk).2.2.2 _ (hreb.1 l φ' hφ')
    have hρρel : ∀ ξ, ρρe.get l = some ξ → ξ.InStratum α :=
      fun ξ e =>
        ResU.inStratum_comp_at (CellU.compS_hC α) hce hρl (fun ω f => hse l ω f) e
    exact ResU.CompS.inStratum_right_at hcp
      (fun ξ e => ResU.updV_outlives_at hρρe hupd hρρel e) hφ
  · -- on it: the reborrowed cell is `imm({α}, ρ_ℓ, v_ℓ)`, and H1 matches `ρ⁺`
    intro l ζ hζ
    have hρl : ρ.get l = some ζ := ResU.restrictDom_get_inv hζ
    obtain ⟨φ', hφ'⟩ := ResU.restrictDom_dom hζ
    obtain ⟨hφ'g, hφ'k⟩ := ResU.exclPart_eq_some.mp hφ'
    obtain ⟨v, w, hw, hζeq, -, -⟩ := ResU.reb_src hreb hρl hφ'g hφ'k
    obtain ⟨s, hs, hpl, -⟩ :=
      hle l (LSet.singleton α) v w hw (by rw [hζ, hζeq])
    exact ⟨s, LSet.singleton α, v, w, hs, hw, hpl, hζeq, rfl⟩

/-!
## Lemma 6.52 · `[TR]` p. 17 · `proved`

> Let ρ_reb = ρ∣dom(ρ′ᵢ∣mut,own). If ρ ∈ reb_α(ρ′ᵢ) and ρ ● ρₑ ↭ ρ′ ● ρ⁺ and @ρₑ ⊐ α and @ρ′ ⊐ α then ρ⁺ = (ρ⁺ ⊟ ρ_reb) ● ρ_reb and @(ρ⁺ ⊟ ρ_reb) ⊐ α

**Printed proof, transcribed.** Unfolding `reb`: `ρ∣own,mut = ∅`, `ρ′ᵢ ⊐ α`, and each `ℓ ∈ dom(ρ′ᵢ∣mut,own) ∩ dom(ρ)` has `ρ(ℓ) = imm({α}, ρ_ℓ, v_ℓ)`.  At such an `ℓ`, the update gives `β_ℓ` with `⦇ρ ● ρₑ⦈(ℓ) = ⦇ρ′ ● ρ⁺⦈(ℓ) = imm(β_ℓ, ρ_ℓ, v_ℓ)` and `α ∈ β_ℓ`; since `ρ′ ⊐ α` there is `β_ℓ⁺ ⊆ β_ℓ` with `⦇ρ⁺⦈(ℓ) = imm(β_ℓ⁺, ρ_ℓ, v_ℓ)` and `α ∈ β_ℓ⁺`; and since `ρ′ᵢ, ρₑ ⊐ α` there are no borrows at any lifetime shorter than `α`, so no borrow contains `ρ(ℓ)`.  Hence (H1) `ρ⁺ = (ρ⁺ ⊟ ℓ ↦ imm({α}, ρ_ℓ, v_ℓ)) ● ℓ ↦ imm({α}, ρ_ℓ, v_ℓ)`.  Noting `ρ_reb = ⨀_{ℓ ∈ dom(ρ′ᵢ∣mut,own) ∩ dom(ρ)} ρ(ℓ)`, rewriting with H1 at every such `ℓ` gives `ρ⁺ = (ρ⁺ ⊟ ρ_reb) ● ρ_reb`.  The outlives constraint: every part of the resource outlives `α` except the locations of `ρ` that are `mut` or `own` in `ρ′ᵢ`.

**Lean.** `BoCa.Fig16.ResU.six52`, alias `TR.lemma_6_52`, tag `[as printed]`.

**Note.** `Fig16.ResU.six52`, on the printed carrier, `[as printed]` — both printed conclusions, all four printed hypotheses verbatim, with `@ρ ⊐ α` at the corrected reading (`Fig16.ResU.InStratum`, `docs/adjudications.md` §C.25) and every composite named by its graph (G4). Stated at `BoCa.Loc`/`BoCa.Val`, as the `Res_α` lemmas it spends are. **The equation.**  *"Unfolding reb"* is `Fig16.ResU.reb_src`; *"`⦇ρ ● ρₑ⦈(ℓ) = ⦇ρ′ ● ρ⁺⦈(ℓ) = imm(β_ℓ, ρ_ℓ, v_ℓ)` and `α ∈ β_ℓ`"* is `Fig16.ResU.Flat.get` with `Fig16.ResU.Flat.get_ls_imm` and `↭`'s first clause; *"since `ρ′ ⊐ α` … there is a `β_ℓ⁺ ⊆ β_ℓ`"* is `Fig16.BoLo.flat_compR` with `Fig16.ResU.CompR.lsOf_inv` — `⦇ρ′⦈ ∈ Res_α`, so `α` is in none of its sets and must come from `⦇ρ⁺⦈`; *"there cannot be any borrow that contains `ρ(ℓ)`"* is `Fig16.ResU.flat_imm_at_top_of_no_shorter`, whose hypothesis is 6.50 (`Fig16.BoLo.updV_outlives`) at `↓α`. H1 and the printed *"note that `ρ_reb = ⨀_{ℓ} ρ(ℓ)`"* and *"rewriting with H1 for every `ℓ`"* are all subsumed by `Fig16.ResU.sub_of_le`, which builds at every location at once what the iteration builds one location at a time. **The outlives constraint.**  *"All parts of the resource outlive `α` except for the locations in `ρ` that are mut or own in `ρ′ᵢ`"* is `Fig16.ResU.Sub.inStratum`, stated at `⊟` itself: the exception is `dom(ρ_reb)`, and Definition 6.3's fourth bullet removes exactly `{α}` there, leaving `imm(β̄_ℓ⁺ ∖ {α}, ρ_ℓ, v_ℓ)` — every lifetime of which outlives `α`, `ρ⁺` carrying no borrow shorter than `α` (`Fig16.ResU.reb_inStratum_down` with 6.50 at `↓α`). Off `dom(ρ_reb)` the printed sentence is 6.50 read at one location (`Fig16.ResU.updV_outlives_at`), which needs the walks to keep `Res_α` at one location: a borrow no shorter than `α` has its witness in `Res_α` (`Fig16.CellU.wit_inStratum_of_down`), so the material the walks raise lies in `Res_α` outright and only `ρ(ℓ)` is asked for (`Fig16.ExW.inStratum_at`, `Fig16.AgW.inStratum_at`, `Fig16.ResU.flat_inStratum_at`)
-/
/-- **`[TR]` Lemma 6.52** (p. 17): `ρ⁺ = (ρ⁺ ⊟ ρ_reb) ● ρ_reb` and
`@(ρ⁺ ⊟ ρ_reb) ⊐ α`, at `ρ_reb = ρ|dom(ρ′ᵢ|mut,own)`.

All four printed hypotheses are carried verbatim, with `@ρ ⊐ α` at the corrected
reading (`ResU.InStratum`, `docs/adjudications.md` §C.25) and `ρ ● ρₑ`, `ρ′ ● ρ⁺`
and the two `⊟`/`●` composites named by their graphs (G4).  Stated at
`BoCa.Loc`/`BoCa.Val`, as the `Res_α` lemmas it spends are.
`[as printed]` -/
theorem ResU.six52 {α : Life}
    {ρ'i ρ ρe ρ'' ρp ρρe ρ'p : ResU BoCa.Loc BoCa.Val}
    (hreb : ResU.Reb α ρ'i ρ)
    (hce : ResU.CompS ρ ρe ρρe)
    (hcp : ResU.CompS ρ'' ρp ρ'p)
    (hupd : ResU.UpdV ρρe ρ'p)
    (hse : ρe.InStratum α)
    (hs' : ρ''.InStratum α) :
    ∃ ψ, ResU.Sub ρp (ρ.restrictDom ρ'i.exclPart) ψ ∧
      ResU.CompS ψ (ρ.restrictDom ρ'i.exclPart) ρp ∧ ψ.InStratum α := by
  classical
  obtain ⟨ψ, hsub, hcomp⟩ :=
    ResU.sub_of_le (ResU.reb_restrictDom_exclPart_empty hreb)
      (ResU.six52_H1 hreb hce hcp hupd hse hs')
  exact ⟨ψ, hsub.toSub, hcomp,
    ResU.six52_sub_inStratum hreb hce hcp hupd hse hs' ψ hsub.toSub⟩

end BoCa.Fig16

alias TR.lemma_6_52 := BoCa.Fig16.ResU.six52

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.53 · `[TR]` p. 18 · `proved*`

> If ρ ∈ reb_β(ρ′) and ρ_f # ℓ ↦ imm(α, ρ′, v) then ρ_f ▸◂ ρ.

**Printed proof, transcribed.** `dom(ρ) ⊆ dom(ρ′)` and `ρ∣own,mut = ∅`.  At `ℓ ∈ dom(ρ_f) ∩ dom(ρ)`, `ρ_f(ℓ)` can fail to compose with `ρ(ℓ)` only by being `own` or `mut`; but `ρ_f # ℓ ↦ imm(α, ρ′, v)`, unfolded with Lemmas 6.18, 6.20 and 6.30, gives `ex(ρ_f)_● ▸◂ ⦇ρ′⦈_○`, so that overlap never happens.

**Lean.** `BoCa.Fig16.ResU.six53`, alias `TR.lemma_6_53`, tag `[restricted: to `EscrowAgree ρ′ ρ (ag ρ_f)`, the sentence `[TR]`.

**Note.** `Fig16.ResU.six53`, on the printed carrier, conclusion exactly as printed, `[restricted: to `Fig16.EscrowAgree ρ′ ρ (ag ρ_f)`]` — the sentence `[TR]` p. 18 asserts inside its proof of **6.55** (*"witnesses and values always stay the same"*) and `reb_α` does not carry; `docs/adjudications.md` §12.41. `reb_α` itself is untouched. The hypothesis is at **`ag(ρ_f)`**, not at `ρ_f`: p. 18 asserts the sentence once and spends it twice, and 6.55's first bullet spends it at the aliasable walk, which is the deeper of the two levels — it carries cells where `ρ_f` carries none, and `mut` cells where `ρ_f` would carry `imm`.  6.53's own use comes back from there through `Fig16.AgW.get_imm`. Naming `ag(ρ_f)` costs nothing: `Fig16.ResU.agW_of_hash_left` produces it from the printed `#`.  §12.41 records the four readings tried and why only this one discharges both rows. The printed proof's opening note `dom(ρ) ⊆ dom(ρ′)` is **derived** (`Fig16.ResU.reb_dom_subset`), and its substance — *"the only way for `ρ_f(ℓ)` to not be composable with `ρ(ℓ)` is for `ρ_f(ℓ)` to be own or mut"* — is `Fig16.ResU.frame_cell`, which spends only the printed `#` and carries no added conjunct. The hypothesis is non-vacuous (`Fig16.escrowAgree_self`) and empty off the `own` clause (`Fig16.escrowAgree_of_no_own`, and `Fig16.escrowAgree_walk_of_no_own` in the shape 6.53 and 6.55 take it)  **At the typed world the restriction is discharged at every reborrow 6.150 takes**: `Fig16.LogRel.Typed.rebChooseO_top` and `Fig16.LogRel.Typed.rebChooseO_deep_tw` return `EscrowAgree` at the frame and at the cell for the reborrow they choose, from the tagged world (§12.71)
-/
/-- **`[TR]` Lemma 6.53** (p. 18): if `ρ ∈ reb_β(ρ′)` and `ρf # ℓ ↦ imm(α, ρ′, v)`
then `ρf ▸◂ ρ`.

`[TR]`'s proof: *"Note `dom(ρ) ⊆ dom(ρ′)`, and `ρ|own,mut = ∅`.  For any
`ℓ ∈ dom(ρf) ∩ dom(ρ)`, the only way for `ρf(ℓ)` to not be composable with
`ρ(ℓ)` is for `ρf(ℓ)` to be own or mut.  But since `ρf # ℓ ↦ imm(α, ρ′, v)`, we
know after unfolding and applying lemmas 6.18 and 6.20 and 6.30, that
`ex(ρf)● ▸◂ ⦇ρ′⦈_○`, which means overlapping with an own or mut can never
happen."*

Step for step: the opening note is `ResU.reb_dom_subset`, derived rather than
assumed; "`ρf(ℓ)` is own or mut" is refuted by `ResU.frame_cell`, which is
6.18/6.20/6.30 packaged and spends only the printed `#`; and `ρ|own,mut = ∅`
with the image's shape is `ResU.reb_imm_cell_kw` and `ResU.reb_src`.

What the printed proof does not reach is that `▸◂` between two `imm` cells asks
for an equal **witness** as well.  At the `imm` and `mut` clauses the witness is
read off the source cell and both sides get the same one; at the `own` clause
`reb_α` fabricates it, and that is the branch `hag` closes.  `hag` is the
sentence at `ag(ρ_f)`, which is the level 6.55 spends it at; 6.53's own use
comes back from there through `AgW.get_imm`, `ag(ρ_f)` carrying `ρ_f`'s `imm`
cells at their own locations over their own witnesses.

`[restricted: to `EscrowAgree ρ′ ρ (ag ρ_f)`, the sentence `[TR]` p. 18 asserts
in the proof of 6.55 and `reb_α` does not carry — `docs/adjudications.md` §12.41.
The conclusion is the printed one and `reb_α` is untouched]` -/
theorem ResU.six53 {β : Life} {ρ' ρ ρf : ResU Loc Val} {l₀ : Loc}
    {s : LSet} {v : Val} {hs : ρ'.InStratum s.join}
    (hreb : ResU.Reb β ρ' ρ)
    (hag : ∀ a, AgW ρf a → EscrowAgree ρ' ρ a)
    (hhash : ResU.Hash ρf (ResU.single l₀ (CellU.immOf s v ρ' hs))) :
    ResU.CompatS ρf ρ := by
  obtain ⟨-, ρc, hcomp, hval⟩ := hhash
  obtain ⟨aF, haF⟩ := ResU.agW_of_hash_left hcomp hval
  intro l ψf ψ hf hg
  obtain ⟨φ, hφ⟩ := ResU.reb_dom_subset hreb hg
  obtain ⟨hkf, hef, hwf⟩ := ResU.frame_cell hcomp hval hf hφ
  by_cases hk : φ.kind = Kind.imm
  · -- the `imm` clause: the image cell is `imm` at the source's value and witness
    obtain ⟨hkψ, heψ, hwψ, -⟩ := ResU.reb_imm_cell_kw hreb hg hφ hk
    exact CellU.compatS_of hkf hkψ (hef.trans heψ.symm)
      (hwψ ▸ hwf (by rw [hk]; exact fun hc => Kind.noConfusion hc))
  · obtain ⟨vv, χ, hχs, hψeq, hvv, hor⟩ := ResU.reb_src hreb hg hφ hk
    have hkψ : ψ.kind = Kind.imm := by rw [hψeq]; exact CellU.kind_immOf _ _ _ _
    have hwψ : ψ.wit = χ := by rw [hψeq, CellU.wit_immOf]
    have heψ : ψ.erase = φ.erase := by rw [hψeq, CellU.erase_immOf, hvv]
    by_cases hown : φ.kind = Kind.own
    · -- the `own` clause: the escrow is fabricated, and `hag` is what pins it
      have hφo : ρ'.get l = some (CellU.ownOf φ.erase) :=
        hφ.trans (congrArg some (CellU.eq_ownOf_of_kind hown))
      obtain ⟨χf, hχf, hkχ, -, hwχ⟩ := AgW.get_imm haF hf hkf
      exact CellU.compatS_of hkf hkψ (hef.trans heψ.symm)
        (hwχ.symm.trans (hag aF haF l φ.erase ψ χf hφo hg hχf
          (by rw [hkψ]; exact fun c => Kind.noConfusion c)
          (by rw [hkχ]; exact fun c => Kind.noConfusion c)))
    · -- the `mut` clause: the witness is read off the cell
      have hmut : φ.wit = χ := hor.resolve_left hown
      exact CellU.compatS_of hkf hkψ (hef.trans heψ.symm)
        (by rw [hwψ, ← hmut, hwf hown])

end BoCa.Fig16

alias TR.lemma_6_53 := BoCa.Fig16.ResU.six53

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.54 · `[TR]` p. 18 · `proved`

> If ρ ∈ reb_β(ρ′) and ✓ℓ ↦ imm(α, ρ′, v) then dom(ag(ρ)) ⊆ dom(⦇ρ′⦈_○)

**Printed proof, transcribed.** Unfolding `ρ ∈ reb_β(ρ′)`: `dom(ρ) ⊆ dom(ρ′)`; `ρ∣dom(ρ′∣imm) = ρ′∣imm∣dom(ρ)`; and for every `ℓ ∈ dom(ρ) ∩ dom(ρ′∣own,mut)` there is `ρ″` with `ρ(ℓ) = imm(_, ρ″, _)` and either `ρ″ ≤ ρ′` or `ρ′(ℓ) = mut(_, ρ″, _, _)`, so `dom(⦇ρ″⦈_○) ⊆ dom(⦇ρ′⦈_○)`.  Collecting these, every immutable borrow in `ρ` is in `⦇ρ′⦈_○`, and every witness is also in `⦇ρ⦈_○`.

**Lean.** `BoCa.Fig16.ResU.six54`, alias `TR.lemma_6_54`, tag `[as printed]`.

**Note.** `Fig16.ResU.six54`, on the printed carrier, `[as printed]` — both printed hypotheses verbatim, `ag(ρ)` and `⦇ρ′⦈_○` named by their graphs (G4) and `dom` pointwise. The printed `✓` is spent: it is what makes `⦇ρ′⦈_○` defined (`Fig16.ResU.flatR_of_valid_single_imm`, through `Fig16.AgW.single_imm_inv`), so the conclusion **produces** that object rather than presupposing it, and `Fig16.ResU.FlatR.functional` makes it the only one. **Nothing is added** — in particular `Fig16.EscrowAgree` is not needed here, since 6.54 compares domains and the witness 6.53 has to pin never enters. The three printed bullets are `reb_α`'s own clauses, derived: `Fig16.ResU.reb_dom_subset`, `Fig16.ResU.reb_imm_cell_kw` (the `imm` clause at a subset, definition row 5.28), and `Fig16.ResU.reb_src` with `Fig16.ResU.reb_own_le` for the *"`ρ″ ≤ ρ′`"* disjunct. The printed *"and therefore `dom(⦇ρ″⦈_○) ⊆ dom(⦇ρ′⦈_○)`"* is **proved**, not read off, `⦇−⦈_○` being a walk here: at a `mut` source cell by the factor lemmas `Fig16.ExW.wit_le` and `Fig16.AgW.mut_wit_le`, at the escrow by 6.20 (`Fig16.AgW.split`) for the `ag` half and `Fig16.ExW.dom_le` for the `ex` half — 6.18 cannot serve there, being at `●` on both sides where `ag`'s third piece calls `ex(−)_○`. The row's **closing line** — *"every immutable borrow in `ρ` is in `⦇ρ′⦈_○`, and every witness is also in `⦇ρ⦈_○`"* — says more than the display, and 6.55's first bullet spends it in that stronger form: `Fig16.ResU.ag_cell_of_reb` carries the cells, not just the domains, with the one exception the `own` clause of `reb_α` creates (there the witness is the escrow and `⦇ρ′⦈_○` still has the source's `own` cell). `Fig16.ResU.ag_dom_of_reb` is the display, read off it. New with it: `Fig16.ResU.Under` with `Fig16.ResU.Under.of_factor`/`.compR`/`.bigComp`, `Fig16.ExW.under_le`, `Fig16.BigComp.dom_inv`, `Fig16.ExW.dom_of_ne_imm`, `Fig16.AgW.imm_wit_le`, `Fig16.ResU.FlatR.dom`, `Fig16.ResU.reb_imm_image` and `Fig16.ResU.del_compS`
-/
/-- **`[TR]` Lemma 6.54** (p. 18): if `ρ ∈ reb_β(ρ′)` and `✓ ℓ ↦ imm(α, ρ′, v)`
then `dom(ag(ρ)) ⊆ dom(⦇ρ′⦈_○)`.

Both printed hypotheses are carried verbatim, and the printed `✓` is what makes
`⦇ρ′⦈_○` defined — so the conclusion produces it rather than assuming it, and
`ResU.FlatR.functional` makes that the only one.  `ag(ρ)` is named by its graph
(G4).  Nothing is added: `reb_α`'s three clauses are unfolded, not supplemented,
and `EscrowAgree` is **not** needed here — 6.54 compares domains, and the
witness 6.53 has to pin never enters.
`[as printed]` (`ag(ρ)` and `⦇ρ′⦈_○` appear as their graphs — G4; `dom` is
pointwise) -/
theorem ResU.six54 {β : Life} {ρ' ρ A : ResU Loc Val} {l₀ : Loc} {s : LSet} {v : Val}
    {hs : ρ'.InStratum s.join}
    (hreb : ResU.Reb β ρ' ρ)
    (hval : ResU.Valid (ResU.single l₀ (CellU.immOf s v ρ' hs)))
    (hagρ : AgW ρ A) :
    ∃ f, ResU.FlatR ρ' f ∧ ∀ l ψ, A.get l = some ψ → ∃ φ, f.get l = some φ := by
  obtain ⟨f, hf⟩ := ResU.flatR_of_valid_single_imm hval
  exact ⟨f, hf, fun l ψ hg => ResU.ag_dom_of_reb hreb hagρ hf hg⟩

end BoCa.Fig16

alias TR.lemma_6_54 := BoCa.Fig16.ResU.six54

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.55 · `[TR]` p. 18 · `proved*`

> If ρ ∈ reb_β(ρ′) and ρ_f # ℓ ↦ imm(α, ρ′, v) then ρ_f # ρ.  As a corollary, ρ # ℓ ↦ imm(α, ρ′, v), which follows from setting ρ_f = ℓ ↦ imm(α, ρ′, v).

**Printed proof, transcribed.** Let `ρᵢ = imm(α, ρ′, v)`.  By Lemma 6.53, `ρ_f ▸◂ ρ`, so it suffices that `⦇ρ_f ● ρ⦈` is defined.  Unfolding the hypothesis with Lemmas 6.20 and 6.18 and the definitions of `ex` and `ag`, `⦇ρ_f ● ρᵢ⦈ = ex(ρ_f)_● ● ex(ρᵢ)_● ● (ag(ρ_f) ○ ag(ρᵢ)) = ex(ρ_f)_● ● (ag(ρ_f) ○ ρᵢ ○ ⦇ρ′⦈_○)`, all defined, and Lemma 6.30 with 6.36 gives `ex(ρ_f)_● ▸◂ ρᵢ ○ ⦇ρ′⦈_○`, `▸◂ ρᵢ` and `▸◂ ⦇ρ′⦈_○`.  Unfolding the goal the same way, with `dom(ρ∣own,mut) = ∅`, `⦇ρ_f ● ρ⦈ = ex(ρ_f)_● ● (ag(ρ_f) ○ ag(ρ))`; by Lemma 6.37 it suffices that `ag(ρ_f) ▷◁ ag(ρ)` and `ex(ρ_f)_● ▸◂ ag(ρ)`, and by Lemma 6.54 `dom(ag(ρ)) ⊆ dom(⦇ρ′⦈_○)`.  First, at a location of both, `ag(ρ_f) ▷◁ ⦇ρ′⦈_○`, and unfolding `reb`, `ρ` and `ρ′` differ only by potentially changing from `own` or `mut` to `imm`, "but witnesses and values always stay the same".  Second, `ex(ρ_f)_● ▸◂ ⦇ρ′⦈_○` with `ex(ρ_f)_●∣imm = ∅` makes their domains disjoint, and `dom(ag(ρ)) ⊆ dom(⦇ρ′⦈_○)`.

**Lean.** `BoCa.Fig16.ResU.six55`, alias `TR.lemma_6_55`, tag `[restricted: to `EscrowAgree ρ′ ρ (ag ρ_f)` — the sentence `[TR]`.

**Note.** `Fig16.ResU.six55`, on the printed carrier, conclusion exactly as printed, `[restricted: to `Fig16.EscrowAgree ρ′ ρ (ag ρ_f)` and to `ag(ρ)` being defined]`. The corollary p. 18 states — *"`ρ # ℓ ↦ imm(α, ρ′, v)`, which follows from setting `ρ_f = ℓ ↦ imm(α, ρ′, v)`"* — is `Fig16.ResU.six55_self`, that substitution and 6.2 at `#`. Every step of the printed proof closes: the first display with 6.30 and 6.36 on it is `Fig16.ResU.frame_flat_facts`; *"noting `dom(ρ
-/
/-- **`[TR]` Lemma 6.55** (p. 18): if `ρ ∈ reb_β(ρ′)` and
`ρ_f # ℓ ↦ imm(α, ρ′, v)` then `ρ_f # ρ`.

The printed proof, step for step.  *"By lemma 6.53, `ρ_f ▸◂ ρ`"* is
`ResU.six53`, over the same conjunct.  *"It suffices to show that `⦇ρ_f ● ρ⦈` is
defined"* is `ResU.Flat.split` at `ρ_f ● ρ`, whose factors the printed second
display names: `ex(ρ_f)●` and `ag(ρ_f)` from `ResU.frame_flat_facts`,
`ex(ρ)● = ∅` from `ExW.empty_of_all_imm` with `ResU.reb_imm_image` — the
printed *"noting `dom(ρ|own,mut) = ∅`"* — and `ag(ρ)`.  *"By lemma 6.37 … it
suffices to show `ag(ρ_f) ▷◁ ag(ρ)` and `ex(ρ_f)● ▸◂ ag(ρ)`"* is `ResU.six37`
applied to `ResU.frame_compatR_ag` (the first bullet) and
`ResU.frame_compatS_ag` (the second, which is where 6.54 is spent), with
`ex(ρ_f)● ▸◂ ag(ρ_f)` the third side of 6.37 and again from
`ResU.frame_flat_facts`.  6.9 (`ResU.compS_defined_iff`,
`ResU.compR_defined_iff`) turns each `▸◂`/`▷◁` back into the composite the
display needs.

`A` names `ag(ρ)` by its graph (G4), and `AgW ρ A` is a genuine restriction: the
printed proof writes `ag(ρ_f) ▷◁ ag(ρ)`, which presupposes that walk has a
value, and no printed hypothesis says so.  `ag(ρ_f)` is *not* a restriction —
`ResU.agW_of_hash_left` produces it from the printed `#`.

`[restricted: to `EscrowAgree ρ′ ρ (ag ρ_f)` — the sentence `[TR]` p. 18 asserts
inside this very proof, `docs/adjudications.md` §12.41 — and to `ag(ρ)` being
defined, which the printed proof's own `ag(ρ_f) ▷◁ ag(ρ)` presupposes
(convention F1).  The conclusion is the printed one and `reb_α` is untouched]` -/
theorem ResU.six55 {β : Life} {ρ' ρ ρf A : ResU Loc Val} {l₀ : Loc}
    {s : LSet} {v : Val} {hs : ρ'.InStratum s.join}
    (hreb : ResU.Reb β ρ' ρ)
    (hesc : ∀ a, AgW ρf a → EscrowAgree ρ' ρ a)
    (hagρ : AgW ρ A)
    (hhash : ResU.Hash ρf (ResU.single l₀ (CellU.immOf s v ρ' hs))) :
    ResU.Hash ρf ρ := by
  have hcs : ResU.CompatS ρf ρ := ResU.six53 hreb hesc hhash
  obtain ⟨-, ρc, hcomp, hval⟩ := hhash
  obtain ⟨e₁, aF, f, hex, haF, hfl, hEA, hEF, hAF⟩ := ResU.frame_flat_facts hcomp hval
  have hb1 : ResU.CompatR aF A :=
    ResU.frame_compatR_ag hreb hagρ hfl hAF (hesc aF haF)
  have hb2 : ResU.CompatS e₁ A := ResU.frame_compatS_ag hreb hex hfl hEF hagρ
  obtain ⟨aa, haa⟩ := (ResU.compR_defined_iff aF A).mpr hb1
  obtain ⟨σ, hσ⟩ := (ResU.compS_defined_iff e₁ aa).mpr (ResU.six37 hEA hb2 haa)
  obtain ⟨w, hw⟩ := (ResU.compS_defined_iff ρf ρ).mpr hcs
  exact ⟨hcs, w, hw, σ, (ResU.Flat.split hw).mpr ⟨e₁, PMap.empty, e₁, aF, A, aa,
    hex, ExW.empty_of_all_imm (fun m ψ h => ResU.reb_imm_image hreb h),
    ResU.comp_empty_right e₁, haF, hagρ, haa, hσ⟩⟩

end BoCa.Fig16

alias TR.lemma_6_55 := BoCa.Fig16.ResU.six55

namespace BoCa.Fig16
variable {Loc Val : Type}

/-! `[about ours]` — what the Lean of Lemma 6.56 needs; the paper prints nothing here. -/
/-- **`[TR]` 6.55's corollary** (p. 18): *"As a corollary, `ρ # ℓ ↦ imm(α, ρ′, v)`,
which follows from setting `ρ_f = ℓ ↦ imm(α, ρ′, v)`."*  That substitution and
6.2 at `#` (`ResU.hash_symm`) are the whole of it; the printed hypothesis, at
that `ρ_f`, is `ℓ ↦ imm(α, ρ′, v) # ℓ ↦ imm(α, ρ′, v)`.
`[restricted: as `ResU.six55`, of which this is the printed instance]` -/
theorem ResU.six55_self {β : Life} {ρ' ρ A : ResU Loc Val} {l₀ : Loc}
    {s : LSet} {v : Val} {hs : ρ'.InStratum s.join}
    (hreb : ResU.Reb β ρ' ρ)
    (hesc : ∀ a, AgW (ResU.single l₀ (CellU.immOf s v ρ' hs)) a → EscrowAgree ρ' ρ a)
    (hagρ : AgW ρ A)
    (hhash : ResU.Hash (ResU.single l₀ (CellU.immOf s v ρ' hs))
      (ResU.single l₀ (CellU.immOf s v ρ' hs))) :
    ResU.Hash ρ (ResU.single l₀ (CellU.immOf s v ρ' hs)) :=
  ResU.hash_symm (ResU.six55 hreb hesc hagρ hhash)

/-- **`ρ_i # ρ_i` from `✓ρ_i`** — 6.43 (`ResU.compS_single_imm`) at one cell with
`LSet.union_self`, which is what `[TR]` 6.55's corollary needs of its printed
hypothesis when `ρ_f` is set to `ρ_i`.
`[about ours: the printed `✓` of 6.55's corollary, in `#` form]` -/
theorem ResU.hash_self_single_imm {l₀ : Loc} {s : LSet} {v : Val}
    {ρ' : ResU Loc Val} {hs : ρ'.InStratum s.join}
    (hval : ResU.Valid (ResU.single l₀ (CellU.immOf s v ρ' hs))) :
    ResU.Hash (ResU.single l₀ (CellU.immOf s v ρ' hs))
      (ResU.single l₀ (CellU.immOf s v ρ' hs)) := by
  have h₃ : ρ'.InStratum (s ∪ s).join := ResU.InStratum.sup hs hs
  have e : CellU.immOf (s ∪ s) v ρ' h₃ = CellU.immOf s v ρ' hs :=
    CellU.immOf_congr (LSet.union_self s) rfl rfl h₃ hs
  have hcomp := ResU.compS_single_imm l₀ s s v ρ' hs hs h₃
  rw [e] at hcomp
  exact ⟨hcomp.1, _, hcomp, hval⟩

/-!
## Lemma 6.56 · `[TR]` p. 19 · `proved*`

> If ρ ∈ reb_β(ρ′) and ✓(ℓ ↦ imm(α, ρ′, v)) then ⟦ρ∣dom(ρ′∣mut,own) ● ℓ ↦ imm(α, ρ′, v)⟧ = ⟦ℓ ↦ imm(α, ρ′, v)⟧

**Printed proof, transcribed.** By Lemma 6.55, `ρ # ℓ ↦ imm(α, ρ′, v)`; by Lemma 6.11, `ρ∣dom(ρ′∣mut,own) # ℓ ↦ imm(α, ρ′, v)`.  Pointwise: unfolding `⟦−⟧`, `⦇−⦈`, `ex` and `ag` and by Lemma 6.20, `⦇ρ∣dom(ρ′∣mut,own) ● ℓ ↦ imm(α, ρ′, v)⦈ = ag(ρ∣dom(ρ′∣mut,own) ● ℓ ↦ imm(α, ρ′, v)) = ag(ρ∣dom(ρ′∣mut,own)) ○ ℓ ↦ imm(α, ρ′, v) ○ ⦇ρ′⦈_○`.  By Lemma 6.54, `dom(⦇ρ∣dom(ρ′∣mut,own)⦈) ⊆ dom(⦇ρ′⦈)`; values and witnesses agree because `ρ∣dom(ρ′∣mut,own) # ℓ ↦ imm(α, ρ′, v)`, so the erasures agree.

**Lean.** `BoCa.Fig16.ResU.six56`, alias `TR.lemma_6_56`.

**Note.** `Fig16.ResU.six56`, on the printed carrier, conclusion exactly as printed, `[restricted: as 6.55, which it spends — to `Fig16.EscrowAgree ρ′ ρ (ag ρ_i)` and to `ag(ρ)` being defined]`. Both printed hypotheses are carried verbatim. The printed `=` is between two partial terms and is carried as one, the `↔` between the two graphs at an arbitrary common result — the shape 6.7 and 6.8 already use (`Fig16.ResU.Lower.congr`); `ρ
-/
/-- **`[TR]` Lemma 6.56** (p. 18): if `ρ ∈ reb_β(ρ′)` and `✓(ℓ ↦ imm(α, ρ′, v))`
then `⟦ρ|dom(ρ′|mut,own) ● ℓ ↦ imm(α, ρ′, v)⟧ = ⟦ℓ ↦ imm(α, ρ′, v)⟧`.

The printed equality is between two partial terms and is carried as one, the
`↔` between the two graphs at an arbitrary common result — the shape 6.7 and 6.8
already use (`ResU.Lower.congr`).  `ρ|dom(ρ′|mut,own) ● ρ_i` is named by its
graph (G4).

`[restricted: as `ResU.six55`, which this spends: to `EscrowAgree ρ′ ρ (ag ρ_i)`
and to `ag(ρ)` being defined.  The printed `✓` and `ρ ∈ reb_β(ρ′)` are carried
verbatim and the conclusion is the printed one]` -/
theorem ResU.six56 {β : Life} {ρ' ρ A X : ResU Loc Val} {l₀ : Loc} {s : LSet}
    {v : Val} {hs : ρ'.InStratum s.join} {w : Loc → Option Val}
    (hreb : ResU.Reb β ρ' ρ)
    (hesc : ∀ a, AgW (ResU.single l₀ (CellU.immOf s v ρ' hs)) a → EscrowAgree ρ' ρ a)
    (hagρ : AgW ρ A)
    (hval : ResU.Valid (ResU.single l₀ (CellU.immOf s v ρ' hs)))
    (hX : ResU.CompS (ρ.restrictDom (ρ'.exclPart))
        (ResU.single l₀ (CellU.immOf s v ρ' hs)) X) :
    ResU.Lower X w ↔
      ResU.Lower (ResU.single l₀ (CellU.immOf s v ρ' hs)) w := by
  -- `ρ_i # ρ_i`, from the printed `✓` and 6.43.
  -- 6.55's corollary, then 6.11.
  have hρi := ResU.six55_self hreb hesc hagρ (ResU.hash_self_single_imm hval)
  have hspl := ResU.restrictDom_compS ρ (ρ'.exclPart)
  obtain ⟨-, τX, hτX, hvX⟩ := (ResU.Hash.split hspl hρi).1
  rw [ResU.CompS.functional hτX hX] at hvX
  -- `ex(−)●` is `∅` on both sides of the display.
  have himmi : ∀ l ψ, (ResU.single l₀ (CellU.immOf s v ρ' hs)).get l = some ψ →
      ψ.kind = Kind.imm := by
    intro l ψ h
    obtain ⟨-, rfl⟩ := ResU.single_get_eq_some h
    exact CellU.kind_immOf _ _ _ _
  have hallX : ∀ l ψ, X.get l = some ψ → ψ.kind = Kind.imm := by
    intro l ψ he
    rcases hX.get l with ⟨-, -, e⟩ | ⟨ζ, e₁, -, e⟩ | ⟨ζ, -, e₂, e⟩ |
        ⟨ζ₁, ζ₂, ζ, e₁, e₂, e, hC⟩
    · rw [e] at he; exact absurd he (by simp)
    · rw [show ψ = ζ from Option.some.inj (he.symm.trans e)]
      exact ResU.reb_imm_image hreb (ResU.restrictDom_get_inv e₁)
    · rw [show ψ = ζ from Option.some.inj (he.symm.trans e)]
      exact himmi l ζ e₂
    · rw [show ψ = ζ from Option.some.inj (he.symm.trans e)]
      exact CellU.CompS.kind hC
  have hei0 : ExS (ResU.single l₀ (CellU.immOf s v ρ' hs)) PMap.empty :=
    ExW.empty_of_all_imm himmi
  have heX0 : ExS X PMap.empty := ExW.empty_of_all_imm hallX
  -- `ag(ρ_i) = ρ_i ○ ⦇ρ′⦈_○`, and `ag(X) = ag(ρ|dom(σ)) ○ ag(ρ_i)`.
  obtain ⟨-, -, ai, -, hai, -⟩ := hval
  obtain ⟨-, -, aX, -, haX, -⟩ := hvX
  obtain ⟨ev, av, f, hev, hav, hf, hagi⟩ := AgW.single_imm_inv hai
  have hflR : ResU.FlatR ρ' f := ⟨av, ev, hav, hev, ResU.CompR.comm hf⟩
  obtain ⟨aD, ai', haD, hai', hcD⟩ := (AgW.split hX).mp haX
  rw [AgW.functional hai' hai] at hcD
  -- 6.54: the extra factor adds no location.
  have hdomD : ∀ l ζ, aD.get l = some ζ → ∃ φ, ai.get l = some φ := by
    intro l ζ hζ
    obtain ⟨aD₂, aR, haD₂, -, hcA⟩ := (AgW.split hspl).mp hagρ
    obtain rfl : aD₂ = aD := AgW.functional haD₂ haD
    obtain ⟨φA, hφA⟩ := hcA.dom_left hζ
    obtain ⟨φf, hφf⟩ := ResU.ag_dom_of_reb hreb hagρ hflR hφA
    exact hagi.dom_right hφf
  -- …and changes no erasure.
  have hmaps : ∀ l, (aX.get l).map CellU.erase = (ai.get l).map CellU.erase := by
    intro l
    rcases hcD.get l with ⟨-, e₂, e⟩ | ⟨ζ, e₁, e₂, -⟩ | ⟨ζ, -, e₂, e⟩ |
        ⟨ζ₁, ζ₂, ζ, -, e₂, e, hC⟩
    · rw [e, e₂]
    · obtain ⟨φ, hφ⟩ := hdomD l ζ e₁
      rw [e₂] at hφ
      exact absurd hφ (by simp)
    · rw [e, e₂]
    · rw [e, e₂]
      show some ζ.erase = some ζ₂.erase
      rw [CellU.CompR.erase_right hC]
  have hflatX : ResU.Flat X aX :=
    ⟨PMap.empty, aX, heX0, haX, ResU.CompS.comm (ResU.comp_empty_right aX)⟩
  have hflati : ResU.Flat (ResU.single l₀ (CellU.immOf s v ρ' hs)) ai :=
    ⟨PMap.empty, ai, hei0, hai, ResU.CompS.comm (ResU.comp_empty_right ai)⟩
  constructor
  · rintro ⟨σ, hσ, hm⟩
    refine ⟨ai, hflati, fun l => ?_⟩
    rw [hm l, ResU.Flat.functional hσ hflatX]
    exact hmaps l
  · rintro ⟨σ, hσ, hm⟩
    refine ⟨aX, hflatX, fun l => ?_⟩
    rw [hm l, ResU.Flat.functional hσ hflati]
    exact (hmaps l).symm

end BoCa.Fig16

alias TR.lemma_6_56 := BoCa.Fig16.ResU.six56

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.57 · `[TR]` p. 19 · `proved*`

> Let ρᵢ = ℓ ↦ imm(α, ρ′ᵢ, v). If ρ ∈ reb_β(ρ′ᵢ), then ⦇ρ∣dom(ρ′ᵢ∣imm) ● ρᵢ⦈ = ⦇ρᵢ⦈

**Printed proof, transcribed.** Unfolding `reb`, `ρ∣dom(ρ′ᵢ∣imm) ≤ ρ′ᵢ∣imm` and `ρ∣dom(ρ′ᵢ∣imm)∣mut,own = ∅`.  Writing `D = dom(ρ′ᵢ∣imm)` and unfolding `⦇−⦈`, `ex`, `ag` with Lemma 6.20: `⦇ρ∣D ● ρᵢ⦈ = ex(ρ∣D ● ρᵢ)_● ● ag(ρ∣D ● ρᵢ) = ag(ρ∣D ● ρᵢ) = ag(ρ∣D) ○ ag(ρᵢ) = ag(ρ∣D) ○ ρᵢ ○ ⦇ρ′ᵢ⦈_○ = ag(ρ∣D) ○ ⦇ρ′ᵢ∣imm⦈_○ ○ ρᵢ ○ ⦇ρ′ᵢ∣mut,own⦈_○ = ⦇ρ′ᵢ∣imm⦈_○ ○ ρᵢ ○ ⦇ρ′ᵢ∣mut,own⦈_○ = ρᵢ ○ ⦇ρ′ᵢ⦈_○ = ag(ρᵢ) = ⦇ρᵢ⦈`.

**Lean.** `BoCa.Fig16.ResU.six57`, alias `TR.lemma_6_57`.

**Note.** `Fig16.ResU.six57`, on the printed carrier, conclusion exactly as printed, `[restricted: to `ag(ρ)` being defined]`. The printed `ρ ∈ reb_β(ρ′ᵢ)` is carried verbatim and **`Fig16.EscrowAgree` is not needed** — 6.57 spends neither 6.53 nor 6.55. Neither hypothesis says either side of the printed `=` is defined, so it is carried as the Kleene equality, the `↔` between the two graphs at an arbitrary common result; `ρ
-/
/-- **`[TR]` Lemma 6.57** (p. 18): let `ρᵢ = ℓ ↦ imm(α, ρ′ᵢ, v)`; if
`ρ ∈ reb_β(ρ′ᵢ)` then `⦇ρ|dom(ρ′ᵢ|imm) ● ρᵢ⦈ = ⦇ρᵢ⦈`.

The printed `=` is between two partial terms and neither hypothesis says either
is defined, so it is carried as the Kleene equality — the `↔` between the two
graphs at an arbitrary common result.  `ρ|dom(ρ′ᵢ|imm) ● ρᵢ` is named by its
graph (G4).

The printed display, step for step: `ex(−)●` is `∅` on both sides, both
resources carrying `imm` cells only (`ExW.empty_of_all_imm`, with
`ResU.reb_imm_image`), which is the printed second line; 6.20 (`AgW.split`) is
the third; and the last six lines carry `ag(ρ|D)` through a split of `⦇ρ′ᵢ⦈_○`
only to drop it against the `imm` half.  What that does is **absorption**, and
absorption at `○` is 6.3 with 6.19 (`ResU.CompR.absorb`), so it is done here
directly and `[TR]` 6.18 is not called at `○`, where it is not printed.

`ρ|D ≤ ρ′ᵢ|imm` is derived (`ResU.restrictDom_compR_restrict`), and the three
pieces of `ag(ρ|D)` — the restriction itself, the empty `mut` family, and each
entry of the `imm` family — are each `○`-factors of `ag(ρᵢ)`, so each absorbs it
and `ResU.CompR.absorb_comp` and `BigComp.absorb` carry that to the whole.

`A` names `ag(ρ)` by its graph (G4), and `AgW ρ A` is what says the printed
`ag(ρ|dom(ρ′ᵢ|imm))` has a value at all: by 6.20 at
`ρ = ρ|dom(σ) ● ρ/dom(σ)` it delivers `ag(ρ|D)`, and no printed hypothesis
delivers it otherwise.

`[restricted: to `ag(ρ)` being defined, which the printed display's
`ag(ρ|dom(ρ′ᵢ|imm))` presupposes (convention F1).  `ρ ∈ reb_β(ρ′ᵢ)` is carried
verbatim, the conclusion is the printed one, and `reb_α` is untouched.
`EscrowAgree` is **not** needed: 6.57 spends neither 6.53 nor 6.55]` -/
theorem ResU.six57 {β : Life} {ρ'i ρ A X σ : ResU Loc Val} {l₀ : Loc} {s : LSet}
    {v : Val} {hs : ρ'i.InStratum s.join}
    (hreb : ResU.Reb β ρ'i ρ)
    (hagρ : AgW ρ A)
    (hX : ResU.CompS (ρ.restrictDom (ρ'i.restrict Kind.imm))
        (ResU.single l₀ (CellU.immOf s v ρ'i hs)) X) :
    ResU.Flat X σ ↔ ResU.Flat (ResU.single l₀ (CellU.immOf s v ρ'i hs)) σ := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  have himmi : ∀ l ψ, (ResU.single l₀ (CellU.immOf s v ρ'i hs)).get l = some ψ →
      ψ.kind = Kind.imm := by
    intro l ψ h
    obtain ⟨-, rfl⟩ := ResU.single_get_eq_some h
    exact CellU.kind_immOf _ _ _ _
  have hallX : ∀ l ψ, X.get l = some ψ → ψ.kind = Kind.imm := by
    intro l ψ he
    rcases hX.get l with ⟨-, -, e⟩ | ⟨ζ, e₁, -, e⟩ | ⟨ζ, -, e₂, e⟩ |
        ⟨ζ₁, ζ₂, ζ, e₁, e₂, e, hC⟩
    · rw [e] at he; exact absurd he (by simp)
    · rw [show ψ = ζ from Option.some.inj (he.symm.trans e)]
      exact ResU.reb_imm_image hreb (ResU.restrictDom_get_inv e₁)
    · rw [show ψ = ζ from Option.some.inj (he.symm.trans e)]
      exact himmi l ζ e₂
    · rw [show ψ = ζ from Option.some.inj (he.symm.trans e)]
      exact CellU.CompS.kind hC
  have hFlat : ∀ Y : ResU Loc Val, ExS Y PMap.empty → ∀ τ,
      ResU.Flat Y τ ↔ AgW Y τ := by
    intro Y hY τ
    constructor
    · rintro ⟨e, a, he, ha, hcs⟩
      rw [ExS.functional he hY] at hcs
      rw [ResU.CompS.functional hcs (ResU.CompS.comm (ResU.comp_empty_right a))]
      exact ha
    · intro ha
      exact ⟨PMap.empty, τ, hY, ha, ResU.CompS.comm (ResU.comp_empty_right τ)⟩
  rw [hFlat X (ExW.empty_of_all_imm hallX) σ,
    hFlat _ (ExW.empty_of_all_imm himmi) σ, AgW.split hX]
  -- `ag(ρ|D)` has a value, by 6.20 at `ρ = ρ|dom(σ) ● ρ/dom(σ)`.
  have hspl := ResU.restrictDom_compS ρ (ρ'i.restrict Kind.imm)
  obtain ⟨aD, aR, haD, -, -⟩ := (AgW.split hspl).mp hagρ
  -- …and it absorbs `ag(ρᵢ)`.
  have habs : ∀ a₂, AgW (ResU.single l₀ (CellU.immOf s v ρ'i hs)) a₂ →
      ResU.CompR aD a₂ a₂ := fun a₂ ha₂ => ResU.reb_immPart_ag_absorbs hreb haD ha₂
  constructor
  · rintro ⟨σ₁, σ₂, h₁, h₂, hc⟩
    rw [AgW.functional h₁ haD] at hc
    rw [ResU.CompR.functional hc (habs σ₂ h₂)]
    exact h₂
  · intro h₂
    exact ⟨aD, σ, haD, h₂, habs σ h₂⟩

end BoCa.Fig16

alias TR.lemma_6_57 := BoCa.Fig16.ResU.six57

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.58 · `[TR]` p. 19 · `proved*`

> Let ρᵢ = ℓ ↦ imm(α, ρ′ᵢ, v). If ρ ∈ reb_β(ρ′ᵢ), ρ ● ρ_b ↭ ρ′ ● ρ⁺, @ρ_b ⊐ β, @ρ′ ⊐ β, ρ_b # ρᵢ, and ρ′ ● ρ⁺ # ρᵢ, then ⟦ρ ● ρ_b ● ρᵢ⟧ = ⟦ρ_b ● ρᵢ⟧ and ⟦ρ′ ● ρ⁺ ● ρᵢ⟧ = ⟦ρ′ ● (ρ⁺ ⊟ ρ∣dom(ρ′ᵢ∣mut,own)) ● ρᵢ⟧

**Printed proof, transcribed.** By Lemma 6.56, (H1) `⟦ρ∣dom(ρ′ᵢ∣mut,own) ● ρᵢ⟧ = ⟦ρᵢ⟧`.  `dom(ρ) ⊆ dom(ρ′ᵢ)` by unfolding `reb`, and by Lemma 6.8, rewriting with H1, `⟦ρ ● ρᵢ⟧ = ⟦ρ∣dom(ρ′ᵢ∣imm) ● ρ∣dom(ρ′ᵢ∣mut,own) ● ρᵢ⟧ = ⟦ρ∣dom(ρ′ᵢ∣imm) ● ρᵢ⟧`.  By Lemma 6.57 `⦇ρᵢ⦈ = ⦇ρ∣dom(ρ′ᵢ∣imm) ● ρᵢ⦈`, so `⟦ρᵢ⟧ = ⟦ρ∣dom(ρ′ᵢ∣imm) ● ρᵢ⟧`, which with the equation above gives (H2) `⟦ρ ● ρᵢ⟧ = ⟦ρᵢ⟧`.  The first conclusion is Lemma 6.8 with H2.  By Lemma 6.52, `ρ⁺ = (ρ⁺ ⊟ ρ∣dom(ρ′ᵢ∣mut,own)) ● ρ∣dom(ρ′ᵢ∣mut,own)`; rewriting, `⟦ρ′ ● ρ⁺ ● ρᵢ⟧ = ⟦ρ′ ● (ρ⁺ ⊟ ρ∣dom(ρ′ᵢ∣mut,own)) ● ρ∣dom(ρ′ᵢ∣mut,own) ● ρᵢ⟧`, and by that equation and Lemma 6.8 the second conclusion reduces to H1.

**Lean.** `BoCa.Fig16.ResU.six58_left`, alias `TR.lemma_6_58_left`; `BoCa.Fig16.ResU.six58_right`, alias `TR.lemma_6_58_right`, tag `[restricted: to the **second** of the two printed conclusions; to `[TR]`.

**Note.** `Fig16.ResU.six58_left` and `Fig16.ResU.six58_right`, on the printed carrier, the two printed conclusions exactly as printed. Each `⟦−⟧` equality is between partial terms and is carried as the `↔` between the two graphs at an arbitrary common result, and every composite the statements name appears as its graph (G4). `[restricted: to `Fig16.EscrowAgree ρ′ᵢ ρ (ag ρ_i)` and to `ag(ρ)` being defined, as 6.55/6.56/6.57; and for `six58_right`, to `[TR]` 6.52's equation]`. The printed proof is followed step for step: *"note `dom(ρ) ⊆ dom(ρ′ᵢ)` by unfolding reb"* with `ρ = ρ
-/
/-- **`[TR]` Lemma 6.58's first conclusion** (p. 19):
`⟦ρ ● ρ_b ● ρᵢ⟧ = ⟦ρ_b ● ρᵢ⟧`.

The printed proof: *"By lemma 6.56, `⟦ρ|dom(ρ′ᵢ|mut,own) ● ρᵢ⟧ = ⟦ρᵢ⟧` (H1).
Note `dom(ρ) ⊆ dom(ρ′ᵢ)` by unfolding reb.  By lemma 6.8 and rewriting with H1,
`⟦ρ ● ρᵢ⟧ = ⟦ρ|dom(ρ′ᵢ|imm) ● ρ|dom(ρ′ᵢ|mut,own) ● ρᵢ⟧ = ⟦ρ|dom(ρ′ᵢ|imm) ● ρᵢ⟧`.
By lemma 6.57 `⦇ρᵢ⦈ = ⦇ρ|dom(ρ′ᵢ|imm) ● ρᵢ⦈`, … means `⟦ρ ● ρᵢ⟧ = ⟦ρᵢ⟧` (H2).
To show `⟦ρ ● ρ_b ● ρᵢ⟧ = ⟦ρ_b ● ρᵢ⟧`, by lemma 6.8, it suffices to show
`⟦ρ ● ρᵢ⟧ = ⟦ρᵢ⟧`, which we have by H2."*

Run here exactly so: `ResU.restrictDom_split` is the note, `ResU.six56` is H1,
`ResU.six57` is the appeal to 6.57, and `ResU.lower_congr_iff` is 6.8 at both
applications, with 6.11 (`ResU.Hash.split`) and 6.15
(`ResU.hash_of_pairwise`) supplying its `#`s from the printed ones.  6.3
(`ResU.CompS.assoc`) is the rebracketing each display line does.

Of 6.58's six printed hypotheses this conclusion spends three — `ρ ∈ reb_β(ρ′ᵢ)`,
`ρ_b # ρᵢ`, and the left half of `ρ ● ρ_b ↭ ρ′ ● ρ⁺`, which is `ρ # ρ_b` — so
the other three are dropped rather than bound (convention 5: ours is the
stronger statement).

`[restricted: to the **first** of the two printed conclusions, and as 6.55/6.56
— to `EscrowAgree ρ′ᵢ ρ (ag ρ_i)` and to `ag(ρ)` being defined.  The three
printed hypotheses this half does not use are dropped]` -/
theorem ResU.six58_left {β : Life} {ρ'i ρ ρb A ρρb X Y : ResU Loc Val}
    {l₀ : Loc} {s : LSet} {v : Val} {hs : ρ'i.InStratum s.join}
    (hreb : ResU.Reb β ρ'i ρ)
    (hesc : ∀ a, AgW (ResU.single l₀ (CellU.immOf s v ρ'i hs)) a →
      EscrowAgree ρ'i ρ a)
    (hagρ : AgW ρ A)
    (hρb : ResU.Hash ρ ρb)
    (hbi : ResU.Hash ρb (ResU.single l₀ (CellU.immOf s v ρ'i hs)))
    (hrb : ResU.CompS ρ ρb ρρb)
    (hX : ResU.CompS ρρb (ResU.single l₀ (CellU.immOf s v ρ'i hs)) X)
    (hY : ResU.CompS ρb (ResU.single l₀ (CellU.immOf s v ρ'i hs)) Y) :
    ∀ w, ResU.Lower X w ↔ ResU.Lower Y w := by
  have hvi : (ResU.single l₀ (CellU.immOf s v ρ'i hs)).Valid := by
    obtain ⟨τ, hτ, hv⟩ := hbi.2
    exact (ResU.Valid.split hτ hv).2
  have hρi := ResU.six55_self hreb hesc hagρ (ResU.hash_self_single_imm hvi)
  have hsp := ResU.restrictDom_split hreb
  obtain ⟨hDiρi, hDmρi⟩ := ResU.Hash.split hsp hρi
  have hvρ : ρ.Valid := by
    obtain ⟨τ, hτ, hv⟩ := hρi.2
    exact (ResU.Valid.split hτ hv).1
  have hDiDm : ResU.Hash (ρ.restrictDom (ρ'i.restrict Kind.imm))
      (ρ.restrictDom ρ'i.exclPart) := ⟨hsp.1, ρ, hsp, hvρ⟩
  obtain ⟨Zm, hZm, -⟩ := hDmρi.2
  obtain ⟨Zi, hZi, -⟩ := hDiρi.2
  have H1 : ∀ w, ResU.Lower Zm w ↔
      ResU.Lower (ResU.single l₀ (CellU.immOf s v ρ'i hs)) w :=
    fun w => ResU.six56 hreb hesc hagρ hvi hZm
  have H57 : ∀ w, ResU.Lower Zi w ↔
      ResU.Lower (ResU.single l₀ (CellU.immOf s v ρ'i hs)) w := by
    refine fun w => ⟨?_, ?_⟩
    · rintro ⟨σ, hσ, hm⟩; exact ⟨σ, (ResU.six57 hreb hagρ hZi).mp hσ, hm⟩
    · rintro ⟨σ, hσ, hm⟩; exact ⟨σ, (ResU.six57 hreb hagρ hZi).mpr hσ, hm⟩
  have hDiZm := ResU.hash_of_pairwise hDiDm hDmρi hDiρi hZm
  obtain ⟨W, hW⟩ :=
    (ResU.compS_defined_iff (ρ.restrictDom (ρ'i.restrict Kind.imm)) Zm).mpr hDiZm.1
  have H8a := ResU.lower_congr_iff H1 hW hDiZm hZi hDiρi
  obtain ⟨R, hR⟩ :=
    (ResU.compS_defined_iff ρ (ResU.single l₀ (CellU.immOf s v ρ'i hs))).mpr hρi.1
  have hWR : W = R := by
    obtain ⟨y, hy, hyR⟩ :=
      (ResU.CompS.assoc (ρ.restrictDom (ρ'i.restrict Kind.imm))
        (ρ.restrictDom ρ'i.exclPart) (ResU.single l₀ (CellU.immOf s v ρ'i hs)) W).mp
        ⟨Zm, hZm, hW⟩
    rw [ResU.CompS.functional hy hsp] at hyR
    exact ResU.CompS.functional hyR hR
  have H2 : ∀ w, ResU.Lower R w ↔
      ResU.Lower (ResU.single l₀ (CellU.immOf s v ρ'i hs)) w := by
    rw [← hWR]
    exact fun w => (H8a w).trans (H57 w)
  have hbR := ResU.hash_of_pairwise (ResU.hash_symm hρb) hρi hbi hR
  obtain ⟨V, hV⟩ := (ResU.compS_defined_iff ρb R).mpr hbR.1
  have H8b := ResU.lower_congr_iff H2 hV hbR hY hbi
  have hVX : V = X := by
    obtain ⟨y, hy, hyV⟩ :=
      (ResU.CompS.assoc ρb ρ (ResU.single l₀ (CellU.immOf s v ρ'i hs)) V).mp ⟨R, hR, hV⟩
    rw [ResU.CompS.functional hy (ResU.CompS.comm hrb)] at hyV
    exact ResU.CompS.functional hyV hX
  rw [← hVX]
  exact H8b

end BoCa.Fig16

alias TR.lemma_6_58_left := BoCa.Fig16.ResU.six58_left

namespace BoCa.Fig16
variable {Loc Val : Type}

/-! Lemma 6.58, continued. -/
/-- **`[TR]` Lemma 6.58's second conclusion** (p. 19):
`⟦ρ′ ● ρ⁺ ● ρᵢ⟧ = ⟦ρ′ ● (ρ⁺ ⊟ ρ|dom(ρ′ᵢ|mut,own)) ● ρᵢ⟧`.

The printed proof: *"By lemma 6.52,
`ρ⁺ = (ρ⁺ ⊟ ρ|dom(ρ′ᵢ|mut,own)) ● ρ|dom(ρ′ᵢ|mut,own)`.  Rewriting with this
equation … by the previous equation and lemma 6.8, it suffices to show
`⟦ρ|dom(ρ′ᵢ|mut,own) ● ρᵢ⟧ = ⟦ρᵢ⟧`, which we have by H1."*

6.52's equation is taken here as the named hypothesis `hsplit`, which is the
only thing the printed proof spends it for; `ResU.six52` discharges it of the
`χ` it builds, and `ResU.sub_underdetermined` says why it is not a consequence
of `_hsub` alone.  `_hsub` is not spent: it is what
makes `χ` the printed `ρ⁺ ⊟ ρ|dom(ρ′ᵢ|mut,own)` rather than an arbitrary
splitting of `ρ⁺`, so it is carried to keep the conclusion the printed one.

`[restricted: to the **second** of the two printed conclusions; to `[TR]` 6.52's
equation, taken as a hypothesis at the `χ` the statement binds; and as
6.55/6.56 — to `EscrowAgree ρ′ᵢ ρ (ag ρ_i)` and to `ag(ρ)` being defined]` -/
theorem ResU.six58_right {β : Life} {ρ'i ρ ρ'' ρp χ A ρ'p ρ'χ P Q : ResU Loc Val}
    {l₀ : Loc} {s : LSet} {v : Val} {hs : ρ'i.InStratum s.join}
    (hreb : ResU.Reb β ρ'i ρ)
    (hesc : ∀ a, AgW (ResU.single l₀ (CellU.immOf s v ρ'i hs)) a →
      EscrowAgree ρ'i ρ a)
    (hagρ : AgW ρ A)
    (hpi : ResU.Hash ρ'p (ResU.single l₀ (CellU.immOf s v ρ'i hs)))
    (hcp : ResU.CompS ρ'' ρp ρ'p)
    (_hsub : ResU.Sub ρp (ρ.restrictDom ρ'i.exclPart) χ)
    (hsplit : ResU.CompS χ (ρ.restrictDom ρ'i.exclPart) ρp)
    (hcχ : ResU.CompS ρ'' χ ρ'χ)
    (hP : ResU.CompS ρ'p (ResU.single l₀ (CellU.immOf s v ρ'i hs)) P)
    (hQ : ResU.CompS ρ'χ (ResU.single l₀ (CellU.immOf s v ρ'i hs)) Q) :
    ∀ w, ResU.Lower P w ↔ ResU.Lower Q w := by
  have hvi : (ResU.single l₀ (CellU.immOf s v ρ'i hs)).Valid := by
    obtain ⟨τ, hτ, hv⟩ := hpi.2
    exact (ResU.Valid.split hτ hv).2
  have hρi := ResU.six55_self hreb hesc hagρ (ResU.hash_self_single_imm hvi)
  obtain ⟨-, hDmρi⟩ := ResU.Hash.split (ResU.restrictDom_split hreb) hρi
  obtain ⟨Zm, hZm, -⟩ := hDmρi.2
  have H1 : ∀ w, ResU.Lower Zm w ↔
      ResU.Lower (ResU.single l₀ (CellU.immOf s v ρ'i hs)) w :=
    fun w => ResU.six56 hreb hesc hagρ hvi hZm
  -- `ρ′ ● ρ⁺ = (ρ′ ● χ) ● ρ|dom(ρ′ᵢ|mut,own)`
  have hmid : ResU.CompS ρ'χ (ρ.restrictDom ρ'i.exclPart) ρ'p := by
    obtain ⟨y, hy, hyp⟩ :=
      (ResU.CompS.assoc ρ'' χ (ρ.restrictDom ρ'i.exclPart) ρ'p).mp ⟨ρp, hsplit, hcp⟩
    rwa [ResU.CompS.functional hy hcχ] at hyp
  obtain ⟨hχi, hDmi⟩ := ResU.Hash.split hmid hpi
  have hvp : ρ'p.Valid := by
    obtain ⟨τ, hτ, hv⟩ := hpi.2
    exact (ResU.Valid.split hτ hv).1
  have hχDm : ResU.Hash ρ'χ (ρ.restrictDom ρ'i.exclPart) := ⟨hmid.1, ρ'p, hmid, hvp⟩
  have hχZm := ResU.hash_of_pairwise hχDm hDmi hχi hZm
  -- `ρ′ ● ρ⁺ ● ρᵢ = (ρ′ ● χ) ● (ρ|dom(ρ′ᵢ|mut,own) ● ρᵢ)`
  have hPZ : ResU.CompS ρ'χ Zm P := by
    obtain ⟨x, hx, hxP⟩ :=
      (ResU.CompS.assoc ρ'χ (ρ.restrictDom ρ'i.exclPart)
        (ResU.single l₀ (CellU.immOf s v ρ'i hs)) P).mpr ⟨ρ'p, hmid, hP⟩
    rwa [ResU.CompS.functional hx hZm] at hxP
  exact ResU.lower_congr_iff H1 hPZ hχZm hQ hχi

end BoCa.Fig16

alias TR.lemma_6_58_right := BoCa.Fig16.ResU.six58_right

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {β : Life} {ρ'i ρ L R Lreb Rreb : ResU BoCa.Loc BoCa.Val}
  {aL aR areb ai aLr aRr aX aY eLr eRr σL σR : ResU BoCa.Loc BoCa.Val}
  {l₀ : BoCa.Loc} {s : LSet} {v : BoCa.Val} {hs : ρ'i.InStratum s.join}
  {es as pS : ResU BoCa.Loc BoCa.Val}

/-! `[about ours]` — what the Lean of Lemma 6.59 needs; the paper prints nothing here. -/
/-- **Step 2's first branch, at every ancestor at once**: an `imm` cell of
`ag(L)` is absorbed by the goal's other side.

`↭`'s first clause pins the cell of `ag(L ● ρ_reb)` it sits in
(`ResU.upd_ag_eq_of_ne_own`), so it stands in `ag(R ● ρ_reb)` too; that walk is
`(ag(R) ○ bi) ○ ρ_reb`, and `CellU.reb_frame_imm_le` cancels the `{β}` — *"all
components of the composition besides for `ρ_reb` outlive `β`, neither have the
immutable borrow at `β` from `ρ_reb`"*.  What is left, `ag(R) ○ bi`, is inside
`ag(R) ○ ag(ρᵢ)` because `bi ≼ ag(ρᵢ)`: *"and both get the borrow from `ρᵢ`"*.
`[about ours: `[TR]` 6.59's closing sentence at an `imm` cell of `ag(L)`]` -/
theorem ResU.reb_frame_absImm
    (hreb : ResU.Reb β ρ'i ρ)
    (hL : L.InStratum β)
    (hupd : ResU.Upd Lreb Rreb)
    (haL : AgW L aL)
    (hareb : AgW (ρ.restrictDom ρ'i.exclPart) areb)
    (hai : AgW (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ai)
    (hexS : ExR ρ'i es) (hagS : AgW ρ'i as) (hfS : ResU.CompR es as pS)
    (hcLr : ResU.CompR aL areb aLr) (hcRr : ResU.CompR aR areb aRr)
    (hcRi : ResU.CompR aR ai aY)
    (haLr : AgW Lreb aLr) (haRr : AgW Rreb aRr)
    (heLr : ExS Lreb eLr) (heRr : ExS Rreb eRr)
    (hfL : ResU.CompS eLr aLr σL) (hfR : ResU.CompS eRr aRr σR) :
    AgW.AbsImm aL aY := by
  classical
  obtain ⟨bi, hbi, hbile⟩ := ResU.reb_ag_split hreb hareb hai hexS hagS hfS
  -- `ag(R) ○ bi` is defined, and `ag(R) ○ bi ○ ρ_reb = ag(R ● ρ_reb)`
  obtain ⟨y, hy₁, hy₂⟩ :=
    (ResU.CompR.assoc aR bi (ρ.restrictDom ρ'i.exclPart) aRr).mp
      ⟨areb, ResU.CompR.comm hbi, hcRr⟩
  have hyY : ResU.CompR y aY aY :=
    ResU.CompR.absorb_comp hy₁ (ResU.LeR.left hcRi).absorb
      (ResU.LeR.trans hbile (ResU.LeR.right hcRi)).absorb
  intro m ψ hgm hk
  have hstr : ψ.InStratum β := BoLo.AgW.inStratum haL β hL m ψ hgm
  obtain ⟨ψt, hψt, hψle⟩ := (ResU.LeR.left hcLr).get_some hgm
  have hψtk : ψt.kind = Kind.imm := by
    obtain ⟨t, ht, e⟩ := CellU.imm_eta hk
    obtain ⟨t', h', e'⟩ := CellU.CompR.imm_left_eq hψle e
    rw [e']; exact CellU.kind_immOf _ _ _ _
  have hRrm : aRr.get m = some ψt :=
    ResU.upd_ag_eq_of_ne_own hupd heLr haLr hfL heRr haRr hfR hψt
      (by rw [hψtk]; exact fun c => Kind.noConfusion c)
  -- `ψ` is absorbed by `(ag(R) ○ bi)(m)`, the `{β}` cancelling off
  have habs : ∃ d, y.get m = some d ∧ CellU.CompR ψ d d := by
    have hdec := hy₂.2 m
    rw [hRrm] at hdec
    cases hr : (ρ.restrictDom ρ'i.exclPart).get m with
    | none =>
        rw [hr] at hdec
        cases hyg : y.get m with
        | none =>
            rw [hyg] at hdec
            exact absurd (show (some ψt : Option (CellU BoCa.Loc BoCa.Val)) = none
              from hdec) (by simp)
        | some d =>
            rw [hyg] at hdec
            obtain rfl : ψt = d :=
              Option.some.inj (show (some ψt : Option (CellU BoCa.Loc BoCa.Val))
                = some d from hdec)
            exact ⟨_, rfl, hψle⟩
    | some B =>
        rw [hr] at hdec
        obtain ⟨φ', hφ'⟩ := ResU.restrictDom_dom hr
        obtain ⟨hφ'g, hφ'k⟩ := ResU.exclPart_eq_some.mp hφ'
        obtain ⟨vm, χm, hχm, hBeq, -, -⟩ :=
          ResU.reb_src hreb (ResU.restrictDom_get_inv hr) hφ'g hφ'k
        subst hBeq
        cases hyg : y.get m with
        | none =>
            rw [hyg] at hdec
            obtain rfl : ψt = CellU.immOf (LSet.singleton β) vm χm hχm :=
              Option.some.inj hdec
            exact absurd rfl (CellU.reb_frame_imm_ne_singleton hψle hstr hk)
        | some d =>
            rw [hyg] at hdec
            obtain ⟨e, he, hde⟩ := hdec
            obtain rfl : ψt = e := Option.some.inj he
            exact ⟨d, rfl, CellU.reb_frame_imm_le hstr hk hde hψle⟩
  obtain ⟨d, hd, hψd⟩ := habs
  obtain ⟨c, hc, hdc⟩ := (ResU.LeR.left hyY).get_some hd
  exact ⟨c, hc, CellU.CompR.absorb_transC hψd hdc⟩

end BoCa.Fig16

namespace BoCa.Fig16
variable {β : Life} {ρ'i ρ L R Lreb Rreb : ResU BoCa.Loc BoCa.Val}
  {aL aR areb ai aLr aRr aX aY eLr eRr σL σR : ResU BoCa.Loc BoCa.Val}
  {l₀ : BoCa.Loc} {s : LSet} {v : BoCa.Val} {hs : ρ'i.InStratum s.join}
  {es as pS : ResU BoCa.Loc BoCa.Val}

/-- **Steps 3 and 4, at every ancestor at once**: the whole `⦇κ⦈_○` under an
`imm` cell of `ag(L)` is a `○`-factor of the goal's other side.

`↭`'s first clause pins the cell **with its witness** (composing with an `imm`
cell only joins lifetime sets, so the witness survives the `○` with `ag(ρ_reb)`), and `ResU.reb_attribute` then places
`⦇κ⦈_○` in `ag(R) ○ ag(ρᵢ)` on all three of its branches.  The walks are
functional, so the `⦇κ⦈_○` it returns is the one the trace started from.
`[about ours: `[TR]` 6.48's ancestor step run at every ancestor of `ag(L)`]` -/
theorem ResU.reb_frame_absAnc
    (hreb : ResU.Reb β ρ'i ρ)
    (hupd : ResU.Upd Lreb Rreb)
    (haR : AgW R aR)
    (hareb : AgW (ρ.restrictDom ρ'i.exclPart) areb)
    (hai : AgW (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ai)
    (hexS : ExR ρ'i es) (hagS : AgW ρ'i as) (hfS : ResU.CompR es as pS)
    (hcLr : ResU.CompR aL areb aLr) (hcRr : ResU.CompR aR areb aRr)
    (hcRi : ResU.CompR aR ai aY)
    (haLr : AgW Lreb aLr) (haRr : AgW Rreb aRr)
    (heLr : ExS Lreb eLr) (heRr : ExS Rreb eRr)
    (hfL : ResU.CompS eLr aLr σL) (hfR : ResU.CompS eRr aRr σR) :
    AgW.AbsAnc aL aY := by
  intro m t u κ hh hgm ev av p hev hav hp
  obtain ⟨t₁, h₁, hLrm⟩ := ResU.CompR.imm_left_get hcLr hgm
  have hRrm : aRr.get m = some (CellU.immOf t₁ u κ h₁) :=
    ResU.upd_ag_eq_of_ne_own hupd heLr haLr hfL heRr haRr hfR hLrm
      (by rw [CellU.kind_immOf]; exact fun c => Kind.noConfusion c)
  obtain ⟨ev', av', p', z, hev', hav', hp', hz⟩ :=
    ResU.reb_attribute hreb haR hareb hai hexS hagS hfS hcRr hcRi hRrm
  cases ExR.functional hev' hev
  cases AgW.functional hav' hav
  cases ResU.CompR.functional hp' hp
  exact (ResU.LeR.left hz).absorb

/-- **`ag(L)` is absorbed by `ag(R) ○ ag(ρᵢ)`.**  The two halves above are
exactly `AgW.absorb_of_ancestors`' two hypotheses, so the walk is accounted for
in full: nothing `ag(L)` carries is lost when `ρ_reb` is exchanged for `ρᵢ`.
`[about ours: `[TR]` 6.59's closing sentence as a `≼` between the two walks]` -/
theorem ResU.reb_frame_ag_le
    (hreb : ResU.Reb β ρ'i ρ)
    (hL : L.InStratum β)
    (hupd : ResU.Upd Lreb Rreb)
    (haL : AgW L aL) (haR : AgW R aR)
    (hareb : AgW (ρ.restrictDom ρ'i.exclPart) areb)
    (hai : AgW (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ai)
    (hexS : ExR ρ'i es) (hagS : AgW ρ'i as) (hfS : ResU.CompR es as pS)
    (hcLr : ResU.CompR aL areb aLr) (hcRr : ResU.CompR aR areb aRr)
    (hcRi : ResU.CompR aR ai aY)
    (haLr : AgW Lreb aLr) (haRr : AgW Rreb aRr)
    (heLr : ExS Lreb eLr) (heRr : ExS Rreb eRr)
    (hfL : ResU.CompS eLr aLr σL) (hfR : ResU.CompS eRr aRr σR) :
    ResU.CompR aL aY aY :=
  AgW.absorb_of_ancestors haL aY
    (ResU.reb_frame_absImm hreb hL hupd haL hareb hai hexS hagS hfS hcLr hcRr
      hcRi haLr haRr heLr heRr hfL hfR)
    (ResU.reb_frame_absAnc hreb hupd haR hareb hai hexS hagS hfS hcLr hcRr
      hcRi haLr haRr heLr heRr hfL hfR)

/-- **`[TR]` 6.59's closing sentence.**  Each side of the goal absorbs the
other — the configuration is symmetric in `L` and `R`, and `↭` is symmetric —
so `ResU.CompR.functional` makes them one resource.

This is the form the step wants: *"`⦇ρᵢ ● ρ_b⦈(ℓ)` and
`⦇ρ′ ● (ρ⁺ ⊟ ρ_reb) ● ρᵢ⦈(ℓ)` each absorb the other at `○`"* — and it comes out
not at one `ℓ` but at the whole aliasable walk, which is what makes the `∼` the
print asks for an equality.
`[about ours: `[TR]` 6.59's closing sentence at the two aliasable walks]` -/
theorem ResU.reb_frame_ag_eq
    (hreb : ResU.Reb β ρ'i ρ)
    (hL : L.InStratum β) (hR : R.InStratum β)
    (hupd : ResU.Upd Lreb Rreb)
    (haL : AgW L aL) (haR : AgW R aR)
    (hareb : AgW (ρ.restrictDom ρ'i.exclPart) areb)
    (hai : AgW (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ai)
    (hexS : ExR ρ'i es) (hagS : AgW ρ'i as) (hfS : ResU.CompR es as pS)
    (hcLr : ResU.CompR aL areb aLr) (hcRr : ResU.CompR aR areb aRr)
    (hcLi : ResU.CompR aL ai aX) (hcRi : ResU.CompR aR ai aY)
    (haLr : AgW Lreb aLr) (haRr : AgW Rreb aRr)
    (heLr : ExS Lreb eLr) (heRr : ExS Rreb eRr)
    (hfL : ResU.CompS eLr aLr σL) (hfR : ResU.CompS eRr aRr σR) :
    aX = aY := by
  have h1 : ResU.CompR aL aY aY :=
    ResU.reb_frame_ag_le hreb hL hupd haL haR hareb hai hexS hagS hfS
      hcLr hcRr hcRi haLr haRr heLr heRr hfL hfR
  have h2 : ResU.CompR aR aX aX :=
    ResU.reb_frame_ag_le hreb hR hupd.symm haR haL hareb hai hexS hagS hfS
      hcRr hcLr hcLi haRr haLr heRr heLr hfR hfL
  have hXY : ResU.CompR aX aY aY :=
    ResU.CompR.absorb_comp hcLi h1 (ResU.LeR.right hcRi).absorb
  have hYX : ResU.CompR aY aX aX :=
    ResU.CompR.absorb_comp hcRi h2 (ResU.LeR.right hcLi).absorb
  exact (ResU.CompR.functional (ResU.CompR.comm hXY) hYX).symm

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- **`[TR]` 6.59's two sides have one aliasable walk**, and where it is silent
so is each side of the update hypothesis.

The first half is `Fig16.ResU.reb_frame_ag_eq` at 6.59's own objects: `ρ = ρ|dom(ρ′ᵢ|imm) ● ρ_reb`
(`ResU.restrictDom_split`), `ρ⁺ = χ ● ρ_reb` (6.52), so both sides of the
hypothesis are `ag(−) ○ ag(ρ_reb)` over the same `ag(L)`, `ag(R)` the goal
composes with `ag(ρᵢ)`; and `ag(ρ|dom(ρ′ᵢ|imm)) ≼ ag(ρᵢ)` (6.57's display) makes
the goal's left walk `ag(ρᵢ ● ρ_b)` on the nose.

The second half is what the print's *"immediate"* case needs: a location where
the goal's walk carries nothing is a location outside `dom(ρ_reb)` — `ag(ρᵢ)`
would stand there otherwise — and off `dom(ρ_reb)` `ag(ρ_reb)` adds nothing
either (`ResU.reb_ag_cell_absorbed_off_dom`), so every factor of both sides of
the hypothesis is silent too.
`[about ours: `[TR]` 6.59's step 4 at the walks, before the print's case
split]` -/
theorem ResU.six59_ag_eq
    {β : Life} {ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY : ResU BoCa.Loc BoCa.Val}
    {l₀ : BoCa.Loc} {s : LSet} {v : BoCa.Val} {hs : ρ'i.InStratum s.join}
    (hreb : ResU.Reb β ρ'i ρ)
    (hce : ResU.CompS ρ ρb ρρb)
    (hcp : ResU.CompS ρ' ρp ρ'p)
    (hupd : ResU.UpdV ρρb ρ'p)
    (hsb : ρb.InStratum β)
    (hs' : ρ'.InStratum β)
    (hsplit : ResU.CompS χ (ρ.restrictDom ρ'i.exclPart) ρp)
    (hχβ : χ.InStratum β)
    (hXc : ResU.CompS (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ρb Xi)
    (hYc : ∃ w, ResU.CompS ρ' χ w ∧
      ResU.CompS w (ResU.single l₀ (CellU.immOf s v ρ'i hs)) Y)
    (hfX : ResU.Flat Xi σX) (hfY : ResU.Flat Y σY) :
    ∃ a, AgW Xi a ∧ AgW Y a ∧
      ∀ aL aR, AgW ρρb aL → AgW ρ'p aR →
        ∀ l, a.get l = none → aL.get l = none ∧ aR.get l = none := by
  classical
  obtain ⟨eX, aXi, heX, haXi, hfX'⟩ := hfX
  obtain ⟨ai, ab, hai, hab, hXag⟩ := (AgW.split hXc).mp haXi
  obtain ⟨eY, aY, heY, haY, hfY'⟩ := hfY
  obtain ⟨R, hRw, hYw⟩ := hYc
  obtain ⟨aR, ai₁, haR, hai₁, hYag⟩ := (AgW.split hYw).mp haY
  cases AgW.functional hai₁ hai
  -- the hypothesis's two walks
  obtain ⟨σL, eLr, aLr, heLr, haLr, hfL⟩ := hupd.2.1
  obtain ⟨σR, eRr, aRr, heRr, haRr, hfR⟩ := hupd.2.2
  obtain ⟨aρ, ab₁, haρ, hab₁, hLag⟩ := (AgW.split hce).mp haLr
  cases AgW.functional hab₁ hab
  obtain ⟨aρ', aρp, haρ', haρp, hRag⟩ := (AgW.split hcp).mp haRr
  -- `ρ = ρ|dom(ρ′ᵢ|imm) ● ρ_reb`
  have hDsplit := ResU.restrictDom_split hreb
  obtain ⟨aD, areb, haD, hareb, hDag⟩ := (AgW.split hDsplit).mp haρ
  obtain ⟨aχ, areb₁, haχ, hareb₁, hPag⟩ := (AgW.split hsplit).mp haρp
  cases AgW.functional hareb₁ hareb
  -- `ag(L) = ag(ρ|dom(ρ′ᵢ|imm)) ○ ag(ρ_b)`, and `ag(L) ○ ag(ρ_reb) = ag(ρ ● ρ_b)`
  obtain ⟨x, hx₁, hx₂⟩ :=
    (ResU.CompR.assoc aD areb ab aLr).mpr ⟨aρ, hDag, hLag⟩
  obtain ⟨aL, hcDab, hcLareb⟩ :=
    (ResU.CompR.assoc aD ab areb aLr).mp ⟨x, ResU.CompR.comm hx₁, hx₂⟩
  -- and `L = ρ|dom(ρ′ᵢ|imm) ● ρ_b` is a resource
  obtain ⟨z, hz₁, hz₂⟩ :=
    (ResU.CompS.assoc (ρ.restrictDom (ρ'i.restrict Kind.imm))
      (ρ.restrictDom ρ'i.exclPart) ρb ρρb).mpr ⟨ρ, hDsplit, hce⟩
  obtain ⟨L, hLc, hLreb⟩ :=
    (ResU.CompS.assoc (ρ.restrictDom (ρ'i.restrict Kind.imm)) ρb
      (ρ.restrictDom ρ'i.exclPart) ρρb).mp ⟨z, ResU.CompS.comm hz₁, hz₂⟩
  have haLW : AgW L aL := (AgW.split hLc).mpr ⟨aD, ab, haD, hab, hcDab⟩
  have hLstr : L.InStratum β :=
    ResU.CompS.inStratum hLc (ResU.reb_immPart_inStratum hreb) hsb
  -- `ag(R) ○ ag(ρ_reb) = ag(ρ′ ● ρ⁺)`
  obtain ⟨aR₀, hcR₀, hcRareb⟩ :=
    (ResU.CompR.assoc aρ' aχ areb aRr).mp ⟨aρp, hPag, hRag⟩
  obtain ⟨b₁, b₂, hb₁, hb₂, hbc⟩ := (AgW.split hRw).mp haR
  cases AgW.functional hb₁ haρ'
  cases AgW.functional hb₂ haχ
  cases ResU.CompR.functional hbc hcR₀
  have hRstr : R.InStratum β := ResU.CompS.inStratum hRw hs' hχβ
  -- `ρᵢ`'s own walks
  obtain ⟨es, as, pS, hexS, hagS, hfS, hagi⟩ := AgW.single_imm_inv hai
  -- `ag(L) ○ ag(ρᵢ) = ag(ρᵢ ● ρ_b)`, because `ag(ρ|dom(ρ′ᵢ|imm)) ≼ ag(ρᵢ)`
  have hDai : ResU.CompR aD ai ai := ResU.reb_immPart_ag_absorbs hreb haD hai
  have hDaXi : ResU.CompR aD aXi aXi :=
    (ResU.LeR.trans ⟨ai, hDai⟩ (ResU.LeR.left hXag)).absorb
  obtain ⟨y, hy₁, hy₂⟩ :=
    (ResU.CompR.assoc aD ab ai aXi).mp ⟨aXi, ResU.CompR.comm hXag, hDaXi⟩
  cases ResU.CompR.functional hy₁ hcDab
  -- `[TR]` 6.59's closing sentence
  have heq : aXi = aY :=
    ResU.reb_frame_ag_eq hreb hLstr hRstr hupd.1 haLW haR hareb hai hexS hagS hfS
      hcLareb hcRareb hy₂ hYag haLr haRr heLr heRr hfL hfR
  subst heq
  refine ⟨aXi, haXi, haY, fun aL' aR' haL' haR' l hn => ?_⟩
  cases AgW.functional haL' haLr
  cases AgW.functional haR' haRr
  -- where the goal's one walk is silent, so is every factor of it
  obtain ⟨hain, habn⟩ := (ResU.Comp.eq_none_iff hXag l).mp hn
  obtain ⟨haRn, -⟩ := (ResU.Comp.eq_none_iff hYag l).mp hn
  obtain ⟨haDn, -⟩ := (ResU.Comp.eq_none_iff hDai l).mp hain
  -- …and `ρ_reb` cannot stand there, since `ag(ρᵢ)` would
  have hrebn : (ρ.restrictDom ρ'i.exclPart).get l = none := by
    cases hr : (ρ.restrictDom ρ'i.exclPart).get l with
    | none => rfl
    | some ζ =>
        obtain ⟨c, hc⟩ := ResU.ag_single_imm_some_of_reb hai hr
        rw [hain] at hc; exact absurd hc (by simp)
  have harebn : areb.get l = none := by
    cases hg : areb.get l with
    | none => rfl
    | some ψ =>
        obtain ⟨φ, hφ, -⟩ :=
          ResU.reb_ag_cell_absorbed_off_dom hreb hareb hai hexS hagS hfS hrebn hg
        rw [hain] at hφ; exact absurd hφ (by simp)
  obtain ⟨haρ'n, haχn⟩ := (ResU.Comp.eq_none_iff hcR₀ l).mp haRn
  have hnone₂ : ∀ {c₁ c₂ c : ResU BoCa.Loc BoCa.Val}, ResU.CompR c₁ c₂ c →
      c₁.get l = none → c₂.get l = none → c.get l = none := by
    intro c₁ c₂ c hc h₁ h₂
    have := hc.2 l
    rw [h₁, h₂] at this
    exact this
  exact ⟨hnone₂ hLag (hnone₂ hDag haDn harebn) habn,
    hnone₂ hRag haρ'n (hnone₂ hPag haχn harebn)⟩

/-- **`[TR]` 6.59's step 6 at a reborrowed `ℓ`, on the printed route.**  Its two
sides' aliasable walks are equal, so the cells at `ℓ` are equal and `∼`
is reflexivity — strictly more than the print's `∼` asks.

`ρ_b # ρᵢ`, `ρ′ ● ρ⁺ # ρᵢ` and `ρ⁺ ⊟ ρ_reb` itself go **unspent**: the first two
are what 6.58 and 6.56 need and this step does not, and the third is what makes
`χ` the printed `ρ⁺ ⊟ ρ_reb` rather than an arbitrary splitting of `ρ⁺`, so it
is carried to keep the statement the printed one.  The two hypotheses that are
spent in its place are 6.52's own conclusions, which 6.59's first sentence
quotes.
`[restricted: to `[TR]` 6.52's two conclusions, taken as named hypotheses at the
`χ` the statement binds — *"By lemma 6.52, `ρ⁺ = (ρ⁺ ⊟ ρ_reb) ● ρ_reb`, and
`@(ρ⁺ ⊟ ρ_reb) ⊐ β`"* (`[TR]` p. 20, the proof's first sentence).  `ResU.Sub` is
Definition 6.3's four bullets and its `ρ″ ≤ ρ|imm` does not pin the lifetime sets
off `dom(ρ_reb)` (`ResU.sub_underdetermined`), so the equation is not a
consequence of it; `ResU.six52` proves both conclusions of a `χ` it constructs,
which is what inhabits this hypothesis set.  The conclusion is the printed
one]` -/
theorem ResU.six59_residual_at
    {β : Life} {ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY : ResU BoCa.Loc BoCa.Val}
    {l₀ : BoCa.Loc} {s : LSet} {v : BoCa.Val} {hs : ρ'i.InStratum s.join}
    (hreb : ResU.Reb β ρ'i ρ)
    (hce : ResU.CompS ρ ρb ρρb)
    (hcp : ResU.CompS ρ' ρp ρ'p)
    (hupd : ResU.UpdV ρρb ρ'p)
    (hsb : ρb.InStratum β)
    (hs' : ρ'.InStratum β)
    (hsplit : ResU.CompS χ (ρ.restrictDom ρ'i.exclPart) ρp)
    (hχβ : χ.InStratum β)
    (_hh1 : ResU.Hash ρb (ResU.single l₀ (CellU.immOf s v ρ'i hs)))
    (_hh2 : ResU.Hash ρ'p (ResU.single l₀ (CellU.immOf s v ρ'i hs)))
    (_hsub : ResU.Sub ρp (ρ.restrictDom ρ'i.exclPart) χ)
    (hXc : ResU.CompS (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ρb Xi)
    (hYc : ∃ w, ResU.CompS ρ' χ w ∧
      ResU.CompS w (ResU.single l₀ (CellU.immOf s v ρ'i hs)) Y)
    (hfX : ResU.Flat Xi σX) (hfY : ResU.Flat Y σY)
    (l : BoCa.Loc) (hl : ∃ ζ, (ρ.restrictDom ρ'i.exclPart).get l = some ζ) :
    ResU.SimFormAt σX σY l := by
  classical
  obtain ⟨a, haXi, haY, -⟩ :=
    ResU.six59_ag_eq hreb hce hcp hupd hsb hs' hsplit hχβ hXc hYc hfX hfY
  obtain ⟨ai, ab, hai, hab, hXag⟩ := (AgW.split hXc).mp haXi
  obtain ⟨eX, a₁, heX, ha₁, hfX'⟩ := hfX
  cases AgW.functional ha₁ haXi
  obtain ⟨eY, a₂, heY, ha₂, hfY'⟩ := hfY
  cases AgW.functional ha₂ haY
  obtain ⟨ζ, hζ⟩ := hl
  obtain ⟨cA, hcA⟩ := ResU.ag_single_imm_some_of_reb hai hζ
  have hXin : ∃ c, a.get l = some c := by
    rcases ResU.Comp.get hXag l with ⟨f₁, -, -⟩ | ⟨ψ, -, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
        ⟨ψ₁, ψ₂, ψ, -, -, f, -⟩
    · rw [hcA] at f₁; exact absurd f₁ (by simp)
    · exact ⟨ψ, f⟩
    · rw [hcA] at f₁; exact absurd f₁ (by simp)
    · exact ⟨ψ, f⟩
  obtain ⟨c, hc⟩ := hXin
  exact ResU.simFormAt_of_eq
    ((ResU.flat_eq_ag_of_immFree (ExS.immFree heX) hfX' hc).trans
      (ResU.flat_eq_ag_of_immFree (ExS.immFree heY) hfY' hc).symm)

end BoCa.Fig16

namespace BoCa.Fig16

/-- **…and it holds.**  `[TR]` 6.52's two conclusions at that `χ` are
`ResU.SubKeep.compS` over `ResU.six52_H1`, and `ResU.six52_sub_inStratum`; the
rest is `ResU.six59_residual_at`. -/
theorem ResU.sixFiftyNineResidualKeep : ResU.SixFiftyNineResidualKeep := by
  intro β ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY l₀ s v hs hreb hce hcp hupd hsb hs'
    hh1 hh2 hsub hXc hYc hfX hfY l hl
  exact ResU.six59_residual_at hreb hce hcp hupd hsb hs'
    (ResU.SubKeep.compS (ResU.six52_H1 hreb hce hcp hupd hsb hs') hsub)
    (ResU.six52_sub_inStratum hreb hce hcp hupd hsb hs' χ hsub.toSub)
    hh1 hh2 hsub.toSub hXc hYc hfX hfY l hl

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- **`[TR]` 6.59's step 6 at `ℓ ∉ dom(ρ_reb)`.**  The print's *"immediate"*,
at the objects: the swap leaves `ex(−)_●` alone, and where the goal's aliasable
walk is silent so is the hypothesis's, so both sides of the goal are their
exclusive walks — which are the hypothesis's.
`[restricted: as `ResU.six59_residual_at`, to `[TR]` 6.52's two conclusions at
the `χ` the statement binds]` -/
theorem ResU.six59_offReb_at
    {β : Life} {ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY : ResU BoCa.Loc BoCa.Val}
    {l₀ : BoCa.Loc} {s : LSet} {v : BoCa.Val} {hs : ρ'i.InStratum s.join}
    (hreb : ResU.Reb β ρ'i ρ)
    (hce : ResU.CompS ρ ρb ρρb)
    (hcp : ResU.CompS ρ' ρp ρ'p)
    (hupd : ResU.UpdV ρρb ρ'p)
    (hsb : ρb.InStratum β)
    (hs' : ρ'.InStratum β)
    (hsplit : ResU.CompS χ (ρ.restrictDom ρ'i.exclPart) ρp)
    (hχβ : χ.InStratum β)
    (hXc : ResU.CompS (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ρb Xi)
    (hYc : ∃ w, ResU.CompS ρ' χ w ∧
      ResU.CompS w (ResU.single l₀ (CellU.immOf s v ρ'i hs)) Y)
    (hfX : ResU.Flat Xi σX) (hfY : ResU.Flat Y σY)
    (l : BoCa.Loc) (_hl : (ρ.restrictDom ρ'i.exclPart).get l = none) :
    ResU.SimFormAt σX σY l := by
  classical
  obtain ⟨a, haXi, haY, hsil⟩ :=
    ResU.six59_ag_eq hreb hce hcp hupd hsb hs' hsplit hχβ hXc hYc hfX hfY
  obtain ⟨eX, a₁, heX, ha₁, hfX'⟩ := hfX
  cases AgW.functional ha₁ haXi
  obtain ⟨eY, a₂, heY, ha₂, hfY'⟩ := hfY
  cases AgW.functional ha₂ haY
  cases hg : a.get l with
  | some c =>
      exact ResU.simFormAt_of_eq
        ((ResU.flat_eq_ag_of_immFree (ExS.immFree heX) hfX' hg).trans
          (ResU.flat_eq_ag_of_immFree (ExS.immFree heY) hfY' hg).symm)
  | none =>
      obtain ⟨σL, eLr, aLr, heLr, haLr, hfL⟩ := hupd.2.1
      obtain ⟨σR, eRr, aRr, heRr, haRr, hfR⟩ := hupd.2.2
      obtain ⟨hLn, hRn⟩ := hsil aLr aRr haLr haRr l hg
      -- Step A: the swap does not move the exclusive walk
      have heL : eLr = eX :=
        ResU.ex_eq_of_swap_immOnly (ResU.reb_immOnly hreb) ResU.single_imm_immOnly
          (ResU.CompS.comm hce) (ResU.CompS.comm hXc) heLr heX
      obtain ⟨R, hRw, hYw⟩ := hYc
      have hRreb : ResU.CompS R (ρ.restrictDom ρ'i.exclPart) ρ'p := by
        obtain ⟨y, hy₁, hy₂⟩ :=
          (ResU.CompS.assoc ρ' χ (ρ.restrictDom ρ'i.exclPart) ρ'p).mp
            ⟨ρp, hsplit, hcp⟩
        rwa [ResU.CompS.functional hy₁ hRw] at hy₂
      have heR : eRr = eY :=
        ResU.ex_eq_of_swap_immOnly (ResU.reb_reb_immOnly hreb)
          ResU.single_imm_immOnly hRreb hYw heRr heY
      refine ResU.simFormAt_congr (τ₁ := σL) (τ₂ := σR) ?_ ?_ ?_
      · rw [ResU.flat_eq_ex_of_ag_none hfX' hg,
          ResU.flat_eq_ex_of_ag_none hfL hLn, heL]
      · rw [ResU.flat_eq_ex_of_ag_none hfY' hg,
          ResU.flat_eq_ex_of_ag_none hfR hRn, heR]
      · exact ResU.simForm_iff_at.mp
          ((ResU.upd_iff_sim ⟨eLr, aLr, heLr, haLr, hfL⟩
            ⟨eRr, aRr, heRr, haRr, hfR⟩).mp hupd.1) l

end BoCa.Fig16

namespace BoCa.Fig16

/-- **…and it holds**, on 6.52's two conclusions at that `χ`. -/
theorem ResU.sixFiftyNineOffRebKeep : ResU.SixFiftyNineOffRebKeep := by
  intro β ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY l₀ s v hs hreb hce hcp hupd hsb hs'
    _hh1 _hh2 hsub hXc hYc hfX hfY l hl
  exact ResU.six59_offReb_at hreb hce hcp hupd hsb hs'
    (ResU.SubKeep.compS (ResU.six52_H1 hreb hce hcp hupd hsb hs') hsub)
    (ResU.six52_sub_inStratum hreb hce hcp hupd hsb hs' χ hsub.toSub)
    hXc hYc hfX hfY l hl

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.59 · `[TR]` p. 20 · `proved`

> Let ρᵢ = ℓ ↦ imm(α, ρ′ᵢ, v). If ρ ∈ reb_β(ρ′ᵢ), ρ ● ρ_b ↭ ρ′ ● ρ⁺, @ρ_b ⊐ β, @ρ′ ⊐ β, ρ_b # ρᵢ, and ρ′ ● ρ⁺ # ρᵢ, then ρᵢ ● ρ_b ↭ ρ′ ● (ρ⁺ ⊟ ρ∣dom(ρ′ᵢ∣mut,own)) ● ρᵢ

**Printed proof, transcribed.** Let `ρ_reb = ρ∣dom(ρ′ᵢ∣mut,own)`.  By Lemma 6.52, `ρ⁺ = (ρ⁺ ⊟ ρ_reb) ● ρ_reb` and `@(ρ⁺ ⊟ ρ_reb) ⊐ β`; unfolding `reb`, `ρ = ρ∣dom(ρ′ᵢ∣imm) ● ρ_reb`.  Rewriting the update hypothesis with both: `ρ∣dom(ρ′ᵢ∣imm) ● ρ_reb ● ρ_b ↭ ρ′ ● (ρ⁺ ⊟ ρ_reb) ● ρ_reb`.  By Lemma 6.57, `⦇ρ∣dom(ρ′ᵢ∣imm) ● ρᵢ⦈ = ⦇ρᵢ⦈`, which also gives `ag(ρ∣dom(ρ′ᵢ∣imm) ● ρᵢ) = ag(ρᵢ)`.  `⦇ρ_b ● ρᵢ⦈` is defined by hypothesis, and unfolding `⦇−⦈` and `ex` with Lemmas 6.18 and 6.20: `⦇ρᵢ ● ρ_b⦈ = ex(ρᵢ)_● ● ex(ρ_b)_● ● ag(ρᵢ) ○ ag(ρ_b) = ex(ρ_b)_● ● ag(ρᵢ) ○ ag(ρ_b) = ex(ρ_b)_● ● ag(ρ∣dom(ρ′ᵢ∣imm) ● ρᵢ) ○ ag(ρ_b) = ex(ρ_b)_● ● ag(ρ∣dom(ρ′ᵢ∣imm) ● ρᵢ ● ρ_b) = ⦇ρ∣dom(ρ′ᵢ∣imm) ● ρᵢ ● ρ_b⦈`.  Rewriting with this, it suffices that `ρ∣dom(ρ′ᵢ∣imm) ● ρᵢ ● ρ_b ↭ ρ′ ● (ρ⁺ ⊟ ρ_reb) ● ρᵢ`: the same `imm`/`mut` domain, and `∼` at every `ℓ` of it.  The rewritten hypothesis gives `⦇ρ∣dom(ρ′ᵢ∣imm) ● ρ_reb ● ρ_b⦈(ℓ) ∼ ⦇ρ′ ● (ρ⁺ ⊟ ρ_reb) ● ρ_reb⦈(ℓ)`.  If `ℓ ∉ dom(ρ_reb)`, the goal is immediate by the hypothesis and unfolding `reb`.  If `ℓ ∈ dom(ρ_reb)`, then since all components of the composition besides `ρ_reb` outlive `β`, neither side has the immutable borrow at `β` from `ρ_reb`, and both get the borrow from `ρᵢ`.

**Lean.** `BoCa.Fig16.ResU.six59`, alias `TR.lemma_6_59`.

**Note.** `Fig16.ResU.six59`, all six printed hypotheses verbatim, the printed conclusion, every composite named by its graph (G4) including the two flattenings.  proved at **Definition 6.3**, i.e. `Fig16.ResU.SubKeep` — its four bullets together with the paragraph one line below them, which is what makes `⊟` a term (`docs/adjudications.md` §12.64). Not a restriction: `Fig16.ResU.Sub` is the bullets without the paragraph, an incomplete transcription, and `Fig16.ResU.sub_not_functional` measures the difference. **The printed proof, step for step.**  Steps 1–3 are `Fig16.ResU.six52` — now with its H1 named (`Fig16.ResU.six52_H1`), its outlives conclusion holding of every admissible `χ` (`Fig16.ResU.six52_sub_inStratum`) and its equation of every admissible `χ` on the corrected bullet (`Fig16.ResU.SubKeep.compS`) — with `Fig16.ResU.restrictDom_split`, `Fig16.ResU.six57` and `Fig16.ResU.six59_display`; step 4 is `Fig16.ResU.six59_reduce` with `Fig16.ResU.upd_iff_sim`; step 5 is the rewritten hypothesis read at one location; step 6 is the print's one case split, on `ℓ ∈ dom(ρ_reb)`. **The closing sentence** (`Fig16.ResU.reb_frame_ag_eq`) is read at the walks, because at a reborrowed `ℓ` the rewritten hypothesis is `imm({β}, v, χ) ∼ imm({β}, v, χ)` and says nothing (`Fig16.CellU.compR_immBeta_nonimm`): both sides of the hypothesis are `ag(−) ○ ag(ρ_reb)` and both sides of the goal `ag(−) ○ ag(ρᵢ)` over the same `ag(L)` and `ag(R)`, and `ag(ρ_reb) = ρ_reb ○ bi` with `bi ≼ ag(ρᵢ)` (`Fig16.ResU.reb_ag_split`) factors each as `(ag(−) ○ bi) ○ ρ_reb`. `↭`'s first clause pins every `imm` cell of `ag(L)` (`Fig16.ResU.upd_ag_eq_of_ne_own`), *"all components of the composition besides for `ρ_reb` outlive `β`, neither have the immutable borrow at `β` from `ρ_reb`"* cancels the `{β}` (`Fig16.CellU.reb_frame_imm_le`), and 6.48's ancestor step with its attribution (`Fig16.ResU.upd_ag_imm_wit_factor`, `Fig16.ResU.reb_attribute`) puts each such cell's witness's whole `⦇−⦈_○` in `ag(R) ○ ag(ρᵢ)` — *"and both get the borrow from `ρᵢ`"*. Those are the two hypotheses of `Fig16.AgW.absorb_of_ancestors`, which is `Fig16.AgW.nonimm_beneath_imm` stated as an **absorption** rather than a trace: *"this cell has an ancestor"* is not enough, a cell of the walk being several raised cells composed. So `ag(L)` is absorbed whole; the configuration and `↭` are both symmetric, so the two walks absorb each other and `Fig16.ResU.CompR.functional` makes them one — cell **equality** at `ℓ`, more than the printed `∼` asks. `Fig16.CellU.CompR.imm_imm_union` is what lets the ancestor survive the `○` with `ag(ρ_reb)`: two `imm` cells compose over one value and one witness and join only the lifetime sets. **The other case** — *"if `ℓ ∉ dom(ρ_reb)`, then this is immediate, by the hypothesis and unfolding reb"* — is *unfolding reb* at `Fig16.ResU.reb_imm_image`: `ρ_reb` and `ρᵢ` are `imm`-only, so the swap does not move `ex(−)_●` at all (`Fig16.ResU.ex_eq_of_swap_immOnly`), off `dom(ρ_reb)` `ag(ρ_reb)` adds nothing to `ag(ρᵢ)` (`Fig16.ResU.reb_ag_cell_absorbed_off_dom`), and a flattening whose aliasable walk is silent **is** its exclusive walk — so each side of the goal is the corresponding side of the hypothesis and *the hypothesis* transfers. That route needs no `ρ # ρᵢ` and so no restricted row. `Fig16.ResU.six59_ag_eq` is the part of both halves that is common. `Fig16.ResU.SixFiftyNineResidual` and `Fig16.ResU.SixFiftyNineOffReb` remain as the same two halves stated at `Fig16.ResU.Sub`, with `Fig16.ResU.SixFiftyNineResidualKeep` and `Fig16.ResU.SixFiftyNineOffRebKeep` their `SubKeep` counterparts, both proved; `Fig16.ResU.upd_of_residuals` composes the first pair and `Fig16.ResU.six59` the second. `ρ_b # ρᵢ` and `ρ′ ● ρ⁺ # ρᵢ` are carried and go unspent at step 6. `Fig16.ResU.RebSwapPreservesUpd` is a second, location-free route to the closing sentence, and `Fig16.ResU.upd_of_swap` shows it would discharge 6.59 too. `docs/adjudications.md` §12.47 records four negatives, §12.55 the statement defect that made a non-obligation look like a corner, and §12.58 the third bullet
-/
/-- **`[TR]` Lemma 6.59** (p. 20): let `ρᵢ = ℓ ↦ imm(ᾱ, ρ′ᵢ, v)`; if
`ρ ∈ reb_β(ρ′ᵢ)`, `ρ ● ρ_b ↭ ρ′ ● ρ⁺`, `@ρ_b ⊐ β`, `@ρ′ ⊐ β`, `ρ_b # ρᵢ` and
`ρ′ ● ρ⁺ # ρᵢ`, then `ρᵢ ● ρ_b ↭ ρ′ ● (ρ⁺ ⊟ ρ|dom(ρ′ᵢ|mut,own)) ● ρᵢ`.

All six printed hypotheses verbatim, the printed conclusion, and every
composite named by its graph (G4), the two flattenings included.  This is the
`ResU.SubKeep` counterpart of `ResU.upd_of_residuals`, and it takes no `Prop`
hypothesis: `ResU.sixFiftyNineResidualKeep` is the `ℓ ∈ dom(ρ_reb)` half and
`ResU.sixFiftyNineOffRebKeep` the half the print calls *"immediate"*.

The printed proof, step for step: 6.52 (`ResU.six52_H1`,
`ResU.six52_sub_inStratum`, `ResU.SubKeep.compS`) and `ρ = ρ|dom(ρ′ᵢ|imm) ●
ρ_reb` (`ResU.restrictDom_split`) rewrite the update hypothesis; 6.57
(`ResU.six57`, at the walk `ResU.reb_immPart_ag_absorbs`) gives the middle
display and `ResU.six59_display` the rewriting it licenses; the closing
sentence is `Fig16.ResU.reb_frame_ag_eq`, *"all components … outlive `β`, neither have the immutable
borrow at `β` from `ρ_reb`"* being `CellU.reb_frame_imm_le` and *"both get the
borrow from `ρᵢ`"* `ResU.reb_ag_split` with `ResU.reb_attribute`; and the
*"immediate"* case is unfolding `reb`.

`[restricted: to `ResU.SubKeep` — Definition 6.3 with its third bullet read
through the paragraph printed below it (`docs/adjudications.md` §12.58) — where
`ResU.Sub` is that bullet's own glyphs and is strictly weaker
(`ResU.SubKeep.toSub`, `ResU.sub_not_functional`)]` -/
theorem ResU.six59
    {β : Life} {ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY : ResU BoCa.Loc BoCa.Val}
    {l₀ : BoCa.Loc} {s : LSet} {v : BoCa.Val} {hs : ρ'i.InStratum s.join}
    (hreb : ResU.Reb β ρ'i ρ)
    (hce : ResU.CompS ρ ρb ρρb) (hcp : ResU.CompS ρ' ρp ρ'p)
    (hupd : ResU.UpdV ρρb ρ'p)
    (hsb : ρb.InStratum β) (hs' : ρ'.InStratum β)
    (hh1 : ResU.Hash ρb (ResU.single l₀ (CellU.immOf s v ρ'i hs)))
    (hh2 : ResU.Hash ρ'p (ResU.single l₀ (CellU.immOf s v ρ'i hs)))
    (hsub : ResU.SubKeep ρp (ρ.restrictDom ρ'i.exclPart) χ)
    (hXc : ResU.CompS (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ρb Xi)
    (hYc : ∃ w, ResU.CompS ρ' χ w ∧
      ResU.CompS w (ResU.single l₀ (CellU.immOf s v ρ'i hs)) Y)
    (hfX : ResU.Flat Xi σX) (hfY : ResU.Flat Y σY) :
    ResU.Upd Xi Y := by
  classical
  refine (ResU.upd_iff_sim hfX hfY).mpr (ResU.simForm_iff_at.mpr (fun l => ?_))
  cases hl : (ρ.restrictDom ρ'i.exclPart).get l with
  | none =>
      exact ResU.sixFiftyNineOffRebKeep β ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY
        l₀ s v hs hreb hce hcp hupd hsb hs' hh1 hh2 hsub hXc hYc hfX hfY l hl
  | some ζ =>
      exact ResU.sixFiftyNineResidualKeep β ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY
        l₀ s v hs hreb hce hcp hupd hsb hs' hh1 hh2 hsub hXc hYc hfX hfY l ⟨ζ, hl⟩

end BoCa.Fig16

alias TR.lemma_6_59 := BoCa.Fig16.ResU.six59

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.60 · `[TR]` p. 21 · `proved`

> If Δ ⊢ T ⊐ @a and δ ∈ ⟦Δ⟧, and ρ ∈ 𝒱⟦T⟧δ then @ρ ⊐ @aδ

**Printed proof, transcribed.** By induction on the derivation of `Δ ⊢ T ⊐ @a`.  `1`: `ρ = ∅`.  `T₁ ⊗ T₂`: `ρ = ρ₁ ● ρ₂` with `ρᵢ ∈ 𝒱⟦Tᵢ⟧δ`; by the IH `@ρᵢ ⊐ @aδ`, and `[]⋆` completes the case.  `T₁ ⊕ T₂`: `ρ ∈ 𝒱⟦T₁⟧δ` or `ρ ∈ 𝒱⟦T₂⟧δ`, and the IH.  `Ref T`: `ρ = ℓ ↦ own(v) ● ρ_T` with `ρ_T ∈ 𝒱⟦T⟧δ(v)`; the IH, `@(ℓ ↦ own(v)) ⊐ @aδ`, and `[]⋆`.  `[@b] T`: `ρ ∈ [@bδ] 𝒱⟦T⟧δ` gives `@ρ ⊐ @bδ`, and the premise `@bδ ⊐ @aδ`.  `Imm @b T`: `ρ = ℓ ↦ imm(β, v, ρ′)` with `𝒱⟦T⟧δ(v)` and `@bδ ⊑ ⊔β`; with the premise `@bδ ⊐ @aδ`, `@ρ ⊐ @aδ`.  `Mut @b T`: `ρ = ℓ ↦ mut(β, v, ρ′, 𝒱⟦T⟧δ)` with `β ⊒ @bδ`; with the premise, `@ρ ⊐ @aδ`.

**Lean.** `BoCa.Fig16.LogRel.vDen_outlives`, alias `TR.lemma_6_60`, tag `[as printed]`.

**Note.** `Fig16.LogRel.vDen_outlives`, on the printed carrier, `[as printed]` — induction on `Δ ⊢ T ⊐ @a`, case for case as p. 21 prints it. The `Imm` case is the printed sentence *"`@bδ ⊑ ⊔β̄`. And by the hypothesis, `@bδ ⊐ @aδ`. Therefore `@ρ ⊐ @aδ`"* at the connective's `@bδ ⊑ ⊓β̄` (definition row 5.30, `docs/adjudications.md` §12.67(a)), where `@ρ = ⊓β̄` and the step is one `lt_of_lt_of_le`. At the literal `⊔β̄` that step does not follow and the row carried a licence on the recorded borrows; `Fig16.LogRel.imm_case_flat` is the literal bullet where `⊔β̄ = ⊓β̄`. **Read as `MutFrame`'s premise** — how 6.173 uses it, [TR] 6.65 spending `P̂ ⊧ [β] P̂` at one point (p. 23) — it is spent in `Fig16.LogRel.withbor2_compat`; `Fig16.LogRel.exists_supported_of_noImmFormer` is the six-rule fragment that reads no `Imm` row. `Fig16.LogRel.immBound_of_members` and `Fig16.LogRel.AliasExample.outlives` read the conclusion off the members of `β̄` (§12.66).
-/
/-- **`[TR]` Lemma 6.60** (p. 21): "If `Δ ⊢ T ⊐ @a` and `δ ∈ ⟦Δ⟧`, and
`ρ ∈ 𝒱⟦T⟧δ` then `@ρ ⊐ @aδ`."  Induction on `Δ ⊢ T ⊐ @a`, case for case as
printed: the `1` and `Ref` cases are `Res_α` at a resource with no borrow cell,
`⊗` and `⊕` glue, `[@b]` carries the conclusion in its own conjunct, and `Mut`
reads it off the row's `β ⊒ @bδ`.  The `Imm` case is the printed sentence —
"`@bδ ⊑ ⊔β̄`.  And by the hypothesis, `@bδ ⊐ @aδ`.  Therefore `@ρ ⊐ @aδ`" — at
the connective's `@bδ ⊑ ⊓β̄` (`Fig16.BoLo.ptoImm`, `docs/adjudications.md`
§12.67), where `@ρ = ⊓β̄` and the step is one `lt_of_lt_of_le`.
`[as printed]` -/
theorem vDen_outlives {Δ : LifeCtx} {δ : LSub} {a : Lifetime.Life} {α : Life}
    (hδ : Δ.Models δ) (ha : a.interp δ = some α) {T : Ty}
    (hT : OutlivesRules Δ a T) :
    ∀ (v : Val) (ρ : WRes), vDen T δ v ρ → BoLo.Outlives ρ α := by
  induction hT with
  | unit =>
      rintro v ρ ⟨rfl, -⟩
      exact ResU.inStratum_empty α
  | tensor _ _ ih₁ ih₂ =>
      rintro v ρ ⟨v₁, v₂, hs⟩
      obtain ⟨-, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hs
      exact (outlives_comp hc α).mpr ⟨ih₁ v₁ ρ₁ h₁, ih₂ v₂ ρ₂ h₂⟩
  | sum _ _ ih₁ ih₂ =>
      rintro v ρ (⟨v₁, hs⟩ | ⟨v₂, hs⟩)
      · exact ih₁ v₁ ρ (pure_sep_iff.mp hs).2
      · exact ih₂ v₂ ρ (pure_sep_iff.mp hs).2
  | ref _ ih =>
      rintro v ρ ⟨ℓ, w, hs⟩
      obtain ⟨-, ρ₁, ρ₂, hc, rfl, h₂⟩ := pure_sep_iff.mp hs
      exact (outlives_comp hc α).mpr
        ⟨ResU.inStratum_single_own α ℓ w, ih w ρ₂ h₂⟩
  | box hlt =>
      rintro v ρ ⟨β, hb, -, ho⟩
      obtain ⟨α', β', ha', hb', hlt'⟩ := hlt δ hδ
      rw [ha] at ha'; cases Option.some.inj ha'
      rw [hb] at hb'; cases Option.some.inj hb'
      exact ho.mono (le_of_lt (show (α : Life) < β from hlt'))
  | imm hlt =>
      rintro v ρ ⟨β, hbi, ℓ, hs⟩
      obtain ⟨-, s, w, σ, hσ, rfl, -, hle⟩ := pure_sep_iff.mp hs
      obtain ⟨α', β', ha', hb', hlt'⟩ := hlt δ hδ
      rw [ha] at ha'; cases Option.some.inj ha'
      rw [hbi] at hb'; cases Option.some.inj hb'
      exact ResU.inStratum_single ℓ (lt_of_lt_of_le (show (α : Life) < β from hlt') hle)
  | «mut» hlt =>
      rintro v ρ ⟨β, hbi, ℓ, hs⟩
      obtain ⟨-, b, w, σ, hσ, Q, hw, hle, rfl, -⟩ := pure_sep_iff.mp hs
      obtain ⟨α', β', ha', hb', hlt'⟩ := hlt δ hδ
      rw [ha] at ha'; cases Option.some.inj ha'
      rw [hbi] at hb'; cases Option.some.inj hb'
      exact ResU.inStratum_single ℓ
        (lt_of_lt_of_le (show (α : Life) < β from hlt') hle)

end BoCa.Fig16.LogRel

alias TR.lemma_6_60 := BoCa.Fig16.LogRel.vDen_outlives

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.61 · `[TR]` p. 22 · `proved`

> If ρ′₁ ∈ reb_α(ρ₁), ρ′₂ ∈ reb_α(ρ₂), and ρ₁ ▸◂ ρ₂, then ρ′₁ ● ρ′₂ ∈ reb_α(ρ₁ ● ρ₂).

**Printed proof, transcribed.** Unfolding `reb`, the only interesting locations are those in both `ρ′₁` and `ρ′₂`.  By `reb`, `ρ′₁∣mut,own = ρ′₂∣mut,own = ∅`; by `●`, `ρ₁∣mut,own` is disjoint from `ρ₂∣mut,own`.  So overlapping locations of `ρ′₁` and `ρ′₂` are in `(ρ₁ ● ρ₂)∣imm`, where `(ρ′₁ ● ρ′₂)(ℓ) = (ρ₁ ● ρ₂)(ℓ)`, which suffices.

**Lean.** `BoCa.Fig16.ResU.six61`, alias `TR.lemma_6_61`, tag `[as printed]`.

**Note.** `Fig16.ResU.six61`, on the printed carrier, `[as printed]`, at `reb_α`'s `imm` clause read at a subset (definition row 5.28, `docs/adjudications.md` §12.67(b)). *"Any overlapping locations of `ρ′₁` and `ρ′₂` are in `(ρ₁ ● ρ₂)∣imm`"* is **derived** (`Fig16.ResU.reb_overlap`) and is the whole of `ρ′₁ ▸◂ ρ′₂`, so the composite the conclusion names is produced rather than presupposed. *"The only interesting cases are locations `ℓ` that are in both `ρ′₁` and `ρ′₂`"*: at an `imm` location of `ρ₁ ● ρ₂` the composite image is `imm` over a subset of the composite's set, at its value and witness, whichever image carries it (`Fig16.ResU.six61_imm_at`, off `Fig16.ResU.six61_side`) — which is what the `imm` clause asks. At the literal `ρ′(ℓ) = ρ(ℓ)` the row carried `ImmSurvives` on each source. The witness for the composite is `π₁ ++ π₂` with `π₂`'s entries at locations already in `dom(ρ′₁)` dropped; with it are `Fig16.BigComp.sublist_factor`, `Fig16.ResU.CompatS.of_factors`, `Fig16.ResU.CompS.inStratum` and `Fig16.ResU.CompS.erase_left`
-/
/-- **`[TR]` Lemma 6.61** (p. 22): if `ρ′₁ ∈ reb_α(ρ₁)`, `ρ′₂ ∈ reb_α(ρ₂)` and
`ρ₁ ▸◂ ρ₂` then `ρ′₁ ● ρ′₂ ∈ reb_α(ρ₁ ● ρ₂)`.

`ρ₁ ● ρ₂` is named by its graph (G4), whose own first conjunct is the printed
`ρ₁ ▸◂ ρ₂`; `ρ′₁ ● ρ′₂` is **produced**, not assumed, since the printed proof's
own overlap argument is exactly its definedness (`ResU.reb_overlap`).

The witness for the composite reborrow is `π₁ ++ π₂` with `π₂`'s entries at
locations already in `dom(ρ′₁)` dropped — at such a location both source cells
are `imm` and both pieces are the singleton `reb_α`'s `imm` clause forces, so
either will do.  `BigComp.sublist_factor` folds what is left,
`ResU.CompatS.of_factors` composes the two folds under the printed `ρ₁ ▸◂ ρ₂`,
and `ResU.CompS.exchange₄` rebrackets `(⨀π₁ ● ⨀π₂′) ● (…)` to give
`ρ ≥ ⨀π`.  `ResU.CompS.inStratum` is `@ρ ⊐ α` for the composite.

Then `reb_α`'s three clauses, at each location.  The `own` and `mut` clauses go
through because a non-`imm` source cell puts the other operand out of the way
(`ResU.CompS.get_split_of_ne_imm`), and with it the other image.  The `imm`
clause is `ResU.six61_imm_at`: the composite image is `imm` over a subset of the
composite source's lifetime set.  `[as printed]` -/
theorem ResU.six61 {α : Life} {ρ₁ ρ₂ ρ'₁ ρ'₂ ρ : ResU Loc Val}
    (hreb₁ : ResU.Reb α ρ₁ ρ'₁) (hreb₂ : ResU.Reb α ρ₂ ρ'₂)
    (hc : ResU.CompS ρ₁ ρ₂ ρ) :
    ∃ ρ', ResU.CompS ρ'₁ ρ'₂ ρ' ∧ ResU.Reb α ρ ρ' := by
  classical
  have hRS : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompS ψ₁ ψ₂ ψ → CellU.CompatS ψ₁ ψ₂ :=
    fun _ _ _ hcc => CellU.CompS.compat hcc
  -- `ρ′₁ ▸◂ ρ′₂`, from the printed overlap argument.
  have hcompat' : ResU.CompatS ρ'₁ ρ'₂ := by
    intro l ψ₁ ψ₂ h₁ h₂
    exact ResU.reb_overlap hreb₁ hreb₂ hc.1 h₁ h₂
  obtain ⟨ρ', hρ'⟩ := (ResU.compS_defined_iff ρ'₁ ρ'₂).mpr hcompat'
  refine ⟨ρ', hρ', ?_⟩
  -- The image of each reborrow is inside its source's domain.
  have hd₂ : ∀ l, ρ₂.get l = none → ρ'₂.get l = none := by
    intro l he
    cases e : ρ'₂.get l with
    | none => rfl
    | some ζ =>
        obtain ⟨φ, hφ⟩ := ResU.reb_dom_subset hreb₂ e
        rw [he] at hφ; exact absurd hφ (by simp)
  obtain ⟨hst₁, π₁, b₁, hdom₁, hbig₁, hle₁, hat₁⟩ := hreb₁
  obtain ⟨hst₂, π₂, b₂, hdom₂, hbig₂, hle₂, hat₂⟩ := hreb₂
  obtain ⟨π₂', hsub, hmem⟩ :
      ∃ L : List (Loc × ResU Loc Val), L.Sublist π₂ ∧
        ∀ q, q ∈ L ↔ q ∈ π₂ ∧ ρ'₁.get q.1 = none :=
    ⟨π₂.filter (fun q => (ρ'₁.get q.1).isNone), List.filter_sublist, by
      intro q
      simp [List.mem_filter, Option.isNone_iff_eq_none]⟩
  -- The fold of what is kept, and its place under `ρ`.
  obtain ⟨b₂', z₂', hb₂', hz₂'⟩ :=
    BigComp.sublist_factor hRS ResU.compLawsS (hsub.map Prod.snd) hbig₂
  obtain ⟨τ₁, hτ₁⟩ := hle₁
  obtain ⟨τ₂, hτ₂⟩ := hle₂
  obtain ⟨y₂, hy₂⟩ := ResU.Comp.factor_trans hRS ResU.compLawsS hz₂' hτ₂
  obtain ⟨b, hb⟩ :=
    (ResU.compS_defined_iff b₁ b₂').mpr (ResU.CompatS.of_factors hτ₁ hy₂ hc.1)
  obtain ⟨S₁, S₂, hS₁, -, hS⟩ :=
    (ResU.CompS.exchange₄ b₁ τ₁ b₂' y₂ ρ).mp ⟨ρ₁, ρ₂, hτ₁, hy₂, hc⟩
  have hSb : ResU.CompS b S₂ ρ := ResU.CompS.functional hS₁ hb ▸ hS
  refine ⟨ResU.CompS.inStratum hc hst₁ hst₂, π₁ ++ π₂', b, ?_, ?_, ⟨S₂, hSb⟩, ?_⟩
  · -- `dom(π₁ ++ π₂′) = dom(ρ′)`
    rw [List.map_append]
    constructor
    · refine List.nodup_append.mpr ⟨hdom₁.1, ?_, ?_⟩
      · exact List.Nodup.sublist (hsub.map Prod.fst) hdom₂.1
      · intro l hm₁ m hm₂ heq
        subst heq
        obtain ⟨ψ, hψ⟩ := (hdom₁.2 l).mp hm₁
        obtain ⟨q, hq, hq₁⟩ := List.mem_map.mp hm₂
        rw [← hq₁, ((hmem q).mp hq).2] at hψ
        exact absurd hψ (by simp)
    · intro l
      rw [List.mem_append]
      constructor
      · rintro (hm | hm)
        · obtain ⟨ψ, hψ⟩ := (hdom₁.2 l).mp hm
          exact hρ'.dom_left hψ
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
          obtain ⟨hq₂, -⟩ := (hmem q).mp hq
          obtain ⟨ψ, hψ⟩ := (hdom₂.2 q.1).mp (List.mem_map.mpr ⟨q, hq₂, rfl⟩)
          exact hρ'.dom_right hψ
      · rintro ⟨ψ, hψ⟩
        rcases hρ'.get l with ⟨-, -, e⟩ | ⟨ζ, e₁, -, -⟩ | ⟨ζ, e₀, e₂, -⟩ |
            ⟨ζ₁, ζ₂, ζ, e₁, -, -, -⟩
        · rw [e] at hψ; exact absurd hψ (by simp)
        · exact Or.inl ((hdom₁.2 l).mpr ⟨ζ, e₁⟩)
        · refine Or.inr ?_
          obtain ⟨q, hq, hq₁⟩ := List.mem_map.mp ((hdom₂.2 l).mpr ⟨ζ, e₂⟩)
          refine List.mem_map.mpr ⟨q, (hmem q).mpr ⟨hq, ?_⟩, hq₁⟩
          rw [hq₁]; exact e₀
        · exact Or.inl ((hdom₁.2 l).mpr ⟨ζ₁, e₁⟩)
  · rw [List.map_append]
    exact (BigComp.append hRS ResU.compLawsS).mpr ⟨b₁, b₂', hbig₁, hb₂', hb⟩
  · -- `reb_α`'s three clauses at each entry
    intro l p hp
    rcases List.mem_append.mp hp with hp₁ | hp₂
    · -- an entry of `π₁`
      obtain ⟨ψ'₁, hψ'₁⟩ := (hdom₁.2 l).mp (List.mem_map.mpr ⟨(l, p), hp₁, rfl⟩)
      obtain ⟨φ₁, hφ₁⟩ := ResU.reb_dom_subset ⟨hst₁, π₁, b₁, hdom₁, hbig₁, ⟨τ₁, hτ₁⟩, hat₁⟩ hψ'₁
      obtain ⟨hpl, hown₁, hmut₁, himm₁⟩ := hat₁ l p hp₁
      refine ⟨hpl, ?_, ?_, ?_⟩
      · intro v he
        rcases ResU.CompS.get_split_of_ne_imm hc he (by simp) with ⟨f₁, f₂⟩ | ⟨f₁, -⟩
        · obtain ⟨hstr, hres⟩ := hown₁ v f₁
          refine ⟨hstr, ?_⟩
          have h2 := hρ'.2 l
          rw [hres, hd₂ l f₂] at h2
          exact h2
        · rw [f₁] at hφ₁; exact absurd hφ₁ (by simp)
      · intro bb v χ hbb P hw he
        rcases ResU.CompS.get_split_of_ne_imm hc he (by simp) with ⟨f₁, f₂⟩ | ⟨f₁, -⟩
        · obtain ⟨⟨hstr, hres⟩, hdp⟩ := hmut₁ bb v χ hbb P hw f₁
          refine ⟨⟨hstr, ?_⟩, hdp⟩
          have h2 := hρ'.2 l
          rw [hres, hd₂ l f₂] at h2
          exact h2
        · rw [f₁] at hφ₁; exact absurd hφ₁ (by simp)
      · intro s v χ h he
        have hk₁ : φ₁.kind = Kind.imm :=
          (ResU.CompS.kind_wit_left hc hφ₁ he).1.symm.trans (CellU.kind_immOf _ _ _ _)
        obtain ⟨s₁, hs₁, heta⟩ := CellU.imm_eta hk₁
        obtain ⟨hres, hdp⟩ :=
          himm₁ s₁ φ₁.erase φ₁.wit hs₁ (hφ₁.trans (congrArg some heta))
        exact ⟨ResU.six61_imm_at ⟨hst₁, π₁, b₁, hdom₁, hbig₁, ⟨τ₁, hτ₁⟩, hat₁⟩
          ⟨hst₂, π₂, b₂, hdom₂, hbig₂, ⟨τ₂, hτ₂⟩, hat₂⟩ hc hρ' he (hρ'.dom_left hψ'₁), hdp⟩
    · -- an entry kept from `π₂`
      obtain ⟨hp₂', hnone₁⟩ := (hmem (l, p)).mp hp₂
      obtain ⟨ψ'₂, hψ'₂⟩ := (hdom₂.2 l).mp (List.mem_map.mpr ⟨(l, p), hp₂', rfl⟩)
      obtain ⟨φ₂, hφ₂⟩ := ResU.reb_dom_subset ⟨hst₂, π₂, b₂, hdom₂, hbig₂, ⟨τ₂, hτ₂⟩, hat₂⟩ hψ'₂
      obtain ⟨hpl, hown₂, hmut₂, himm₂⟩ := hat₂ l p hp₂'
      refine ⟨hpl, ?_, ?_, ?_⟩
      · intro v he
        rcases ResU.CompS.get_split_of_ne_imm hc he (by simp) with ⟨-, f₂⟩ | ⟨-, f₂⟩
        · rw [f₂] at hφ₂; exact absurd hφ₂ (by simp)
        · obtain ⟨hstr, hres⟩ := hown₂ v f₂
          refine ⟨hstr, ?_⟩
          have h2 := hρ'.2 l
          rw [hres, hnone₁] at h2
          exact h2
      · intro bb v χ hbb P hw he
        rcases ResU.CompS.get_split_of_ne_imm hc he (by simp) with ⟨-, f₂⟩ | ⟨-, f₂⟩
        · rw [f₂] at hφ₂; exact absurd hφ₂ (by simp)
        · obtain ⟨⟨hstr, hres⟩, hdp⟩ := hmut₂ bb v χ hbb P hw f₂
          refine ⟨⟨hstr, ?_⟩, hdp⟩
          have h2 := hρ'.2 l
          rw [hres, hnone₁] at h2
          exact h2
      · intro s v χ h he
        have hk₂ : φ₂.kind = Kind.imm :=
          (ResU.CompS.kind_wit_left (ResU.CompS.comm hc) hφ₂ he).1.symm.trans
            (CellU.kind_immOf _ _ _ _)
        obtain ⟨s₂, hs₂, heta⟩ := CellU.imm_eta hk₂
        obtain ⟨hres, hdp⟩ :=
          himm₂ s₂ φ₂.erase φ₂.wit hs₂ (hφ₂.trans (congrArg some heta))
        exact ⟨ResU.six61_imm_at ⟨hst₁, π₁, b₁, hdom₁, hbig₁, ⟨τ₁, hτ₁⟩, hat₁⟩
          ⟨hst₂, π₂, b₂, hdom₂, hbig₂, ⟨τ₂, hτ₂⟩, hat₂⟩ hc hρ' he (hρ'.dom_right hψ'₂), hdp⟩

end BoCa.Fig16

alias TR.lemma_6_61 := BoCa.Fig16.ResU.six61

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-! `[about ours]` — what the Lean of Lemma 6.62 needs; the paper prints nothing here. -/
/-- 6.62's fold over `⊛_{x∈dom(Γ)}`: `[]⋆` at each live slot and 6.60 at its
clause.  On `gSep`, so that it recurses. -/
theorem gSep_outlives {Δ : LifeCtx} {δ : LSub} {a : Lifetime.Life} {α : Life}
    (hδ : Δ.Models δ) (ha : a.interp δ = some α) :
    ∀ {Γ : Ctx Ty} {γ : List Val} {ρ : WRes},
      (∀ s ∈ Γ, s.live = true → OutlivesRules Δ a s.ty) →
      gSep δ Γ γ ρ → BoLo.Outlives ρ α := by
  intro Γ
  induction Γ with
  | nil =>
      rintro γ ρ - ⟨rfl, -⟩
      exact ResU.inStratum_empty α
  | cons s Γ ih =>
      intro γ ρ hT hg
      cases γ with
      | nil =>
          obtain ⟨rfl, -⟩ := hg
          exact ResU.inStratum_empty α
      | cons v γ =>
          have hT' : ∀ t ∈ Γ, t.live = true → OutlivesRules Δ a t.ty :=
            fun t ht => hT t (List.mem_cons.mpr (Or.inr ht))
          by_cases hl : s.live = true
          · rw [gSep, if_pos hl] at hg
            obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := hg
            exact (outlives_comp hc α).mpr
              ⟨vDen_outlives hδ ha (hT s (List.mem_cons.mpr (Or.inl rfl)) hl) v ρ₁ hv,
               ih hT' hrest⟩
          · rw [gSep, if_neg hl] at hg
            exact ih hT' hg

/-!
## Lemma 6.62 · `[TR]` p. 22 · `proved`

> If Δ ⊢ Γ ⊐ @a and δ ∈ ⟦Δ⟧, then 𝒢⟦Γ⟧δ(γ) ⊧ [@aδ] 𝒢⟦Γ⟧δ(γ).

**Printed proof, transcribed.** Let (H1) `ρ ∈ 𝒢⟦Γ⟧δ(γ)`; the goal (G1) `[@aδ] 𝒢⟦Γ⟧δ(γ)` unfolds to (G2) `@ρ ⊐ @aδ`.  Unfolding `𝒢` in H1, (H2) `ρ ∈ ⌜dom(Γ) ⊆ dom(δ)⌝ ⋆ ⊛_{x∈dom(Γ)} 𝒱⟦Γ(x)⟧δ(γ(x))`, so there are `ρₓ` with (H3) `ρ = ⨀ ρₓ` and (H4) `ρₓ ∈ 𝒱⟦Γ(x)⟧δ(γ(x))` for every `x ∈ dom(Γ)`.  By `[]⋆` it suffices that `@ρₓ ⊐ @aδ` for every `x ∈ dom(Γ)`, and by Lemma 6.60 that `Δ ⊧ Γ(x) ⊐ @a` and `δ ∈ ⟦Δ⟧`, both of which follow from the hypotheses.

**Lean.** `BoCa.Fig16.LogRel.gDen_box`, alias `TR.lemma_6_62`, tag `[as printed]`.

**Note.** `Fig16.LogRel.gDen_box`, `[as printed]` — "By `[]⋆`, it suffices to show `∀x ∈ dom(Γ). @ρₓ ⊐ @aδ`", each by 6.60 (`Fig16.LogRel.vDen_outlives`), folded over the live slots by `Fig16.LogRel.gSep_outlives`. `Δ ⊢ Γ ⊐ @a` is `Ctx.Outlives`, [CONF] Figs. 6/7's reading of the judgment [TR] leaves undefined (§12.6), carrying [TR] p. 2's own presupposition `Δ ⊨ @a`.
-/
/-- **`[TR]` Lemma 6.62** (p. 22): "If `Δ ⊢ Γ ⊐ @a` and `δ ∈ ⟦Δ⟧`, then
`𝒢⟦Γ⟧δ(γ) ⊨ [@aδ] 𝒢⟦Γ⟧δ(γ)`."  "By `[]⋆`, it suffices to show
`∀x ∈ dom(Γ). @ρₓ ⊐ @aδ`", each by 6.60.  `[as printed]` -/
theorem gDen_box {Δ : LifeCtx} {δ : LSub} {a : Lifetime.Life} {α : Life}
    (hδ : Δ.Models δ) (ha : a.interp δ = some α) {Γ : Ctx Ty}
    (hΓ : Ctx.Outlives Δ Γ a)
    (γ : List Val) : Entails (gDen δ Γ γ) (box α (gDen δ Γ γ)) :=
  fun _ hg => ⟨hg, gSep_outlives hδ ha hΓ.2 (gDen_iff.mp hg).2⟩

end BoCa.Fig16.LogRel

alias TR.lemma_6_62 := BoCa.Fig16.LogRel.gDen_box

end
