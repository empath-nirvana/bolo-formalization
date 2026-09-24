import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S5_Model.Definitions
import Support.LogicalRelation.ClosedJudgment
import Support.LogicalRelation.ClosingSubstitutions
import Support.LogicalRelation.Facts
import Support.Model.Algebra
import Support.Model.Propositions
import Support.Statics.Contexts

/-!
# [TR] §4 Logical Relation — remarks on the definitions

Row 4.16's two directions between the `Mut` clause and `Supported`, and row
4.18's `sem_iff` (the judgment at `∅` is the judgment).

These are theorems about printed definitions — rows of the source's
`docs/definition-inventory.md` whose Lean is a theorem — whose proofs use results
of `[TR]` §6, so they cannot sit with the definitions.  Each carries the row's
number, printed form, page, tag and note.  A row's theorem that a §6 result's Lean
needs is declared in that result's file, and the row here says where.
-/

noncomputable section

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
### 4.16 · — no printed counterpart — · [TR] p. 4 · `[repair]`

Fig. 16 row 5's `P̂ : Val → SProp_β` as a predicate, because the model file encodes `SProp_β` as a SUBSET of `SProp` rather than a type. Forced by putting the real predicate in the `mut` cell; it makes visible the side condition the printed `Mut` clause carries silently. Adjudicated at `BoCa/Fig16LogRel.lean` §3's preamble with `BoCa/Fig16.lean` §24: Fig. 16 row 5's `P̂ : Val → SProp_β` is a TYPE, and §24 encodes `SProp_β` as a subset of `SProp` (`BoCa.Fig16.SPropS.toU_range`), so on this carrier the condition is not enforceable by typing and has to be re-expressed as a predicate to be stated at all. [TR] p. 4 writes the relation with the unsubscripted `SProp` while printing both `SProp` and `SProp_α`, so which stratum 𝒱 inhabits is a condition the print carries silently. Both directions are proved
-/
/-- **The `Mut` clause carries the paper's implicit stratum typing.**  A
resource in `𝒱⟦Mut @a T⟧δ` exhibits a `β ⊒ @aδ` at which `𝒱⟦T⟧δ` is a
`Val → SProp_β`, and a value and a resource satisfying it.
`[about ours: what Fig. 16 row 5's two printed conditions give back on this
carrier]` -/
theorem vDen_mut_supported {δ : LSub} {a : Lifetime.Life} {T : Ty} {v : Val} {ρ : WRes}
    (h : vDen (.mut a T) δ v ρ) :
    ∃ α β w σ, a.interp δ = some α ∧ α ⊑ β ∧ Supported β (vDen T δ) ∧ vDen T δ w σ := by
  obtain ⟨α, ha, ℓ, hsep⟩ := h
  obtain ⟨-, b, w, σ, hσ, Q, hw, hab, -, hofS⟩ := pure_sep_iff.mp hsep
  refine ⟨α, b, w, σ, ha, hab, fun u τ hu => ?_, ?_⟩
  · rw [← hofS] at hu
    exact hu.1
  · rw [← hofS]
    exact ⟨hσ, hw⟩

/-!
Row 4.16, continued.
-/
/-- **…and that is all it carries.**  Given the stratum typing, a witness for
`𝒱⟦T⟧δ` builds the cell, so the clause is inhabited.  Together with
`vDen_mut_supported` this is an exact characterisation.
`[about ours: the converse of `vDen_mut_supported`, at the cell Fig. 16 row 5
prints]` -/
theorem vDen_mut_of_supported {δ : LSub} {a : Lifetime.Life} {T : Ty}
    {α β : Life} {w : Val} {σ : WRes} (ha : a.interp δ = some α) (hab : α ⊑ β)
    (hs : Supported β (vDen T δ)) (hw : vDen T δ w σ) (ℓ : BoCa.Loc) :
    ∃ ρ, vDen (.mut a T) δ (.loc ℓ) ρ := by
  have hofS : ofS (fun u => SPropU.toS β (vDen T δ u)) = vDen T δ := by
    funext u
    funext τ
    exact propext ((SPropU.toU_toS_iff β (vDen T δ u) τ).trans
      ⟨fun k => k.1, fun k => ⟨k, hs u τ k⟩⟩)
  have hcell := ptoMut_of_cell ℓ α β hab w σ (hs w σ hw)
    (fun u => SPropU.toS β (vDen T δ u)) hw
  rw [hofS] at hcell
  exact ⟨_, α, ha, ℓ, pure_sep_mk rfl hcell⟩

/-!
### 4.18 · — no printed counterpart — · [TR] p. 4 · `[about ours]`

Row 4.14 evaluated at ∅, as a `Prop`. Forced by `!P ≜ emp ∧ P`: a persistent proposition holds exactly when it holds of ∅, so this is a faithful re-presentation and not a second judgment — but every compatibility lemma of §6.8 is stated at it, so `BoCa.Fig16.LogRel.sem_iff` is what keeps that block about the printed object. It is proved, both directions. A `Prop`-level re-presentation of row 4.14 at ∅, carrying its own correctness lemma: [TR] p. 6 prints `!P ≜ emp ∧ P`, `emp ≜ ⌜⊤⌝` and `⌜PMeta⌝(ρ) ≜ ρ = ∅ ∧ PMeta`, so the judgment holds of ρ only at ρ = ∅ and evaluating there loses nothing. The risk the note above names is discharged by the proof of `BoCa.Fig16.LogRel.sem_iff`, which runs both ways
-/
theorem sem_iff {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty} :
    Sem Δ Γ e T ↔
      ∀ δ γ ρ, Δ.Models δ → gDen δ Γ γ ρ → wp (substAll γ e) (vDen T δ) ρ := by
  constructor
  · rintro ⟨-, hw⟩ δ γ ρ hδ hg
    have h₁ := hw δ γ PMap.empty PMap.empty ⟨rfl, hδ⟩ (ResU.comp_empty_right _)
    exact h₁ ρ ρ hg (compS_empty_left ρ)
  · intro h
    refine ⟨emp_empty, ?_⟩
    intro δ γ ρ₁ ρ₂ hd hc
    obtain ⟨rfl, hδ⟩ := hd
    have h₂ : ρ₂ = PMap.empty := eq_of_compS_empty_left hc
    subst h₂
    intro ρ₃ ρ₄ hg hc'
    have h₄ : ρ₄ = ρ₃ := eq_of_compS_empty_left hc'
    subst h₄
    exact h δ γ _ hδ hg

end BoCa.Fig16.LogRel

end
