import Paper.S1_Syntax.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_2_NonStandardLemmas.Definitions
import Paper.S6_2_NonStandardLemmas.Lemmas
import Support.Model.Notation
import Support.Model.Prelude
import Support.Model.ReborrowFrame
import Support.Model.Singletons
import Support.Model.Subtraction

/-!
# Support — Model — ReborrowRule

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
what `[TR]` 6.150 names and does not prove: the hypothesis `RebEscrow` (6.55's two inputs at the reborrows `↺_β P̂` names), a lifetime below two given ones, and `ρ⁺|own = ∅` through the pieces of `ρᵢ ● ρ⁺′`.
-/

noncomputable section

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps)

/-- The two inputs `[TR]` 6.55 adds, quantified over exactly the reborrows
`↺_β P̂` produces: `χ ∈ reb_β(σ)` with `P̂(w)(χ)`.  Nothing else about `σ`, `χ`
or the frame is assumed.

`EscrowAgree σ χ a` is asked of every `a` that is *some* resource's aliasable
walk, which is the shape 6.55 takes it in (`∀a. ag(ρ_f) = a ⇒ …`) with the
frame left free — 6.150's proof spends 6.55 at three different frames.

The `b` that indexes `P̂` is the `b` of the reborrow: `↺_β P̂` puts `P̂` under
the `Иβ` binder, so the predicate read off a reborrow at `β` is `P̂(β)`.
`[about ours: the two added inputs of `Fig16.ResU.six55`, at the reborrows
`[TR]` 6.150's precondition names]` -/
def RebEscrow (P : Life → BoCa.Val → WProp) : Prop :=
  ∀ (b : Life) (w : BoCa.Val) (σ χ : WRes),
    ResU.Reb b σ χ → P b w χ →
      (∃ A, AgW χ A) ∧ ∀ r a : WRes, AgW r a → EscrowAgree σ χ a

/-- *"Such a `β` always exists because for any lifetime, the set of lifetimes
shorter than it is infinite."* — `[TR]` p. 39, H11.  `↓γ` is `[TR]` p. 5's
next-shorter lifetime, and `γᵢ ⊓ γ_b` the shorter of the two bounds.
`[about ours: the sentence `[TR]` p. 39 gives for H11, at `↓`]` -/
theorem exists_shorter (gi gb : Life) : ∃ b : Life, b ⊏ gi ∧ b ⊏ gb :=
  ⟨↓(gi ⊓ gb),
    lt_of_lt_of_le (Life.down_sqsubset _) inf_le_left,
    lt_of_lt_of_le (Life.down_sqsubset _) inf_le_right⟩

/-- A single `imm` cell carries no `own` cell. -/
theorem noOwn_single_imm (l : BoCa.Loc) (s : LSet) (v : BoCa.Val) (σ : WRes)
    (hs : σ.InStratum s.join) : NoOwn (ResU.single l (CellU.immOf s v σ hs)) := by
  refine noOwn_iff.mpr fun m ψ hm => ?_
  by_cases hml : m = l
  · subst hml
    rw [ResU.single_get_self] at hm
    cases Option.some.inj hm
    rw [CellU.kind_immOf]
    exact fun h => Kind.noConfusion h
  · rw [ResU.single_get_ne _ hml] at hm; exact absurd hm (by simp)

/-- `ρ|own,mut` has no `own` cell when `ρ` has none. -/
theorem noOwn_exclPart {ρ : WRes} (h : NoOwn ρ) : NoOwn ρ.exclPart :=
  noOwn_iff.mpr fun l ψ hl =>
    noOwn_iff.mp h l ψ (ResU.exclPart_eq_some.mp hl).1

/-- A `●`-factor of an all-`imm` resource has no `own` cell: `●` composes two
`imm` cells and nothing else (`Fig16.CellU.CompS`), so an `own` cell of the
factor would have to survive into the composite.
`[about ours: the `|own = ∅` of a factor of `ρ|imm`, which `[TR]` 6.150's G6
takes in one step]` -/
theorem noOwn_le_restrict_imm {τ ρ : WRes} (h : ResU.Le τ (ρ.restrict Kind.imm)) :
    NoOwn τ := by
  obtain ⟨f, hf⟩ := h
  refine noOwn_iff.mpr fun l ψ hl hk => ?_
  have hc := hf.2 l
  rw [hl] at hc
  cases e : f.get l with
  | none =>
      rw [e] at hc
      have : (ρ.restrict Kind.imm).get l = some ψ := hc
      exact absurd (ResU.restrict_eq_some.mp this).2 (by rw [hk]; exact fun c => Kind.noConfusion c)
  | some φ =>
      rw [e] at hc
      obtain ⟨ζ, -, hC⟩ := hc
      obtain ⟨s₁, s₂, w, χ, k₁, k₂, k₃, e₁, -, -⟩ := hC
      rw [e₁, CellU.kind_immOf] at hk
      exact Kind.noConfusion hk

/-- `ρ⁺ ⊟ ρ_reb` has no `own` cell when `ρ⁺` has none — `⊟`'s two factors are
`ρ⁺|own,mut` and a `ρ″ ≤ ρ⁺|imm`. -/
theorem noOwn_subKeep {ρp D ψ : WRes} (h : ResU.SubKeep ρp D ψ) (hn : NoOwn ρp) :
    NoOwn ψ := by
  obtain ⟨ρ'', -, hle, -, -, hcomp⟩ := h
  exact noOwn_compS hcomp (noOwn_exclPart hn) (noOwn_le_restrict_imm hle)

end BoCa.Fig16.BoLo

end
