import Paper.S5_Model.Definitions
import Support.Model.Algebra
import Support.Model.Walks

/-!
# Support — Model — Compatibility

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
cell-level compatibility read off tags, values and witnesses, and `○` at an `imm` cell.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {R : CellU Loc Val → CellU Loc Val → Prop}
variable {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}

/-- A factor of a factor is a factor: `[TR]` Lemma 6.3 (`ResU.Comp.assoc`, §20)
with both intermediate values discarded.  This is how the printed proof drops
`ex(ρ)_●` and `ag(ρ)` from its display and keeps `ρₘ ● ex(ρᵥ)_●`.
`[about ours: `[TR]` Lemma 6.3 with both intermediate values existentially
quantified away]` -/
theorem ResU.Comp.factor_trans (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂)
    (hC : ResU.CompLaws C) {x y u v w : ResU Loc Val}
    (h₁ : ResU.Comp R C x y u) (h₂ : ResU.Comp R C u v w) :
    ∃ z, ResU.Comp R C x z w := by
  obtain ⟨z, -, hz⟩ := (ResU.Comp.assoc hR hC.assoc x y v w).mpr ⟨u, h₁, h₂⟩
  exact ⟨z, hz⟩

/-- **Every member of an iterated composition is a factor of it.**  `⨀` is a
right fold, so a member is reached by one `◐` and then `[TR]` Lemmas 6.2 and 6.3
for the rest of the fold.
`[about ours: `[TR]` Lemmas 6.2 and 6.3 carried along §16's fold]` -/
theorem BigComp.mem_factor (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) (hC : ResU.CompLaws C) :
    ∀ {xs : List (ResU Loc Val)} {b : ResU Loc Val}, BigComp R C xs b →
      ∀ x ∈ xs, ∃ z, ResU.Comp R C x z b := by
  intro xs
  induction xs with
  | nil => intro b _ x hx; exact absurd hx (by simp)
  | cons y ys ih =>
      intro b hbc x hx
      cases hbc with
      | cons hb hc =>
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact ⟨_, hc⟩
          · obtain ⟨υ, hυ⟩ := ih hb x hx'
            exact ResU.Comp.factor_trans hR hC hυ (ResU.Comp.comm_of_laws hR hC hc)

end BoCa.Fig16

end
