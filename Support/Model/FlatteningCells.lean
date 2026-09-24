import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Support.Model.Algebra
import Support.Model.AlgebraInstances
import Support.Model.Compatibility
import Support.Model.Composition
import Support.Model.Prelude
import Support.Model.Singletons
import Support.Model.WalkSplitting
import Support.Model.Walks

/-!
# Support — Model — FlatteningCells

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
the cells of a flattening: a cell of `ρ` reappears in `⦇ρ⦈`, the walks' witnesses lie beneath their cells, and the order `≤` on resources.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- Where the left operand of a `●` is `imm`-free, every cell of the right
operand passes into the composite unchanged: `▶◀` relates `imm` cells only, so
there is nothing at that location in the left operand to compose with. -/
theorem ResU.CompS.get_right_of_immFree {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    (himm : ρ₁.ImmFree) {l : Loc} {ψ : CellU Loc Val} (e : ρ₂.get l = some ψ) :
    ρ.get l = some ψ := by
  rcases h.get l with ⟨-, f₂, -⟩ | ⟨χ, -, f₂, -⟩ | ⟨χ, -, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, -, hC⟩
  · rw [f₂] at e; exact absurd e (by simp)
  · rw [f₂] at e; exact absurd e (by simp)
  · rw [f₂] at e; cases Option.some.inj e; exact f
  · exact absurd (CellU.CompatS.kinds (CellU.CompS.compat hC)).1 (himm l χ₁ f₁)

/-- An `imm` cell of the left operand of a `○` reappears in the composite as an
`imm` cell over the same value and witness — `CellU.CompR.imm_left` at one
location, with `◐`'s outer piece folded in for the case where the other operand
is silent there. -/
theorem ResU.CompR.get_imm_left {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompR ρ₁ ρ₂ ρ)
    {l : Loc} {ψ : CellU Loc Val} (e : ρ₁.get l = some ψ) (hk : ψ.kind = Kind.imm) :
    ∃ χ, ρ.get l = some χ ∧ χ.kind = Kind.imm ∧ χ.erase = ψ.erase ∧ χ.wit = ψ.wit := by
  rcases h.get l with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, f, hC⟩
  · rw [f₁] at e; exact absurd e (by simp)
  · rw [f₁] at e; cases Option.some.inj e; exact ⟨_, f, hk, rfl, rfl⟩
  · rw [f₁] at e; exact absurd e (by simp)
  · rw [f₁] at e
    cases Option.some.inj e
    obtain ⟨m₁, m₂, m₃⟩ := CellU.CompR.imm_left hC hk
    exact ⟨χ, f, m₁, m₂, m₃⟩

/-- The mirror of `ResU.CompR.get_imm_left`, through `[TR]` Lemma 6.2 at `○`
(`ResU.CompR.comm`, §20).
`[about ours: `ResU.CompR.get_imm_left` with the operands transposed]` -/
theorem ResU.CompR.get_imm_right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompR ρ₁ ρ₂ ρ)
    {l : Loc} {ψ : CellU Loc Val} (e : ρ₂.get l = some ψ) (hk : ψ.kind = Kind.imm) :
    ∃ χ, ρ.get l = some χ ∧ χ.kind = Kind.imm ∧ χ.erase = ψ.erase ∧ χ.wit = ψ.wit :=
  ResU.CompR.get_imm_left h.comm e hk

/-- **`ex(ρ)_●` keeps every own-or-mut cell of `ρ` where it is.**  Such a cell
lies in `ρ|own` or in `ρ|mut`, and neither the `●` joining those two nor the `●`
with the fold of the witness family can compose anything onto it.
`[about ours: the own-or-mut half of "the cells of `ρ′` are a subset of those of
`⦇ρ′⦈`" (`[TR]` Lemma 6.16's proof, p. 8), at the exclusive walk]` -/
theorem ExS.get_of_ne_imm {ρ σ : ResU Loc Val} (h : ExS ρ σ) {l : Loc}
    {ψ : CellU Loc Val} (e : ρ.get l = some ψ) (hk : ψ.kind ≠ Kind.imm) :
    σ.get l = some ψ := by
  cases h with
  | mk hs hw hb hnm hσ =>
      refine (ResU.CompS.get_left_of_ne_imm hσ ?_ hk).2
      cases hkk : ψ.kind with
      | own => exact (ResU.CompS.get_left_of_ne_imm hnm (ResU.restrict_get_some e hkk) hk).2
      | imm => exact absurd hkk hk
      | «mut» =>
          exact (ResU.CompS.get_right_of_ne_imm hnm (ResU.restrict_get_some e hkk) hk).2

/-- **`ag(ρ)` keeps every `imm` cell of `ρ` at its own location, as an `imm`
cell over the same value and witness.**  Both of its `○`s can only merge such a
cell with a cell over that same value and witness (`CellU.CompR.imm_left`); the
lifetime set is what they may change, and that is exactly the slack `▶◀`
ignores.
`[about ours: the `imm` half of "the cells of `ρ′` are a subset of those of
`⦇ρ′⦈`" (`[TR]` Lemma 6.16's proof, p. 8), at the aliasable walk]` -/
theorem AgW.get_imm {ρ σ : ResU Loc Val} (h : AgW ρ σ) {l : Loc}
    {ψ : CellU Loc Val} (e : ρ.get l = some ψ) (hk : ψ.kind = Kind.imm) :
    ∃ χ, σ.get l = some χ ∧ χ.kind = Kind.imm ∧ χ.erase = ψ.erase ∧ χ.wit = ψ.wit := by
  cases h with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      obtain ⟨χ₀, f₀, k₀, e₀, w₀⟩ :=
        ResU.CompR.get_imm_left ha (ResU.restrict_get_some e hk) hk
      obtain ⟨χ, f, k', e', w'⟩ := ResU.CompR.get_imm_left hσ f₀ k₀
      exact ⟨χ, f, k', e'.trans e₀, w'.trans w₀⟩

/-- **"The cells of `ρ` are a subset of those of `⦇ρ⦈`"** — the one step of
`[TR]` Lemma 6.16's proof (p. 8), on a carrier where `⦇−⦈` is a walk and not a
set of cells.  An `own` or `mut` cell of `ρ` reappears in `⦇ρ⦈` at its own
location unchanged; an `imm` cell reappears as an `imm` cell over the same value
and witness, its lifetime set possibly enlarged by the `○`s inside `ag`.  Those
three projections are all `▶◀` looks at (`CellU.compatS_iff`), which is why the
printed sentence is enough for 6.16.
`[about ours: the step of `[TR]` Lemma 6.16's proof that unravels `⦇−⦈`, at the
walks]` -/
theorem ResU.Flat.get {ρ σ : ResU Loc Val} (h : ResU.Flat ρ σ) {l : Loc}
    {ψ : CellU Loc Val} (e : ρ.get l = some ψ) :
    ∃ χ, σ.get l = some χ ∧ χ.kind = ψ.kind ∧ χ.erase = ψ.erase ∧ χ.wit = ψ.wit := by
  obtain ⟨ex, ag, hex, hag, hc⟩ := h
  by_cases hk : ψ.kind = Kind.imm
  · obtain ⟨χ, f, k', e', w'⟩ := AgW.get_imm hag e hk
    exact ⟨χ, ResU.CompS.get_right_of_immFree hc (ExS.immFree hex) f,
      k'.trans hk.symm, e', w'⟩
  · exact ⟨ψ, (ResU.CompS.get_left_of_ne_imm hc (ExS.get_of_ne_imm hex e hk) hk).2,
      rfl, rfl, rfl⟩

end BoCa.Fig16

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

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- Either factor of a `○` is `≼` the composite. -/
theorem ResU.LeR.left {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompR ρ₁ ρ₂ ρ) :
    ResU.LeR ρ₁ ρ := ⟨ρ₂, h⟩

theorem ResU.LeR.right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompR ρ₁ ρ₂ ρ) :
    ResU.LeR ρ₂ ρ := ⟨ρ₁, ResU.CompR.comm h⟩

/-- `≼` is transitive — `ResU.Comp.factor_trans` at `○`. -/
theorem ResU.LeR.trans {ρ σ τ : ResU Loc Val}
    (h₁ : ResU.LeR ρ σ) (h₂ : ResU.LeR σ τ) : ResU.LeR ρ τ := by
  obtain ⟨z₁, hz₁⟩ := h₁
  obtain ⟨z₂, hz₂⟩ := h₂
  exact ResU.Comp.factor_trans (fun _ _ ψ hc => ⟨ψ, hc⟩) ResU.compLawsR hz₁ hz₂

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {R : CellU Loc Val → CellU Loc Val → Prop}
variable {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}

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

/-- **`ex(ρᵥ)_◐` is a factor of `ex(ρ)_◐` wherever `ρ(ℓ) = mut(_,_,ρᵥ,_)`.**  The
walk composes the family `{ex(ρ′)_◐ | ∃ℓ. ρ(ℓ) = mut(_,_,ρ′,_)}`, and `ℓ` indexes
one of its entries (convention G6), so the entry is a factor of `⨀` and `⨀` is a
factor of the walk.  This is the `ρₘ ● ex(ρᵥ)_●` of `[TR]` Lemma 6.17's display,
stated for a `mut` cell anywhere rather than for a lone one.
`[about ours: the factor of `[TR]` Lemma 6.17's display (p. 8) that its proof
actually uses, at §17's walk schema]` -/
theorem ExW.wit_le (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) (hC : ResU.CompLaws C)
    {ρ σ : ResU Loc Val} (h : ExW R C ρ σ) {l : Loc} {ψ : CellU Loc Val}
    (e : ρ.get l = some ψ) (hk : ψ.kind = Kind.mut) :
    ∃ ev z, ExW R C ψ.wit ev ∧ ResU.Comp R C ev z σ := by
  cases h with
  | mk hs hw hb hnm hσ =>
      obtain ⟨p, hp, hp₁⟩ := List.mem_map.mp ((hs.2 l).mpr ⟨ψ, e, hk⟩)
      obtain ⟨χ, hχ, hev⟩ := ExWits.mem hw p hp
      rw [hp₁, e] at hχ
      cases Option.some.inj hχ
      obtain ⟨z, hz⟩ := BigComp.mem_factor hR hC hb p.2 (List.mem_map.mpr ⟨p, hp, rfl⟩)
      obtain ⟨z', hz'⟩ :=
        ResU.Comp.factor_trans hR hC hz (ResU.Comp.comm_of_laws hR hC hσ)
      exact ⟨p.2, z', hev, hz'⟩

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- **`ag(ρᵥ)` is a factor of `ag(ρ)` wherever `ρ(ℓ) = mut(_,_,ρᵥ,_)`** — the
`mut` half of the aliasable walk's two families, and the `ag(ρᵥ)` of `[TR]`
Lemma 6.17's display, again stated for a `mut` cell anywhere.
`[about ours: the factor of `[TR]` Lemma 6.17's display (p. 8) that its proof
actually uses]` -/
theorem AgW.mut_wit_le {ρ σ : ResU Loc Val} (h : AgW ρ σ) {l : Loc}
    {ψ : CellU Loc Val} (e : ρ.get l = some ψ) (hk : ψ.kind = Kind.mut) :
    ∃ av z, AgW ψ.wit av ∧ ResU.CompR av z σ := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  cases h with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      obtain ⟨p, hp, hp₁⟩ := List.mem_map.mp ((hsm.2 l).mpr ⟨ψ, e, hk⟩)
      obtain ⟨χ, hχ, hav⟩ := AgWitsM.mem hwm p hp
      rw [hp₁, e] at hχ
      cases Option.some.inj hχ
      obtain ⟨z, hz⟩ :=
        BigComp.mem_factor hR ResU.compLawsR hbm p.2 (List.mem_map.mpr ⟨p, hp, rfl⟩)
      obtain ⟨z₁, hz₁⟩ :=
        ResU.Comp.factor_trans hR ResU.compLawsR hz
          (ResU.Comp.comm_of_laws hR ResU.compLawsR ha)
      obtain ⟨z₂, hz₂⟩ := ResU.Comp.factor_trans hR ResU.compLawsR hz₁ hσ
      exact ⟨p.2, z₂, hav, hz₂⟩

/-- **What `✓(ρ ● ρₘ)` says about a borrowed resource.**  If `ρₘ` carries
`mut(_, _, ρᵥ, _)` at some location and `ρ ● ρₘ` is valid, then `ρ ▸◂ ρᵥ`.

This is `[TR]` Lemma 6.17's two closing sentences at once.  On this carrier
"`ρ` and `ρᵥ` agree on imm cells up to lifetimes" and "`ρ` and `ρₘ ● ρᵥ` have
disjoint own-or-mut cells" are the single statement `ρ ▸◂ ρᵥ`, and the printed
display supplies both halves.  At a location, an own-or-mut cell of either
resource reaches `ex(ρ)_●` or `ex(ρₘ)_●` unchanged (`ExS.get_of_ne_imm`, with
`ExW.wit_le` for the descent into `ρᵥ`), while an `imm` cell reaches `ag(ρ)` or
`ag(ρₘ)` over the same value and witness (`AgW.get_imm`, `AgW.mut_wit_le`).  The
final `●` of `⦇ρ ● ρₘ⦈` rules out the three mixed cases, since `ex` carries no
`imm` cell (Lemma 6.36, `ExS.immFree`, §18); and in the remaining one `○` forces
the two `imm` cells to share a value and a witness.
`[about ours: `[TR]` Lemma 6.17's proof (p. 8) from its display onward, stated
for a `mut` cell in any `ρₘ` rather than a lone one]` -/
theorem ResU.CompatS.of_valid_mut {ρ ρm ρv ρ' : ResU Loc Val} {l : Loc}
    {ψ : CellU Loc Val} (hm : ρm.get l = some ψ) (hk : ψ.kind = Kind.mut)
    (hwit : ψ.wit = ρv) (h : ResU.CompS ρ ρm ρ') (hval : ResU.Valid ρ') :
    ResU.CompatS ρ ρv := by
  obtain ⟨σ, hσ⟩ := hval
  obtain ⟨e₁, e₂, e, a₁, a₂, a, -, -, he₁, he₂, hec, ha₁, ha₂, hac, hc, -, -⟩ :=
    ResU.Flat.split_factors h hσ
  obtain ⟨ev, zv, hev, hzv⟩ :=
    ExW.wit_le (fun _ _ _ hcc => CellU.CompS.compat hcc) ResU.compLawsS he₂ hm hk
  obtain ⟨av, za, hav, hza⟩ := AgW.mut_wit_le ha₂ hm hk
  rw [hwit] at hev hav
  intro l' χ χv f fv
  by_cases k₁ : χ.kind = Kind.imm <;> by_cases k₂ : χv.kind = Kind.imm
  · -- Both `imm`.  Their images meet inside `ag(ρ) ○ ag(ρₘ)`, whose cell-level
    -- `○` forces one value and one witness on them.
    obtain ⟨d₁, g₁, m₁, n₁, w₁⟩ := AgW.get_imm ha₁ f k₁
    obtain ⟨d₂, g₂, m₂, n₂, w₂⟩ := AgW.get_imm hav fv k₂
    obtain ⟨d₃, g₃, m₃, n₃, w₃⟩ := ResU.CompR.get_imm_left hza g₂ m₂
    obtain ⟨hve, hwt⟩ := CellU.compatR_iff.mp (hac.1 l' d₁ d₃ g₁ g₃)
    refine CellU.compatS_iff.mpr ⟨k₁, k₂, ?_, ?_⟩
    · exact n₁.symm.trans (hve.trans (n₃.trans n₂))
    · refine w₁.symm.trans ?_
      exact (hwt (by rw [m₁]; simp) (by rw [m₃]; simp)).trans (w₃.trans w₂)
  · -- `χ` is `imm` and `χᵥ` is not: the first reaches `ag`, the second `ex`, and
    -- the final `●` of `⦇ρ ● ρₘ⦈` would have to compose them.
    obtain ⟨d₁, g₁, m₁, -, -⟩ := AgW.get_imm ha₁ f k₁
    obtain ⟨d, g, -, -, -⟩ := ResU.CompR.get_imm_left hac g₁ m₁
    have hev' : e.get l' = some χv :=
      (ResU.CompS.get_right_of_ne_imm hec
        (ResU.CompS.get_left_of_ne_imm hzv (ExS.get_of_ne_imm hev fv k₂) k₂).2 k₂).2
    exact absurd (CellU.CompatS.kinds (hc.1 l' χv d hev' g)).1 k₂
  · -- The mirror: `χ` is not `imm` and `χᵥ` is.
    obtain ⟨d₂, g₂, m₂, -, -⟩ := AgW.get_imm hav fv k₂
    obtain ⟨d₃, g₃, m₃, -, -⟩ := ResU.CompR.get_imm_left hza g₂ m₂
    obtain ⟨d, g, -, -, -⟩ := ResU.CompR.get_imm_right hac g₃ m₃
    have he' : e.get l' = some χ :=
      (ResU.CompS.get_left_of_ne_imm hec (ExS.get_of_ne_imm he₁ f k₁) k₁).2
    exact absurd (CellU.CompatS.kinds (hc.1 l' χ d he' g)).1 k₁
  · -- Neither is `imm`: both reach `ex(ρ)_●` and `ex(ρₘ)_●` at `ℓ′` unchanged,
    -- and `●` keeps the own-or-mut cells of its two operands disjoint.
    have h₂ : e₂.get l' = some χv :=
      (ResU.CompS.get_left_of_ne_imm hzv (ExS.get_of_ne_imm hev fv k₂) k₂).2
    have h₁ := (ResU.CompS.get_left_of_ne_imm hec (ExS.get_of_ne_imm he₁ f k₁) k₁).1
    rw [h₁] at h₂
    exact absurd h₂ (by simp)

end BoCa.Fig16

end
