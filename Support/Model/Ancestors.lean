import Paper.S5_Model.Definitions
import Support.Model.Algebra
import Support.Model.CellFacts
import Support.Model.Cells
import Support.Model.Prelude
import Support.Model.WalkSplitting

/-!
# Support — Model — Ancestors

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
the immutable ancestor of a cell of the aliasable walk: every cell of `ag(ρ)` sits beneath an `imm` cell, carried across `↭` — the step of Lemma 6.48's printed proof that 6.59 reaches for.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- A cell of kind `imm` is `imm(ᾱ, v, ρ)` at its own value and witness. -/
theorem CellU.imm_eta {ψ : CellU Loc Val} (h : ψ.kind = Kind.imm) :
    ∃ (s : LSet) (hs : ψ.wit.InStratum s.join),
      ψ = CellU.immOf s ψ.erase ψ.wit hs := by
  rcases CellU.rep ψ with ⟨v, rfl⟩ | ⟨s, v, ρ, hs, rfl⟩ | ⟨b, v, ρ, hs, P, hw, rfl⟩
  · exact absurd h (by simp)
  · exact ⟨s, by simpa using hs, by simp⟩
  · exact absurd h (by simp)

/-- **`○` does not invent a non-`imm` cell.**  If the composite is not `imm`
then one of the operands is not `imm`, over the same value and the same witness:
clause (2) and clause (5) return an `imm` cell, and every other clause returns an
operand or, at clause (3), a `mut` over both operands' shared value and witness.
This is `CellU.CompR.mut_source` with `own` cells allowed alongside.
`[about ours: `[TR]` p. 5's `○` read backwards at a non-`imm` result]` -/
theorem CellU.CompR.nonimm_source {ψ₁ ψ₂ ψ : CellU Loc Val}
    (h : CellU.CompR ψ₁ ψ₂ ψ) (hk : ψ.kind ≠ Kind.imm) :
    (ψ₁.kind ≠ Kind.imm ∧ ψ₁.wit = ψ.wit ∧ ψ₁.erase = ψ.erase) ∨
    (ψ₂.kind ≠ Kind.imm ∧ ψ₂.wit = ψ.wit ∧ ψ₂.erase = ψ.erase) := by
  have hmut : ∀ (b : Life) (v : Val) (ρ : ResU Loc Val) (hb : ρ.InStratum b)
      (P : Val → SPropS Loc Val b) (hP : P v ⟨ρ, hb⟩),
      (CellU.mutOf b v ρ hb P hP).kind ≠ Kind.imm := by
    intro b v ρ hb P hP
    rw [CellU.kind_mutOf]
    exact fun c => Kind.noConfusion c
  cases h with
  | same ζ => exact Or.inl ⟨hk, rfl, rfl⟩
  | strict k => exact absurd (CellU.CompS.kind (CellU.compS_spec _ _ k)) hk
  | mutMut a b v ρ ha hb P Q hP hQ =>
      exact Or.inl ⟨hmut _ _ _ _ _ _, by simp, by simp⟩
  | mutOwn a v ρ ha P hP => exact Or.inl ⟨hmut _ _ _ _ _ _, rfl, rfl⟩
  | ownMut a v ρ ha P hP => exact Or.inr ⟨hmut _ _ _ _ _ _, rfl, rfl⟩
  | immOwn s v ρ hh => exact absurd (CellU.kind_immOf s v ρ hh) hk
  | ownImm s v ρ hh => exact absurd (CellU.kind_immOf s v ρ hh) hk
  | immMut s v ρ hh b hb P hP => exact absurd (CellU.kind_immOf s v ρ hh) hk
  | mutImm s v ρ hh b hb P hP => exact absurd (CellU.kind_immOf s v ρ hh) hk

/-- The same at a location of a `○`. -/
theorem ResU.CompR.nonimm_source {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompR ρ₁ ρ₂ ρ)
    {m : Loc} {ψ : CellU Loc Val} (hg : ρ.get m = some ψ)
    (hk : ψ.kind ≠ Kind.imm) :
    (∃ ξ, ρ₁.get m = some ξ ∧ ξ.kind ≠ Kind.imm ∧ ξ.wit = ψ.wit ∧
        ξ.erase = ψ.erase) ∨
    (∃ ξ, ρ₂.get m = some ξ ∧ ξ.kind ≠ Kind.imm ∧ ξ.wit = ψ.wit ∧
        ξ.erase = ψ.erase) := by
  rcases ResU.Comp.get h m with ⟨-, -, f⟩ | ⟨ξ, f₁, -, f⟩ | ⟨ξ, -, f₂, f⟩ |
      ⟨ξ₁, ξ₂, ξ, f₁, f₂, f, hC⟩
  · rw [f] at hg; exact absurd hg (by simp)
  · rw [show ξ = ψ from Option.some.inj (f.symm.trans hg)] at f₁
    exact Or.inl ⟨ψ, f₁, hk, rfl, rfl⟩
  · rw [show ξ = ψ from Option.some.inj (f.symm.trans hg)] at f₂
    exact Or.inr ⟨ψ, f₂, hk, rfl, rfl⟩
  · rw [show ξ = ψ from Option.some.inj (f.symm.trans hg)] at hC
    rcases CellU.CompR.nonimm_source hC hk with ⟨k₁, w₁, e₁⟩ | ⟨k₂, w₂, e₂⟩
    · exact Or.inl ⟨ξ₁, f₁, k₁, w₁, e₁⟩
    · exact Or.inr ⟨ξ₂, f₂, k₂, w₂, e₂⟩

/-- …and along `⨀`. -/
theorem BigComp.nonimm_source :
    ∀ {L : List (ResU Loc Val)} {b : ResU Loc Val},
      BigComp CellU.CompatR CellU.CompR L b →
      ∀ {m : Loc} {ψ : CellU Loc Val}, b.get m = some ψ → ψ.kind ≠ Kind.imm →
      ∃ σ ∈ L, ∃ ξ, σ.get m = some ξ ∧ ξ.kind ≠ Kind.imm ∧ ξ.wit = ψ.wit ∧
        ξ.erase = ψ.erase := by
  intro L
  induction L with
  | nil => intro b h m ψ hg hk; cases h; exact absurd hg (by simp)
  | cons σ L' ih =>
      intro b h m ψ hg hk
      cases h with
      | cons hrest hc =>
          rcases ResU.CompR.nonimm_source hc hg hk with
            ⟨ξ, e, k, w, er⟩ | ⟨ξ, e, k, w, er⟩
          · exact ⟨σ, List.mem_cons_self, ξ, e, k, w, er⟩
          · obtain ⟨τ, hm, ξ', e', k', w', er'⟩ := ih hrest e k
            exact ⟨τ, List.mem_cons_of_mem _ hm, ξ', e',
              k', w'.trans w, er'.trans er⟩

/-- **An `imm` operand survives `○`**: the composite is an `imm` cell over the
same value and the same witness.  Clauses (1), (2) and (5) are the only ones
with an `imm` operand, and each returns one. -/
theorem CellU.CompR.imm_left_eq {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompR ψ₁ ψ₂ ψ)
    {s : LSet} {u : Val} {χ : ResU Loc Val} {hh : χ.InStratum s.join}
    (e : ψ₁ = CellU.immOf s u χ hh) :
    ∃ (s' : LSet) (h' : χ.InStratum s'.join), ψ = CellU.immOf s' u χ h' := by
  cases h with
  | same ζ => exact ⟨s, hh, e⟩
  | strict k =>
      obtain ⟨s₁, s₂, v, ρ, k₁, k₂, k₃, e₁, e₂, e₃⟩ := CellU.compS_spec _ _ k
      rw [e₁] at e
      obtain ⟨-, hv, hρ⟩ := CellU.immOf_inj e.symm
      subst hv; subst hρ
      exact ⟨s₁ ∪ s₂, k₃, e₃⟩
  | mutMut a b v ρ ha hb P Q hP hQ => exact absurd e.symm CellU.immOf_ne_mutOf
  | mutOwn a v ρ ha P hP => exact absurd e.symm CellU.immOf_ne_mutOf
  | ownMut a v ρ ha P hP => exact absurd e CellU.ownOf_ne_immOf
  | immOwn s' v ρ hh' =>
      obtain ⟨-, hv, hρ⟩ := CellU.immOf_inj e.symm
      subst hv; subst hρ
      exact ⟨s', hh', rfl⟩
  | ownImm s' v ρ hh' => exact absurd e CellU.ownOf_ne_immOf
  | immMut s' v ρ hh' b hb P hP =>
      obtain ⟨-, hv, hρ⟩ := CellU.immOf_inj e.symm
      subst hv; subst hρ
      exact ⟨s', hh', rfl⟩
  | mutImm s' v ρ hh' b hb P hP => exact absurd e.symm CellU.immOf_ne_mutOf

/-- The same at a location of a `○`: an `imm` cell of a `○`-factor is an `imm`
cell of the composite, over the same value and the same witness. -/
theorem ResU.CompR.imm_left_get {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompR ρ₁ ρ₂ ρ)
    {m : Loc} {s : LSet} {u : Val} {χ : ResU Loc Val} {hh : χ.InStratum s.join}
    (hg : ρ₁.get m = some (CellU.immOf s u χ hh)) :
    ∃ (s' : LSet) (h' : χ.InStratum s'.join),
      ρ.get m = some (CellU.immOf s' u χ h') := by
  rcases ResU.Comp.get h m with ⟨f₁, -, -⟩ | ⟨ξ, f₁, -, f⟩ | ⟨ξ, f₁, -, -⟩ |
      ⟨ξ₁, ξ₂, ξ, f₁, f₂, f, hC⟩
  · rw [hg] at f₁; exact absurd f₁ (by simp)
  · exact ⟨s, hh, f.trans (congrArg some (Option.some.inj (f₁.symm.trans hg)))⟩
  · rw [hg] at f₁; exact absurd f₁ (by simp)
  · obtain ⟨s', h', he⟩ :=
      CellU.CompR.imm_left_eq hC (Option.some.inj (f₁.symm.trans hg))
    exact ⟨s', h', f.trans (congrArg some he)⟩

end BoCa.Fig16

end
