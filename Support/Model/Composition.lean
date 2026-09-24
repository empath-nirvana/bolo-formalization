import Paper.S5_Model.Definitions
import Support.Model.CellFacts
import Support.Model.Lifetimes
import Support.Model.Prelude

/-!
# Support — Model — Composition

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
the cell- and resource-level compositions `●` and `○` and compatibilities `▶◀` and `⋈` as graphs: functionality, symmetry, the specification of each clause, erasure and witnesses.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

theorem CellU.CompatS.symm {ψ₁ ψ₂ : CellU Loc Val} (h : ψ₁.CompatS ψ₂) : ψ₂.CompatS ψ₁ := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, e₁, e₂⟩ := h
  exact ⟨s₂, s₁, v, ρ, h₂, h₁, e₂, e₁⟩

/-- `▶◀` relates `imm` cells only. -/
theorem CellU.CompatS.kinds {ψ₁ ψ₂ : CellU Loc Val} (h : ψ₁.CompatS ψ₂) :
    ψ₁.kind = Kind.imm ∧ ψ₂.kind = Kind.imm := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, e₁, e₂⟩ := h
  exact ⟨by rw [e₁]; rfl, by rw [e₂]; rfl⟩

theorem CellU.mutOf_congr {b b' : Life} (e : b = b') (v : Val) (ρ : ResU Loc Val)
    (h : ρ.InStratum b) (h' : ρ.InStratum b')
    (P : Val → SPropS Loc Val b) (P' : Val → SPropS Loc Val b')
    (hP : P v ⟨ρ, h⟩) (hP' : P' v ⟨ρ, h'⟩)
    (eP : ∀ (r : ResU Loc Val) (hr : r.InStratum b) (hr' : r.InStratum b') (w : Val),
        P w ⟨r, hr⟩ ↔ P' w ⟨r, hr'⟩) :
    CellU.mutOf b v ρ h P hP = CellU.mutOf b' v ρ h' P' hP' := by
  subst e
  have hPP : P = P' := by
    funext w r
    exact propext (eP r.val r.property r.property w)
  subst hPP
  rfl

theorem CellU.CompS.compat {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompS ψ₁ ψ₂ ψ) :
    ψ₁.CompatS ψ₂ := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, -, e₁, e₂, -⟩ := h
  exact ⟨s₁, s₂, v, ρ, h₁, h₂, e₁, e₂⟩

/-- `ψ ● ψ = ψ`, the case `○`'s clauses (1) and (2) share. -/
theorem CellU.compS_self (ψ : CellU Loc Val) (h : ψ.CompatS ψ) : CellU.compS ψ ψ h = ψ := by
  obtain ⟨s₁, s₂, v, ρ, k₁, k₂, k₃, e₁, e₂, e₃⟩ := CellU.compS_spec ψ ψ h
  obtain ⟨hs, -, -⟩ := CellU.immOf_inj (e₁.symm.trans e₂)
  subst hs
  rw [e₃, e₁]
  exact CellU.immOf_congr (LSet.union_self s₁) rfl rfl k₃ k₁

/-- The overlap of clauses (1) and (3): two equal `mut` cells.  Clause (1)
returns `mut(α, v, ρ, P̂)` and clause (3) returns `mut(α ⊓ α, v, ρ, P̂ ∧ P̂)`, and
those are the same cell — `α ⊓ α = α`, and `P̂ ∧ P̂` and `P̂` are the same subset
of `Res_α`. -/
theorem CellU.compR_same_mutMut (a : Life) (v : Val) (ρ : ResU Loc Val)
    (ha : ρ.InStratum a) (P : Val → SPropS Loc Val a) (hP : P v ⟨ρ, ha⟩) :
    CellU.mutOf (a ⊓ a) v ρ ha.inf_left (SPropS.conj P P)
        (SPropS.conj_holds ha ha hP hP)
      = CellU.mutOf a v ρ ha P hP := by
  refine CellU.mutOf_congr (Life.meet_self a) v ρ _ _ _ _ _ _ ?_
  intro r hr hr' w
  constructor
  · rintro ⟨⟨k, hk⟩, -⟩; exact hk
  · intro hw; exact ⟨⟨hr', hw⟩, ⟨hr', hw⟩⟩

/-- A weakening of inversion for `○`, and only that: the six clauses that
return one of their arguments are recorded by *which* argument they return
together with the tags of the two cells.  **It is not an inversion principle.**
The last four disjuncts discard the shared `v` and the shared `ρ`, so they are
satisfiable by tags alone and cannot be used to refute a composition.  What
recovers the sharing is `CompR.erase` and `CompR.wit`, which are proved by
`cases` on `CompR` directly.  This weakening exists because it is exactly what
`CompR.functional` needs and no more. -/
theorem CellU.CompR.inv {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompR ψ₁ ψ₂ ψ) :
    (ψ₁ = ψ₂ ∧ ψ = ψ₁)
    ∨ (∃ k : ψ₁.CompatS ψ₂, ψ = CellU.compS ψ₁ ψ₂ k)
    ∨ (∃ (a b : Life) (v : Val) (ρ : ResU Loc Val) (ha : ρ.InStratum a) (hb : ρ.InStratum b)
        (P : Val → SPropS Loc Val a) (Q : Val → SPropS Loc Val b)
        (hP : P v ⟨ρ, ha⟩) (hQ : Q v ⟨ρ, hb⟩),
        ψ₁ = CellU.mutOf a v ρ ha P hP ∧ ψ₂ = CellU.mutOf b v ρ hb Q hQ ∧
        ψ = CellU.mutOf (a ⊓ b) v ρ ha.inf_left (SPropS.conj P Q)
              (SPropS.conj_holds ha hb hP hQ))
    ∨ (ψ = ψ₁ ∧ ψ₂.kind = Kind.own ∧ ψ₁.kind ≠ Kind.own)
    ∨ (ψ = ψ₂ ∧ ψ₁.kind = Kind.own ∧ ψ₂.kind ≠ Kind.own)
    ∨ (ψ = ψ₁ ∧ ψ₁.kind = Kind.imm ∧ ψ₂.kind = Kind.mut)
    ∨ (ψ = ψ₂ ∧ ψ₁.kind = Kind.mut ∧ ψ₂.kind = Kind.imm) := by
  cases h with
  | same χ => exact Or.inl ⟨rfl, rfl⟩
  | strict k => exact Or.inr (Or.inl ⟨k, rfl⟩)
  | mutMut a b v ρ ha hb P Q hP hQ =>
      exact Or.inr (Or.inr (Or.inl ⟨a, b, v, ρ, ha, hb, P, Q, hP, hQ, rfl, rfl, rfl⟩))
  | mutOwn a v ρ ha P hP =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by simp⟩)))
  | ownMut a v ρ ha P hP =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by simp⟩))))
  | immOwn s v ρ hs =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by simp⟩)))
  | ownImm s v ρ hs =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by simp⟩))))
  | immMut s v ρ hs b hb P hP =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))))
  | mutImm s v ρ hs b hb P hP =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))))

/-- Clause (3) applied to two cells that clause (1) also matches. -/
theorem CellU.compR_mutMut_of_eq {a b : Life} {v : Val} {ρ : ResU Loc Val}
    {ha : ρ.InStratum a} {hb : ρ.InStratum b}
    {P : Val → SPropS Loc Val a} {Q : Val → SPropS Loc Val b}
    {hP : P v ⟨ρ, ha⟩} {hQ : Q v ⟨ρ, hb⟩}
    (e : CellU.mutOf a v ρ ha P hP = CellU.mutOf b v ρ hb Q hQ) :
    CellU.mutOf (a ⊓ b) v ρ ha.inf_left (SPropS.conj P Q)
        (SPropS.conj_holds ha hb hP hQ)
      = CellU.mutOf b v ρ hb Q hQ := by
  have hab : a = b := CellU.mutOf_at e
  subst hab
  obtain ⟨-, -, hPQ⟩ := CellU.mutOf_inj e
  subst hPQ
  exact CellU.compR_same_mutMut a v ρ ha P hP

/-- Clause (3) is determined by its two operands. -/
theorem CellU.compR_mutMut_det {a b a' b' : Life} {v v' : Val} {ρ ρ' : ResU Loc Val}
    {ha : ρ.InStratum a} {hb : ρ.InStratum b}
    {ha' : ρ'.InStratum a'} {hb' : ρ'.InStratum b'}
    {P : Val → SPropS Loc Val a} {Q : Val → SPropS Loc Val b}
    {P' : Val → SPropS Loc Val a'} {Q' : Val → SPropS Loc Val b'}
    {hP : P v ⟨ρ, ha⟩} {hQ : Q v ⟨ρ, hb⟩} {hP' : P' v' ⟨ρ', ha'⟩} {hQ' : Q' v' ⟨ρ', hb'⟩}
    (e1 : CellU.mutOf a v ρ ha P hP = CellU.mutOf a' v' ρ' ha' P' hP')
    (e2 : CellU.mutOf b v ρ hb Q hQ = CellU.mutOf b' v' ρ' hb' Q' hQ') :
    CellU.mutOf (a ⊓ b) v ρ ha.inf_left (SPropS.conj P Q)
        (SPropS.conj_holds ha hb hP hQ)
      = CellU.mutOf (a' ⊓ b') v' ρ' ha'.inf_left (SPropS.conj P' Q')
          (SPropS.conj_holds ha' hb' hP' hQ') := by
  have haa : a = a' := CellU.mutOf_at e1
  subst haa
  obtain ⟨hv, hρ, hPP⟩ := CellU.mutOf_inj e1
  subst hv; subst hρ; subst hPP
  have hbb : b = b' := CellU.mutOf_at e2
  subst hbb
  obtain ⟨-, -, hQQ⟩ := CellU.mutOf_inj e2
  subst hQQ
  rfl

set_option maxHeartbeats 1000000 in
/-- **`○` is single-valued.**  Its printed clauses overlap in exactly two
places — (1) with (2) at two equal `imm` cells, and (1) with (3) at two equal
`mut` cells — and at both the two clauses return the same cell, by
`compS_self` and `compR_same_mutMut`.  Every other pair of clauses is excluded
by the tags of the two operands. -/
theorem CellU.CompR.functional {ψ₁ ψ₂ ψ ψ' : CellU Loc Val}
    (h : CellU.CompR ψ₁ ψ₂ ψ) (h' : CellU.CompR ψ₁ ψ₂ ψ') : ψ = ψ' := by
  have H := h.inv
  have H' := h'.inv
  clear h h'
  rcases H with ⟨e12, rfl⟩ | ⟨k, rfl⟩ | ⟨a, b, v, ρ, ha, hb, P, Q, hP, hQ, rfl, e2, rfl⟩ |
      ⟨rfl, ka, kb⟩ | ⟨rfl, ka, kb⟩ | ⟨rfl, ka, kb⟩ | ⟨rfl, ka, kb⟩ <;>
    rcases H' with ⟨f12, rfl⟩ | ⟨k', rfl⟩ |
        ⟨a', b', v', ρ', ha', hb', P', Q', hP', hQ', g1, g2, rfl⟩ |
      ⟨rfl, ma, mb⟩ | ⟨rfl, ma, mb⟩ | ⟨rfl, ma, mb⟩ | ⟨rfl, ma, mb⟩ <;>
    first
      | rfl
      | simp_all
      | skip
  case inl.inr.inl => exact (CellU.compS_self _ _).symm
  case inl.inr.inr.inl => exact (CellU.compR_mutMut_of_eq e12).symm
  case inr.inl.inl => exact CellU.compS_self _ _
  case inr.inl.inr.inr.inl => exact absurd (CellU.CompatS.kinds k).1 (by rw [g1]; simp)
  case inr.inl.inr.inr.inr.inl => exact absurd (CellU.CompatS.kinds k).2 (by rw [ma]; simp)
  case inr.inl.inr.inr.inr.inr.inl =>
    exact absurd (CellU.CompatS.kinds k).1 (by rw [ma]; simp)
  case inr.inr.inl.inl => exact CellU.compR_mutMut_of_eq f12
  case inr.inr.inl.inr.inl => exact absurd (CellU.CompatS.kinds k').1 (by simp)
  case inr.inr.inl.inr.inr.inl => exact CellU.compR_mutMut_det g1 e2.symm
  case inr.inr.inr.inl.inr.inl =>
    exact absurd (CellU.CompatS.kinds k').2 (by rw [ka]; simp)
  case inr.inr.inr.inr.inl.inr.inl =>
    exact absurd (CellU.CompatS.kinds k').1 (by rw [ka]; simp)
  case inr.inl.inr.inr.inr.inr.inr.inl =>
    exact absurd (CellU.CompatS.kinds k).2 (by rw [mb]; simp)
  case inr.inl.inr.inr.inr.inr.inr.inr =>
    exact absurd (CellU.CompatS.kinds k).1 (by rw [ma]; simp)
  case inr.inr.inr.inr.inr.inl.inr.inl =>
    exact absurd (CellU.CompatS.kinds k').2 (by rw [kb]; simp)
  case inr.inr.inr.inr.inr.inr.inr.inl =>
    exact absurd (CellU.CompatS.kinds k').1 (by rw [ka]; simp)

theorem ResU.Compat.comm {C : CellU Loc Val → CellU Loc Val → Prop}
    (hC : ∀ ψ₁ ψ₂, C ψ₁ ψ₂ → C ψ₂ ψ₁) {ρ₁ ρ₂ : ResU Loc Val}
    (h : ResU.Compat C ρ₁ ρ₂) : ResU.Compat C ρ₂ ρ₁ :=
  fun l ψ₁ ψ₂ e₁ e₂ => hC _ _ (h l ψ₂ ψ₁ e₂ e₁)

theorem ResU.Compat.of_disjoint {C : CellU Loc Val → CellU Loc Val → Prop}
    {ρ₁ ρ₂ : ResU Loc Val} (h : ∀ l, ρ₁.get l = none ∨ ρ₂.get l = none) :
    ResU.Compat C ρ₁ ρ₂ := by
  intro l ψ₁ ψ₂ e₁ e₂
  rcases h l with e | e
  · rw [e] at e₁; exact absurd e₁ (by simp)
  · rw [e] at e₂; exact absurd e₂ (by simp)

/-- The schema is single-valued whenever the cellwise operation is. -/
theorem ResU.Comp.functional {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ ψ', C ψ₁ ψ₂ ψ → C ψ₁ ψ₂ ψ' → ψ = ψ')
    {ρ₁ ρ₂ ρ ρ' : ResU Loc Val}
    (h : ResU.Comp R C ρ₁ ρ₂ ρ) (h' : ResU.Comp R C ρ₁ ρ₂ ρ') : ρ = ρ' := by
  refine PMap.ext fun l => ?_
  have h₁ := h.2 l
  have h₂ := h'.2 l
  cases e₁ : ρ₁.get l <;> cases e₂ : ρ₂.get l <;> rw [e₁, e₂] at h₁ h₂
  · rw [h₁, h₂]
  · rw [h₁, h₂]
  · rw [h₁, h₂]
  · obtain ⟨ψa, ha, hCa⟩ := h₁
    obtain ⟨ψb, hb, hCb⟩ := h₂
    rw [ha, hb, hC _ _ _ _ hCa hCb]

theorem ResU.CompatS.symm {ρ₁ ρ₂ : ResU Loc Val} (h : ResU.CompatS ρ₁ ρ₂) :
    ResU.CompatS ρ₂ ρ₁ := ResU.Compat.comm (fun _ _ a => a.symm) h

theorem ResU.CompS.functional {ρ₁ ρ₂ ρ ρ' : ResU Loc Val}
    (h : ResU.CompS ρ₁ ρ₂ ρ) (h' : ResU.CompS ρ₁ ρ₂ ρ') : ρ = ρ' :=
  ResU.Comp.functional (R := CellU.CompatS) (C := CellU.CompS)
    (fun _ _ _ _ a b => CellU.CompS.functional a b) h h'

theorem optCompS_optComp (o₁ o₂ : Option (CellU Loc Val))
    (k : ∀ ψ₁ ψ₂, o₁ = some ψ₁ → o₂ = some ψ₂ → CellU.CompatS ψ₁ ψ₂) :
    OptComp CellU.CompS o₁ o₂ (optCompS o₁ o₂ k) := by
  cases o₁ with
  | none => cases o₂ with
    | none => rfl
    | some ψ => rfl
  | some ψ₁ => cases o₂ with
    | none => rfl
    | some ψ₂ => exact ⟨_, rfl, CellU.compS_spec _ _ _⟩

theorem ResU.compS_spec (ρ₁ ρ₂ : ResU Loc Val) (h : ResU.CompatS ρ₁ ρ₂) :
    ResU.CompS ρ₁ ρ₂ (ρ₁.compS ρ₂ h) :=
  ⟨h, fun l => optCompS_optComp (ρ₁.get l) (ρ₂.get l) _⟩

/-- `ρ₁ ▶◀ ρ₂` iff `ρ₁ ● ρ₂` is defined — `[TR]` Lemma 6.9 (p. 7, 600 dpi),
whose own proof is "By definition".  `ResU.Comp` carries the printed guard as
its first conjunct, so the forward direction is that conjunct and nothing more.
The content is the converse — building the composite from `▶◀` alone, which
goes through `CellU.compS_defined_iff` at every overlapping location.
Stated on this file's carrier, which is Fig. 16 on the settled reading of the
`fin` mark (§3, and the `[variant: …]` at `Res`).  `[as printed]` -/
theorem ResU.compS_defined_iff (ρ₁ ρ₂ : ResU Loc Val) :
    (∃ ρ, ResU.CompS ρ₁ ρ₂ ρ) ↔ ResU.CompatS ρ₁ ρ₂ :=
  ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨_, ResU.compS_spec ρ₁ ρ₂ h⟩⟩

/-- `●` merges cells over a common value, so it preserves the erasure. -/
theorem CellU.CompS.erase {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompS ψ₁ ψ₂ ψ) :
    ψ.erase = ψ₁.erase ∧ ψ.erase = ψ₂.erase := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, e₁, e₂, e₃⟩ := h
  subst e₁; subst e₂; subst e₃
  exact ⟨rfl, rfl⟩

/-- **Every clause of `○` composes cells over a common value.**  The print binds
one `v` in each of the five clauses; this reads that back off the relation. -/
theorem CellU.CompR.erase {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompR ψ₁ ψ₂ ψ) :
    ψ₁.erase = ψ₂.erase ∧ ψ.erase = ψ₁.erase := by
  cases h with
  | same χ => exact ⟨rfl, rfl⟩
  | strict k =>
      obtain ⟨e₁, e₂⟩ := CellU.CompS.erase (CellU.compS_spec _ _ k)
      exact ⟨e₁.symm.trans e₂, e₁⟩
  | mutMut a b v ρ ha hb P Q hP hQ => exact ⟨rfl, rfl⟩
  | mutOwn a v ρ ha P hP => exact ⟨rfl, rfl⟩
  | ownMut a v ρ ha P hP => exact ⟨rfl, rfl⟩
  | immOwn s v ρ hs => exact ⟨rfl, rfl⟩
  | ownImm s v ρ hs => exact ⟨rfl, rfl⟩
  | immMut s v ρ hs b hb P hP => exact ⟨rfl, rfl⟩
  | mutImm s v ρ hs b hb P hP => exact ⟨rfl, rfl⟩

/-- **Every clause of `○` that composes two non-`own` cells composes them over a
common witness.**  The print binds one `ρ` in clauses (2), (3) and (5); this
reads that back off the relation. -/
theorem CellU.CompR.wit {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompR ψ₁ ψ₂ ψ)
    (k₁ : ψ₁.kind ≠ Kind.own) (k₂ : ψ₂.kind ≠ Kind.own) : ψ₁.wit = ψ₂.wit := by
  cases h with
  | same χ => rfl
  | strict k =>
      obtain ⟨s₁, s₂, v, ρ, h₁, h₂, e₁, e₂⟩ := k
      rw [e₁, e₂, CellU.wit_immOf, CellU.wit_immOf]
  | mutMut a b v ρ ha hb P Q hP hQ => rw [CellU.wit_mutOf, CellU.wit_mutOf]
  | mutOwn a v ρ ha P hP => exact absurd rfl k₂
  | ownMut a v ρ ha P hP => exact absurd rfl k₁
  | immOwn s v ρ hs => exact absurd rfl k₂
  | ownImm s v ρ hs => exact absurd rfl k₁
  | immMut s v ρ hs b hb P hP => rw [CellU.wit_immOf, CellU.wit_mutOf]
  | mutImm s v ρ hs b hb P hP => rw [CellU.wit_mutOf, CellU.wit_immOf]

theorem CellU.compS_comm (ψ₁ ψ₂ : CellU Loc Val) (h : ψ₁.CompatS ψ₂) :
    CellU.compS ψ₁ ψ₂ h = CellU.compS ψ₂ ψ₁ h.symm := by
  obtain ⟨s₁, s₂, v, ρ, k₁, k₂, k₃, e₁, e₂, e₃⟩ := CellU.compS_spec ψ₂ ψ₁ h.symm
  refine CellU.CompS.functional (CellU.compS_spec ψ₁ ψ₂ h) ?_
  refine ⟨s₂, s₁, v, ρ, k₂, k₁, ?_, e₂, e₁, ?_⟩
  · exact (LSet.union_comm s₁ s₂) ▸ k₃
  · rw [e₃]
    exact CellU.immOf_congr (LSet.union_comm s₁ s₂) rfl rfl k₃ _

theorem SPropS.conj_comm {a b : Life} (P : Val → SPropS Loc Val a)
    (Q : Val → SPropS Loc Val b) (r : ResU Loc Val)
    (hr : r.InStratum (a ⊓ b)) (hr' : r.InStratum (b ⊓ a)) (w : Val) :
    SPropS.conj P Q w ⟨r, hr⟩ ↔ SPropS.conj Q P w ⟨r, hr'⟩ :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- `○` is commutative on cells — the cell half of `[TR]` Lemma 6.2 (p. 6).
`[about ours: the cell-level fact the resource-level Lemma 6.2 is proved from;
6.2 itself is `ResU.Comp.comm` in §20]` -/
theorem CellU.CompR.comm {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompR ψ₁ ψ₂ ψ) :
    CellU.CompR ψ₂ ψ₁ ψ := by
  cases h with
  | same => exact CellU.CompR.same _
  | strict k => exact (CellU.compS_comm _ _ k) ▸ CellU.CompR.strict k.symm
  | mutMut a b v ρ ha hb P Q hP hQ =>
      have := CellU.CompR.mutMut b a v ρ hb ha Q P hQ hP
      refine (?_ : CellU.mutOf (b ⊓ a) v ρ _ (SPropS.conj Q P) _
        = CellU.mutOf (a ⊓ b) v ρ _ (SPropS.conj P Q) _) ▸ this
      refine CellU.mutOf_congr (Life.meet_comm b a) v ρ _ _ _ _ _ _ ?_
      intro r hr hr' w
      exact (SPropS.conj_comm Q P r hr hr' w)
  | mutOwn a v ρ ha P hP => exact .ownMut a v ρ ha P hP
  | ownMut a v ρ ha P hP => exact .mutOwn a v ρ ha P hP
  | immOwn s v ρ hs => exact .ownImm s v ρ hs
  | ownImm s v ρ hs => exact .immOwn s v ρ hs
  | immMut s v ρ hs b hb P hP => exact .mutImm s v ρ hs b hb P hP
  | mutImm s v ρ hs b hb P hP => exact .immMut s v ρ hs b hb P hP

theorem CellU.CompatR.symm {ψ₁ ψ₂ : CellU Loc Val} (h : ψ₁.CompatR ψ₂) : ψ₂.CompatR ψ₁ :=
  ⟨h.choose, h.choose_spec.comm⟩

theorem CellU.CompatR.of_compatS {ψ₁ ψ₂ : CellU Loc Val} (h : ψ₁.CompatS ψ₂) :
    ψ₁.CompatR ψ₂ := ⟨_, CellU.CompR.strict h⟩

theorem ResU.CompR.functional {ρ₁ ρ₂ ρ ρ' : ResU Loc Val}
    (h : ResU.CompR ρ₁ ρ₂ ρ) (h' : ResU.CompR ρ₁ ρ₂ ρ') : ρ = ρ' :=
  ResU.Comp.functional (R := CellU.CompatR) (C := CellU.CompR)
    (fun _ _ _ _ a b => CellU.CompR.functional a b) h h'

end BoCa.Fig16

end
