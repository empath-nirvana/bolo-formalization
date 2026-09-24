import Paper.S5_Model.Definitions
import Support.Model.Cells
import Support.Model.Composition
import Support.Model.Lifetimes
import Support.Model.Prelude

/-!
# Support — Model — Algebra

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
the associativity and commutativity machinery behind Lemmas 6.1–6.4: cell-level associativity of `○` clause by clause, the laws of the schema `◐`, and the iterated composition `⨀` up to permutation.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Fig16

/-- Proof apparatus: an option is `none` or a `some`, without rewriting the
goal the way `cases e : o` does. -/
theorem optSplit {A : Type} (o : Option A) : o = none ∨ ∃ a, o = some a := by
  cases o
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- The four shapes a location can take in a composite.  Proof apparatus for the
lemmas below that unfold `◐`. -/
theorem ResU.Comp.get {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.Comp R C ρ₁ ρ₂ ρ) (l : Loc) :
    (ρ₁.get l = none ∧ ρ₂.get l = none ∧ ρ.get l = none)
    ∨ (∃ ψ, ρ₁.get l = some ψ ∧ ρ₂.get l = none ∧ ρ.get l = some ψ)
    ∨ (∃ ψ, ρ₁.get l = none ∧ ρ₂.get l = some ψ ∧ ρ.get l = some ψ)
    ∨ (∃ ψ₁ ψ₂ ψ, ρ₁.get l = some ψ₁ ∧ ρ₂.get l = some ψ₂ ∧ ρ.get l = some ψ ∧
        C ψ₁ ψ₂ ψ) := by
  have hp := h.2 l
  rcases optSplit (ρ₁.get l) with e₁ | ⟨ψ₁, e₁⟩ <;>
    rcases optSplit (ρ₂.get l) with e₂ | ⟨ψ₂, e₂⟩ <;> rw [e₁, e₂] at hp
  · exact Or.inl ⟨e₁, e₂, hp⟩
  · exact Or.inr (Or.inr (Or.inl ⟨ψ₂, e₁, e₂, hp⟩))
  · exact Or.inr (Or.inl ⟨ψ₁, e₁, e₂, hp⟩)
  · obtain ⟨χ, hχ, hC⟩ := hp
    exact Or.inr (Or.inr (Or.inr ⟨ψ₁, ψ₂, χ, e₁, e₂, hχ, hC⟩))

/-- `●` is commutative on cells — the cell half of `[TR]` Lemma 6.2 at `●`,
by commutativity of `∪` on lifetime sets, which is what its proof says.
`[about ours: the cell-level fact the resource-level 6.2 is proved from]` -/
theorem CellU.CompS.comm {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompS ψ₁ ψ₂ ψ) :
    CellU.CompS ψ₂ ψ₁ ψ := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, e₁, e₂, e₃⟩ := h
  have hu : s₁ ∪ s₂ = s₂ ∪ s₁ := LSet.union_comm s₁ s₂
  refine ⟨s₂, s₁, v, ρ, h₂, h₁, hu ▸ h₃, e₂, e₁, ?_⟩
  rw [e₃]
  exact CellU.immOf_congr hu rfl rfl h₃ _

/-- **`[TR]` Lemma 6.2** (p. 6): `ρ₁ ◐ ρ₂ = ρ₂ ◐ ρ₁`.  As a graph this is
definedness and value together, which is the print's equation between partial
expressions.  Stated once in the schema and discharged below at both `●` and
`○`, which is how the print proves it.  `[as printed]` -/
theorem ResU.Comp.comm {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hR : ∀ ψ₁ ψ₂, R ψ₁ ψ₂ → R ψ₂ ψ₁)
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → C ψ₂ ψ₁ ψ)
    {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.Comp R C ρ₁ ρ₂ ρ) :
    ResU.Comp R C ρ₂ ρ₁ ρ := by
  refine ⟨ResU.Compat.comm hR h.1, fun l => ?_⟩
  rcases h.get l with ⟨e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ |
      ⟨ψ₁, ψ₂, ψ, e₁, e₂, e, hC'⟩ <;> rw [e₁, e₂]
  · exact e
  · exact e
  · exact e
  · exact ⟨ψ, e, hC _ _ _ hC'⟩

/-- `[TR]` Lemma 6.2 at `●`.  `[as printed]` -/
theorem ResU.CompS.comm {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ) :
    ResU.CompS ρ₂ ρ₁ ρ :=
  ResU.Comp.comm (fun _ _ a => a.symm) (fun _ _ _ a => a.comm) h

/-- `[TR]` Lemma 6.2 at `○`.  `[as printed]` -/
theorem ResU.CompR.comm {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompR ρ₁ ρ₂ ρ) :
    ResU.CompR ρ₂ ρ₁ ρ :=
  ResU.Comp.comm (fun _ _ a => a.symm) (fun _ _ _ a => a.comm) h

/-- `●` is associative on cells.  Both sides compose three `imm` cells over one
`v` and one `ρ`, and the lifetime set of the result is the three-fold union
either way, so this is `LSet.union_assoc` and nothing else — which is what
`[TR]` Lemma 6.3's `●` case says: "associativity follows from the associativity
of `∪`".
`[about ours: the cell-level fact the resource-level 6.3 is proved from]` -/
theorem CellU.compS_assoc (ψ₁ ψ₂ ψ₃ ω : CellU Loc Val) :
    (∃ χ, CellU.CompS ψ₂ ψ₃ χ ∧ CellU.CompS ψ₁ χ ω) ↔
    (∃ υ, CellU.CompS ψ₁ ψ₂ υ ∧ CellU.CompS υ ψ₃ ω) := by
  constructor
  · rintro ⟨χ, ⟨t₂, t₃, v, ρ, k₂, k₃, k₂₃, e₂, e₃, eχ⟩,
      ⟨s₁, s', u, σ, m₁, m', m'', f₁, fχ, fω⟩⟩
    obtain ⟨hs, hv, hρ⟩ := CellU.immOf_inj (eχ.symm.trans fχ)
    subst hs; subst hv; subst hρ
    have h₁₂ : ρ.InStratum (s₁ ∪ t₂).join := by
      show ρ.InStratum (s₁.join ⊔ t₂.join)
      rcases le_total s₁.join t₂.join with hle | hle
      · rw [sup_eq_right.mpr hle]; exact k₂
      · rw [sup_eq_left.mpr hle]; exact m₁
    refine ⟨CellU.immOf (s₁ ∪ t₂) v ρ h₁₂,
      ⟨s₁, t₂, v, ρ, m₁, k₂, h₁₂, f₁, e₂, rfl⟩,
      ⟨s₁ ∪ t₂, t₃, v, ρ, h₁₂, k₃, ?_, rfl, e₃, ?_⟩⟩
    · exact (LSet.union_assoc s₁ t₂ t₃) ▸ m''
    · rw [fω]
      exact CellU.immOf_congr (LSet.union_assoc s₁ t₂ t₃).symm rfl rfl m'' _
  · rintro ⟨υ, ⟨s₁, t₂, v, ρ, m₁, k₂, m₁₂, f₁, e₂, eυ⟩,
      ⟨s', t₃, u, σ, m', k₃, m'', fυ, e₃, fω⟩⟩
    obtain ⟨hs, hv, hρ⟩ := CellU.immOf_inj (eυ.symm.trans fυ)
    subst hs; subst hv; subst hρ
    have h₂₃ : ρ.InStratum (t₂ ∪ t₃).join := by
      show ρ.InStratum (t₂.join ⊔ t₃.join)
      rcases le_total t₂.join t₃.join with hle | hle
      · rw [sup_eq_right.mpr hle]; exact k₃
      · rw [sup_eq_left.mpr hle]; exact k₂
    refine ⟨CellU.immOf (t₂ ∪ t₃) v ρ h₂₃,
      ⟨t₂, t₃, v, ρ, k₂, k₃, h₂₃, e₂, e₃, rfl⟩,
      ⟨s₁, t₂ ∪ t₃, v, ρ, m₁, h₂₃, ?_, f₁, rfl, ?_⟩⟩
    · exact (LSet.union_assoc s₁ t₂ t₃).symm ▸ m''
    · rw [fω]
      exact CellU.immOf_congr (LSet.union_assoc s₁ t₂ t₃) rfl rfl m'' _

/-- Clause (2) of `○` in the shape the case analysis below needs it: at two
`imm` cells over one `v` and one `ρ`, `○` is `●`, whose value is the `imm` cell
on the union of the two lifetime sets. -/
theorem CellU.compR_immImm (s t : LSet) (v : Val) (ρ : ResU Loc Val)
    (hs : ρ.InStratum s.join) (ht : ρ.InStratum t.join)
    (hst : ρ.InStratum (s ∪ t).join) :
    CellU.CompR (CellU.immOf s v ρ hs) (CellU.immOf t v ρ ht)
      (CellU.immOf (s ∪ t) v ρ hst) := by
  have k : CellU.CompatS (CellU.immOf s v ρ hs) (CellU.immOf t v ρ ht) :=
    ⟨s, t, v, ρ, hs, ht, rfl, rfl⟩
  exact (CellU.compS_immOf k hst) ▸ CellU.CompR.strict k

/-- `own` is a left unit of `○`: clauses (1), (4) and (5) between them return the
other operand whenever the first is `own(v)`. -/
theorem CellU.compR_own_left {v : Val} {ψ ω : CellU Loc Val}
    (h : CellU.CompR (CellU.ownOf v) ψ ω) : ω = ψ := by
  cases h with
  | same => rfl
  | strict k => exact absurd (CellU.CompatS.kinds k).1 (by simp)
  | ownMut => rfl
  | ownImm => rfl

/-- `own` is a right unit of `○`. -/
theorem CellU.compR_own_right {v : Val} {ψ ω : CellU Loc Val}
    (h : CellU.CompR ψ (CellU.ownOf v) ω) : ω = ψ := by
  cases h with
  | same => rfl
  | strict k => exact absurd (CellU.CompatS.kinds k).2 (by simp)
  | mutOwn => rfl
  | immOwn => rfl

/-- …and it is a left unit exactly on the cells carrying its value: clause (1)
for an `own` cell, clause (5) for an `imm`, clause (4) for a `mut`. -/
theorem CellU.compR_own_left_of_erase {v : Val} {ψ : CellU Loc Val}
    (h : ψ.erase = v) : CellU.CompR (CellU.ownOf v) ψ ψ := by
  rcases CellU.rep ψ with ⟨w, rfl⟩ | ⟨s, w, ρ, hs, rfl⟩ | ⟨b, w, ρ, hb, P, hP, rfl⟩ <;>
    simp only [CellU.erase_ownOf, CellU.erase_immOf, CellU.erase_mutOf] at h <;> subst h
  · exact CellU.CompR.same _
  · exact CellU.CompR.ownImm _ _ _ _
  · exact CellU.CompR.ownMut _ _ _ _ _ _

/-- …and a right unit on the same cells. -/
theorem CellU.compR_own_right_of_erase {v : Val} {ψ : CellU Loc Val}
    (h : ψ.erase = v) : CellU.CompR ψ (CellU.ownOf v) ψ := by
  rcases CellU.rep ψ with ⟨w, rfl⟩ | ⟨s, w, ρ, hs, rfl⟩ | ⟨b, w, ρ, hb, P, hP, rfl⟩ <;>
    simp only [CellU.erase_ownOf, CellU.erase_immOf, CellU.erase_mutOf] at h <;> subst h
  · exact CellU.CompR.same _
  · exact CellU.CompR.immOwn _ _ _ _
  · exact CellU.CompR.mutOwn _ _ _ _ _ _

/-- `[TR]` p. 7, the `○` case at `ψ₁ = own(v)`: "if `ρ₁(ℓ)` is owned, then the
`mut`/`imm` is the result" — and, in clause (1), the `own` itself.  Either way
`ψ₁ ○ (ψ₂ ○ ψ₃) = ψ₂ ○ ψ₃`, so `ψ₁ ○ ψ₂ = ψ₂` is the intermediate. -/
theorem CellU.compR_assoc_own_left {v : Val} {ψ₂ ψ₃ χ ω : CellU Loc Val}
    (h₂₃ : CellU.CompR ψ₂ ψ₃ χ) (h₁χ : CellU.CompR (CellU.ownOf v) χ ω) :
    ∃ υ, CellU.CompR (CellU.ownOf v) ψ₂ υ ∧ CellU.CompR υ ψ₃ ω := by
  have hω : ω = χ := CellU.compR_own_left h₁χ
  subst hω
  refine ⟨ψ₂, CellU.compR_own_left_of_erase ?_, h₂₃⟩
  have e₁ := (CellU.CompR.erase h₁χ).1
  have e₂ := (CellU.CompR.erase h₂₃).2
  simp only [CellU.erase_ownOf] at e₁
  exact (e₂.symm.trans e₁.symm)

/-- `[TR]` p. 7, the `○` case at `ψ₂ = own(v)`: the middle operand drops out on
both sides. -/
theorem CellU.compR_assoc_own_mid {v : Val} {ψ₁ ψ₃ χ ω : CellU Loc Val}
    (h₂₃ : CellU.CompR (CellU.ownOf v) ψ₃ χ) (h₁χ : CellU.CompR ψ₁ χ ω) :
    ∃ υ, CellU.CompR ψ₁ (CellU.ownOf v) υ ∧ CellU.CompR υ ψ₃ ω := by
  have hχ : χ = ψ₃ := CellU.compR_own_left h₂₃
  subst hχ
  refine ⟨ψ₁, CellU.compR_own_right_of_erase ?_, h₁χ⟩
  have e₁ := (CellU.CompR.erase h₁χ).1
  have e₂ := (CellU.CompR.erase h₂₃).1
  simp only [CellU.erase_ownOf] at e₂
  exact e₁.trans e₂.symm

/-- `[TR]` p. 7, the `○` case at `ψ₃ = own(v)`: the last operand drops out on
both sides, so the result of the left-hand composite is itself the
intermediate. -/
theorem CellU.compR_assoc_own_right {v : Val} {ψ₁ ψ₂ χ ω : CellU Loc Val}
    (h₂₃ : CellU.CompR ψ₂ (CellU.ownOf v) χ) (h₁χ : CellU.CompR ψ₁ χ ω) :
    ∃ υ, CellU.CompR ψ₁ ψ₂ υ ∧ CellU.CompR υ (CellU.ownOf v) ω := by
  have hχ : χ = ψ₂ := CellU.compR_own_right h₂₃
  subst hχ
  refine ⟨ω, h₁χ, CellU.compR_own_right_of_erase ?_⟩
  have e₁ := (CellU.CompR.erase h₁χ).2
  have e₂ := (CellU.CompR.erase h₁χ).1
  have e₃ := (CellU.CompR.erase h₂₃).1
  simp only [CellU.erase_ownOf] at e₃
  exact e₁.trans (e₂.trans e₃)

end BoCa.Fig16

namespace BoCa.Fig16

/-- `(α ⊓ β) ⊓ γ = α ⊓ (β ⊓ γ)` — the "associativity of `⊓`" `[TR]` Lemma 6.3's
`○` case appeals to (p. 7), at `⊓ ≜ max`.
`[about ours: an arithmetic fact the print cites by name]` -/
theorem Life.meet_assoc (a b c : Life) : (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c) :=
  Nat.max_assoc a b c

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- `(P̂ ∧ Q̂) ∧ R̂` and `P̂ ∧ (Q̂ ∧ R̂)` are the same subset of `Res` — the
"associativity of `∧`" the same case appeals to.  The two are stated at the two
strata `(α ⊓ β) ⊓ γ` and `α ⊓ (β ⊓ γ)`, which `Life.meet_assoc` identifies, and
each conjunct carries its own stratum-membership proof, so the equivalence is
just reassociation. -/
theorem SPropS.conj_assoc {a b c : Life} (P : Val → SPropS Loc Val a)
    (Q : Val → SPropS Loc Val b) (T : Val → SPropS Loc Val c) (r : ResU Loc Val)
    (hr : r.InStratum ((a ⊓ b) ⊓ c)) (hr' : r.InStratum (a ⊓ (b ⊓ c))) (w : Val) :
    SPropS.conj (SPropS.conj P Q) T w ⟨r, hr⟩ ↔
      SPropS.conj P (SPropS.conj Q T) w ⟨r, hr'⟩ := by
  simp only [SPropS.conj, SPropS.embed]
  constructor
  · rintro ⟨⟨hab, ⟨h₁, hp⟩, h₂, hq⟩, h₃, ht⟩
    have hbc : r.InStratum (b ⊓ c) := by
      rcases le_total b c with hle | hle
      · rw [inf_eq_left.mpr hle]; exact h₂
      · rw [inf_eq_right.mpr hle]; exact h₃
    exact ⟨⟨h₁, hp⟩, ⟨hbc, ⟨h₂, hq⟩, ⟨h₃, ht⟩⟩⟩
  · rintro ⟨⟨h₁, hp⟩, hbc, ⟨h₂, hq⟩, h₃, ht⟩
    have hab : r.InStratum (a ⊓ b) := by
      rcases le_total a b with hle | hle
      · rw [inf_eq_left.mpr hle]; exact h₁
      · rw [inf_eq_right.mpr hle]; exact h₂
    exact ⟨⟨hab, ⟨h₁, hp⟩, ⟨h₂, hq⟩⟩, ⟨h₃, ht⟩⟩

/-- An `imm` cell is not an `own` cell — a side condition `CompR.wit` takes. -/
theorem CellU.kind_immOf_ne_own {s : LSet} {v : Val} {ρ : ResU Loc Val}
    {h : ρ.InStratum s.join} : (CellU.immOf s v ρ h).kind ≠ Kind.own :=
  fun hk => Kind.noConfusion hk

/-- A `mut` cell is not an `own` cell — the other side condition. -/
theorem CellU.kind_mutOf_ne_own {b : Life} {v : Val} {ρ : ResU Loc Val} {h : ρ.InStratum b}
    {P : Val → SPropS Loc Val b} {hw : P v ⟨ρ, h⟩} :
    (CellU.mutOf b v ρ h P hw).kind ≠ Kind.own :=
  fun hk => Kind.noConfusion hk

/-- The `○` case of `[TR]` Lemma 6.3 (pp. 6-7) at the cell level, left to
right.
`[about ours: one direction of the cell-level fact 6.3's `○` case needs]` -/
theorem CellU.compR_assoc_forward {ψ₁ ψ₂ ψ₃ χ ω : CellU Loc Val}
    (h₂₃ : CellU.CompR ψ₂ ψ₃ χ) (h₁χ : CellU.CompR ψ₁ χ ω) :
    ∃ υ, CellU.CompR ψ₁ ψ₂ υ ∧ CellU.CompR υ ψ₃ ω := by
  rcases CellU.rep ψ₁ with ⟨v₁, rfl⟩ | ⟨s, v₁, σ, ks, rfl⟩ | ⟨a, v₁, σ, ka, P, hP, rfl⟩
  · exact CellU.compR_assoc_own_left h₂₃ h₁χ
  · rcases CellU.rep ψ₂ with ⟨v₂, rfl⟩ | ⟨t, v₂, ρ, kt, rfl⟩ | ⟨b, v₂, ρ, kb, Q, hQ, rfl⟩
    · exact CellU.compR_assoc_own_mid h₂₃ h₁χ
    · rcases CellU.rep ψ₃ with ⟨v₃, rfl⟩ | ⟨u, v₃, τ, ku, rfl⟩ | ⟨c, v₃, τ, kc, T, hT, rfl⟩
      · exact CellU.compR_assoc_own_right h₂₃ h₁χ
      · -- `imm ○ (imm ○ imm)`: three unions, reassociated.
        have ev := (CellU.CompR.erase h₂₃).1
        have ew := CellU.CompR.wit h₂₃ CellU.kind_immOf_ne_own CellU.kind_immOf_ne_own
        simp only [CellU.erase_immOf] at ev
        simp only [CellU.wit_immOf] at ew
        subst ev; subst ew
        have ktu : ρ.InStratum (t ∪ u).join := by
          show ρ.InStratum (t.join ⊔ u.join)
          rcases le_total t.join u.join with hle | hle
          · rw [sup_eq_right.mpr hle]; exact ku
          · rw [sup_eq_left.mpr hle]; exact kt
        have hχ : χ = CellU.immOf (t ∪ u) v₂ ρ ktu :=
          CellU.CompR.functional h₂₃ (CellU.compR_immImm t u v₂ ρ kt ku ktu)
        subst hχ
        have ev' := ((CellU.CompR.erase h₁χ).1).symm
        have ew' := (CellU.CompR.wit h₁χ CellU.kind_immOf_ne_own CellU.kind_immOf_ne_own).symm
        simp only [CellU.erase_immOf] at ev'
        simp only [CellU.wit_immOf] at ew'
        subst ev'; subst ew'
        have kstu : ρ.InStratum (s ∪ (t ∪ u)).join := by
          show ρ.InStratum (s.join ⊔ (t ∪ u).join)
          rcases le_total s.join (t ∪ u).join with hle | hle
          · rw [sup_eq_right.mpr hle]; exact ktu
          · rw [sup_eq_left.mpr hle]; exact ks
        have hω : ω = CellU.immOf (s ∪ (t ∪ u)) v₂ ρ kstu :=
          CellU.CompR.functional h₁χ (CellU.compR_immImm s (t ∪ u) v₂ ρ ks ktu kstu)
        subst hω
        have kst : ρ.InStratum (s ∪ t).join := by
          show ρ.InStratum (s.join ⊔ t.join)
          rcases le_total s.join t.join with hle | hle
          · rw [sup_eq_right.mpr hle]; exact kt
          · rw [sup_eq_left.mpr hle]; exact ks
        refine ⟨CellU.immOf (s ∪ t) v₂ ρ kst,
          CellU.compR_immImm s t v₂ ρ ks kt kst, ?_⟩
        have kstu' : ρ.InStratum ((s ∪ t) ∪ u).join := by
          show ρ.InStratum ((s ∪ t).join ⊔ u.join)
          rcases le_total (s ∪ t).join u.join with hle | hle
          · rw [sup_eq_right.mpr hle]; exact ku
          · rw [sup_eq_left.mpr hle]; exact kst
        have h := CellU.compR_immImm (s ∪ t) u v₂ ρ kst ku kstu'
        rwa [CellU.immOf_congr (LSet.union_assoc s t u) rfl rfl kstu' kstu] at h
      · -- `imm ○ (imm ○ mut)`: the `mut` is absorbed on both sides.
        have ev := (CellU.CompR.erase h₂₃).1
        have ew := CellU.CompR.wit h₂₃ CellU.kind_immOf_ne_own CellU.kind_mutOf_ne_own
        simp only [CellU.erase_immOf, CellU.erase_mutOf] at ev
        simp only [CellU.wit_immOf, CellU.wit_mutOf] at ew
        subst ev; subst ew
        have hχ : χ = CellU.immOf t v₂ ρ kt :=
          CellU.CompR.functional h₂₃ (CellU.CompR.immMut t v₂ ρ kt c kc T hT)
        subst hχ
        have ev' := ((CellU.CompR.erase h₁χ).1).symm
        have ew' := (CellU.CompR.wit h₁χ CellU.kind_immOf_ne_own CellU.kind_immOf_ne_own).symm
        simp only [CellU.erase_immOf] at ev'
        simp only [CellU.wit_immOf] at ew'
        subst ev'; subst ew'
        have kst : ρ.InStratum (s ∪ t).join := ResU.InStratum.sup ks kt
        have hω : ω = CellU.immOf (s ∪ t) v₂ ρ kst :=
          CellU.CompR.functional h₁χ (CellU.compR_immImm s t v₂ ρ ks kt kst)
        subst hω
        exact ⟨CellU.immOf (s ∪ t) v₂ ρ kst, CellU.compR_immImm s t v₂ ρ ks kt kst,
          CellU.CompR.immMut (s ∪ t) v₂ ρ kst c kc T hT⟩
    · rcases CellU.rep ψ₃ with ⟨v₃, rfl⟩ | ⟨u, v₃, τ, ku, rfl⟩ | ⟨c, v₃, τ, kc, T, hT, rfl⟩
      · exact CellU.compR_assoc_own_right h₂₃ h₁χ
      · -- `imm ○ (mut ○ imm)`: the `mut` is absorbed on both sides.
        have ev := (CellU.CompR.erase h₂₃).1
        have ew := CellU.CompR.wit h₂₃ CellU.kind_mutOf_ne_own CellU.kind_immOf_ne_own
        simp only [CellU.erase_immOf, CellU.erase_mutOf] at ev
        simp only [CellU.wit_immOf, CellU.wit_mutOf] at ew
        subst ev; subst ew
        have hχ : χ = CellU.immOf u v₂ ρ ku :=
          CellU.CompR.functional h₂₃ (CellU.CompR.mutImm u v₂ ρ ku b kb Q hQ)
        subst hχ
        have ev' := ((CellU.CompR.erase h₁χ).1).symm
        have ew' := (CellU.CompR.wit h₁χ CellU.kind_immOf_ne_own CellU.kind_immOf_ne_own).symm
        simp only [CellU.erase_immOf] at ev'
        simp only [CellU.wit_immOf] at ew'
        subst ev'; subst ew'
        have ksu : ρ.InStratum (s ∪ u).join := ResU.InStratum.sup ks ku
        have hω : ω = CellU.immOf (s ∪ u) v₂ ρ ksu :=
          CellU.CompR.functional h₁χ (CellU.compR_immImm s u v₂ ρ ks ku ksu)
        subst hω
        exact ⟨CellU.immOf s v₂ ρ ks, CellU.CompR.immMut s v₂ ρ ks b kb Q hQ,
          CellU.compR_immImm s u v₂ ρ ks ku ksu⟩
      · -- `imm ○ (mut ○ mut)`: the `imm` is the result either way.
        have ev := (CellU.CompR.erase h₂₃).1
        have ew := CellU.CompR.wit h₂₃ CellU.kind_mutOf_ne_own CellU.kind_mutOf_ne_own
        simp only [CellU.erase_mutOf] at ev
        simp only [CellU.wit_mutOf] at ew
        subst ev; subst ew
        have kbc : ρ.InStratum (b ⊓ c) := kb.mono inf_le_left
        have hQT : SPropS.conj Q T v₂ ⟨ρ, kbc⟩ := SPropS.conj_holds kb kc hQ hT
        have hχ : χ = CellU.mutOf (b ⊓ c) v₂ ρ kbc (SPropS.conj Q T) hQT :=
          CellU.CompR.functional h₂₃ (CellU.CompR.mutMut b c v₂ ρ kb kc Q T hQ hT)
        subst hχ
        have ev' := ((CellU.CompR.erase h₁χ).1).symm
        have ew' := (CellU.CompR.wit h₁χ CellU.kind_immOf_ne_own CellU.kind_mutOf_ne_own).symm
        simp only [CellU.erase_immOf, CellU.erase_mutOf] at ev'
        simp only [CellU.wit_immOf, CellU.wit_mutOf] at ew'
        subst ev'; subst ew'
        have hω : ω = CellU.immOf s v₂ ρ ks :=
          CellU.CompR.functional h₁χ
            (CellU.CompR.immMut s v₂ ρ ks (b ⊓ c) kbc (SPropS.conj Q T) hQT)
        subst hω
        exact ⟨CellU.immOf s v₂ ρ ks, CellU.CompR.immMut s v₂ ρ ks b kb Q hQ,
          CellU.CompR.immMut s v₂ ρ ks c kc T hT⟩
  · rcases CellU.rep ψ₂ with ⟨v₂, rfl⟩ | ⟨t, v₂, ρ, kt, rfl⟩ | ⟨b, v₂, ρ, kb, Q, hQ, rfl⟩
    · exact CellU.compR_assoc_own_mid h₂₃ h₁χ
    · rcases CellU.rep ψ₃ with ⟨v₃, rfl⟩ | ⟨u, v₃, τ, ku, rfl⟩ | ⟨c, v₃, τ, kc, T, hT, rfl⟩
      · exact CellU.compR_assoc_own_right h₂₃ h₁χ
      · -- `mut ○ (imm ○ imm)`: the `mut` is absorbed on both sides.
        have ev := (CellU.CompR.erase h₂₃).1
        have ew := CellU.CompR.wit h₂₃ CellU.kind_immOf_ne_own CellU.kind_immOf_ne_own
        simp only [CellU.erase_immOf] at ev
        simp only [CellU.wit_immOf] at ew
        subst ev; subst ew
        have ktu : ρ.InStratum (t ∪ u).join := ResU.InStratum.sup kt ku
        have hχ : χ = CellU.immOf (t ∪ u) v₂ ρ ktu :=
          CellU.CompR.functional h₂₃ (CellU.compR_immImm t u v₂ ρ kt ku ktu)
        subst hχ
        have ev' := ((CellU.CompR.erase h₁χ).1).symm
        have ew' := (CellU.CompR.wit h₁χ CellU.kind_mutOf_ne_own CellU.kind_immOf_ne_own).symm
        simp only [CellU.erase_immOf, CellU.erase_mutOf] at ev'
        simp only [CellU.wit_immOf, CellU.wit_mutOf] at ew'
        subst ev'; subst ew'
        have hω : ω = CellU.immOf (t ∪ u) v₂ ρ ktu :=
          CellU.CompR.functional h₁χ (CellU.CompR.mutImm (t ∪ u) v₂ ρ ktu a ka P hP)
        subst hω
        exact ⟨CellU.immOf t v₂ ρ kt, CellU.CompR.mutImm t v₂ ρ kt a ka P hP,
          CellU.compR_immImm t u v₂ ρ kt ku ktu⟩
      · -- `mut ○ (imm ○ mut)`: the `imm` is the result either way.
        have ev := (CellU.CompR.erase h₂₃).1
        have ew := CellU.CompR.wit h₂₃ CellU.kind_immOf_ne_own CellU.kind_mutOf_ne_own
        simp only [CellU.erase_immOf, CellU.erase_mutOf] at ev
        simp only [CellU.wit_immOf, CellU.wit_mutOf] at ew
        subst ev; subst ew
        have hχ : χ = CellU.immOf t v₂ ρ kt :=
          CellU.CompR.functional h₂₃ (CellU.CompR.immMut t v₂ ρ kt c kc T hT)
        subst hχ
        have ev' := ((CellU.CompR.erase h₁χ).1).symm
        have ew' := (CellU.CompR.wit h₁χ CellU.kind_mutOf_ne_own CellU.kind_immOf_ne_own).symm
        simp only [CellU.erase_immOf, CellU.erase_mutOf] at ev'
        simp only [CellU.wit_immOf, CellU.wit_mutOf] at ew'
        subst ev'; subst ew'
        have hω : ω = CellU.immOf t v₂ ρ kt :=
          CellU.CompR.functional h₁χ (CellU.CompR.mutImm t v₂ ρ kt a ka P hP)
        subst hω
        exact ⟨CellU.immOf t v₂ ρ kt, CellU.CompR.mutImm t v₂ ρ kt a ka P hP,
          CellU.CompR.immMut t v₂ ρ kt c kc T hT⟩
    · rcases CellU.rep ψ₃ with ⟨v₃, rfl⟩ | ⟨u, v₃, τ, ku, rfl⟩ | ⟨c, v₃, τ, kc, T, hT, rfl⟩
      · exact CellU.compR_assoc_own_right h₂₃ h₁χ
      · -- `mut ○ (mut ○ imm)`: the `imm` is the result either way.
        have ev := (CellU.CompR.erase h₂₃).1
        have ew := CellU.CompR.wit h₂₃ CellU.kind_mutOf_ne_own CellU.kind_immOf_ne_own
        simp only [CellU.erase_immOf, CellU.erase_mutOf] at ev
        simp only [CellU.wit_immOf, CellU.wit_mutOf] at ew
        subst ev; subst ew
        have hχ : χ = CellU.immOf u v₂ ρ ku :=
          CellU.CompR.functional h₂₃ (CellU.CompR.mutImm u v₂ ρ ku b kb Q hQ)
        subst hχ
        have ev' := ((CellU.CompR.erase h₁χ).1).symm
        have ew' := (CellU.CompR.wit h₁χ CellU.kind_mutOf_ne_own CellU.kind_immOf_ne_own).symm
        simp only [CellU.erase_immOf, CellU.erase_mutOf] at ev'
        simp only [CellU.wit_immOf, CellU.wit_mutOf] at ew'
        subst ev'; subst ew'
        have hω : ω = CellU.immOf u v₂ ρ ku :=
          CellU.CompR.functional h₁χ (CellU.CompR.mutImm u v₂ ρ ku a ka P hP)
        subst hω
        exact ⟨CellU.mutOf (a ⊓ b) v₂ ρ (ka.mono inf_le_left) (SPropS.conj P Q)
            (SPropS.conj_holds ka kb hP hQ),
          CellU.CompR.mutMut a b v₂ ρ ka kb P Q hP hQ,
          CellU.CompR.mutImm u v₂ ρ ku (a ⊓ b) (ka.mono inf_le_left) (SPropS.conj P Q)
            (SPropS.conj_holds ka kb hP hQ)⟩
      · -- `mut ○ (mut ○ mut)`: associativity of `⊓` and of `∧`.
        have ev := (CellU.CompR.erase h₂₃).1
        have ew := CellU.CompR.wit h₂₃ CellU.kind_mutOf_ne_own CellU.kind_mutOf_ne_own
        simp only [CellU.erase_mutOf] at ev
        simp only [CellU.wit_mutOf] at ew
        subst ev; subst ew
        have kbc : ρ.InStratum (b ⊓ c) := kb.mono inf_le_left
        have hQT : SPropS.conj Q T v₂ ⟨ρ, kbc⟩ := SPropS.conj_holds kb kc hQ hT
        have hχ : χ = CellU.mutOf (b ⊓ c) v₂ ρ kbc (SPropS.conj Q T) hQT :=
          CellU.CompR.functional h₂₃ (CellU.CompR.mutMut b c v₂ ρ kb kc Q T hQ hT)
        subst hχ
        have ev' := ((CellU.CompR.erase h₁χ).1).symm
        have ew' := (CellU.CompR.wit h₁χ CellU.kind_mutOf_ne_own CellU.kind_mutOf_ne_own).symm
        simp only [CellU.erase_mutOf] at ev'
        simp only [CellU.wit_mutOf] at ew'
        subst ev'; subst ew'
        -- The composite of all three, in either association: `⊓` and `∧` do the work.
        have kabc : ρ.InStratum (a ⊓ (b ⊓ c)) := ka.mono inf_le_left
        have hPQT : SPropS.conj P (SPropS.conj Q T) v₂ ⟨ρ, kabc⟩ :=
          SPropS.conj_holds ka kbc hP hQT
        have hω : ω = CellU.mutOf (a ⊓ (b ⊓ c)) v₂ ρ kabc
            (SPropS.conj P (SPropS.conj Q T)) hPQT :=
          CellU.CompR.functional h₁χ
            (CellU.CompR.mutMut a (b ⊓ c) v₂ ρ ka kbc P (SPropS.conj Q T) hP hQT)
        subst hω
        have kab : ρ.InStratum (a ⊓ b) := ka.mono inf_le_left
        have hPQ : SPropS.conj P Q v₂ ⟨ρ, kab⟩ := SPropS.conj_holds ka kb hP hQ
        refine ⟨CellU.mutOf (a ⊓ b) v₂ ρ kab (SPropS.conj P Q) hPQ,
          CellU.CompR.mutMut a b v₂ ρ ka kb P Q hP hQ, ?_⟩
        have kabc' : ρ.InStratum ((a ⊓ b) ⊓ c) := kab.mono inf_le_left
        have hPQT' : SPropS.conj (SPropS.conj P Q) T v₂ ⟨ρ, kabc'⟩ :=
          SPropS.conj_holds kab kc hPQ hT
        have h : CellU.CompR (CellU.mutOf (a ⊓ b) v₂ ρ kab (SPropS.conj P Q) hPQ)
            (CellU.mutOf c v₂ ρ kc T hT)
            (CellU.mutOf ((a ⊓ b) ⊓ c) v₂ ρ kabc' (SPropS.conj (SPropS.conj P Q) T) hPQT') :=
          CellU.CompR.mutMut (a ⊓ b) c v₂ ρ kab kc (SPropS.conj P Q) T hPQ hT
        rwa [CellU.mutOf_congr (Life.meet_assoc a b c) v₂ ρ kabc' kabc
          (SPropS.conj (SPropS.conj P Q) T) (SPropS.conj P (SPropS.conj Q T)) hPQT' hPQT
          (fun r hr hr' w => SPropS.conj_assoc P Q T r hr hr' w)] at h

/-- **`○` is associative on cells** — the `○` half of `[TR]` Lemma 6.3, as the
Kleene equality between the two partial expressions.  The right-to-left half is
the left-to-right one read through `[TR]` Lemma 6.2: `○` is commutative, and the
printed equation is its own mirror image.
`[about ours: the cell-level fact the resource-level 6.3 is proved from]` -/
theorem CellU.compR_assoc (ψ₁ ψ₂ ψ₃ ω : CellU Loc Val) :
    (∃ χ, CellU.CompR ψ₂ ψ₃ χ ∧ CellU.CompR ψ₁ χ ω) ↔
    (∃ υ, CellU.CompR ψ₁ ψ₂ υ ∧ CellU.CompR υ ψ₃ ω) := by
  constructor
  · rintro ⟨χ, h₂₃, h₁χ⟩
    exact CellU.compR_assoc_forward h₂₃ h₁χ
  · rintro ⟨υ, h₁₂, hυ₃⟩
    obtain ⟨χ, hχ, hω⟩ := CellU.compR_assoc_forward h₁₂.comm hυ₃.comm
    exact ⟨χ, hχ.comm, hω.comm⟩

/-- `[TR]` Lemma 6.3 at one location, left to right.  Seven of the eight
patterns of definedness carry the composite through unchanged; the eighth is the
print's "only interesting case", and there the cell-level hypothesis is used. 
`[about ours: 6.3 read at a single location, which is how the print proves it]` -/
theorem OptComp.assoc_left {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ₃ ω, (∃ χ, C ψ₂ ψ₃ χ ∧ C ψ₁ χ ω) → (∃ υ, C ψ₁ ψ₂ υ ∧ C υ ψ₃ ω))
    {o₁ o₂ o₃ ox ow : Option (CellU Loc Val)}
    (h₂₃ : OptComp C o₂ o₃ ox) (h₁x : OptComp C o₁ ox ow) :
    ∃ oy, OptComp C o₁ o₂ oy ∧ OptComp C oy o₃ ow := by
  cases o₁ with
  | none =>
      cases o₂ with
      | none =>
          cases o₃ with
          | none =>
              have e : ox = none := h₂₃
              subst e
              have f : ow = none := h₁x
              subst f
              exact ⟨none, rfl, rfl⟩
          | some ψ₃ =>
              have e : ox = some ψ₃ := h₂₃
              subst e
              have f : ow = some ψ₃ := h₁x
              subst f
              exact ⟨none, rfl, rfl⟩
      | some ψ₂ =>
          cases o₃ with
          | none =>
              have e : ox = some ψ₂ := h₂₃
              subst e
              have f : ow = some ψ₂ := h₁x
              subst f
              exact ⟨some ψ₂, rfl, rfl⟩
          | some ψ₃ =>
              obtain ⟨χ, e, hc⟩ : ∃ χ, ox = some χ ∧ C ψ₂ ψ₃ χ := h₂₃
              subst e
              have f : ow = some χ := h₁x
              subst f
              exact ⟨some ψ₂, rfl, ⟨χ, rfl, hc⟩⟩
  | some ψ₁ =>
      cases o₂ with
      | none =>
          cases o₃ with
          | none =>
              have e : ox = none := h₂₃
              subst e
              have f : ow = some ψ₁ := h₁x
              subst f
              exact ⟨some ψ₁, rfl, rfl⟩
          | some ψ₃ =>
              have e : ox = some ψ₃ := h₂₃
              subst e
              obtain ⟨ω', f, hc⟩ : ∃ ω', ow = some ω' ∧ C ψ₁ ψ₃ ω' := h₁x
              subst f
              exact ⟨some ψ₁, rfl, ⟨ω', rfl, hc⟩⟩
      | some ψ₂ =>
          cases o₃ with
          | none =>
              have e : ox = some ψ₂ := h₂₃
              subst e
              obtain ⟨ω', f, hc⟩ : ∃ ω', ow = some ω' ∧ C ψ₁ ψ₂ ω' := h₁x
              subst f
              exact ⟨some ω', ⟨ω', rfl, hc⟩, rfl⟩
          | some ψ₃ =>
              obtain ⟨χ, e, hc₁⟩ : ∃ χ, ox = some χ ∧ C ψ₂ ψ₃ χ := h₂₃
              subst e
              obtain ⟨ω', f, hc₂⟩ : ∃ ω', ow = some ω' ∧ C ψ₁ χ ω' := h₁x
              subst f
              obtain ⟨υ, k₁, k₂⟩ := hC ψ₁ ψ₂ ψ₃ ω' ⟨χ, hc₁, hc₂⟩
              exact ⟨some υ, ⟨υ, rfl, k₁⟩, ⟨ω', rfl, k₂⟩⟩

/-- `[TR]` Lemma 6.3 at the resource level, left to right.  The intermediate
`ρ₁ ◐ ρ₂` is built location by location from `OptComp.assoc_left`; it is finite
because its domain is inside `dom(ρ₁) ∪ dom(ρ₂)`, and both printed guards are
read back off the cellwise composition through `hR`. 
`[about ours: one direction of 6.3; the printed Kleene equality is `ResU.Comp.assoc`]` -/
theorem ResU.Comp.assoc_left {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂)
    (hC : ∀ ψ₁ ψ₂ ψ₃ ω, (∃ χ, C ψ₂ ψ₃ χ ∧ C ψ₁ χ ω) → (∃ υ, C ψ₁ ψ₂ υ ∧ C υ ψ₃ ω))
    {ρ₁ ρ₂ ρ₃ x w : ResU Loc Val}
    (h₂₃ : ResU.Comp R C ρ₂ ρ₃ x) (h₁x : ResU.Comp R C ρ₁ x w) :
    ∃ y, ResU.Comp R C ρ₁ ρ₂ y ∧ ResU.Comp R C y ρ₃ w := by
  have key : ∀ l, ∃ o, OptComp C (ρ₁.get l) (ρ₂.get l) o ∧
      OptComp C o (ρ₃.get l) (w.get l) :=
    fun l => OptComp.assoc_left hC (h₂₃.2 l) (h₁x.2 l)
  -- Choosing at every location at once, so that the composite is a function.
  have choice : ∃ f : Loc → Option (CellU Loc Val), ∀ l,
      OptComp C (ρ₁.get l) (ρ₂.get l) (f l) ∧ OptComp C (f l) (ρ₃.get l) (w.get l) :=
    ⟨fun l => (key l).choose, fun l => (key l).choose_spec⟩
  obtain ⟨f, hf⟩ := choice
  have fin : FinDom f := by
    obtain ⟨d₁, k₁⟩ := ρ₁.finite
    obtain ⟨d₂, k₂⟩ := ρ₂.finite
    refine ⟨d₁ ++ d₂, fun l hl => ?_⟩
    cases e₁ : ρ₁.get l with
    | some ψ => exact List.mem_append.mpr (Or.inl (k₁ l (by rw [e₁]; simp)))
    | none =>
        cases e₂ : ρ₂.get l with
        | some ψ => exact List.mem_append.mpr (Or.inr (k₂ l (by rw [e₂]; simp)))
        | none =>
            have h := (hf l).1
            rw [e₁, e₂] at h
            exact absurd (show f l = none from h) hl
  refine ⟨⟨f, fin⟩, ⟨?_, fun l => (hf l).1⟩, ⟨?_, fun l => (hf l).2⟩⟩
  · intro l ψ₁ ψ₂ e₁ e₂
    have h := (hf l).1
    rw [e₁, e₂] at h
    obtain ⟨ψ, -, hc⟩ : ∃ ψ, f l = some ψ ∧ C ψ₁ ψ₂ ψ := h
    exact hR _ _ _ hc
  · intro l ψ ψ₃ e e₃
    have h := (hf l).2
    have e' : f l = some ψ := e
    rw [e', e₃] at h
    obtain ⟨ω, -, hc⟩ : ∃ ω, w.get l = some ω ∧ C ψ ψ₃ ω := h
    exact hR _ _ _ hc

/-- `◐` with its two arguments swapped is again an instance of `[TR]` p. 5's
schema — the guard and the cellwise composition are parameters, and swapping
them is a choice of parameter, not a new definition.  This is what makes the
right-to-left half of Lemma 6.3 the left-to-right half of its mirror. 
`[about ours: the schema at swapped parameters, proof apparatus]` -/
theorem OptComp.swap {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (o₁ o₂ o : Option (CellU Loc Val)) :
    OptComp (fun a b c => C b a c) o₁ o₂ o ↔ OptComp C o₂ o₁ o := by
  cases o₁ <;> cases o₂ <;> exact Iff.rfl

/-- The same, lifted: swapping `▶◁` and `◐` swaps the two operands of `ρ₁ ◐ ρ₂`
and leaves everything else alone. -/
theorem ResU.Comp.swap {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (ρ₁ ρ₂ ρ : ResU Loc Val) :
    ResU.Comp (fun a b => R b a) (fun a b c => C b a c) ρ₁ ρ₂ ρ ↔
      ResU.Comp R C ρ₂ ρ₁ ρ := by
  constructor
  · exact fun h => ⟨fun l ψ₁ ψ₂ e₁ e₂ => h.1 l ψ₂ ψ₁ e₂ e₁,
      fun l => (OptComp.swap _ _ _).mp (h.2 l)⟩
  · exact fun h => ⟨fun l ψ₁ ψ₂ e₁ e₂ => h.1 l ψ₂ ψ₁ e₂ e₁,
      fun l => (OptComp.swap _ _ _).mpr (h.2 l)⟩

/-- **`[TR]` Lemma 6.3** (p. 6, its `○` case on p. 7):
`ρ₁ ◐ (ρ₂ ◐ ρ₃) = ρ₁ ◐ ρ₂ ◐ ρ₃`.  Both sides are partial, so the printed
equation is the Kleene equality of the two partial expressions: at every result
`w`, one side is defined with value `w` exactly when the other is.  Stated once
in the schema, as the print states it; `hR` and `hC` are the print's own facts
about the cell-level `◐` the schema is instantiated at, discharged below at both
`●` and `○`, which is how the print proves it.  `[as printed]` -/
theorem ResU.Comp.assoc {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂)
    (hC : ∀ ψ₁ ψ₂ ψ₃ ω, (∃ χ, C ψ₂ ψ₃ χ ∧ C ψ₁ χ ω) ↔ (∃ υ, C ψ₁ ψ₂ υ ∧ C υ ψ₃ ω))
    (ρ₁ ρ₂ ρ₃ w : ResU Loc Val) :
    (∃ x, ResU.Comp R C ρ₂ ρ₃ x ∧ ResU.Comp R C ρ₁ x w) ↔
    (∃ y, ResU.Comp R C ρ₁ ρ₂ y ∧ ResU.Comp R C y ρ₃ w) := by
  constructor
  · rintro ⟨x, h₂₃, h₁x⟩
    exact ResU.Comp.assoc_left hR (fun a b c d => (hC a b c d).mp) h₂₃ h₁x
  · rintro ⟨y, h₁₂, hy₃⟩
    obtain ⟨x, hx, hw⟩ :=
      ResU.Comp.assoc_left (R := fun a b => R b a) (C := fun a b c => C b a c)
        (fun ψ₁ ψ₂ ψ h => hR ψ₂ ψ₁ ψ h)
        (fun ψ₁ ψ₂ ψ₃ ω h => (hC ψ₃ ψ₂ ψ₁ ω).mpr h)
        ((ResU.Comp.swap _ _ _).mpr h₁₂) ((ResU.Comp.swap _ _ _).mpr hy₃)
    exact ⟨x, (ResU.Comp.swap _ _ _).mp hx, (ResU.Comp.swap _ _ _).mp hw⟩

/-- `[TR]` Lemma 6.3 at `●`.  `[as printed]` -/
theorem ResU.CompS.assoc (ρ₁ ρ₂ ρ₃ w : ResU Loc Val) :
    (∃ x, ResU.CompS ρ₂ ρ₃ x ∧ ResU.CompS ρ₁ x w) ↔
    (∃ y, ResU.CompS ρ₁ ρ₂ y ∧ ResU.CompS y ρ₃ w) :=
  ResU.Comp.assoc (fun _ _ _ h => CellU.CompS.compat h)
    (fun ψ₁ ψ₂ ψ₃ ω => CellU.compS_assoc ψ₁ ψ₂ ψ₃ ω) ρ₁ ρ₂ ρ₃ w

/-- **`[TR]` Lemma 6.4** (p. 7): `ρ ◐ ∅ = ρ`.  Definedness and value together,
in the schema, hence at both `●` and `○`.  `[as printed]` -/
theorem ResU.comp_empty_right {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} (ρ : ResU Loc Val) :
    ResU.Comp R C ρ PMap.empty ρ := by
  refine ⟨ResU.Compat.of_disjoint (fun _ => Or.inr rfl), fun l => ?_⟩
  show OptComp C (ρ.get l) none (ρ.get l)
  cases e : ρ.get l with
  | none => rfl
  | some ψ => rfl

/-- `ρ ○ ρ = ρ` — clause (1) of `○` read pointwise.  Stronger than the instance
`[TR]` Lemma 6.19 needs, which is at `⦇ρ⦈_○` alone.
`[about ours: an unconditional resource-level fact; 6.19 is its instance]` -/
theorem ResU.compR_self (ρ : ResU Loc Val) : ResU.CompR ρ ρ ρ := by
  refine ⟨fun l ψ₁ ψ₂ e₁ e₂ => ?_, fun l => ?_⟩
  · rw [e₁] at e₂
    cases Option.some.inj e₂
    exact ⟨_, CellU.CompR.same _⟩
  · show OptComp CellU.CompR (ρ.get l) (ρ.get l) (ρ.get l)
    cases e : ρ.get l with
    | none => rfl
    | some ψ => exact ⟨ψ, rfl, CellU.CompR.same ψ⟩

/-- **`[TR]` Lemma 6.31** (p. 11): if `ρ ▶◀ ρ′` then `ρ ○ ρ′ = ρ ● ρ′`.  As an
equality of graphs, which is definedness and value together.  `[as printed]` -/
theorem ResU.compR_iff_compS {ρ₁ ρ₂ : ResU Loc Val} (h : ResU.CompatS ρ₁ ρ₂)
    (σ : ResU Loc Val) : ResU.CompR ρ₁ ρ₂ σ ↔ ResU.CompS ρ₁ ρ₂ σ := by
  constructor
  · intro hr
    refine ⟨h, fun l => ?_⟩
    rcases hr.get l with ⟨e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ |
        ⟨ψ₁, ψ₂, ψ, e₁, e₂, e, hC⟩ <;> rw [e₁, e₂]
    · exact e
    · exact e
    · exact e
    · have hk := h l _ _ e₁ e₂
      have hψ : ψ = CellU.compS _ _ hk :=
        CellU.CompR.functional hC (CellU.CompR.strict hk)
      exact ⟨ψ, e, hψ ▸ CellU.compS_spec _ _ hk⟩
  · intro hs
    refine ⟨fun l ψ₁ ψ₂ e₁ e₂ => CellU.CompatR.of_compatS (h l ψ₁ ψ₂ e₁ e₂), fun l => ?_⟩
    rcases hs.get l with ⟨e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ |
        ⟨ψ₁, ψ₂, ψ, e₁, e₂, e, hC⟩ <;> rw [e₁, e₂]
    · exact e
    · exact e
    · exact e
    · have hk := h l _ _ e₁ e₂
      have hψ : ψ = CellU.compS _ _ hk :=
        CellU.CompS.functional hC (CellU.compS_spec _ _ hk)
      exact ⟨ψ, e, hψ ▸ CellU.CompR.strict hk⟩

/-- **`[TR]` Lemma 6.6** (p. 7), one direction: `ρ₁ # ρ₂` implies `ρ₂ # ρ₁`.
`[as printed]` -/
theorem ResU.hash_symm {ρ₁ ρ₂ : ResU Loc Val} (h : ResU.Hash ρ₁ ρ₂) :
    ResU.Hash ρ₂ ρ₁ := by
  obtain ⟨hc, ρ, hcomp, hv⟩ := h
  exact ⟨hc.symm, ρ, hcomp.comm, hv⟩

end BoCa.Fig16

end
