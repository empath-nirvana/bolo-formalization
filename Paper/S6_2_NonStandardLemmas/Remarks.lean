import Paper.S5_Model.Definitions
import Paper.S6_2_NonStandardLemmas.Definitions
import Support.Model.CellFacts
import Support.Model.Prelude
import Support.Model.Update

/-!
# [TR] §6.2 — remarks on Definition 6.2

`ψ ∼ ψ′` (row 5.65): transitivity, and `upd_iff_sim`, the theorem that `[CONF]`
Fig. 18b's two clauses of `↭` and `[TR]` §6's "same domain, `∼` pointwise" form are
the same relation.  Lemmas 6.39 and 6.59 read `↭` through it.

These are theorems about printed definitions — definition rows of
`Paper/INDEX.md` whose Lean is a theorem — whose proofs use results
of `[TR]` §6, so they cannot sit with the definitions.  Each carries the row's
number, printed form, page, tag and note.  A row's theorem that a §6 result's Lean
needs is declared in that result's file, and the row here says where.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### 5.65 · `ψ ∼ ψ′ ≔ (ψ = mut(α,_,_,P̂) ∧ ψ′ = mut(α,_,_,P̂)) ∨ (ψ = ψ′ = imm(ᾱ,v,ρ))` — [TR] Definition 6.2, not a p. 5 row · [TR] p. 13 · `[as printed]`

[TR] p. 13 prints it and then unfolds `↭` through it at Lemmas 6.39, 6.40, 6.44 and 6.59, always as "dom(⦇ρ₁⦈∣imm,mut) = dom(⦇ρ₂⦈∣imm,mut) and for every ℓ in that domain, ⦇ρ₁⦈(ℓ) ∼ ⦇ρ₂⦈(ℓ)". Read at 1200 dpi: α and P̂ are bound outside the `mut` conjunction and the two `_`s — value and witness — inside each conjunct, while the `imm` disjunct asks for equality outright, which is `BoCa.Fig16.ResU.UpdImm`/`UpdMut`'s asymmetry printed as one relation. `upd_iff_sim` is the bridge and it is a theorem: [CONF] Fig. 18b's two clauses and [TR] §6's `dom + ∼` form are the same relation, both flattenings named (G4). `ResU.borrowPart` is `ρ∣imm,mut`, the same printed coverage gap row 5.51 closes for `ρ∣own,mut`. [TR] Lemma 6.44's proof asserts `∼` is transitive "since imms are required to be equal and muts are required to have" the same lifetime and invariant; `CellU.Sim.trans` is that. **This definition had no row and no Lean declaration before this entry**, which is why [TR] §6's proofs had no printed route to follow
-/
/-- **`∼` is transitive** — `[TR]` Lemma 6.44's proof says so and why: *"imms
are required to be equal and muts are required to have"* the same lifetime and
invariant.  The middle cell cannot be both an `imm` and a `mut`, so the two
disjuncts cannot be crossed.
`[about ours: the transitivity of `∼` that `[TR]` Lemma 6.44's proof asserts]` -/
theorem CellU.Sim.trans {ψ₁ ψ₂ ψ₃ : CellU Loc Val} (h₁ : CellU.Sim ψ₁ ψ₂)
    (h₂ : CellU.Sim ψ₂ ψ₃) : CellU.Sim ψ₁ ψ₃ := by
  rcases h₁ with ⟨a, P, hA, ⟨v₂, χ₂, h₂', hw₂, e₂⟩⟩ | ⟨s, v, χ, hh, e₁, e₂⟩
  · rcases h₂ with ⟨a', P', ⟨v₃, χ₃, h₃', hw₃, e₃⟩, hC⟩ | ⟨s', v', χ', hh', e₃, e₄⟩
    · rw [e₂] at e₃
      obtain rfl : a = a' := CellU.mutOf_at e₃
      obtain ⟨-, -, rfl⟩ := CellU.mutOf_inj e₃
      exact Or.inl ⟨a, P, hA, hC⟩
    · exact absurd (e₃.symm.trans e₂) CellU.immOf_ne_mutOf
  · rcases h₂ with ⟨a', P', ⟨v₃, χ₃, h₃', hw₃, e₃⟩, -⟩ | ⟨s', v', χ', hh', e₃, e₄⟩
    · exact absurd (e₂.symm.trans e₃) CellU.immOf_ne_mutOf
    · rw [e₂] at e₃
      obtain ⟨rfl, rfl, rfl⟩ := CellU.immOf_inj e₃
      exact Or.inr ⟨s, v, χ, hh, e₁, e₄⟩

/-!
Row 5.65, continued.
-/
/-- **`↭` is the form `[TR]` §6's proofs unfold it to.**  `[CONF]` Fig. 18b's
two clauses and `[TR]`'s *"`dom(⦇ρ₁⦈|imm,mut) = dom(⦇ρ₂⦈|imm,mut)` and pointwise
`∼`"* are the same relation, with both flattenings named (G4).
`[about ours: `[CONF]` Fig. 18b's `↭` against the form `[TR]` §6's proofs use]` -/
theorem ResU.upd_iff_sim {ρ₁ ρ₂ σ₁ σ₂ : ResU Loc Val}
    (h₁ : ResU.Flat ρ₁ σ₁) (h₂ : ResU.Flat ρ₂ σ₂) :
    ResU.Upd ρ₁ ρ₂ ↔ ResU.SimForm σ₁ σ₂ := by
  constructor
  · intro h
    refine ⟨fun l => ⟨?_, ?_⟩, fun l ψ hb => ?_⟩
    · rintro ⟨ψ, hb⟩
      obtain ⟨hg, hk⟩ := ResU.borrowPart_eq_some.mp hb
      obtain ⟨ψ', hg', hsim⟩ := ResU.sim_of_upd h h₁ h₂ hg hk
      refine ⟨ψ', ResU.borrowPart_eq_some.mpr ⟨hg', ?_⟩⟩
      rcases hsim with ⟨a, P, -, ⟨v, χ, hh, hw, rfl⟩⟩ | ⟨s, v, χ, hh, -, rfl⟩
      · simp
      · simp
    · rintro ⟨ψ, hb⟩
      obtain ⟨hg, hk⟩ := ResU.borrowPart_eq_some.mp hb
      obtain ⟨ψ', hg', hsim⟩ := ResU.sim_of_upd h.symm h₂ h₁ hg hk
      refine ⟨ψ', ResU.borrowPart_eq_some.mpr ⟨hg', ?_⟩⟩
      rcases hsim with ⟨a, P, -, ⟨v, χ, hh, hw, rfl⟩⟩ | ⟨s, v, χ, hh, -, rfl⟩
      · simp
      · simp
    · obtain ⟨hg, hk⟩ := ResU.borrowPart_eq_some.mp hb
      exact ResU.sim_of_upd h h₁ h₂ hg hk
  · rintro ⟨hd, hs⟩
    have hback : ∀ (l : Loc) (ψ₂ : CellU Loc Val), σ₂.borrowPart.get l = some ψ₂ →
        ∃ ψ₁, σ₁.get l = some ψ₁ ∧ CellU.Sim ψ₂ ψ₁ := by
      intro l ψ₂ hb₂
      obtain ⟨ψ₁, hb₁⟩ := (hd l).mpr ⟨ψ₂, hb₂⟩
      obtain ⟨ψ₂', hg₂', hsim⟩ := hs l ψ₁ hb₁
      obtain ⟨hg₂, -⟩ := ResU.borrowPart_eq_some.mp hb₂
      rw [hg₂] at hg₂'
      cases Option.some.inj hg₂'
      exact ⟨ψ₁, (ResU.borrowPart_eq_some.mp hb₁).1, hsim.symm⟩
    refine ⟨fun l s v χ hh => ?_, fun l b P => ?_⟩
    · rw [ResU.flatAt_iff h₁, ResU.flatAt_iff h₂]
      constructor
      · intro hg
        obtain ⟨ψ', hg', hsim⟩ :=
          hs l _ (ResU.borrowPart_eq_some.mpr ⟨hg, by simp⟩)
        rcases hsim with ⟨a, P, ⟨v₁, χ₁, h₁', hw₁, e₁⟩, -⟩ | ⟨s', v', χ', h', e₁, e₂⟩
        · exact absurd e₁ CellU.immOf_ne_mutOf
        · obtain ⟨hs2, hv2, hχ2⟩ := CellU.immOf_inj e₁
          subst hs2; subst hv2; subst hχ2
          rw [hg']; exact congrArg some e₂
      · intro hg
        obtain ⟨ψ', hg', hsim⟩ :=
          hback l _ (ResU.borrowPart_eq_some.mpr ⟨hg, by simp⟩)
        rcases hsim with ⟨a, P, ⟨v₁, χ₁, h₁', hw₁, e₁⟩, -⟩ | ⟨s', v', χ', h', e₁, e₂⟩
        · exact absurd e₁ CellU.immOf_ne_mutOf
        · obtain ⟨hs2, hv2, hχ2⟩ := CellU.immOf_inj e₁
          subst hs2; subst hv2; subst hχ2
          rw [hg']; exact congrArg some e₂
    · constructor
      · rintro ⟨v, χ, hh, hw, hfa⟩
        rw [ResU.flatAt_iff h₁] at hfa
        obtain ⟨ψ', hg', hsim⟩ :=
          hs l _ (ResU.borrowPart_eq_some.mpr ⟨hfa, by simp⟩)
        rcases hsim with ⟨a, P', ⟨v₁, χ₁, h₁', hw₁, e₁⟩, ⟨v₂, χ₂, h₂', hw₂, e₂⟩⟩ |
            ⟨s', v', χ', h', e₁, e₂⟩
        · obtain rfl : b = a := CellU.mutOf_at e₁
          obtain ⟨-, -, hPP⟩ := CellU.mutOf_inj e₁
          subst hPP
          exact ⟨v₂, χ₂, h₂', hw₂, (ResU.flatAt_iff h₂ l _).mpr (e₂ ▸ hg')⟩
        · exact absurd e₁.symm CellU.immOf_ne_mutOf
      · rintro ⟨v, χ, hh, hw, hfa⟩
        rw [ResU.flatAt_iff h₂] at hfa
        obtain ⟨ψ', hg', hsim⟩ :=
          hback l _ (ResU.borrowPart_eq_some.mpr ⟨hfa, by simp⟩)
        rcases hsim with ⟨a, P', ⟨v₁, χ₁, h₁', hw₁, e₁⟩, ⟨v₂, χ₂, h₂', hw₂, e₂⟩⟩ |
            ⟨s', v', χ', h', e₁, e₂⟩
        · obtain rfl : b = a := CellU.mutOf_at e₁
          obtain ⟨-, -, hPP⟩ := CellU.mutOf_inj e₁
          subst hPP
          exact ⟨v₂, χ₂, h₂', hw₂, (ResU.flatAt_iff h₁ l _).mpr (e₂ ▸ hg')⟩
        · exact absurd e₁.symm CellU.immOf_ne_mutOf

end BoCa.Fig16

end
