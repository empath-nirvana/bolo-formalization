import Paper.S5_Model.Definitions
import Support.Model.Algebra
import Support.Model.Composition
import Support.Model.Prelude

/-!
# Support — Model — Walks

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
the exclusive walk `ex(ρ)_◐` and `imm`-free resources, and the functionality of the walks `ex`, `ag` and of `⦇−⦈`, `⟦−⟧` (the witness families they range over).  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- `ρ|imm = ∅`, written pointwise. -/
def ResU.ImmFree (ρ : ResU Loc Val) : Prop :=
  ∀ l ψ, ρ.get l = some ψ → ψ.kind ≠ Kind.imm

theorem ResU.restrict_imm_empty_iff (ρ : ResU Loc Val) :
    ρ.restrict Kind.imm = PMap.empty ↔ ρ.ImmFree := by
  constructor
  · intro h l ψ hl hk
    have : (ρ.restrict Kind.imm).get l = some ψ := ResU.restrict_eq_some.mpr ⟨hl, hk⟩
    rw [h] at this
    exact absurd this (by simp)
  · intro h
    refine PMap.ext fun l => ?_
    cases e : (ρ.restrict Kind.imm).get l with
    | none => rfl
    | some ψ =>
        obtain ⟨hl, hk⟩ := ResU.restrict_eq_some.mp e
        exact absurd hk (h l ψ hl)

theorem ResU.immFree_empty : ResU.ImmFree (PMap.empty : ResU Loc Val) := by
  intro l ψ h; exact absurd h (by simp)

theorem ResU.immFree_restrict {ρ : ResU Loc Val} {k : Kind} (hk : k ≠ Kind.imm) :
    (ρ.restrict k).ImmFree := by
  intro l ψ h
  exact fun e => hk (((ResU.restrict_eq_some.mp h).2).symm.trans e)

/-- A composition of two `imm`-free resources is `imm`-free, provided the cell
operation never manufactures an `imm` cell out of two non-`imm` ones. -/
theorem ResU.ImmFree.comp {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ₁.kind ≠ Kind.imm → ψ₂.kind ≠ Kind.imm →
        ψ.kind ≠ Kind.imm)
    {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.Comp R C ρ₁ ρ₂ ρ)
    (h₁ : ρ₁.ImmFree) (h₂ : ρ₂.ImmFree) : ρ.ImmFree := by
  intro l ψ hl
  have hp := h.2 l
  cases e₁ : ρ₁.get l <;> cases e₂ : ρ₂.get l <;> rw [e₁, e₂] at hp
  · rw [hp] at hl; exact absurd hl (by simp)
  · rw [hp] at hl; cases Option.some.inj hl; exact h₂ l _ e₂
  · rw [hp] at hl; cases Option.some.inj hl; exact h₁ l _ e₁
  · obtain ⟨χ, hχ, hCχ⟩ := hp
    rw [hχ] at hl
    cases Option.some.inj hl
    exact hC _ _ _ hCχ (h₁ l _ e₁) (h₂ l _ e₂)

theorem ResU.ImmFree.bigComp {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ₁.kind ≠ Kind.imm → ψ₂.kind ≠ Kind.imm →
        ψ.kind ≠ Kind.imm)
    {es : List (ResU Loc Val)} {b : ResU Loc Val} (h : BigComp R C es b) :
    (∀ e ∈ es, ResU.ImmFree e) → ResU.ImmFree b := by
  induction h with
  | nil => intro _; exact ResU.immFree_empty
  | cons hrest hcomp ih =>
      intro hall
      exact ResU.ImmFree.comp hC hcomp (hall _ (by simp))
        (ih (fun e he => hall e (by simp [he])))

theorem CellU.compS_ne_imm (ψ₁ ψ₂ ψ : CellU Loc Val) (h : CellU.CompS ψ₁ ψ₂ ψ)
    (h₁ : ψ₁.kind ≠ Kind.imm) : ψ.kind ≠ Kind.imm := by
  obtain ⟨s₁, s₂, v, ρ, k₁, k₂, k₃, e₁, -, -⟩ := h
  exact absurd (by rw [e₁]; rfl) h₁

end BoCa.Fig16

namespace BoCa.Fig16

/-- Key-indexed lists whose key lists are duplicate-free permutations of each
other, and whose values agree key by key, are permutations of each other.
`List.Pairwise.of_map` supplies the step from duplicate-free keys to
duplicate-free pairs; the rest is `List.perm_ext_iff_of_nodup`. -/
theorem List.perm_of_keys {α β : Type} {w w' : List (α × β)}
    (hk : (w.map Prod.fst).Nodup)
    (hkeys : (w.map Prod.fst).Perm (w'.map Prod.fst))
    (hval : ∀ p ∈ w, ∀ q ∈ w', p.1 = q.1 → p.2 = q.2) : w.Perm w' := by
  have nd : ∀ {v : List (α × β)}, (v.map Prod.fst).Nodup → v.Nodup :=
    fun h => List.Pairwise.of_map Prod.fst (fun _ _ hne e => hne (congrArg Prod.fst e)) h
  refine (List.perm_ext_iff_of_nodup (nd hk) (nd (hk.perm hkeys))).mpr fun p => ⟨?_, ?_⟩
  -- An entry of one list has its key in the other, hence a partner there; the
  -- partner's value is forced, so the partner *is* the entry.
  · intro hp
    obtain ⟨q, hq, hql⟩ :=
      List.mem_map.mp (hkeys.mem_iff.mp (List.mem_map.mpr ⟨p, hp, rfl⟩))
    exact Prod.ext hql.symm (hval p hp q hq hql.symm) ▸ hq
  · intro hp
    obtain ⟨q, hq, hql⟩ :=
      List.mem_map.mp (hkeys.mem_iff.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩))
    exact Prod.ext hql.symm (hval q hq p hp hql).symm ▸ hq

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- Two index lists for the same tag of the same resource are permutations of
each other: `ResU.Sites` says each is duplicate-free and lists exactly the
locations carrying that tag.
`[about ours: `ResU.Sites` is convention G6's index set, and this says the set
determines the list up to order]` -/
theorem ResU.Sites.perm {ρ : ResU Loc Val} {k : Kind} {d d' : List Loc}
    (h : ρ.Sites k d) (h' : ρ.Sites k d') : d.Perm d' :=
  (List.perm_ext_iff_of_nodup h.1 h'.1).mpr fun l => (h.2 l).trans (h'.2 l).symm

/-- The cell-level facts about `◐` the order-independence of `⨀` rests on:
single-valuedness, which `ResU.Comp.functional` takes, and the cell halves of
`[TR]` Lemmas 6.2 and 6.3.  All three are proved above at both values of `◐`;
this only names them together.
`[about ours: the hypotheses of §12's schema, collected]` -/
structure ResU.CompLaws (C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop) :
    Prop where
  /-- `◐` is a partial function on cells. -/
  functional : ∀ ψ₁ ψ₂ ψ ψ', C ψ₁ ψ₂ ψ → C ψ₁ ψ₂ ψ' → ψ = ψ'
  /-- The cell half of `[TR]` Lemma 6.2. -/
  comm : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → C ψ₂ ψ₁ ψ
  /-- The cell half of `[TR]` Lemma 6.3, as a Kleene equality. -/
  assoc : ∀ ψ₁ ψ₂ ψ₃ ω, (∃ χ, C ψ₂ ψ₃ χ ∧ C ψ₁ χ ω) ↔ (∃ υ, C ψ₁ ψ₂ υ ∧ C υ ψ₃ ω)

/-- The discharge of `ResU.CompLaws` at `●`, from `CellU.CompS.functional`,
`CellU.CompS.comm` and `CellU.compS_assoc`.
`[about ours: `ResU.CompLaws` collects the schema's hypotheses]` -/
theorem ResU.compLawsS : ResU.CompLaws (Loc := Loc) (Val := Val) CellU.CompS where
  functional := fun _ _ _ _ a b => CellU.CompS.functional a b
  comm := fun _ _ _ a => a.comm
  assoc := CellU.compS_assoc

/-- The discharge of `ResU.CompLaws` at `○`, from `CellU.CompR.functional`,
`CellU.CompR.comm` and `CellU.compR_assoc`.
`[about ours: `ResU.CompLaws` collects the schema's hypotheses]` -/
theorem ResU.compLawsR : ResU.CompLaws (Loc := Loc) (Val := Val) CellU.CompR where
  functional := fun _ _ _ _ a b => CellU.CompR.functional a b
  comm := fun _ _ _ a => a.comm
  assoc := CellU.compR_assoc

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {R : CellU Loc Val → CellU Loc Val → Prop}
variable {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}

/-- When `◐`-composability implies the guard, the guard is redundant: `▶◁` can
be read back off the cellwise data rather than assumed.  This is why nothing
below needs `▶◁` to be symmetric. -/
theorem ResU.Comp.of_pointwise (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂)
    {ρ₁ ρ₂ ρ : ResU Loc Val}
    (h : ∀ l, OptComp C (ρ₁.get l) (ρ₂.get l) (ρ.get l)) :
    ResU.Comp R C ρ₁ ρ₂ ρ := by
  refine ⟨fun l ψ₁ ψ₂ e₁ e₂ => ?_, h⟩
  have hp := h l
  rw [e₁, e₂] at hp
  obtain ⟨ψ, -, hc⟩ := hp
  exact hR _ _ _ hc

/-- `[TR]` Lemma 6.2 with the guard hypothesis weakened to what the fold has.
`ResU.Comp.comm` asks for `▶◁` to be symmetric outright; here `▶◁` is only ever
met at a pair `◐` composes, and there `hR` and 6.2's cell half supply it.
`[about ours: 6.2 at the guard hypothesis the fold can discharge; the printed
statement is `ResU.Comp.comm`]` -/
theorem ResU.Comp.comm_of_laws (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂)
    (hC : ResU.CompLaws C) {ρ₁ ρ₂ ρ : ResU Loc Val}
    (h : ResU.Comp R C ρ₁ ρ₂ ρ) : ResU.Comp R C ρ₂ ρ₁ ρ :=
  ResU.Comp.of_pointwise hR fun l => by
    rcases h.get l with ⟨e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ |
        ⟨ψ₁, ψ₂, ψ, e₁, e₂, e, hc⟩ <;> rw [e₁, e₂]
    · exact e
    · exact e
    · exact e
    · exact ⟨ψ, e, hC.comm _ _ _ hc⟩

/-- `⨀` is single-valued at a *fixed* list: each step is `ResU.Comp`, which
`ResU.Comp.functional` shows single-valued.  The order-independence is
`BigComp.perm`.
`[about ours: `BigComp` is §16's fold shape for a printed iterated operator]` -/
theorem BigComp.functional (hC : ResU.CompLaws C)
    {l : List (ResU Loc Val)} {b b' : ResU Loc Val}
    (h : BigComp R C l b) (h' : BigComp R C l b') : b = b' := by
  induction h generalizing b' with
  | nil => cases h'; rfl
  | cons _ hc ih =>
      cases h' with
      | cons hτ' hc' =>
          cases ih hτ'
          exact ResU.Comp.functional hC.functional hc hc'

/-- Reading the exclusive family off its list: an entry is a `mut` location of
`ρ` paired with *a* walk of that cell's witness.  Proved by induction on the
list rather than on the derivation, which avoids the mutual recursor. -/
theorem ExWits.mem {ρ : ResU Loc Val} :
    ∀ {w : List (Loc × ResU Loc Val)}, ExWits R C ρ w →
      ∀ p ∈ w, ∃ ψ, ρ.get p.1 = some ψ ∧ ExW R C ψ.wit p.2 := by
  intro w
  induction w with
  | nil => intro _ p hp; exact absurd hp (by simp)
  | cons q w ih =>
      intro h p hp
      cases h with
      | cons ψ hψ _ he hw =>
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨ψ, hψ, he⟩
          · exact ih hw p hp

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- Reading `{ag(ρ′) | ∃ℓ. ρ(ℓ) = mut(_,_,ρ′,_)}` off its list. -/
theorem AgWitsM.mem {ρ : ResU Loc Val} :
    ∀ {w : List (Loc × ResU Loc Val)}, AgWitsM ρ w →
      ∀ p ∈ w, ∃ ψ, ρ.get p.1 = some ψ ∧ AgW ψ.wit p.2 := by
  intro w
  induction w with
  | nil => intro _ p hp; exact absurd hp (by simp)
  | cons q w ih =>
      intro h p hp
      cases h with
      | cons ψ hψ _ he hw =>
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨ψ, hψ, he⟩
          · exact ih hw p hp

/-- Reading `{ex(ρ′)_○ ○ ag(ρ′) | ∃ℓ. ρ(ℓ) = imm(_,_,ρ′)}` off its list: each
entry is a location paired with *some* composite of the two walks. -/
theorem AgWitsI.mem {ρ : ResU Loc Val} :
    ∀ {w : List (Loc × ResU Loc Val)}, AgWitsI ρ w →
      ∀ p ∈ w, ∃ ψ e a, ρ.get p.1 = some ψ ∧
        ExR ψ.wit e ∧ AgW ψ.wit a ∧ ResU.CompR e a p.2 := by
  intro w
  induction w with
  | nil => intro _ p hp; exact absurd hp (by simp)
  | cons q w ih =>
      intro h p hp
      cases h with
      | cons ψ hψ _ e a hex hag hc hw =>
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨ψ, e, a, hψ, hex, hag, hc⟩
          · exact ih hw p hp

end BoCa.Fig16

end
