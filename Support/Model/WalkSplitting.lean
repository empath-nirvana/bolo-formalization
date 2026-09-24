import Paper.S5_Model.Definitions
import Paper.S6_2_NonStandardLemmas.Remarks
import Support.Model.Algebra
import Support.Model.Composition
import Support.Model.Prelude
import Support.Model.Walks

/-!
# Support — Model — WalkSplitting

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
the pieces of Lemmas 6.18 and 6.20: the sites of a composite, the witness families of each walk and how they split across `●`, and inclusion–exclusion over shared `imm` cells.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- `●` returns an `imm` cell.  With `CellU.CompatS.kinds` this says `●` never
moves a cell across tags, which is why restriction distributes over it at every
tag (`ResU.CompS.restrict`). -/
theorem CellU.CompS.kind {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompS ψ₁ ψ₂ ψ) :
    ψ.kind = Kind.imm := by
  obtain ⟨s₁, s₂, v, ρ, k₁, k₂, k₃, e₁, e₂, e₃⟩ := h
  rw [e₃]
  rfl

/-- `●` composes over a common witness and hands it on unchanged — the print's
`imm(ᾱ₁, ρ, v) ● imm(ᾱ₂, ρ, v) = imm(ᾱ₁ ∪ ᾱ₂, ρ, v)`, in which only the
lifetime set moves. -/
theorem CellU.CompS.wit {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompS ψ₁ ψ₂ ψ) :
    ψ.wit = ψ₁.wit ∧ ψ.wit = ψ₂.wit := by
  obtain ⟨s₁, s₂, v, ρ, k₁, k₂, k₃, e₁, e₂, e₃⟩ := h
  subst e₁; subst e₂; subst e₃
  exact ⟨by rw [CellU.wit_immOf, CellU.wit_immOf],
    by rw [CellU.wit_immOf, CellU.wit_immOf]⟩

end BoCa.Fig16

namespace BoCa.Fig16

/-- `Kind.mut` is not `Kind.imm` — the side condition the index-set lemmas below
take, and the only tag disjointness either printed proof is actually spent on
here.  The `own` tag needs no such side condition, because `ResU.CompS.restrict`
holds at every tag (`ResU.CompS.restrict`). -/
theorem Kind.mut_ne_imm : Kind.mut ≠ Kind.imm := by decide

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- **The own-or-mut cells are disjoint.**  A cell of `ρ₁` whose tag is not
`imm` has no partner in `ρ₂`, since `▶◀` would force both to be `imm`. -/
theorem ResU.CompatS.right_eq_none {ρ₁ ρ₂ : ResU Loc Val} (h : ResU.CompatS ρ₁ ρ₂)
    {l : Loc} {ψ₁ : CellU Loc Val} (e₁ : ρ₁.get l = some ψ₁)
    (hk : ψ₁.kind ≠ Kind.imm) : ρ₂.get l = none := by
  cases e₂ : ρ₂.get l with
  | none => rfl
  | some ψ₂ => exact absurd (CellU.CompatS.kinds (h l ψ₁ ψ₂ e₁ e₂)).1 hk

/-- Where `ρ₁` is defined, the composite carries a cell of the same tag over the
same witness: off the overlap it is `ρ₁`'s own cell, and on it `●` merges two
`imm` cells over one witness.  This is all that either printed proof's family
transfers look at. -/
theorem ResU.CompS.kind_wit_left {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {l : Loc} {ψ₁ ψ : CellU Loc Val} (e₁ : ρ₁.get l = some ψ₁) (e : ρ.get l = some ψ) :
    ψ.kind = ψ₁.kind ∧ ψ.wit = ψ₁.wit := by
  rcases ResU.Comp.get h l with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, f, hC⟩
  · rw [e₁] at f₁; exact absurd f₁ (by simp)
  · rw [e₁] at f₁
    obtain rfl := Option.some.inj f₁
    rw [e] at f
    obtain rfl := Option.some.inj f
    exact ⟨rfl, rfl⟩
  · rw [e₁] at f₁; exact absurd f₁ (by simp)
  · rw [e₁] at f₁
    obtain rfl := Option.some.inj f₁
    rw [e] at f
    obtain rfl := Option.some.inj f
    exact ⟨(CellU.CompS.kind hC).trans
        (CellU.CompatS.kinds (CellU.CompS.compat hC)).1.symm,
      (CellU.CompS.wit hC).1⟩

/-- Where `ρ₁` is defined the composite is too, with a cell of the same tag over
the same witness.  This is the form the `imm` families need in [TR] 6.20, where
the two operands' cells at an overlap are *not* equal — only their tags and
witnesses are.
`[about ours: `CellU.wit` is this file's projection, not the print's; the
statement is about `ResU.CompS`, whose graph is the printed `●`]` -/
theorem ResU.CompS.get_left {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {l : Loc} {ψ₁ : CellU Loc Val} (e₁ : ρ₁.get l = some ψ₁) :
    ∃ ψ, ρ.get l = some ψ ∧ ψ.kind = ψ₁.kind ∧ ψ.wit = ψ₁.wit := by
  rcases optSplit (ρ.get l) with e | ⟨ψ, e⟩
  · rcases ResU.Comp.get h l with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
        ⟨χ₁, χ₂, χ, f₁, -, f, -⟩
    · rw [e₁] at f₁; exact absurd f₁ (by simp)
    · rw [e] at f; exact absurd f (by simp)
    · rw [e₁] at f₁; exact absurd f₁ (by simp)
    · rw [e] at f; exact absurd f (by simp)
  · exact ⟨ψ, e, ResU.CompS.kind_wit_left h e₁ e⟩

/-- The mirror of `ResU.CompS.get_left`. -/
theorem ResU.CompS.get_right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {l : Loc} {ψ₂ : CellU Loc Val} (e₂ : ρ₂.get l = some ψ₂) :
    ∃ ψ, ρ.get l = some ψ ∧ ψ.kind = ψ₂.kind ∧ ψ.wit = ψ₂.wit :=
  ResU.CompS.get_left (ResU.CompS.comm h) e₂

/-- A non-`imm` cell of `ρ₁` survives into the composite unchanged, and `ρ₂` is
silent at that location. -/
theorem ResU.CompS.get_left_of_ne_imm {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {l : Loc} {ψ : CellU Loc Val} (e₁ : ρ₁.get l = some ψ) (hk : ψ.kind ≠ Kind.imm) :
    ρ₂.get l = none ∧ ρ.get l = some ψ := by
  have e₂ : ρ₂.get l = none := ResU.CompatS.right_eq_none h.1 e₁ hk
  have hp := h.2 l
  rw [e₁, e₂] at hp
  exact ⟨e₂, hp⟩

/-- The mirror of `ResU.CompS.get_left_of_ne_imm`. -/
theorem ResU.CompS.get_right_of_ne_imm {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {l : Loc} {ψ : CellU Loc Val} (e₂ : ρ₂.get l = some ψ) (hk : ψ.kind ≠ Kind.imm) :
    ρ₁.get l = none ∧ ρ.get l = some ψ :=
  ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm h) e₂ hk

/-- **A non-`imm` cell of the composite comes from exactly one side.**  This is
the converse half of "disjoint own-or-mut cells": the `own` and `mut` locations
of `ρ₁ ● ρ₂` are partitioned by which operand supplies them. -/
theorem ResU.CompS.get_split_of_ne_imm {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {l : Loc} {ψ : CellU Loc Val} (e : ρ.get l = some ψ) (hk : ψ.kind ≠ Kind.imm) :
    (ρ₁.get l = some ψ ∧ ρ₂.get l = none) ∨ (ρ₁.get l = none ∧ ρ₂.get l = some ψ) := by
  rcases ResU.Comp.get h l with ⟨-, -, f⟩ | ⟨χ, f₁, f₂, f⟩ | ⟨χ, f₁, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, -, -, f, hC⟩
  · rw [e] at f; exact absurd f (by simp)
  · rw [e] at f
    obtain rfl := Option.some.inj f
    exact Or.inl ⟨f₁, f₂⟩
  · rw [e] at f
    obtain rfl := Option.some.inj f
    exact Or.inr ⟨f₁, f₂⟩
  · rw [e] at f
    obtain rfl := Option.some.inj f
    exact absurd (CellU.CompS.kind hC) hk

/-- `ρ|ι` is undefined where `ρ` is. -/
theorem ResU.restrict_get_none {ρ : ResU Loc Val} {k : Kind} {l : Loc}
    (e : ρ.get l = none) : (ρ.restrict k).get l = none := by
  show (ρ.get l).bind _ = none
  rw [e]
  rfl

/-- `ρ|ι` keeps a cell of tag `ι`. -/
theorem ResU.restrict_get_some {ρ : ResU Loc Val} {k : Kind} {l : Loc}
    {ψ : CellU Loc Val} (e : ρ.get l = some ψ) (hk : ψ.kind = k) :
    (ρ.restrict k).get l = some ψ :=
  ResU.restrict_eq_some.mpr ⟨e, hk⟩

/-- `ρ|ι` drops a cell of any other tag. -/
theorem ResU.restrict_get_ne {ρ : ResU Loc Val} {k : Kind} {l : Loc}
    {ψ : CellU Loc Val} (e : ρ.get l = some ψ) (hk : ψ.kind ≠ k) :
    (ρ.restrict k).get l = none := by
  show (ρ.get l).bind _ = none
  rw [e]
  exact if_neg hk

/-- **`(ρ₁ ● ρ₂)|ι = ρ₁|ι ● ρ₂|ι`**, as a graph, at every tag.  This is the
second line of both printed proofs.
`[about ours: the printed `ρ|ι` and `●`; the equation has no printed row of its
own, being a step inside 6.18's and 6.20's proofs]` -/
theorem ResU.CompS.restrict {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    (k : Kind) :
    ResU.CompS (ρ₁.restrict k) (ρ₂.restrict k) (ρ.restrict k) := by
  refine ⟨fun l χ₁ χ₂ f₁ f₂ => h.1 l χ₁ χ₂ (ResU.restrict_eq_some.mp f₁).1
    (ResU.restrict_eq_some.mp f₂).1, fun l => ?_⟩
  rcases ResU.Comp.get h l with ⟨f₁, f₂, f⟩ | ⟨χ, f₁, f₂, f⟩ | ⟨χ, f₁, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, f₁, f₂, f, hC⟩
  · rw [ResU.restrict_get_none f₁, ResU.restrict_get_none f₂, ResU.restrict_get_none f]
    rfl
  · by_cases hk : χ.kind = k
    · rw [ResU.restrict_get_some f₁ hk, ResU.restrict_get_none f₂,
        ResU.restrict_get_some f hk]
      rfl
    · rw [ResU.restrict_get_ne f₁ hk, ResU.restrict_get_none f₂,
        ResU.restrict_get_ne f hk]
      rfl
  · by_cases hk : χ.kind = k
    · rw [ResU.restrict_get_none f₁, ResU.restrict_get_some f₂ hk,
        ResU.restrict_get_some f hk]
      rfl
    · rw [ResU.restrict_get_none f₁, ResU.restrict_get_ne f₂ hk,
        ResU.restrict_get_ne f hk]
      rfl
  · -- Every cell in sight is `imm`, so the three restrictions stand or fall
    -- together and `●` is the composition it already was.
    obtain ⟨k₁, k₂⟩ := CellU.CompatS.kinds (CellU.CompS.compat hC)
    have k₃ : χ.kind = Kind.imm := CellU.CompS.kind hC
    by_cases hk : k = Kind.imm
    · subst hk
      rw [ResU.restrict_get_some f₁ k₁, ResU.restrict_get_some f₂ k₂,
        ResU.restrict_get_some f k₃]
      exact ⟨χ, rfl, hC⟩
    · rw [ResU.restrict_get_ne f₁ (fun e => hk (k₁ ▸ e).symm),
        ResU.restrict_get_ne f₂ (fun e => hk (k₂ ▸ e).symm),
        ResU.restrict_get_ne f (fun e => hk (k₃ ▸ e).symm)]
      rfl

/-- `●` is an instance of `○` — `[TR]` Lemma 6.31 read left to right.
`[restricted: the `●`-implies-`○` half of the printed Kleene equality; the
other half is `ResU.compR_iff_compS`'s forward direction]` -/
theorem ResU.CompS.toCompR {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ) :
    ResU.CompR ρ₁ ρ₂ ρ :=
  (ResU.compR_iff_compS h.1 ρ).mpr h

/-- **`(ρ₁ ● ρ₂)|ι = ρ₁|ι ○ ρ₂|ι`** — the form 6.20 uses, whose composites are
all at `○` although its hypothesis is at `●`.
`[about ours: the printed `ρ|ι` and `●`, composed at `○` by 6.31; the equation
itself has no printed row]` -/
theorem ResU.CompS.restrictR {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    (k : Kind) :
    ResU.CompR (ρ₁.restrict k) (ρ₂.restrict k) (ρ.restrict k) :=
  ResU.CompS.toCompR (ResU.CompS.restrict h k)

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {R : CellU Loc Val → CellU Loc Val → Prop}
variable {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}

/-- `⨀[σ] = σ`, by [TR] Lemma 6.4 — and nothing else folds to anything else.
`[about ours: `BigComp` is §16's fold shape for the printed `⨀`]` -/
theorem BigComp.singleton_iff (hC : ResU.CompLaws C) {σ τ : ResU Loc Val} :
    BigComp R C [σ] τ ↔ τ = σ := by
  constructor
  · intro h
    cases h with
    | cons ht hc =>
        cases ht
        exact ResU.Comp.functional hC.functional hc (ResU.comp_empty_right _)
  · rintro rfl
    exact BigComp.cons BigComp.nil (ResU.comp_empty_right _)

/-- `⨀[σ₁, σ₂] = σ₁ ◐ σ₂` — the two-element fold is the binary composition.
`[about ours: `BigComp` is §16's fold shape for the printed `⨀`]` -/
theorem BigComp.pair (hC : ResU.CompLaws C) {σ₁ σ₂ τ : ResU Loc Val} :
    BigComp R C [σ₁, σ₂] τ ↔ ResU.Comp R C σ₁ σ₂ τ := by
  constructor
  · intro h
    cases h with
    | cons ht hc =>
        obtain rfl := BigComp.singleton_iff hC |>.mp ht
        exact hc
  · intro h
    exact BigComp.cons (BigComp.singleton_iff hC |>.mpr rfl) h

/-- **`⨀(l₁ ++ l₂) = ⨀l₁ ◐ ⨀l₂`**, as a Kleene equality: the concatenation
folds exactly when both halves fold to composable values, and then to their
composite.  This is where [TR] 6.3 and 6.4 are spent.
`[about ours: `BigComp` is §16's fold shape; the rebracketing is the printed
6.3 and the base case the printed 6.4]` -/
theorem BigComp.append (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) (hC : ResU.CompLaws C)
    {l₁ l₂ : List (ResU Loc Val)} {b : ResU Loc Val} :
    BigComp R C (l₁ ++ l₂) b ↔
      ∃ b₁ b₂, BigComp R C l₁ b₁ ∧ BigComp R C l₂ b₂ ∧ ResU.Comp R C b₁ b₂ b := by
  induction l₁ generalizing b with
  | nil =>
      refine ⟨fun h => ⟨PMap.empty, b, BigComp.nil, h, ResU.Comp.comm_of_laws hR hC (ResU.comp_empty_right b)⟩, ?_⟩
      rintro ⟨b₁, b₂, h₁, h₂, hc⟩
      cases h₁
      exact ResU.Comp.functional hC.functional
        (ResU.Comp.comm_of_laws hR hC (ResU.comp_empty_right b₂)) hc ▸ h₂
  | cons σ l ih =>
      constructor
      · intro h
        cases h with
        | cons hτ hcσ =>
            obtain ⟨b₁, b₂, k₁, k₂, kc⟩ := ih.mp hτ
            obtain ⟨y, hy₁, hy₂⟩ :=
              (ResU.Comp.assoc hR hC.assoc σ b₁ b₂ b).mp ⟨_, kc, hcσ⟩
            exact ⟨y, b₂, BigComp.cons k₁ hy₁, k₂, hy₂⟩
      · rintro ⟨b₁, b₂, h₁, h₂, hc⟩
        cases h₁ with
        | cons hτ hcσ =>
            obtain ⟨x, hx₁, hx₂⟩ :=
              (ResU.Comp.assoc hR hC.assoc σ _ b₂ b).mpr ⟨b₁, hcσ, hc⟩
            exact BigComp.cons (ih.mpr ⟨_, b₂, hτ, h₂, hx₁⟩) hx₂

/-- **The exchange of the middle two factors**, as a Kleene equality:

    (a₁ ◐ a₂) ◐ (b₁ ◐ b₂)  =  (a₁ ◐ b₁) ◐ (a₂ ◐ b₂).

Neither side's intermediate composites are assumed to exist — each is bound by
its own existential — so this is definedness and value together, which is what
"Kleene-equal" asks for.
`[about ours: the rearrangement [TR] 6.18's and 6.20's proofs perform on a
four-fold composite; the printed rows behind it are 6.2 and 6.3]` -/
theorem ResU.Comp.exchange₄ (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) (hC : ResU.CompLaws C)
    (a₁ a₂ b₁ b₂ x : ResU Loc Val) :
    (∃ A B, ResU.Comp R C a₁ a₂ A ∧ ResU.Comp R C b₁ b₂ B ∧ ResU.Comp R C A B x) ↔
      (∃ S₁ S₂, ResU.Comp R C a₁ b₁ S₁ ∧ ResU.Comp R C a₂ b₂ S₂ ∧
        ResU.Comp R C S₁ S₂ x) := by
  -- Both sides are the fold of a four-element list; the two lists differ by the
  -- transposition of their middle entries.
  have hleft : (∃ A B, ResU.Comp R C a₁ a₂ A ∧ ResU.Comp R C b₁ b₂ B ∧
      ResU.Comp R C A B x) ↔ BigComp R C [a₁, a₂, b₁, b₂] x := by
    rw [show ([a₁, a₂, b₁, b₂] : List (ResU Loc Val)) = [a₁, a₂] ++ [b₁, b₂] from rfl,
      BigComp.append hR hC]
    exact ⟨fun ⟨A, B, hA, hB, hx⟩ =>
        ⟨A, B, BigComp.pair hC |>.mpr hA, BigComp.pair hC |>.mpr hB, hx⟩,
      fun ⟨A, B, hA, hB, hx⟩ =>
        ⟨A, B, BigComp.pair hC |>.mp hA, BigComp.pair hC |>.mp hB, hx⟩⟩
  have hright : (∃ S₁ S₂, ResU.Comp R C a₁ b₁ S₁ ∧ ResU.Comp R C a₂ b₂ S₂ ∧
      ResU.Comp R C S₁ S₂ x) ↔ BigComp R C [a₁, b₁, a₂, b₂] x := by
    rw [show ([a₁, b₁, a₂, b₂] : List (ResU Loc Val)) = [a₁, b₁] ++ [a₂, b₂] from rfl,
      BigComp.append hR hC]
    exact ⟨fun ⟨S₁, S₂, h₁, h₂, hx⟩ =>
        ⟨S₁, S₂, BigComp.pair hC |>.mpr h₁, BigComp.pair hC |>.mpr h₂, hx⟩,
      fun ⟨S₁, S₂, h₁, h₂, hx⟩ =>
        ⟨S₁, S₂, BigComp.pair hC |>.mp h₁, BigComp.pair hC |>.mp h₂, hx⟩⟩
  have hp : ([a₁, a₂, b₁, b₂] : List (ResU Loc Val)).Perm [a₁, b₁, a₂, b₂] :=
    List.Perm.cons a₁ (List.Perm.swap b₁ a₂ [b₂])
  rw [hleft, hright]
  exact ⟨BigComp.of_perm hR hC hp, BigComp.of_perm hR hC hp.symm⟩

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- The exchange at `●`, which is the one [TR] 6.18 uses.
`[about ours: `ResU.Comp.exchange₄` instantiated at `●`]` -/
theorem ResU.CompS.exchange₄ (a₁ a₂ b₁ b₂ x : ResU Loc Val) :
    (∃ A B, ResU.CompS a₁ a₂ A ∧ ResU.CompS b₁ b₂ B ∧ ResU.CompS A B x) ↔
      (∃ S₁ S₂, ResU.CompS a₁ b₁ S₁ ∧ ResU.CompS a₂ b₂ S₂ ∧ ResU.CompS S₁ S₂ x) :=
  ResU.Comp.exchange₄ (fun _ _ _ hc => CellU.CompS.compat hc) ResU.compLawsS
    a₁ a₂ b₁ b₂ x

end BoCa.Fig16

namespace BoCa.Fig16

/-- A list is a permutation of its `p`-part followed by its non-`p`-part.  Only
the transposition is at issue, and `List.perm_middle` supplies it. -/
theorem List.filter_perm_append {α : Type} (p : α → Bool) (l : List α) :
    l.Perm (l.filter p ++ l.filter (fun a => !(p a))) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons a l ih =>
      by_cases ha : p a = true
      · rw [List.filter_cons_of_pos ha, List.filter_cons_of_neg (by simp [ha])]
        exact List.Perm.cons a ih
      · have ha' : p a = false := by
          cases e : p a with
          | false => rfl
          | true => exact absurd e ha
        rw [List.filter_cons_of_neg (by simp [ha']),
          List.filter_cons_of_pos (by simp [ha'])]
        exact (List.Perm.cons a ih).trans List.perm_middle.symm

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- The split of a key-indexed list by a predicate on the key.  The two pieces
are characterised by membership in both directions, which is what turns them
into `ResU.Sites` lists below.  `Classical` decides the predicate, which is
convention G8's standing entry point: `Loc` is abstract. -/
theorem List.split_by_key {α β : Type} (q : α → Prop) (w : List (α × β)) :
    ∃ w₁ w₂ : List (α × β), w.Perm (w₁ ++ w₂) ∧
      (∀ p, p ∈ w₁ ↔ (p ∈ w ∧ q p.1)) ∧ (∀ p, p ∈ w₂ ↔ (p ∈ w ∧ ¬ q p.1)) := by
  classical
  refine ⟨w.filter (fun p => decide (q p.1)), w.filter (fun p => !(decide (q p.1))),
    List.filter_perm_append _ w, fun p => ?_, fun p => ?_⟩
  · rw [List.mem_filter]
    exact ⟨fun hx => ⟨hx.1, of_decide_eq_true hx.2⟩, fun hx => ⟨hx.1, decide_eq_true hx.2⟩⟩
  · rw [List.mem_filter]
    refine ⟨fun hx => ⟨hx.1, fun hq => ?_⟩, fun hx => ⟨hx.1, ?_⟩⟩
    · rw [decide_eq_true hq] at hx
      exact absurd hx.2 (by simp)
    · simp [hx.2]

/-- **The `own` and `mut` sites of `ρ₁ ● ρ₂` are those of `ρ₁` then those of
`ρ₂`.**  Duplicate-freeness survives the concatenation because `ResU.CompatS.right_eq_none` makes the two
lists disjoint. -/
theorem ResU.Sites.append_of_compS {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {k : Kind} (hk : k ≠ Kind.imm) {d₁ d₂ : List Loc}
    (h₁ : ρ₁.Sites k d₁) (h₂ : ρ₂.Sites k d₂) : ρ.Sites k (d₁ ++ d₂) := by
  refine ⟨List.nodup_append.mpr ⟨h₁.1, h₂.1, ?_⟩, fun l => ?_⟩
  · rintro a ha b hb rfl
    obtain ⟨ψ₁, g₁, gk₁⟩ := (h₁.2 a).mp ha
    obtain ⟨ψ₂, g₂, -⟩ := (h₂.2 a).mp hb
    rw [ResU.CompatS.right_eq_none h.1 g₁ (fun e => hk (gk₁.symm.trans e))] at g₂
    exact absurd g₂ (by simp)
  · refine ⟨fun hm => ?_, fun hm => ?_⟩
    · rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨ψ, g, gk⟩ := (h₁.2 l).mp hm
        exact ⟨ψ, (ResU.CompS.get_left_of_ne_imm h g (fun e => hk (gk.symm.trans e))).2, gk⟩
      · obtain ⟨ψ, g, gk⟩ := (h₂.2 l).mp hm
        exact ⟨ψ, (ResU.CompS.get_right_of_ne_imm h g (fun e => hk (gk.symm.trans e))).2, gk⟩
    · obtain ⟨ψ, g, gk⟩ := hm
      rcases ResU.CompS.get_split_of_ne_imm h g (fun e => hk (gk.symm.trans e)) with
        ⟨g₁, -⟩ | ⟨-, g₂⟩
      · exact List.mem_append.mpr (Or.inl ((h₁.2 l).mpr ⟨ψ, g₁, gk⟩))
      · exact List.mem_append.mpr (Or.inr ((h₂.2 l).mpr ⟨ψ, g₂, gk⟩))

/-- **A key-indexed family over the `own` or `mut` sites of `ρ₁ ● ρ₂` cuts into
a family over `ρ₁`'s sites and one over `ρ₂`'s**, up to order and with no entry
invented or lost.
`[about ours: `ResU.Sites` is convention G6's index set (§16), and this is how
two of them sit inside a third]` -/
theorem ResU.Sites.split_pairs {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {k : Kind} (hk : k ≠ Kind.imm) {A : Type} {w : List (Loc × A)}
    (hs : ρ.Sites k (w.map Prod.fst)) :
    ∃ w₁ w₂ : List (Loc × A), w.Perm (w₁ ++ w₂) ∧
      ρ₁.Sites k (w₁.map Prod.fst) ∧ ρ₂.Sites k (w₂.map Prod.fst) ∧
      (∀ p ∈ w₁, p ∈ w) ∧ (∀ p ∈ w₂, p ∈ w) := by
  obtain ⟨w₁, w₂, hp, hm₁, hm₂⟩ :=
    List.split_by_key (fun l => ∃ ψ, ρ₁.get l = some ψ ∧ ψ.kind = k) w
  -- The key lists inherit duplicate-freeness from `hs` along `hp`.
  have hnd : ((w₁.map Prod.fst) ++ (w₂.map Prod.fst)).Nodup := by
    rw [← List.map_append]
    exact (hp.map Prod.fst).nodup hs.1
  obtain ⟨nd₁, nd₂, -⟩ := List.nodup_append.mp hnd
  refine ⟨w₁, w₂, hp, ⟨nd₁, fun l => ⟨?_, ?_⟩⟩, ⟨nd₂, fun l => ⟨?_, ?_⟩⟩,
    fun p hp' => ((hm₁ p).mp hp').1, fun p hp' => ((hm₂ p).mp hp').1⟩
  · intro hl
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hl
    exact ((hm₁ p).mp hp').2
  · intro hl
    obtain ⟨ψ, g, gk⟩ := hl
    have hρ : ρ.get l = some ψ :=
      (ResU.CompS.get_left_of_ne_imm h g (fun e => hk (gk.symm.trans e))).2
    obtain ⟨p, hp', hp1⟩ := List.mem_map.mp ((hs.2 l).mpr ⟨ψ, hρ, gk⟩)
    exact List.mem_map.mpr ⟨p, (hm₁ p).mpr ⟨hp', hp1 ▸ ⟨ψ, g, gk⟩⟩, hp1⟩
  · intro hl
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hl
    obtain ⟨hpw, hq⟩ := (hm₂ p).mp hp'
    obtain ⟨ψ, g, gk⟩ := (hs.2 p.1).mp (List.mem_map.mpr ⟨p, hpw, rfl⟩)
    rcases ResU.CompS.get_split_of_ne_imm h g (fun e => hk (gk.symm.trans e)) with
      ⟨g₁, -⟩ | ⟨-, g₂⟩
    · exact absurd ⟨ψ, g₁, gk⟩ hq
    · exact ⟨ψ, g₂, gk⟩
  · intro hl
    obtain ⟨ψ, g, gk⟩ := hl
    have hρ : ρ.get l = some ψ :=
      (ResU.CompS.get_right_of_ne_imm h g (fun e => hk (gk.symm.trans e))).2
    have hnone : ρ₁.get l = none :=
      (ResU.CompS.get_right_of_ne_imm h g (fun e => hk (gk.symm.trans e))).1
    obtain ⟨p, hp', hp1⟩ := List.mem_map.mp ((hs.2 l).mpr ⟨ψ, hρ, gk⟩)
    refine List.mem_map.mpr ⟨p, (hm₂ p).mpr ⟨hp', ?_⟩, hp1⟩
    rintro ⟨χ, gχ, -⟩
    rw [hp1, hnone] at gχ
    exact absurd gχ (by simp)

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {R : CellU Loc Val → CellU Loc Val → Prop}
variable {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}

/-- **The exclusive family, entry by entry.**  `ExWits.mem` (§20a) is the
forward half without the tag; this adds the tag and the converse, fixing the
relation by its entries, which makes cutting and concatenating it one-liners.
Proved by induction on the list rather than on the derivation, which avoids the
mutual recursor. -/
theorem ExWits.iff_mem {ρ : ResU Loc Val} {w : List (Loc × ResU Loc Val)} :
    ExWits R C ρ w ↔
      ∀ p ∈ w, ∃ ψ, ρ.get p.1 = some ψ ∧ ψ.kind = Kind.mut ∧ ExW R C ψ.wit p.2 := by
  induction w with
  | nil => exact ⟨fun _ p hp => absurd hp (by simp), fun _ => ExWits.nil⟩
  | cons q w ih =>
      constructor
      · intro h p hp
        cases h with
        | cons ψ hψ hk he hw =>
            rcases List.mem_cons.mp hp with rfl | hp
            · exact ⟨ψ, hψ, hk, he⟩
            · exact ih.mp hw p hp
      · intro h
        obtain ⟨ψ, hψ, hk, he⟩ := h q (by simp)
        exact ExWits.cons ψ hψ hk he (ih.mpr fun p hp => h p (by simp [hp]))

/-- Two exclusive families over one resource concatenate. -/
theorem ExWits.append {ρ : ResU Loc Val} {w₁ w₂ : List (Loc × ResU Loc Val)}
    (h₁ : ExWits R C ρ w₁) (h₂ : ExWits R C ρ w₂) : ExWits R C ρ (w₁ ++ w₂) :=
  ExWits.iff_mem.mpr fun p hp => by
    rcases List.mem_append.mp hp with hp | hp
    · exact ExWits.iff_mem.mp h₁ p hp
    · exact ExWits.iff_mem.mp h₂ p hp

/-- **`ρ₁`'s exclusive family is one of `ρ₁ ● ρ₂`'s**: at a `mut` location of
`ρ₁` the composite carries the very same cell, so the entry is unchanged. -/
theorem ExWits.of_compS_left {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w : List (Loc × ResU Loc Val)} (hw : ExWits R C ρ₁ w) : ExWits R C ρ w :=
  ExWits.iff_mem.mpr fun p hp => by
    obtain ⟨ψ, hψ, hk, he⟩ := ExWits.iff_mem.mp hw p hp
    exact ⟨ψ,
      (ResU.CompS.get_left_of_ne_imm h hψ (fun e => Kind.mut_ne_imm (hk.symm.trans e))).2,
      hk, he⟩

/-- The mirror of `ExWits.of_compS_left`. -/
theorem ExWits.of_compS_right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w : List (Loc × ResU Loc Val)} (hw : ExWits R C ρ₂ w) : ExWits R C ρ w :=
  ExWits.of_compS_left (ResU.CompS.comm h) hw

/-- **The entries of `ρ₁ ● ρ₂`'s exclusive family that lie over `ρ₁` are `ρ₁`'s
exclusive family.**  With `ResU.Sites.split_pairs` this is the cut [TR] 6.18's
forward direction makes.  Nothing has to be re-derived: the composite's cell at
such a location *is* `ρ₁`'s cell, so the walk paired with it is already a walk
of `ρ₁`'s witness.
`[about ours: `ExWits` is §17's family relation, convention G6's reading of the
printed comprehension]` -/
theorem ExWits.to_compS_left {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w w₁ : List (Loc × ResU Loc Val)} (hw : ExWits R C ρ w)
    (hsub : ∀ p ∈ w₁, p ∈ w) (hs₁ : ρ₁.Sites Kind.mut (w₁.map Prod.fst)) :
    ExWits R C ρ₁ w₁ := by
  refine ExWits.iff_mem.mpr fun p hp => ?_
  obtain ⟨ψ₁, g₁, gk₁⟩ := (hs₁.2 p.1).mp (List.mem_map.mpr ⟨p, hp, rfl⟩)
  obtain ⟨ψ, hψ, -, hwalk⟩ := ExWits.iff_mem.mp hw p (hsub p hp)
  have hg : ρ.get p.1 = some ψ₁ :=
    (ResU.CompS.get_left_of_ne_imm h g₁ (fun e => Kind.mut_ne_imm (gk₁.symm.trans e))).2
  rw [hψ] at hg
  obtain rfl := Option.some.inj hg
  exact ⟨_, g₁, gk₁, hwalk⟩

/-- The mirror of `ExWits.to_compS_left`. -/
theorem ExWits.to_compS_right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w w₂ : List (Loc × ResU Loc Val)} (hw : ExWits R C ρ w)
    (hsub : ∀ p ∈ w₂, p ∈ w) (hs₂ : ρ₂.Sites Kind.mut (w₂.map Prod.fst)) :
    ExWits R C ρ₂ w₂ :=
  ExWits.to_compS_left (ResU.CompS.comm h) hw hsub hs₂

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- **`[TR]` Lemma 6.18** (p. 8): if `ρ₁ ▸◂ ρ₂` then `ex(ρ₁ ● ρ₂)_●` and
`ex(ρ₁)_● ● ex(ρ₂)_●` are Kleene-equal.  `[as printed]` (as a graph — G4) -/
theorem ExS.split {ρ₁ ρ₂ ρ₁₂ w : ResU Loc Val} (h₁₂ : ResU.CompS ρ₁ ρ₂ ρ₁₂) :
    ExS ρ₁₂ w ↔ ∃ σ₁ σ₂, ExS ρ₁ σ₁ ∧ ExS ρ₂ σ₂ ∧ ResU.CompS σ₁ σ₂ w := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompS ψ₁ ψ₂ ψ → CellU.CompatS ψ₁ ψ₂ :=
    fun _ _ _ hc => CellU.CompS.compat hc
  -- The printed second line, at `own` and at `mut`.
  have hown : ResU.CompS (ρ₁.restrict Kind.own) (ρ₂.restrict Kind.own)
      (ρ₁₂.restrict Kind.own) := ResU.CompS.restrict h₁₂ Kind.own
  have hmut : ResU.CompS (ρ₁.restrict Kind.mut) (ρ₂.restrict Kind.mut)
      (ρ₁₂.restrict Kind.mut) := ResU.CompS.restrict h₁₂ Kind.mut
  constructor
  · -- `ex(ρ₁₂)_●` is defined: cut its index set, its family and its fold in two,
    -- then exchange twice.
    intro h
    cases h with
    | mk hs hw hb hnm hσ =>
        rename_i u
        obtain ⟨u₁, u₂, hperm, hs₁, hs₂, hsub₁, hsub₂⟩ :=
          ResU.Sites.split_pairs h₁₂ Kind.mut_ne_imm hs
        have hperm' : (u.map Prod.snd).Perm (u₁.map Prod.snd ++ u₂.map Prod.snd) := by
          rw [← List.map_append]
          exact hperm.map Prod.snd
        obtain ⟨b₁, b₂, hb₁, hb₂, hbc⟩ :=
          (BigComp.append hR ResU.compLawsS).mp
            (BigComp.of_perm hR ResU.compLawsS hperm' hb)
        -- The printed third line.
        obtain ⟨nm₁, nm₂, hnm₁, hnm₂, hnmc⟩ :=
          (ResU.CompS.exchange₄ _ _ _ _ _).mp ⟨_, _, hown, hmut, hnm⟩
        -- The printed fourth line.
        obtain ⟨σ₁, σ₂, hσ₁, hσ₂, hσc⟩ :=
          (ResU.CompS.exchange₄ nm₁ nm₂ b₁ b₂ w).mp ⟨_, _, hnmc, hbc, hσ⟩
        exact ⟨σ₁, σ₂,
          ExW.mk hs₁ (ExWits.to_compS_left h₁₂ hw hsub₁ hs₁) hb₁ hnm₁ hσ₁,
          ExW.mk hs₂ (ExWits.to_compS_right h₁₂ hw hsub₂ hs₂) hb₂ hnm₂ hσ₂,
          hσc⟩
  · -- Both operands' walks are defined and compose: assemble the composite's
    -- index set, family and fold, then run the same two exchanges backwards.
    rintro ⟨σ₁, σ₂, h₁, h₂, hc⟩
    cases h₁ with
    | mk hs₁ hw₁ hb₁ hnm₁ hσ₁ =>
        rename_i u₁
        cases h₂ with
        | mk hs₂ hw₂ hb₂ hnm₂ hσ₂ =>
            rename_i u₂
            -- The printed fourth line, read right to left.
            obtain ⟨nm, b, hnmc, hbc, hσ⟩ :=
              (ResU.CompS.exchange₄ _ _ _ _ w).mpr ⟨σ₁, σ₂, hσ₁, hσ₂, hc⟩
            -- The printed third line, read right to left; the two composites it
            -- produces are `ρ₁₂|own` and `ρ₁₂|mut` by single-valuedness of `●`.
            obtain ⟨O, M, hO, hM, hOM⟩ :=
              (ResU.CompS.exchange₄ _ _ _ _ nm).mpr ⟨_, _, hnm₁, hnm₂, hnmc⟩
            obtain rfl : O = ρ₁₂.restrict Kind.own := ResU.CompS.functional hO hown
            obtain rfl : M = ρ₁₂.restrict Kind.mut := ResU.CompS.functional hM hmut
            refine ExW.mk (w := u₁ ++ u₂) ?_
              (ExWits.append (ExWits.of_compS_left h₁₂ hw₁)
                (ExWits.of_compS_right h₁₂ hw₂)) ?_ hOM hσ
            · rw [List.map_append]
              exact ResU.Sites.append_of_compS h₁₂ Kind.mut_ne_imm hs₁ hs₂
            · rw [List.map_append]
              exact (BigComp.append hR ResU.compLawsS).mpr ⟨_, _, hb₁, hb₂, hbc⟩

/-- **The `mut` half of the aliasable family, entry by entry.** -/
theorem AgWitsM.iff_mem {ρ : ResU Loc Val} {w : List (Loc × ResU Loc Val)} :
    AgWitsM ρ w ↔
      ∀ p ∈ w, ∃ ψ, ρ.get p.1 = some ψ ∧ ψ.kind = Kind.mut ∧ AgW ψ.wit p.2 := by
  induction w with
  | nil => exact ⟨fun _ p hp => absurd hp (by simp), fun _ => AgWitsM.nil⟩
  | cons q w ih =>
      constructor
      · intro h p hp
        cases h with
        | cons ψ hψ hk he hw =>
            rcases List.mem_cons.mp hp with rfl | hp
            · exact ⟨ψ, hψ, hk, he⟩
            · exact ih.mp hw p hp
      · intro h
        obtain ⟨ψ, hψ, hk, he⟩ := h q (by simp)
        exact AgWitsM.cons ψ hψ hk he (ih.mpr fun p hp => h p (by simp [hp]))

/-- **The `imm` half of the aliasable family, entry by entry.** -/
theorem AgWitsI.iff_mem {ρ : ResU Loc Val} {w : List (Loc × ResU Loc Val)} :
    AgWitsI ρ w ↔
      ∀ p ∈ w, ∃ ψ, ρ.get p.1 = some ψ ∧ ψ.kind = Kind.imm ∧
        ∃ e a, ExR ψ.wit e ∧ AgW ψ.wit a ∧ ResU.CompR e a p.2 := by
  induction w with
  | nil => exact ⟨fun _ p hp => absurd hp (by simp), fun _ => AgWitsI.nil⟩
  | cons q w ih =>
      constructor
      · intro h p hp
        cases h with
        | cons ψ hψ hk e a hex hag hc hw =>
            rcases List.mem_cons.mp hp with rfl | hp
            · exact ⟨ψ, hψ, hk, e, a, hex, hag, hc⟩
            · exact ih.mp hw p hp
      · intro h
        obtain ⟨ψ, hψ, hk, e, a, hex, hag, hc⟩ := h q (by simp)
        exact AgWitsI.cons ψ hψ hk e a hex hag hc (ih.mpr fun p hp => h p (by simp [hp]))

/-- Two `mut` halves over one resource concatenate. -/
theorem AgWitsM.append {ρ : ResU Loc Val} {w₁ w₂ : List (Loc × ResU Loc Val)}
    (h₁ : AgWitsM ρ w₁) (h₂ : AgWitsM ρ w₂) : AgWitsM ρ (w₁ ++ w₂) :=
  AgWitsM.iff_mem.mpr fun p hp => by
    rcases List.mem_append.mp hp with hp | hp
    · exact AgWitsM.iff_mem.mp h₁ p hp
    · exact AgWitsM.iff_mem.mp h₂ p hp

/-- Two `imm` halves over one resource concatenate. -/
theorem AgWitsI.append {ρ : ResU Loc Val} {w₁ w₂ : List (Loc × ResU Loc Val)}
    (h₁ : AgWitsI ρ w₁) (h₂ : AgWitsI ρ w₂) : AgWitsI ρ (w₁ ++ w₂) :=
  AgWitsI.iff_mem.mpr fun p hp => by
    rcases List.mem_append.mp hp with hp | hp
    · exact AgWitsI.iff_mem.mp h₁ p hp
    · exact AgWitsI.iff_mem.mp h₂ p hp

/-- Any sub-family of the `imm` half is one. -/
theorem AgWitsI.subset {ρ : ResU Loc Val} {w w' : List (Loc × ResU Loc Val)}
    (h : AgWitsI ρ w) (hsub : ∀ p ∈ w', p ∈ w) : AgWitsI ρ w' :=
  AgWitsI.iff_mem.mpr fun p hp => AgWitsI.iff_mem.mp h p (hsub p hp)

/-- `ρ₁`'s `mut` half is one of `ρ₁ ● ρ₂`'s: the cell is unchanged. -/
theorem AgWitsM.of_compS_left {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w : List (Loc × ResU Loc Val)} (hw : AgWitsM ρ₁ w) : AgWitsM ρ w :=
  AgWitsM.iff_mem.mpr fun p hp => by
    obtain ⟨ψ, hψ, hk, he⟩ := AgWitsM.iff_mem.mp hw p hp
    exact ⟨ψ,
      (ResU.CompS.get_left_of_ne_imm h hψ (fun e => Kind.mut_ne_imm (hk.symm.trans e))).2,
      hk, he⟩

/-- The mirror of `AgWitsM.of_compS_left`. -/
theorem AgWitsM.of_compS_right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w : List (Loc × ResU Loc Val)} (hw : AgWitsM ρ₂ w) : AgWitsM ρ w :=
  AgWitsM.of_compS_left (ResU.CompS.comm h) hw

/-- **`ρ₁`'s `imm` half is one of `ρ₁ ● ρ₂`'s**, overlaps included.  Here the
composite's cell is *not* `ρ₁`'s — the lifetime sets have been unioned — but the
tag and the witness are, and an entry reads nothing else. -/
theorem AgWitsI.of_compS_left {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w : List (Loc × ResU Loc Val)} (hw : AgWitsI ρ₁ w) : AgWitsI ρ w :=
  AgWitsI.iff_mem.mpr fun p hp => by
    obtain ⟨ψ, hψ, hk, e, a, hex, hag, hc⟩ := AgWitsI.iff_mem.mp hw p hp
    obtain ⟨χ, g, gk, gw⟩ := ResU.CompS.get_left h hψ
    exact ⟨χ, g, gk.trans hk, e, a, by rw [gw]; exact hex, by rw [gw]; exact hag, hc⟩

/-- The mirror of `AgWitsI.of_compS_left`. -/
theorem AgWitsI.of_compS_right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w : List (Loc × ResU Loc Val)} (hw : AgWitsI ρ₂ w) : AgWitsI ρ w :=
  AgWitsI.of_compS_left (ResU.CompS.comm h) hw

/-- The entries of `ρ₁ ● ρ₂`'s `mut` half that lie over `ρ₁` are `ρ₁`'s. -/
theorem AgWitsM.to_compS_left {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w w₁ : List (Loc × ResU Loc Val)} (hw : AgWitsM ρ w)
    (hsub : ∀ p ∈ w₁, p ∈ w) (hs₁ : ρ₁.Sites Kind.mut (w₁.map Prod.fst)) :
    AgWitsM ρ₁ w₁ := by
  refine AgWitsM.iff_mem.mpr fun p hp => ?_
  obtain ⟨ψ₁, g₁, gk₁⟩ := (hs₁.2 p.1).mp (List.mem_map.mpr ⟨p, hp, rfl⟩)
  obtain ⟨ψ, hψ, -, hwalk⟩ := AgWitsM.iff_mem.mp hw p (hsub p hp)
  have hg : ρ.get p.1 = some ψ₁ :=
    (ResU.CompS.get_left_of_ne_imm h g₁ (fun e => Kind.mut_ne_imm (gk₁.symm.trans e))).2
  rw [hψ] at hg
  obtain rfl := Option.some.inj hg
  exact ⟨_, g₁, gk₁, hwalk⟩

/-- The mirror of `AgWitsM.to_compS_left`. -/
theorem AgWitsM.to_compS_right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w w₂ : List (Loc × ResU Loc Val)} (hw : AgWitsM ρ w)
    (hsub : ∀ p ∈ w₂, p ∈ w) (hs₂ : ρ₂.Sites Kind.mut (w₂.map Prod.fst)) :
    AgWitsM ρ₂ w₂ :=
  AgWitsM.to_compS_left (ResU.CompS.comm h) hw hsub hs₂

/-- **The entries of `ρ₁ ● ρ₂`'s `imm` half that lie over `ρ₁` are `ρ₁`'s.**  No
disjointness is asked for: an entry over an `imm` location shared with `ρ₂` is
`ρ₁`'s entry too, because the witness is shared. -/
theorem AgWitsI.to_compS_left {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w w₁ : List (Loc × ResU Loc Val)} (hw : AgWitsI ρ w)
    (hsub : ∀ p ∈ w₁, p ∈ w) (hs₁ : ρ₁.Sites Kind.imm (w₁.map Prod.fst)) :
    AgWitsI ρ₁ w₁ := by
  refine AgWitsI.iff_mem.mpr fun p hp => ?_
  obtain ⟨ψ₁, g₁, gk₁⟩ := (hs₁.2 p.1).mp (List.mem_map.mpr ⟨p, hp, rfl⟩)
  obtain ⟨ψ, hψ, -, e, a, hex, hag, hc⟩ := AgWitsI.iff_mem.mp hw p (hsub p hp)
  obtain ⟨χ, g, -, gw⟩ := ResU.CompS.get_left h g₁
  rw [hψ] at g
  obtain rfl := Option.some.inj g
  exact ⟨ψ₁, g₁, gk₁, e, a, by rw [← gw]; exact hex, by rw [← gw]; exact hag, hc⟩

/-- The mirror of `AgWitsI.to_compS_left`. -/
theorem AgWitsI.to_compS_right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w w₂ : List (Loc × ResU Loc Val)} (hw : AgWitsI ρ w)
    (hsub : ∀ p ∈ w₂, p ∈ w) (hs₂ : ρ₂.Sites Kind.imm (w₂.map Prod.fst)) :
    AgWitsI ρ₂ w₂ :=
  AgWitsI.to_compS_left (ResU.CompS.comm h) hw hsub hs₂

/-- **The value the `imm` half pairs with a location depends only on the cell's
witness.**  This is what makes [TR] 6.20's `ρ₁ ∩ ρ₂` term *one* term rather than
two: the entry `ex(ρ′)_○ ○ ag(ρ′)` is the same on either side of the overlap, so
Lemma 6.19 can duplicate it.  `ExR.functional` and `AgW.functional` (§20a) fix
the two halves, and `ResU.CompR.functional` their composite.
`[about ours: `AgWitsI` is §18's family relation; the printed 6.19 is
`ResU.flatR_idem`]` -/
theorem AgWitsI.value_functional {ρ ρ' : ResU Loc Val}
    {w w' : List (Loc × ResU Loc Val)} (h : AgWitsI ρ w) (h' : AgWitsI ρ' w')
    {p q : Loc × ResU Loc Val} (hp : p ∈ w) (hq : q ∈ w')
    {ψ χ : CellU Loc Val} (hψ : ρ.get p.1 = some ψ) (hχ : ρ'.get q.1 = some χ)
    (hwit : ψ.wit = χ.wit) : p.2 = q.2 := by
  obtain ⟨ψ₀, g, -, e, a, hex, hag, hc⟩ := AgWitsI.iff_mem.mp h p hp
  obtain ⟨χ₀, g', -, e', a', hex', hag', hc'⟩ := AgWitsI.iff_mem.mp h' q hq
  rw [hψ] at g; obtain rfl := Option.some.inj g
  rw [hχ] at g'; obtain rfl := Option.some.inj g'
  have hee : e = e' := ExR.functional hex (by rw [← hwit] at hex'; exact hex')
  have haa : a = a' := AgW.functional hag (by rw [← hwit] at hag'; exact hag')
  exact ResU.CompR.functional hc (hee ▸ haa ▸ hc')

/-- Two `▶◀`-compatible cells carry the same witness — `CellU.CompatS`'s single
bound `ρ`, read off the relation.  It is the other half of "agree up to
lifetimes", `CellU.CompatS.kinds` being the first. -/
theorem CellU.CompatS.wit {ψ₁ ψ₂ : CellU Loc Val} (h : CellU.CompatS ψ₁ ψ₂) :
    ψ₁.wit = ψ₂.wit := by
  obtain ⟨s₁, s₂, v, ρ, k₁, k₂, e₁, e₂⟩ := h
  rw [e₁, e₂, CellU.wit_immOf, CellU.wit_immOf]

/-- At an overlap the two operands' cells share their witness, so the two `imm`
families pair the *same* value with that location. -/
theorem ResU.CompatS.wit_of_overlap {ρ₁ ρ₂ : ResU Loc Val} (h : ResU.CompatS ρ₁ ρ₂)
    {l : Loc} {ψ₁ ψ₂ : CellU Loc Val}
    (e₁ : ρ₁.get l = some ψ₁) (e₂ : ρ₂.get l = some ψ₂) : ψ₁.wit = ψ₂.wit :=
  CellU.CompatS.wit (h l ψ₁ ψ₂ e₁ e₂)

/-- **The `imm` locations of `ρ₁ ● ρ₂` are the union of those of `ρ₁` and
`ρ₂`.**  Union, not disjoint union: both disjuncts can hold at once, and that is
the whole difference between 6.20 and 6.18.
`[about ours: the printed `▶◀` and `●` read at the `imm` tag; no printed row
states it]` -/
theorem ResU.CompS.imm_site_iff {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    (l : Loc) :
    (∃ ψ, ρ.get l = some ψ ∧ ψ.kind = Kind.imm) ↔
      ((∃ ψ, ρ₁.get l = some ψ ∧ ψ.kind = Kind.imm) ∨
        (∃ ψ, ρ₂.get l = some ψ ∧ ψ.kind = Kind.imm)) := by
  constructor
  · rintro ⟨ψ, g, gk⟩
    rcases ResU.Comp.get h l with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
        ⟨χ₁, χ₂, χ, f₁, -, -, hC⟩
    · rw [g] at f; exact absurd f (by simp)
    · obtain rfl : ψ = χ := Option.some.inj (g.symm.trans f)
      exact Or.inl ⟨ψ, f₁, gk⟩
    · obtain rfl : ψ = χ := Option.some.inj (g.symm.trans f)
      exact Or.inr ⟨ψ, f₂, gk⟩
    · exact Or.inl ⟨χ₁, f₁, (CellU.CompatS.kinds (CellU.CompS.compat hC)).1⟩
  · rintro (⟨ψ, g, gk⟩ | ⟨ψ, g, gk⟩)
    · obtain ⟨χ, f, fk, -⟩ := ResU.CompS.get_left h g
      exact ⟨χ, f, fk.trans gk⟩
    · obtain ⟨χ, f, fk, -⟩ := ResU.CompS.get_right h g
      exact ⟨χ, f, fk.trans gk⟩

/-- **A family over the `imm` sites of `ρ₁ ● ρ₂` cuts into three blocks** — over
`ρ₁` alone, over `ρ₂` alone, and over both — with `ρ₁`'s own index set the first
block together with the third, and `ρ₂`'s the second with the third.  This is
[TR] 6.20's inclusion-exclusion, at the index sets.
`[about ours: `ResU.Sites` is convention G6's index set (§16); this is 6.20's
inclusion-exclusion read at the index sets]` -/
theorem ResU.Sites.split_pairs_imm {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {A : Type} {w : List (Loc × A)} (hs : ρ.Sites Kind.imm (w.map Prod.fst)) :
    ∃ wa wb wc : List (Loc × A), w.Perm (wa ++ (wb ++ wc)) ∧
      ρ₁.Sites Kind.imm ((wa ++ wc).map Prod.fst) ∧
      ρ₂.Sites Kind.imm ((wb ++ wc).map Prod.fst) ∧
      (∀ p ∈ wa, p ∈ w) ∧ (∀ p ∈ wb, p ∈ w) ∧ (∀ p ∈ wc, p ∈ w) := by
  classical
  -- `u` is the part of `w` lying over `ρ₁` and `wb` the rest; `u` then splits by
  -- whether the location lies over `ρ₂` as well.
  obtain ⟨u, wb, hpu, hmu, hmb⟩ :=
    List.split_by_key (fun l => ∃ ψ, ρ₁.get l = some ψ ∧ ψ.kind = Kind.imm) w
  obtain ⟨wc, wa, hpc, hmc, hma⟩ :=
    List.split_by_key (fun l => ∃ ψ, ρ₂.get l = some ψ ∧ ψ.kind = Kind.imm) u
  have hperm : w.Perm (wa ++ (wb ++ wc)) := by
    refine hpu.trans ((hpc.append_right wb).trans ?_)
    rw [List.append_assoc, ← List.append_assoc wa wb wc]
    exact List.perm_append_comm
  have hsubw : ∀ p ∈ u, p ∈ w := fun p hp => ((hmu p).mp hp).1
  have hsuba : ∀ p ∈ wa, p ∈ w := fun p hp => hsubw p ((hma p).mp hp).1
  have hsubb : ∀ p ∈ wb, p ∈ w := fun p hp => ((hmb p).mp hp).1
  have hsubc : ∀ p ∈ wc, p ∈ w := fun p hp => hsubw p ((hmc p).mp hp).1
  -- Duplicate-freeness of the three key blocks, and their pairwise
  -- disjointness, travel from `hs` along the permutation.
  have hkeys : (w.map Prod.fst).Perm
      ((wa.map Prod.fst) ++ ((wb.map Prod.fst) ++ (wc.map Prod.fst))) := by
    have hm := hperm.map Prod.fst
    rwa [List.map_append, List.map_append] at hm
  obtain ⟨nda, ndbc, hdis⟩ := List.nodup_append.mp (hkeys.nodup hs.1)
  obtain ⟨ndb, ndc, hdbc⟩ := List.nodup_append.mp ndbc
  have hcov : ∀ p ∈ w, (∃ ψ, ρ₁.get p.1 = some ψ ∧ ψ.kind = Kind.imm) ∨
      (∃ ψ, ρ₂.get p.1 = some ψ ∧ ψ.kind = Kind.imm) := fun p hp =>
    (ResU.CompS.imm_site_iff h p.1).mp ((hs.2 p.1).mp (List.mem_map.mpr ⟨p, hp, rfl⟩))
  refine ⟨wa, wb, wc, hperm, ⟨?_, fun l => ⟨?_, ?_⟩⟩, ⟨?_, fun l => ⟨?_, ?_⟩⟩,
    hsuba, hsubb, hsubc⟩
  · rw [List.map_append]
    exact List.nodup_append.mpr ⟨nda, ndc, fun a ha b hb =>
      hdis a ha b (List.mem_append.mpr (Or.inr hb))⟩
  · intro hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    rcases List.mem_append.mp hp with hp | hp
    · exact ((hmu p).mp ((hma p).mp hp).1).2
    · exact ((hmu p).mp ((hmc p).mp hp).1).2
  · intro hl
    obtain ⟨p, hp, hp1⟩ :=
      List.mem_map.mp ((hs.2 l).mpr ((ResU.CompS.imm_site_iff h l).mpr (Or.inl hl)))
    have hpu' : p ∈ u := (hmu p).mpr ⟨hp, hp1 ▸ hl⟩
    refine List.mem_map.mpr ⟨p, ?_, hp1⟩
    by_cases hq : ∃ ψ, ρ₂.get p.1 = some ψ ∧ ψ.kind = Kind.imm
    · exact List.mem_append.mpr (Or.inr ((hmc p).mpr ⟨hpu', hq⟩))
    · exact List.mem_append.mpr (Or.inl ((hma p).mpr ⟨hpu', hq⟩))
  · rw [List.map_append]
    exact List.nodup_append.mpr ⟨ndb, ndc, hdbc⟩
  · intro hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨hpw, hnq⟩ := (hmb p).mp hp
      exact (hcov p hpw).resolve_left hnq
    · exact ((hmc p).mp hp).2
  · intro hl
    obtain ⟨p, hp, hp1⟩ :=
      List.mem_map.mp ((hs.2 l).mpr ((ResU.CompS.imm_site_iff h l).mpr (Or.inr hl)))
    refine List.mem_map.mpr ⟨p, ?_, hp1⟩
    by_cases hq : ∃ ψ, ρ₁.get l = some ψ ∧ ψ.kind = Kind.imm
    · exact List.mem_append.mpr (Or.inr ((hmc p).mpr ⟨(hmu p).mpr ⟨hp, hp1 ▸ hq⟩, hp1 ▸ hl⟩))
    · exact List.mem_append.mpr (Or.inl ((hmb p).mpr ⟨hp, hp1 ▸ hq⟩))

/-- **`⨀(l ++ (m ++ m)) = ⨀(l ++ m)` at `○`** — a repeated block folds to what
one copy folds to.  At `○` this needs no hypothesis: `ResU.compR_self` says
`ρ ○ ρ = ρ` for every `ρ`, which is clause (1) of `○` read pointwise, and [TR]
Lemma 6.19 is its instance at `⦇ρ⦈_○`.
`[about ours: `BigComp` is §16's fold shape; the printed 6.19 is
`ResU.flatR_idem`, and this is the fold-level fact 6.20 spends it on]` -/
theorem BigComp.dupR {l m : List (ResU Loc Val)} {x : ResU Loc Val} :
    BigComp CellU.CompatR CellU.CompR (l ++ (m ++ m)) x ↔
      BigComp CellU.CompatR CellU.CompR (l ++ m) x := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  rw [BigComp.append hR ResU.compLawsR, BigComp.append hR ResU.compLawsR]
  refine ⟨fun ⟨L, Y, hL, hY, hx⟩ => ?_, fun ⟨L, M, hL, hM, hx⟩ => ?_⟩
  · obtain ⟨M₁, M₂, hM₁, hM₂, hMc⟩ := (BigComp.append hR ResU.compLawsR).mp hY
    obtain rfl : M₁ = M₂ := BigComp.functional ResU.compLawsR hM₁ hM₂
    obtain rfl : Y = M₁ := ResU.CompR.functional hMc (ResU.compR_self M₁)
    exact ⟨L, Y, hL, hM₁, hx⟩
  · exact ⟨L, M, hL,
      (BigComp.append hR ResU.compLawsR).mpr ⟨M, M, hM, hM, ResU.compR_self M⟩, hx⟩

/-- **A block already present may be appended again**, at `○`: if `d` is, up to
order, one of the blocks of `l`, then `⨀(l ++ d) = ⨀l`.  This is
`BigComp.dupR` with the repetition located inside a larger fold, which is the
shape [TR] 6.20's converse takes — only the `ρ₁ ∩ ρ₂` block is doubled, not the
whole composite.
`[about ours: `BigComp` is §16's fold shape; the printed 6.19 is
`ResU.flatR_idem`]` -/
theorem BigComp.dup_of_perm {l m d : List (ResU Loc Val)} (hp : l.Perm (m ++ d))
    {x : ResU Loc Val} :
    BigComp CellU.CompatR CellU.CompR (l ++ d) x ↔
      BigComp CellU.CompatR CellU.CompR l x := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  have h₁ : (l ++ d).Perm (m ++ (d ++ d)) := by
    rw [← List.append_assoc]
    exact hp.append_right d
  constructor
  · intro h
    exact BigComp.of_perm hR ResU.compLawsR hp.symm
      (BigComp.dupR.mp (BigComp.of_perm hR ResU.compLawsR h₁ h))
  · intro h
    exact BigComp.of_perm hR ResU.compLawsR h₁.symm
      (BigComp.dupR.mpr (BigComp.of_perm hR ResU.compLawsR hp h))

/-- The exchange of the middle two factors at `○`, which is the one [TR] 6.20
uses.
`[about ours: `ResU.Comp.exchange₄` instantiated at `○`]` -/
theorem ResU.CompR.exchange₄ (a₁ a₂ b₁ b₂ x : ResU Loc Val) :
    (∃ A B, ResU.CompR a₁ a₂ A ∧ ResU.CompR b₁ b₂ B ∧ ResU.CompR A B x) ↔
      (∃ S₁ S₂, ResU.CompR a₁ b₁ S₁ ∧ ResU.CompR a₂ b₂ S₂ ∧ ResU.CompR S₁ S₂ x) :=
  ResU.Comp.exchange₄ (fun _ _ ψ hc => ⟨ψ, hc⟩) ResU.compLawsR a₁ a₂ b₁ b₂ x

end BoCa.Fig16

namespace BoCa.Fig16

/-- `BoCa.Fig16.List.perm_of_keys` with the permutation of the key lists
replaced by same-membership, which is the form `ResU.Sites` hands over.
`[about ours: a restatement of §20a's list lemma; it is about `List`, not about
any printed row]` -/
theorem List.perm_of_keys_mem {α β : Type} {w w' : List (α × β)}
    (hk : (w.map Prod.fst).Nodup) (hk' : (w'.map Prod.fst).Nodup)
    (hmem : ∀ l, l ∈ w.map Prod.fst ↔ l ∈ w'.map Prod.fst)
    (hval : ∀ p ∈ w, ∀ q ∈ w', p.1 = q.1 → p.2 = q.2) : w.Perm w' :=
  BoCa.Fig16.List.perm_of_keys hk
    ((List.perm_ext_iff_of_nodup hk hk').mpr hmem) hval

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- **The composite's `imm` family, assembled from the two operands'.**  `w₂a`
is the part of `ρ₂`'s family at locations `ρ₁` does not carry, `w₂c` the part it
does, and `w₁c` the block of `ρ₁`'s family sitting over the same locations —
which `w₂c` permutes, so `⨀` cannot tell them apart.  `w₁ ++ w₂a` is then a
family for `ρ₁₂` over its whole `imm` index set.
`[about ours: `ResU.Sites` is convention G6's index set (§16) and `AgWitsI`
§18's family; this is 6.20's inclusion-exclusion read in the assembling
direction]` -/
theorem AgWitsI.assemble {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w₁ w₂ : List (Loc × ResU Loc Val)}
    (hs₁ : ρ₁.Sites Kind.imm (w₁.map Prod.fst)) (hw₁ : AgWitsI ρ₁ w₁)
    (hs₂ : ρ₂.Sites Kind.imm (w₂.map Prod.fst)) (hw₂ : AgWitsI ρ₂ w₂) :
    ∃ w₂a w₂c w₁r w₁c : List (Loc × ResU Loc Val),
      w₂.Perm (w₂a ++ w₂c) ∧ w₁.Perm (w₁r ++ w₁c) ∧ w₁c.Perm w₂c ∧
      ρ.Sites Kind.imm ((w₁ ++ w₂a).map Prod.fst) ∧
      AgWitsI ρ (w₁ ++ w₂a) := by
  classical
  -- `w₂c` is the shared block of `ρ₂`'s family, `w₁c` the matching block of
  -- `ρ₁`'s.  Each is cut by asking whether the *other* operand is `imm` there.
  obtain ⟨w₂c, w₂a, hp2, hm2c, hm2a⟩ :=
    List.split_by_key (fun l => ∃ ψ, ρ₁.get l = some ψ ∧ ψ.kind = Kind.imm) w₂
  obtain ⟨w₁c, w₁r, hp1, hm1c, -⟩ :=
    List.split_by_key (fun l => ∃ ψ, ρ₂.get l = some ψ ∧ ψ.kind = Kind.imm) w₁
  have hperm2 : w₂.Perm (w₂a ++ w₂c) := hp2.trans List.perm_append_comm
  have hperm1 : w₁.Perm (w₁r ++ w₁c) := hp1.trans List.perm_append_comm
  have hsub2a : ∀ p ∈ w₂a, p ∈ w₂ := fun p hp => ((hm2a p).mp hp).1
  -- Key lists inherit duplicate-freeness from the two `ResU.Sites`.
  have hk2 : ((w₂a.map Prod.fst) ++ (w₂c.map Prod.fst)).Nodup := by
    rw [← List.map_append]
    exact ((hperm2.map Prod.fst)).nodup hs₂.1
  obtain ⟨nd2a, nd2c, -⟩ := List.nodup_append.mp hk2
  have hk1 : ((w₁r.map Prod.fst) ++ (w₁c.map Prod.fst)).Nodup := by
    rw [← List.map_append]
    exact ((hperm1.map Prod.fst)).nodup hs₁.1
  obtain ⟨-, nd1c, -⟩ := List.nodup_append.mp hk1
  -- Both shared blocks are indexed by the locations `imm` in *both* operands.
  have hkey : ∀ l, l ∈ w₁c.map Prod.fst ↔ l ∈ w₂c.map Prod.fst := by
    intro l
    constructor
    · intro hl
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
      obtain ⟨hp1, hq2⟩ := (hm1c p).mp hp
      obtain ⟨q, hq, hq1⟩ := List.mem_map.mp ((hs₂.2 p.1).mpr hq2)
      exact List.mem_map.mpr ⟨q, (hm2c q).mpr ⟨hq, hq1 ▸
        (hs₁.2 p.1).mp (List.mem_map.mpr ⟨p, hp1, rfl⟩)⟩, hq1⟩
    · intro hl
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
      obtain ⟨hq2, hp1⟩ := (hm2c q).mp hq
      obtain ⟨p, hp, hp1'⟩ := List.mem_map.mp ((hs₁.2 q.1).mpr hp1)
      exact List.mem_map.mpr ⟨p, (hm1c p).mpr ⟨hp, hp1' ▸
        (hs₂.2 q.1).mp (List.mem_map.mpr ⟨q, hq2, rfl⟩)⟩, hp1'⟩
  -- At a shared location the two cells have one witness, so the two families
  -- pair the same value with it.
  have hval : ∀ p ∈ w₁c, ∀ q ∈ w₂c, p.1 = q.1 → p.2 = q.2 := by
    intro p hp q hq hpq
    obtain ⟨hp1, -⟩ := (hm1c p).mp hp
    obtain ⟨hq2, -⟩ := (hm2c q).mp hq
    obtain ⟨ψ₁, g₁, -⟩ := (hs₁.2 p.1).mp (List.mem_map.mpr ⟨p, hp1, rfl⟩)
    obtain ⟨ψ₂, g₂, -⟩ := (hs₂.2 q.1).mp (List.mem_map.mpr ⟨q, hq2, rfl⟩)
    exact AgWitsI.value_functional hw₁ hw₂ hp1 hq2 g₁ g₂
      (ResU.CompatS.wit_of_overlap h.1 g₁ (hpq ▸ g₂))
  refine ⟨w₂a, w₂c, w₁r, w₁c, hperm2, hperm1,
    List.perm_of_keys_mem nd1c nd2c hkey hval, ⟨?_, fun l => ⟨?_, ?_⟩⟩, ?_⟩
  · -- `w₁`'s keys and `w₂a`'s are disjoint: every `w₁` key is `imm` in `ρ₁`,
    -- and no `w₂a` key is.
    rw [List.map_append]
    refine List.nodup_append.mpr ⟨hs₁.1, nd2a, fun a ha b hb hab => ?_⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
    exact ((hm2a q).mp hq).2 (hab ▸ (hs₁.2 a).mp ha)
  · intro hl
    rw [List.map_append] at hl
    rcases List.mem_append.mp hl with hl | hl
    · exact (ResU.CompS.imm_site_iff h l).mpr (Or.inl ((hs₁.2 l).mp hl))
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
      exact (ResU.CompS.imm_site_iff h q.1).mpr
        (Or.inr ((hs₂.2 q.1).mp (List.mem_map.mpr ⟨q, hsub2a q hq, rfl⟩)))
  · intro hl
    rw [List.map_append]
    rcases (ResU.CompS.imm_site_iff h l).mp hl with hq | hq
    · exact List.mem_append.mpr (Or.inl ((hs₁.2 l).mpr hq))
    · by_cases hq₁ : ∃ ψ, ρ₁.get l = some ψ ∧ ψ.kind = Kind.imm
      · exact List.mem_append.mpr (Or.inl ((hs₁.2 l).mpr hq₁))
      · obtain ⟨q, hq', hq1⟩ := List.mem_map.mp ((hs₂.2 l).mpr hq)
        exact List.mem_append.mpr (Or.inr
          (List.mem_map.mpr ⟨q, (hm2a q).mpr ⟨hq', hq1 ▸ hq₁⟩, hq1⟩))
  · exact AgWitsI.append (AgWitsI.of_compS_left h hw₁)
      (AgWitsI.of_compS_right h (AgWitsI.subset hw₂ hsub2a))

/-- **The exchange when one factor is shared**, at `○`:

    A ◐ (B ◐ C)  =  (A ◐ C) ◐ (B ◐ C),

as a Kleene equality.  `C` occurs once on the left and twice on the right; at
`○` that costs nothing, because a repeated block folds to one copy
(`BigComp.dup_of_perm`, whose printed row is Lemma 6.19).  This is the whole
content of [TR] 6.20's inclusion-exclusion once the index sets have been cut.
`[about ours: the rearrangement 6.20's proof performs on the `imm` families;
the printed rows behind it are 6.2, 6.3 and 6.19]` -/
theorem ResU.CompR.exchange₃dup (A B C x : ResU Loc Val) :
    (∃ Y, ResU.CompR B C Y ∧ ResU.CompR A Y x) ↔
      (∃ S₁ S₂, ResU.CompR A C S₁ ∧ ResU.CompR B C S₂ ∧ ResU.CompR S₁ S₂ x) := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  have hleft : (∃ Y, ResU.CompR B C Y ∧ ResU.CompR A Y x) ↔
      BigComp CellU.CompatR CellU.CompR [A, B, C] x := by
    constructor
    · rintro ⟨Y, hY, hx⟩
      exact BigComp.cons (BigComp.pair ResU.compLawsR |>.mpr hY) hx
    · intro h
      cases h with
      | cons ht hx => exact ⟨_, BigComp.pair ResU.compLawsR |>.mp ht, hx⟩
  have hright : (∃ S₁ S₂, ResU.CompR A C S₁ ∧ ResU.CompR B C S₂ ∧ ResU.CompR S₁ S₂ x) ↔
      BigComp CellU.CompatR CellU.CompR [A, C, B, C] x := by
    rw [show ([A, C, B, C] : List (ResU Loc Val)) = [A, C] ++ [B, C] from rfl,
      BigComp.append hR ResU.compLawsR]
    exact ⟨fun ⟨S₁, S₂, h₁, h₂, hx⟩ =>
        ⟨S₁, S₂, BigComp.pair ResU.compLawsR |>.mpr h₁,
          BigComp.pair ResU.compLawsR |>.mpr h₂, hx⟩,
      fun ⟨S₁, S₂, h₁, h₂, hx⟩ =>
        ⟨S₁, S₂, BigComp.pair ResU.compLawsR |>.mp h₁,
          BigComp.pair ResU.compLawsR |>.mp h₂, hx⟩⟩
  -- `[A, C, B, C]` is `[A, B, C]` with its own last entry appended again.
  have hp : ([A, C, B, C] : List (ResU Loc Val)).Perm ([A, B, C] ++ [C]) :=
    List.Perm.cons A (List.Perm.swap B C [C])
  have hd : BigComp CellU.CompatR CellU.CompR ([A, B, C] ++ [C]) x ↔
      BigComp CellU.CompatR CellU.CompR [A, B, C] x :=
    BigComp.dup_of_perm (m := [A, B]) (List.Perm.refl _)
  rw [hleft, hright]
  exact ⟨fun h => BigComp.of_perm hR ResU.compLawsR hp.symm (hd.mpr h),
    fun h => hd.mp (BigComp.of_perm hR ResU.compLawsR hp h)⟩

/-- **`[TR]` Lemma 6.20** (p. 9): if `ρ₁ ▸◂ ρ₂` then `ag(ρ₁ ● ρ₂)` and
`ag(ρ₁) ○ ag(ρ₂)` are Kleene-equal.  The hypothesis is at `●` and the
conclusion composes at `○`, as printed.  `[as printed]` (as a graph — G4) -/
theorem AgW.split {ρ₁ ρ₂ ρ₁₂ w : ResU Loc Val} (h₁₂ : ResU.CompS ρ₁ ρ₂ ρ₁₂) :
    AgW ρ₁₂ w ↔ ∃ σ₁ σ₂, AgW ρ₁ σ₁ ∧ AgW ρ₂ σ₂ ∧ ResU.CompR σ₁ σ₂ w := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  have himm : ResU.CompR (ρ₁.restrict Kind.imm) (ρ₂.restrict Kind.imm)
      (ρ₁₂.restrict Kind.imm) := ResU.CompS.restrictR h₁₂ Kind.imm
  constructor
  · intro h
    cases h with
    | mk hsm hsi hwm hwi hbm hbi ha hσ =>
        rename_i wm wi
        -- The `mut` index set is cut in two, as in 6.18.
        obtain ⟨wm₁, wm₂, hpm, hsm₁, hsm₂, hsubm₁, hsubm₂⟩ :=
          ResU.Sites.split_pairs h₁₂ Kind.mut_ne_imm hsm
        have hpm' : (wm.map Prod.snd).Perm (wm₁.map Prod.snd ++ wm₂.map Prod.snd) := by
          rw [← List.map_append]
          exact hpm.map Prod.snd
        obtain ⟨bm₁, bm₂, hbm₁, hbm₂, hbmc⟩ :=
          (BigComp.append hR ResU.compLawsR).mp
            (BigComp.of_perm hR ResU.compLawsR hpm' hbm)
        -- The `imm` index set is cut in three: `ρ₁` alone, `ρ₂` alone, shared.
        obtain ⟨wa, wb, wc, hpi, hsi₁, hsi₂, hsuba, hsubb, hsubc⟩ :=
          ResU.Sites.split_pairs_imm h₁₂ hsi
        have hpi' : (wi.map Prod.snd).Perm
            (wa.map Prod.snd ++ (wb.map Prod.snd ++ wc.map Prod.snd)) := by
          rw [← List.map_append, ← List.map_append]
          exact hpi.map Prod.snd
        obtain ⟨A, X, hA, hX, hAX⟩ :=
          (BigComp.append hR ResU.compLawsR).mp
            (BigComp.of_perm hR ResU.compLawsR hpi' hbi)
        obtain ⟨B, Cc, hB, hCc, hBC⟩ := (BigComp.append hR ResU.compLawsR).mp hX
        -- The shared block is handed to both sides; this is 6.19's step.
        obtain ⟨bi₁, bi₂, hS₁, hS₂, hbic⟩ :=
          (ResU.CompR.exchange₃dup A B Cc _).mp ⟨X, hBC, hAX⟩
        have hbi₁ : BigComp CellU.CompatR CellU.CompR ((wa ++ wc).map Prod.snd) bi₁ := by
          rw [List.map_append]
          exact (BigComp.append hR ResU.compLawsR).mpr ⟨A, Cc, hA, hCc, hS₁⟩
        have hbi₂ : BigComp CellU.CompatR CellU.CompR ((wb ++ wc).map Prod.snd) bi₂ := by
          rw [List.map_append]
          exact (BigComp.append hR ResU.compLawsR).mpr ⟨B, Cc, hB, hCc, hS₂⟩
        -- The two exchanges of the print's final regrouping.
        obtain ⟨a₁, a₂, ha₁, ha₂, hac⟩ :=
          (ResU.CompR.exchange₄ _ _ _ _ _).mp ⟨_, _, himm, hbmc, ha⟩
        obtain ⟨σ₁, σ₂, hσ₁, hσ₂, hσc⟩ :=
          (ResU.CompR.exchange₄ a₁ a₂ bi₁ bi₂ w).mp ⟨_, _, hac, hbic, hσ⟩
        refine ⟨σ₁, σ₂,
          AgW.mk hsm₁ hsi₁ (AgWitsM.to_compS_left h₁₂ hwm hsubm₁ hsm₁)
            (AgWitsI.to_compS_left h₁₂ hwi ?_ hsi₁) hbm₁ hbi₁ ha₁ hσ₁,
          AgW.mk hsm₂ hsi₂ (AgWitsM.to_compS_right h₁₂ hwm hsubm₂ hsm₂)
            (AgWitsI.to_compS_right h₁₂ hwi ?_ hsi₂) hbm₂ hbi₂ ha₂ hσ₂,
          hσc⟩
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hsuba p hp
          · exact hsubc p hp
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hsubb p hp
          · exact hsubc p hp
  · rintro ⟨σ₁, σ₂, h₁, h₂, hc⟩
    cases h₁ with
    | mk hsm₁ hsi₁ hwm₁ hwi₁ hbm₁ hbi₁ ha₁ hσ₁ =>
        rename_i wm₁ wi₁
        cases h₂ with
        | mk hsm₂ hsi₂ hwm₂ hwi₂ hbm₂ hbi₂ ha₂ hσ₂ =>
            rename_i wm₂ wi₂
            -- The two exchanges, read right to left.
            obtain ⟨a, bi, hac, hbic, hσ⟩ :=
              (ResU.CompR.exchange₄ _ _ _ _ w).mpr ⟨σ₁, σ₂, hσ₁, hσ₂, hc⟩
            obtain ⟨I, bm, hI, hbmc, ha⟩ :=
              (ResU.CompR.exchange₄ _ _ _ _ a).mpr ⟨_, _, ha₁, ha₂, hac⟩
            obtain rfl : I = ρ₁₂.restrict Kind.imm := ResU.CompR.functional hI himm
            -- The composite's `imm` family, assembled with its shared block named.
            obtain ⟨w₂a, w₂c, w₁r, w₁c, hperm2, hperm1, hcperm, hsi, hwi⟩ :=
              AgWitsI.assemble h₁₂ hsi₁ hwi₁ hsi₂ hwi₂
            refine AgW.mk (wm := wm₁ ++ wm₂) (wi := wi₁ ++ w₂a) ?_ hsi
              (AgWitsM.append (AgWitsM.of_compS_left h₁₂ hwm₁)
                (AgWitsM.of_compS_right h₁₂ hwm₂)) hwi ?_ ?_ ha hσ
            · rw [List.map_append]
              exact ResU.Sites.append_of_compS h₁₂ Kind.mut_ne_imm hsm₁ hsm₂
            · rw [List.map_append]
              exact (BigComp.append hR ResU.compLawsR).mpr ⟨_, _, hbm₁, hbm₂, hbmc⟩
            · -- `wi₁ ++ w₂a` folds to `bi` because the block `w₂c` that `ρ₂`'s
              -- family adds is, entry for entry, the block `w₁c` of `ρ₁`'s.
              have hsplit : (wi₁ ++ w₂a).Perm ((w₁r ++ w₂a) ++ w₂c) := by
                refine (hperm1.append_right w₂a).trans ?_
                refine ((hcperm.append_left w₁r).append_right w₂a).trans ?_
                rw [List.append_assoc, List.append_assoc]
                exact List.Perm.append_left w₁r List.perm_append_comm
              have hdup : ((wi₁ ++ w₂a).map Prod.snd).Perm
                  (((w₁r ++ w₂a).map Prod.snd) ++ (w₂c.map Prod.snd)) := by
                rw [← List.map_append]
                exact hsplit.map Prod.snd
              refine BigComp.dup_of_perm hdup |>.mp ?_
              rw [List.map_append, List.append_assoc, ← List.map_append]
              exact (BigComp.append hR ResU.compLawsR).mpr ⟨_, _, hbi₁,
                BigComp.of_perm hR ResU.compLawsR (hperm2.map Prod.snd) hbi₂, hbic⟩

/-- **`⦇ρ₁ ● ρ₂⦈ = ex(ρ₁)_● ● ex(ρ₂)_● ● (ag(ρ₁) ○ ag(ρ₂))`**, as a Kleene
equality — the expansion [TR] 6.15's proof (p. 8) opens with, obtained from 6.18
and 6.20 exactly as printed.  The mixed operators are the print's: the two
exclusive walks compose at `●` and the two aliasable walks at `○`.
`[about ours: the equation [TR] 6.15's proof obtains from 6.18 and 6.20; it
carries no numbered row of its own]` -/
theorem ResU.Flat.split {ρ₁ ρ₂ ρ₁₂ σ : ResU Loc Val} (h₁₂ : ResU.CompS ρ₁ ρ₂ ρ₁₂) :
    ResU.Flat ρ₁₂ σ ↔ ∃ e₁ e₂ e a₁ a₂ a,
      ExS ρ₁ e₁ ∧ ExS ρ₂ e₂ ∧ ResU.CompS e₁ e₂ e ∧
      AgW ρ₁ a₁ ∧ AgW ρ₂ a₂ ∧ ResU.CompR a₁ a₂ a ∧ ResU.CompS e a σ := by
  constructor
  · rintro ⟨e, a, he, ha, hc⟩
    obtain ⟨e₁, e₂, he₁, he₂, hec⟩ := (ExS.split h₁₂).mp he
    obtain ⟨a₁, a₂, ha₁, ha₂, hac⟩ := (AgW.split h₁₂).mp ha
    exact ⟨e₁, e₂, e, a₁, a₂, a, he₁, he₂, hec, ha₁, ha₂, hac, hc⟩
  · rintro ⟨e₁, e₂, e, a₁, a₂, a, he₁, he₂, hec, ha₁, ha₂, hac, hc⟩
    exact ⟨e, a, (ExS.split h₁₂).mpr ⟨e₁, e₂, he₁, he₂, hec⟩,
      (AgW.split h₁₂).mpr ⟨a₁, a₂, ha₁, ha₂, hac⟩, hc⟩

end BoCa.Fig16

end
