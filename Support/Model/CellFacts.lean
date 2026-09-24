import Paper.S5_Model.Definitions
import Support.Model.Prelude

/-!
# Support — Model — CellFacts

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
facts about the cell constructors: injectivity and distinctness of `own`/`imm`/`mut`, the lifetime of a `mut` cell, and the stored predicate.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Fig16.PMap
variable {Loc A B : Type}

/-- `Loc` is infinite.  **Ours** — neither document states it (§3). -/
def Infinite (Loc : Type) : Prop := ∀ d : List Loc, ∃ l : Loc, l ∉ d

/-- The step `[TR]` Lemma 6.141 (`wp-alloc`, p. 37) takes without justification:
a finite map over an infinite `Loc` misses a location.  This is what the `fin`
mark buys.
`[about ours: the existence of a fresh location, which 6.141's proof uses in one
unjustified step; 6.141 itself is a `wp` rule and is not stated here]` -/
theorem exists_fresh (h : Infinite Loc) (p : PMap Loc A) : ∃ l, p.get l = none := by
  obtain ⟨d, hd⟩ := p.finite
  obtain ⟨l, hl⟩ := h d
  refine ⟨l, ?_⟩
  cases e : p.get l with
  | none => rfl
  | some ψ => exact absurd (hd l (by rw [e]; intro h'; simp at h')) hl

end BoCa.Fig16.PMap

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- The invariant of a `mut` cell, read as a predicate on `Res` — extension by
falsity outside `Res_β`.  Non-dependent, unlike the `P` field, which is what
makes it usable to read an invariant off an equation between cells. -/
def MutU.pred (m : MutU Loc Val) : Val → ResU Loc Val → Prop :=
  fun v r => ∃ h : r.InStratum m.β, m.P v (ResU.toStratum r h)

theorem ResS.toS_toStratum {α : Life} (r : ResS Loc Val α) (h : r.val.InStratum α) :
    (ResU.toStratum r.val h).toS = r := ResS.toS_toRes r

theorem CellU.ownOf_ne_immOf {v v' : Val} {s : LSet} {ρ : ResU Loc Val}
    {h : ρ.InStratum s.join} : ownOf v ≠ immOf s v' ρ h := by
  intro e; simp [ownOf, immOf] at e

theorem CellU.ownOf_ne_mutOf {v v' : Val} {b : Life} {ρ : ResU Loc Val}
    {h : ρ.InStratum b} {P : Val → SPropS Loc Val b} {hw : P v' ⟨ρ, h⟩} :
    ownOf v ≠ mutOf b v' ρ h P hw := by
  intro e; simp [ownOf, mutOf] at e

theorem CellU.immOf_ne_mutOf {s : LSet} {v v' : Val} {ρ ρ' : ResU Loc Val}
    {h : ρ.InStratum s.join} {b : Life} {h' : ρ'.InStratum b}
    {P : Val → SPropS Loc Val b} {hw : P v' ⟨ρ', h'⟩} :
    immOf s v ρ h ≠ mutOf b v' ρ' h' P hw := by
  intro e; simp [immOf, mutOf] at e

theorem CellU.mutOf_at {b₁ b₂ : Life} {v₁ v₂ : Val} {ρ₁ ρ₂ : ResU Loc Val}
    {h₁ : ρ₁.InStratum b₁} {h₂ : ρ₂.InStratum b₂}
    {P₁ : Val → SPropS Loc Val b₁} {P₂ : Val → SPropS Loc Val b₂}
    {hw₁ : P₁ v₁ ⟨ρ₁, h₁⟩} {hw₂ : P₂ v₂ ⟨ρ₂, h₂⟩}
    (e : mutOf b₁ v₁ ρ₁ h₁ P₁ hw₁ = mutOf b₂ v₂ ρ₂ h₂ P₂ hw₂) : b₁ = b₂ :=
  congrArg CellU.at e

theorem CellU.mutOf_inj {b : Life} {v₁ v₂ : Val} {ρ₁ ρ₂ : ResU Loc Val}
    {h₁ : ρ₁.InStratum b} {h₂ : ρ₂.InStratum b}
    {P₁ P₂ : Val → SPropS Loc Val b}
    {hw₁ : P₁ v₁ ⟨ρ₁, h₁⟩} {hw₂ : P₂ v₂ ⟨ρ₂, h₂⟩}
    (e : mutOf b v₁ ρ₁ h₁ P₁ hw₁ = mutOf b v₂ ρ₂ h₂ P₂ hw₂) :
    v₁ = v₂ ∧ ρ₁ = ρ₂ ∧ P₁ = P₂ := by
  simp only [mutOf] at e
  injection e with e'
  refine ⟨congrArg MutU.v e', ?_, ?_⟩
  · have := congrArg MutU.res e'
    simpa [MutU.res] using this
  · have hP := congrArg MutU.pred e'
    funext v r
    have h1 := congrFun (congrFun hP v) r.val
    simp only [MutU.pred] at h1
    apply propext
    constructor
    · intro hx
      have hy : ∃ hh : r.val.InStratum b, P₁ v ((ResU.toStratum r.val hh).toS) :=
        ⟨r.property, by rw [ResS.toS_toStratum]; exact hx⟩
      rw [h1] at hy
      obtain ⟨hh, hz⟩ := hy
      rw [ResS.toS_toStratum] at hz
      exact hz
    · intro hx
      have hy : ∃ hh : r.val.InStratum b, P₂ v ((ResU.toStratum r.val hh).toS) :=
        ⟨r.property, by rw [ResS.toS_toStratum]; exact hx⟩
      rw [← h1] at hy
      obtain ⟨hh, hz⟩ := hy
      rw [ResS.toS_toStratum] at hz
      exact hz

/-- **The meet-compare implies membership in the stratum, at every `α`.**  `@ψ`
is `⊤` on an `own` cell and `Res_α` asks nothing of it, so a bound on `@ρ` is a
bound on the borrow cells alone — which is all `Res_α` constrains. -/
theorem ResU.inStratum_of_atLife {ρ : ResU Loc Val} {a α : Life} (ha : ρ.AtLife a)
    (h : a ⊐ α) : ρ.InStratum α := by
  intro l ψ e
  have hle : a ⊑ ψ.at := ha.1 l ψ e
  cases ψ with
  | own v => exact trivial
  | imm i => exact lt_of_lt_of_le h hle
  | «mut» m => exact lt_of_lt_of_le h hle

end BoCa.Fig16

end
