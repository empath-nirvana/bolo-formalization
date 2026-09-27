import Paper.S1_Syntax.Definitions
import Paper.S3_Dynamics.Definitions
import Support.Dynamics.Machine
import Support.Model.Prelude

/-!
# Support — Dynamics — Policy

`[about ours]`.  Runs under an allocation policy.  `[TR]` p. 4's `alloc↦` allocates any
location the memory misses; a policy `pol` fixes which, as a function of the memory.  A policy
step is a step of the machine whose allocation, if it makes one, is at `pol μ` (`PolStep`); a
policy run is a sequence of them (`PolRun`).  Every policy run is a run (`PolRun.toSteps`), and
policy runs are closed under the operations `wp`'s rules build runs with: the empty run, a step
that allocates nothing, an allocation at `pol μ`, plugging into a context, and concatenation
(docs/adjudications.md §12.74).
-/

noncomputable section

namespace BoCa.BoLo

/-- An allocation policy: a location for each memory, missing from every finite memory. -/
structure Policy where
  pick : Heap → Loc
  fresh : ∀ μ : Heap, Fig16.FinDom μ → μ (pick μ) = none

/-- A step whose allocation, if any, is at `pol.pick μ`. -/
def PolStep (pol : Policy) (μ : Heap) (e : Expr) (μ' : Heap) (e' : Expr) : Prop :=
  Step1 μ e μ' e' ∧ ∀ ℓ, μ' ℓ ≠ none → μ ℓ = none → ℓ = pol.pick μ

/-- A run under the policy `pol`. -/
inductive PolRun (pol : Policy) : Heap → Expr → Heap → Expr → Prop where
  | refl (μ : Heap) (e : Expr) : PolRun pol μ e μ e
  | more {μ μ₁ μ' : Heap} {e e₁ e' : Expr}
      (h : PolStep pol μ e μ₁ e₁) (t : PolRun pol μ₁ e₁ μ' e') : PolRun pol μ e μ' e'

open Classical in
/-- The least location a finite memory misses. -/
def leastFree : Policy where
  pick μ := if h : ∃ l, μ l = none then Nat.find h else 0
  fresh μ hfin := by
    obtain ⟨d, hd⟩ := hfin
    have h : ∃ l, μ l = none := ⟨d.sum + 1, by
      by_contra hne
      exact Nat.not_succ_le_self _ (List.le_sum_of_mem (hd _ hne))⟩
    simp only [dif_pos h]
    exact Nat.find_spec h

namespace PolRun

theorem toSteps {pol : Policy} {μ μ' : Heap} {e e' : Expr} (h : PolRun pol μ e μ' e') :
    Steps μ e μ' e' := by
  induction h with
  | refl => exact .refl _ _
  | more h _ ih => exact .more h.1 ih

/-- A step that allocates no location, then a policy run. -/
theorem cons {pol : Policy} {μ μ₁ μ' : Heap} {e e₁ e' : Expr} (h : Step1 μ e μ₁ e₁)
    (hdom : ∀ ℓ, μ₁ ℓ ≠ none → μ ℓ ≠ none) (t : PolRun pol μ₁ e₁ μ' e') :
    PolRun pol μ e μ' e' :=
  .more ⟨h, fun ℓ h₁ h₀ => absurd h₀ (hdom ℓ h₁)⟩ t

theorem trans {pol : Policy} {μ μ₁ μ' : Heap} {e e₁ e' : Expr} (h₁ : PolRun pol μ e μ₁ e₁)
    (h₂ : PolRun pol μ₁ e₁ μ' e') : PolRun pol μ e μ' e' := by
  induction h₁ with
  | refl => exact h₂
  | more h _ ih => exact .more h (ih h₂)

theorem plug {pol : Policy} (K : Kont) {μ μ' : Heap} {e e' : Expr} (h : PolRun pol μ e μ' e') :
    PolRun pol μ (K.plug e) μ' (K.plug e') := by
  induction h with
  | refl => exact .refl _ _
  | more h _ ih => exact .more ⟨Step1.plug K h.1, h.2⟩ ih

/-- The allocation at the policy's location. -/
theorem alloc (pol : Policy) (μ : Heap) (v : Val) (hfin : Fig16.FinDom μ) :
    PolRun pol μ (.app (.val (.prim .alloc)) (.val v)) (μ.upd (pol.pick μ) v)
      (.val (.loc (pol.pick μ))) := by
  refine .more ⟨Step1.head (Head.alloc μ v _ (pol.fresh μ hfin)), fun ℓ h₁ h₀ => ?_⟩ (.refl _ _)
  by_contra hne
  exact h₁ (by rw [Heap.upd_other hne, h₀])

end PolRun

end BoCa.BoLo

end
