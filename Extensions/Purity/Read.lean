import Purity.Syntax

/-!
# Purity — the read footprint

A head step *touches* the location it loads, stores to or frees (`Touch`).  `RunIn S` is a run
each of whose steps touches only a location of `S` or one that an earlier step of the run
allocated.  `Footprint` bounds what a run changes; this bounds what it inspects.

* **Every run of every term** reads only what its term reaches (`steps_runIn`): from a set `S`
  closed for `(μ, e)`, every run is `RunIn S`.  A step touches a location its redex mentions,
  and a location enters the term only from the term, from a cell of `S`, or from `alloc↦`.
* **A well-typed program** reads only what its arguments reach (`derivesWf_runIn`): every run of
  `γ(e)` is `RunIn (Reach μ (ArgLocs γ))`, because `e` names no location (`Syntax.lean`).

The second statement is where typing is needed: `Boundary.lean` gives a term the semantic
judgment types, with no arguments, whose every run from one typed world loads a cell of the
frame.

`[about ours]`: an extension, not a transcription.
-/

noncomputable section

namespace BoCa.Purity
open BoCa
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LifeCtx)

/-- The redex `a` touches `ℓ`: it loads, stores to or frees `ℓ`. -/
inductive Touch : Expr → Loc → Prop where
  | load (ℓ : Loc) : Touch (.app (.val (.prim .load)) (.val (.loc ℓ))) ℓ
  | free (ℓ : Loc) : Touch (.app (.val (.prim .free)) (.val (.loc ℓ))) ℓ
  | store (ℓ : Loc) (v : Val) :
      Touch (.app (.app (.val (.prim .store)) (.val (.loc ℓ))) (.val v)) ℓ

theorem Touch.occ {a : Expr} {ℓ : Loc} (h : Touch a ℓ) : a.Occ ℓ := by
  cases h <;> simp [Expr.Occ, Expr.val, Val.loc]

/-- `S` extended by the locations a step from `μ` to `μ₁` allocates. -/
def Grow (S : Loc → Prop) (μ μ₁ : Heap) (ℓ : Loc) : Prop := S ℓ ∨ (μ ℓ = none ∧ μ₁ ℓ ≠ none)

/-- A run each of whose steps touches only locations in `S`, or allocated by an earlier step. -/
inductive RunIn : (Loc → Prop) → Heap → Expr → Heap → Expr → Prop where
  | refl (S : Loc → Prop) (μ : Heap) (e : Expr) : RunIn S μ e μ e
  | more {S : Loc → Prop} {μ μ₁ μ' : Heap} {e e₁ e' : Expr} (K : Kont) (a a' : Expr)
      (he : e = K.plug a) (he₁ : e₁ = K.plug a') (hh : Head μ a μ₁ a')
      (ht : ∀ ℓ, Touch a ℓ → S ℓ) (t : RunIn (Grow S μ μ₁) μ₁ e₁ μ' e') : RunIn S μ e μ' e'

theorem RunIn.toSteps {S : Loc → Prop} {μ μ' : Heap} {e e' : Expr} (h : RunIn S μ e μ' e') :
    Steps μ e μ' e' := by
  induction h with
  | refl => exact .refl _ _
  | more K a a' he he₁ hh _ _ ih => exact .more ⟨K, a, a', he, he₁, hh⟩ ih

/-- **One step keeps a closed set closed**, extended by what it allocates; and it touches only
locations of the set. -/
theorem closed_head {S : Loc → Prop} {μ μ₁ : Heap} {K : Kont} {a a' : Expr}
    (hS : Closed S μ (K.plug a)) (hh : Head μ a μ₁ a') :
    (∀ ℓ, Touch a ℓ → S ℓ) ∧ Closed (Grow S μ μ₁) μ₁ (K.plug a') := by
  obtain ⟨hterm, hheap⟩ := hS
  have ha : ∀ ℓ, a.Occ ℓ → S ℓ := fun ℓ o => hterm ℓ ((Kont.occ_plug_iff K).mpr (Or.inr o))
  have hK : ∀ ℓ, (K.plug .unit).Occ ℓ → S ℓ :=
    fun ℓ o => hterm ℓ ((Kont.occ_plug_iff K).mpr (Or.inl o))
  refine ⟨fun ℓ ht => ha ℓ ht.occ, ?_⟩
  -- the term: `K`'s locations, and the result's
  have term : (∀ ℓ, a'.Occ ℓ → Grow S μ μ₁ ℓ) → ∀ ℓ, (K.plug a').Occ ℓ → Grow S μ μ₁ ℓ :=
    fun h ℓ o => by
      rcases (Kont.occ_plug_iff K).mp o with o | o
      · exact Or.inl (hK ℓ o)
      · exact h ℓ o
  have sub : ∀ {e : Expr} {s : Val} {j : Nat}, (∀ ℓ, e.Occ ℓ → S ℓ) → (∀ ℓ, s.1.Occ ℓ → S ℓ) →
      ∀ ℓ, (e.subst j s).Occ ℓ → Grow S μ μ₁ ℓ := fun he hs ℓ o => by
    rcases Expr.occ_subst _ _ _ o with o | o
    · exact Or.inl (he ℓ o)
    · exact Or.inl (hs ℓ o)
  -- the heap, at a step that changes none of it
  have same : μ₁ = μ → ∀ x v, Grow S μ μ₁ x → μ₁ x = some v → ∀ k, v.1.Occ k →
      Grow S μ μ₁ k := fun e x v hx hv k o => by
    subst e
    rcases hx with hx | ⟨h0, -⟩
    · exact Or.inl (hheap x v hx hv k o)
    · rw [h0] at hv; cases hv
  cases hh with
  | beta b v =>
      exact ⟨term (sub (fun ℓ o => ha ℓ (Or.inl o)) (fun ℓ o => ha ℓ (Or.inr o))), same rfl⟩
  | seq => exact ⟨term fun ℓ o => Or.inl (ha ℓ (Or.inr o)), same rfl⟩
  | letpair v₁ v₂ e =>
      refine ⟨term fun ℓ o => ?_, same rfl⟩
      rcases Expr.occ_subst _ _ _ o with o | o
      · rcases Expr.occ_subst _ _ _ o with o | o
        · exact Or.inl (ha ℓ (Or.inr o))
        · exact Or.inl (ha ℓ (Or.inl (Or.inr ((Val.occ_shift 1 0 v₂).mp o))))
      · exact Or.inl (ha ℓ (Or.inl (Or.inl o)))
  | case₁ v e₁ e₂ =>
      exact ⟨term (sub (fun ℓ o => ha ℓ (Or.inr (Or.inl o))) (fun ℓ o => ha ℓ (Or.inl o))),
        same rfl⟩
  | case₂ v e₁ e₂ =>
      exact ⟨term (sub (fun ℓ o => ha ℓ (Or.inr (Or.inr o))) (fun ℓ o => ha ℓ (Or.inl o))),
        same rfl⟩
  | load ℓ v h =>
      exact ⟨term fun k o => Or.inl (hheap ℓ v (ha ℓ (Or.inr rfl)) h k o), same rfl⟩
  | free ℓ v h =>
      refine ⟨term fun k o => Or.inl (hheap ℓ v (ha ℓ (Or.inr rfl)) h k o),
        fun x w hx hw k o => ?_⟩
      by_cases e : x = ℓ
      · subst e; simp at hw
      · rw [BoLo.Heap.del_other e] at hw
        rcases hx with hx | ⟨h0, -⟩
        · exact Or.inl (hheap x w hx hw k o)
        · rw [h0] at hw; cases hw
  | store ℓ v w h =>
      refine ⟨term fun k o => by simp [Expr.Occ, Expr.val, Val.unit] at o,
        fun x u hx hu k o => ?_⟩
      by_cases e : x = ℓ
      · subst e; rw [BoLo.Heap.upd_same] at hu; cases hu; exact Or.inl (ha k (Or.inr o))
      · rw [BoLo.Heap.upd_other e] at hu
        rcases hx with hx | ⟨h0, -⟩
        · exact Or.inl (hheap x u hx hu k o)
        · rw [h0] at hu; cases hu
  | alloc v ℓ h =>
      refine ⟨term fun k o => ?_, fun x u hx hu k o => ?_⟩
      · simp only [Expr.Occ, Expr.val, Val.loc] at o
        subst o
        exact Or.inr ⟨h, by simp⟩
      · by_cases e : x = ℓ
        · subst e; rw [BoLo.Heap.upd_same] at hu; cases hu; exact Or.inl (ha k (Or.inr o))
        · rw [BoLo.Heap.upd_other e] at hu
          rcases hx with hx | ⟨h0, -⟩
          · exact Or.inl (hheap x u hx hu k o)
          · rw [h0] at hu; cases hu

/-- **Every run reads only what its term reaches.**  From a set closed for `(μ, e)`, every run of
`e` touches only locations of the set or locations it allocated itself. -/
theorem steps_runIn {S : Loc → Prop} {μ μ' : Heap} {e e' : Expr} (hS : Closed S μ e)
    (h : Steps μ e μ' e') : RunIn S μ e μ' e' := by
  induction h generalizing S with
  | refl => exact .refl _ _ _
  | more hs _ ih =>
      obtain ⟨K, a, a', rfl, rfl, hh⟩ := hs
      obtain ⟨ht, hS'⟩ := closed_head hS hh
      exact .more K a a' rfl rfl hh ht (ih hS')

theorem Reach.mono {μ : Heap} {A B : Loc → Prop} (h : ∀ ℓ, A ℓ → B ℓ) {ℓ : Loc}
    (hr : Reach μ A ℓ) : Reach μ B ℓ := by
  induction hr with
  | base ha => exact .base (h _ ha)
  | step _ hv hk ih => exact .step ih hv hk

/-- The locations reachable from `γ` form a closed set for `γ(e)`, when `e` names none. -/
theorem closed_argLocs {γ : List Val} {e : Expr} (he : LocFree e) (μ : Heap) :
    Closed (Reach μ (ArgLocs γ)) μ (Fig16.LogRel.substAll γ e) :=
  ⟨fun _ o => .base (occ_substAll_of_locFree he o), fun _ _ hx hv _ hk => .step hx hv hk⟩

/-- **A well-typed program reads only what its arguments reach.**  Every run of `γ(e)`, for
`e` typed by `DerivesWf`, from any heap `μ`, touches only locations reachable from the values
`γ` through `μ`, or locations it allocated itself. -/
theorem derivesWf_runIn {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty}
    (hD : DerivesWf Δ Γ e T) (γ : List Val) {μ μ' : Heap} {e' : Expr}
    (h : Steps μ (Fig16.LogRel.substAll γ e) μ' e') :
    RunIn (Reach μ (ArgLocs γ)) μ (Fig16.LogRel.substAll γ e) μ' e' :=
  steps_runIn (closed_argLocs (derivesWf_locFree hD) μ) h

end BoCa.Purity

end
