import Purity.Rename

/-!
# Purity — unique decomposition, and determinism away from `alloc`

A step of `K[e]`, with `e` not a value, is a step of `e` under `K` (`plug_decomp`,
`step1_plug_inv`).  The head reduction is a function except at `alloc↦`, which may pick any
location the heap misses (`head_det`); so a step whose redex is not an allocation is the only
step (`step1_det`), and a run that never allocates is the only run to a value from its start
(`stepsNA_det`).

The library's `wp` development only builds runs, so it does not state these facts; a statement
about *every* run of a term needs them.

`[about ours]`: an extension, not a transcription.
-/

noncomputable section

namespace BoCa.Purity
open BoCa BoCa.BoLo

/-- A value, at each of the forms a redex holds one in. -/
syntax "isv" : tactic
macro_rules
  | `(tactic| isv) => `(tactic| first
      | exact Subtype.property _ | exact IsVal.lam | exact IsVal.prim | exact IsVal.loc
      | exact IsVal.unit | exact IsVal.pair (Subtype.property _) (Subtype.property _)
      | exact IsVal.inj₁ (Subtype.property _) | exact IsVal.inj₂ (Subtype.property _)
      | exact IsVal.storeV IsVal.loc)

/-- A head redex is `K[e]` with `e` not a value only at `K = []`. -/
theorem head_plug {μ μ' : Heap} {E a' : Expr} (hh : Head μ E μ' a') :
    ∀ (K : Kont) {e : Expr}, ¬ IsVal e → E = K.plug e → K = .hole := by
  intro K e hnv hE
  cases K with
  | hole => rfl
  | pairL K e₂ => subst hE; cases hh
  | pairR v K => subst hE; cases hh
  | inj₁ K => subst hE; cases hh
  | inj₂ K => subst hE; cases hh
  | letpair K e₂ =>
      exfalso; apply hnv; apply K.isVal_of_plug
      cases hh <;> simp only [Kont.plug] at hE <;>
        first | (simp at hE; done) | (injection hE with h1 h2; rw [← h1]; isv)
  | case K e₁ e₂ =>
      exfalso; apply hnv; apply K.isVal_of_plug
      cases hh <;> simp only [Kont.plug] at hE <;>
        first | (simp at hE; done) | (injection hE with h1 h2 h3; rw [← h1]; isv)
  | seq K e₂ =>
      exfalso; apply hnv; apply K.isVal_of_plug
      cases hh <;> simp only [Kont.plug] at hE <;>
        first | (simp at hE; done) | (injection hE with h1 h2; rw [← h1]; isv)
  | appR f K =>
      exfalso; apply hnv; apply K.isVal_of_plug
      cases hh <;> simp only [Kont.plug] at hE <;>
        first | (simp at hE; done) | (injection hE with h1 h2; rw [← h2]; isv)
  | appL K v =>
      exfalso; apply hnv; apply K.isVal_of_plug
      cases hh <;> simp only [Kont.plug] at hE <;>
        first | (simp at hE; done) | (injection hE with h1 h2; rw [← h1]; isv)

/-- Unique decomposition: `K[e] = K′[a]` with `a` a redex and `e` not a value puts `a` inside
`e`. -/
theorem plug_decomp {μ μ' : Heap} {a a' : Expr} (hh : Head μ a μ' a') (K : Kont) :
    ∀ (K' : Kont) {e : Expr}, ¬ IsVal e → K.plug e = K'.plug a →
      ∃ K'', e = K''.plug a ∧ K' = K.comp K'' := by
  have hna : ¬ IsVal a := hh.not_isVal
  induction K with
  | hole => intro K' e _ h; exact ⟨K', h, rfl⟩
  | pairL K e₂ ih =>
      intro K' e hnv h
      cases K' with
      | hole => exact absurd (head_plug hh (.pairL K e₂) hnv h.symm) (by simp)
      | pairL K' e₂' =>
          simp only [Kont.plug, Expr.pair.injEq] at h
          obtain ⟨K'', h₁, h₂⟩ := ih K' hnv h.1
          exact ⟨K'', h₁, by rw [h₂, h.2]; rfl⟩
      | pairR v K' =>
          simp only [Kont.plug, Expr.pair.injEq] at h
          exact absurd (K.isVal_of_plug (h.1 ▸ v.2)) hnv
      | _ => simp [Kont.plug] at h
  | pairR v K ih =>
      intro K' e hnv h
      cases K' with
      | hole => exact absurd (head_plug hh (.pairR v K) hnv h.symm) (by simp)
      | pairL K' e₂' =>
          simp only [Kont.plug, Expr.pair.injEq] at h
          exact absurd (K'.isVal_of_plug (h.1 ▸ v.2)) hna
      | pairR v' K' =>
          simp only [Kont.plug, Expr.pair.injEq] at h
          obtain ⟨K'', h₁, h₂⟩ := ih K' hnv h.2
          have hv : v = v' := Subtype.ext h.1
          exact ⟨K'', h₁, by rw [h₂, hv]; rfl⟩
      | _ => simp [Kont.plug] at h
  | letpair K e₂ ih =>
      intro K' e hnv h
      cases K' with
      | hole => exact absurd (head_plug hh (.letpair K e₂) hnv h.symm) (by simp)
      | letpair K' e₂' =>
          simp only [Kont.plug, Expr.letpair.injEq] at h
          obtain ⟨K'', h₁, h₂⟩ := ih K' hnv h.1
          exact ⟨K'', h₁, by rw [h₂, h.2]; rfl⟩
      | _ => simp [Kont.plug] at h
  | case K e₁ e₂ ih =>
      intro K' e hnv h
      cases K' with
      | hole => exact absurd (head_plug hh (.case K e₁ e₂) hnv h.symm) (by simp)
      | case K' e₁' e₂' =>
          simp only [Kont.plug, Expr.case.injEq] at h
          obtain ⟨K'', h₁, h₂⟩ := ih K' hnv h.1
          exact ⟨K'', h₁, by rw [h₂, h.2.1, h.2.2]; rfl⟩
      | _ => simp [Kont.plug] at h
  | seq K e₂ ih =>
      intro K' e hnv h
      cases K' with
      | hole => exact absurd (head_plug hh (.seq K e₂) hnv h.symm) (by simp)
      | seq K' e₂' =>
          simp only [Kont.plug, Expr.seq.injEq] at h
          obtain ⟨K'', h₁, h₂⟩ := ih K' hnv h.1
          exact ⟨K'', h₁, by rw [h₂, h.2]; rfl⟩
      | _ => simp [Kont.plug] at h
  | inj₁ K ih =>
      intro K' e hnv h
      cases K' with
      | hole => exact absurd (head_plug hh (.inj₁ K) hnv h.symm) (by simp)
      | inj₁ K' =>
          simp only [Kont.plug, Expr.inj₁.injEq] at h
          obtain ⟨K'', h₁, h₂⟩ := ih K' hnv h
          exact ⟨K'', h₁, by rw [h₂]; rfl⟩
      | _ => simp [Kont.plug] at h
  | inj₂ K ih =>
      intro K' e hnv h
      cases K' with
      | hole => exact absurd (head_plug hh (.inj₂ K) hnv h.symm) (by simp)
      | inj₂ K' =>
          simp only [Kont.plug, Expr.inj₂.injEq] at h
          obtain ⟨K'', h₁, h₂⟩ := ih K' hnv h
          exact ⟨K'', h₁, by rw [h₂]; rfl⟩
      | _ => simp [Kont.plug] at h
  | appR f K ih =>
      intro K' e hnv h
      cases K' with
      | hole => exact absurd (head_plug hh (.appR f K) hnv h.symm) (by simp)
      | appR f' K' =>
          simp only [Kont.plug, Expr.app.injEq] at h
          obtain ⟨K'', h₁, h₂⟩ := ih K' hnv h.2
          exact ⟨K'', h₁, by rw [h₂, h.1]; rfl⟩
      | appL K' v =>
          simp only [Kont.plug, Expr.app.injEq] at h
          exact absurd (K.isVal_of_plug (h.2 ▸ v.2)) hnv
      | _ => simp [Kont.plug] at h
  | appL K v ih =>
      intro K' e hnv h
      cases K' with
      | hole => exact absurd (head_plug hh (.appL K v) hnv h.symm) (by simp)
      | appR f' K' =>
          simp only [Kont.plug, Expr.app.injEq] at h
          exact absurd (K'.isVal_of_plug (h.2 ▸ v.2)) hna
      | appL K' v' =>
          simp only [Kont.plug, Expr.app.injEq] at h
          obtain ⟨K'', h₁, h₂⟩ := ih K' hnv h.1
          have hv : v = v' := Subtype.ext h.2
          exact ⟨K'', h₁, by rw [h₂, hv]; rfl⟩
      | _ => simp [Kont.plug] at h

/-- A step of `K[e]`, `e` not a value, is a step of `e` under `K`. -/
theorem step1_plug_inv {μ μ₁ : Heap} {e e₁ : Expr} (K : Kont) (hnv : ¬ IsVal e)
    (h : Step1 μ (K.plug e) μ₁ e₁) : ∃ e', e₁ = K.plug e' ∧ Step1 μ e μ₁ e' := by
  obtain ⟨K', a, a', hE, rfl, hh⟩ := h
  obtain ⟨K'', rfl, rfl⟩ := plug_decomp hh K K' hnv hE
  exact ⟨K''.plug a', Kont.plug_comp K K'' a', ⟨K'', a, a', rfl, rfl, hh⟩⟩

/-- A run from a value is empty. -/
theorem steps_from_val {μ μ' : Heap} {v w : Val} (h : Steps μ v.1 μ' w.1) : μ' = μ ∧ w = v := by
  obtain ⟨h₁, h₂⟩ := steps_val_inv h
  exact ⟨h₁, Subtype.ext h₂⟩

theorem not_step1_of_isVal {μ μ' : Heap} {e e' : Expr} (h : IsVal e) : ¬ Step1 μ e μ' e' :=
  BoLo.no_step_val (w := ⟨e, h⟩)

/-! ### The head step is a function away from `alloc` -/

/-- The redex `alloc v`. -/
def allocRedex (v : Val) : Expr := .app (.val (.prim .alloc)) (.val v)

/-- Two head steps from one configuration agree, unless the redex is an allocation. -/
theorem head_det_gen {μ μ' μ₁ μ₂ : Heap} {a b a₁ a₂ : Expr} (h₁ : Head μ a μ₁ a₁)
    (h₂ : Head μ' b μ₂ a₂) (hab : a = b) (hμ : μ = μ')
    (hna : ∀ v : Val, a ≠ allocRedex v) : μ₂ = μ₁ ∧ a₂ = a₁ := by
  subst hμ
  cases h₁ with
  | alloc v _ _ => exact absurd rfl (hna v)
  | _ => cases h₂ <;> simp_all [allocRedex, Expr.val, Subtype.val_inj]

theorem head_det {μ μ₁ μ₂ : Heap} {a a₁ a₂ : Expr} (h₁ : Head μ a μ₁ a₁)
    (h₂ : Head μ a μ₂ a₂) (hna : ∀ v : Val, a ≠ allocRedex v) : μ₂ = μ₁ ∧ a₂ = a₁ :=
  head_det_gen h₁ h₂ rfl rfl hna

/-- The head steps of an allocation redex. -/
theorem head_alloc_inv {μ μ' : Heap} {a a' : Expr} (h : Head μ a μ' a') {v : Val}
    (ha : a = allocRedex v) : ∃ ℓ, μ ℓ = none ∧ μ' = μ.upd ℓ v ∧ a' = .val (.loc ℓ) := by
  cases h with
  | alloc w ℓ hℓ =>
      simp only [allocRedex, Expr.app.injEq] at ha
      obtain rfl : w = v := Subtype.ext ha.2
      exact ⟨ℓ, hℓ, rfl, rfl⟩
  | _ => simp_all [allocRedex, Expr.val, Val.prim, Val.lam]

theorem not_allocRedex_rename (σ : Loc → Loc) {a : Expr} (hna : ∀ v : Val, a ≠ allocRedex v) :
    ∀ v : Val, a.rename σ ≠ allocRedex v := by
  intro v h
  cases a with
  | app f x =>
      simp only [Expr.rename, allocRedex, Expr.app.injEq] at h
      obtain ⟨h₁, h₂⟩ := h
      cases f with
      | prim p =>
          simp only [Expr.rename, Expr.val, Val.prim, Expr.prim.injEq] at h₁
          have hx : IsVal x := isVal_of_rename σ (h₂ ▸ v.2)
          exact hna ⟨x, hx⟩ (by rw [h₁]; rfl)
      | _ => simp [Expr.rename, Val.prim] at h₁
  | _ => simp [Expr.rename, allocRedex] at h

/-- A step whose redex is not an allocation. -/
def Step1NA (μ : Heap) (e : Expr) (μ' : Heap) (e' : Expr) : Prop :=
  ∃ (K : Kont) (a a' : Expr), e = K.plug a ∧ e' = K.plug a' ∧ Head μ a μ' a' ∧
    ∀ v : Val, a ≠ allocRedex v

/-- A run that takes no `alloc↦` step. -/
inductive StepsNA : Heap → Expr → Heap → Expr → Prop where
  | refl (μ : Heap) (e : Expr) : StepsNA μ e μ e
  | more {μ μ₁ μ' : Heap} {e e₁ e' : Expr}
      (h : Step1NA μ e μ₁ e₁) (t : StepsNA μ₁ e₁ μ' e') : StepsNA μ e μ' e'

theorem Step1NA.toStep1 {μ μ' : Heap} {e e' : Expr} (h : Step1NA μ e μ' e') :
    Step1 μ e μ' e' := by
  obtain ⟨K, a, a', h₁, h₂, h₃, -⟩ := h
  exact ⟨K, a, a', h₁, h₂, h₃⟩

theorem StepsNA.toSteps {μ μ' : Heap} {e e' : Expr} (h : StepsNA μ e μ' e') :
    Steps μ e μ' e' := by
  induction h with
  | refl => exact .refl _ _
  | more h _ ih => exact .more h.toStep1 ih

/-- A step that is not an allocation is the only step. -/
theorem step1_det {μ μ₁ μ₂ : Heap} {e e₁ e₂ : Expr} (h₁ : Step1NA μ e μ₁ e₁)
    (h₂ : Step1 μ e μ₂ e₂) : μ₂ = μ₁ ∧ e₂ = e₁ := by
  obtain ⟨K, a, a', rfl, rfl, hh₁, hna⟩ := h₁
  obtain ⟨K', b, b', hE, rfl, hh₂⟩ := h₂
  obtain ⟨K'', rfl, rfl⟩ := plug_decomp hh₂ K K' hh₁.not_isVal hE
  obtain rfl : K'' = .hole := head_plug hh₁ K'' hh₂.not_isVal rfl
  obtain ⟨rfl, rfl⟩ := head_det hh₁ hh₂ hna
  exact ⟨rfl, by rw [Kont.plug_comp]; rfl⟩

/-- **A run that does not allocate is the only run to a value.**  Every run to a value from
the same configuration ends at the same heap and value. -/
theorem stepsNA_det {μ μ₁ : Heap} {e e₁ : Expr} (h₁ : StepsNA μ e μ₁ e₁) :
    ∀ {v₁ : Val} {μ₂ : Heap} {v₂ : Val}, e₁ = v₁.1 → Steps μ e μ₂ v₂.1 → μ₂ = μ₁ ∧ v₂ = v₁ := by
  induction h₁ with
  | refl μ e =>
      intro v₁ μ₂ v₂ he h₂
      subst he
      exact steps_from_val h₂
  | more hs _ ih =>
      intro v₁ μ₂ v₂ he h₂
      cases h₂ with
      | refl =>
          exact absurd hs.toStep1 (BoCa.BoLo.no_step_val (w := v₂))
      | more h t =>
          obtain ⟨rfl, rfl⟩ := step1_det hs h
          exact ih he t

end BoCa.Purity

end
