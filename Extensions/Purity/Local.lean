import Purity.Sim

/-!
# Purity — a run reads only what its term can reach

The machine forges no location: a location enters a term only from the term itself, from a
cell the term already names, or from `alloc↦`.  So a run touches only locations reachable
from its initial term through the initial heap, together with the locations it allocates.

`Reach μ A` is the set of locations reachable from `A` through `μ`: `A`, and every location a
value stored at a reachable location mentions.  A set `S` is *closed* for `(μ, e)` when it
contains the locations of `e` and every location mentioned by a cell of `μ` at a location of
`S`; `Reach μ (Occ e)` is the least such set.

**Locality** (`fresh_run_local`).  Let a fresh run from `(μ₁, e)` reach the value `v₁`, and let
any run from `(μ₂, e)` reach `v₂`.  If `μ₂` agrees with `μ₁` on every allocated location of
`Reach μ₁ (Occ e)`, then `v₂` is `v₁` with its locations renamed.  The two heaps may differ
arbitrarily elsewhere.

The proof is `Sim.lean`'s lockstep simulation, relativised to a set `S` that is closed for the
fresh run's configuration (`LocRel`).  The fresh run `B` and the arbitrary run `A` are related
along `g : Loc → Loc`: `A`'s term is `B`'s renamed; every allocated location of `S` is sent by
`g`, injectively, to an allocated location of `A`'s heap holding the renamed value.  A step of
`B` touches only locations its term mentions, which lie in `S`; an allocation of `B` adds its
location to `S`.

This is a fact about the machine and every term; nothing here is typed.  What typing adds is
that a well-typed term mentions no location of its own (`Syntax.lean`), so the reachable set
of `γ(e)` is the one reachable from the values `γ`.

`[about ours]`: an extension, not a transcription.
-/

noncomputable section

namespace BoCa

/-! ### The locations of a shifted and a substituted term -/

theorem Expr.occ_shift {ℓ : Loc} : ∀ (d c : Nat) (e : Expr), (e.shift d c).Occ ℓ ↔ e.Occ ℓ
  | d, c, .var i => by
      simp only [Expr.shift]; split <;> simp [Expr.Occ]
  | _, _, .unit | _, _, .prim _ | _, _, .loc _ => Iff.rfl
  | d, c, .pair a b | d, c, .seq a b | d, c, .app a b => by
      simp only [Expr.shift, Expr.Occ, Expr.occ_shift d c a, Expr.occ_shift d c b]
  | d, c, .letpair a b => by
      simp only [Expr.shift, Expr.Occ, Expr.occ_shift d c a, Expr.occ_shift d (c + 2) b]
  | d, c, .inj₁ a | d, c, .inj₂ a => by simp only [Expr.shift, Expr.Occ, Expr.occ_shift d c a]
  | d, c, .lam a => by simp only [Expr.shift, Expr.Occ, Expr.occ_shift d (c + 1) a]
  | d, c, .case a b e => by
      simp only [Expr.shift, Expr.Occ, Expr.occ_shift d c a, Expr.occ_shift d (c + 1) b,
        Expr.occ_shift d (c + 1) e]

theorem Val.occ_shift {ℓ : Loc} (d c : Nat) (v : Val) : (v.shift d c).1.Occ ℓ ↔ v.1.Occ ℓ :=
  Expr.occ_shift d c v.1

/-- A location of `e[s/j]` is a location of `e` or of `s`. -/
theorem Expr.occ_subst {ℓ : Loc} :
    ∀ (j : Nat) (s : Val) (e : Expr), (e.subst j s).Occ ℓ → e.Occ ℓ ∨ s.1.Occ ℓ
  | j, s, .var i, h => by
      simp only [Expr.subst] at h
      split at h
      · exact Or.inr h
      · split at h <;> simp [Expr.Occ] at h
  | _, _, .unit, h | _, _, .prim _, h => h.elim
  | _, _, .loc _, h => Or.inl h
  | j, s, .pair a b, h | j, s, .seq a b, h | j, s, .app a b, h => by
      simp only [Expr.subst, Expr.Occ] at h
      rcases h with h | h
      · rcases Expr.occ_subst j s a h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Expr.occ_subst j s b h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | j, s, .letpair a b, h => by
      simp only [Expr.subst, Expr.Occ] at h
      rcases h with h | h
      · rcases Expr.occ_subst j s a h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Expr.occ_subst (j + 2) (s.shift 2 0) b h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr ((Val.occ_shift 2 0 s).mp h')
  | j, s, .inj₁ a, h | j, s, .inj₂ a, h => by
      simp only [Expr.subst, Expr.Occ] at h
      exact Expr.occ_subst j s a h
  | j, s, .lam a, h => by
      simp only [Expr.subst, Expr.Occ] at h
      rcases Expr.occ_subst (j + 1) (s.shift 1 0) a h with h' | h'
      · exact Or.inl h'
      · exact Or.inr ((Val.occ_shift 1 0 s).mp h')
  | j, s, .case a b c, h => by
      simp only [Expr.subst, Expr.Occ] at h
      rcases h with h | h | h
      · rcases Expr.occ_subst j s a h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Expr.occ_subst (j + 1) (s.shift 1 0) b h with h' | h'
        · exact Or.inl (Or.inr (Or.inl h'))
        · exact Or.inr ((Val.occ_shift 1 0 s).mp h')
      · rcases Expr.occ_subst (j + 1) (s.shift 1 0) c h with h' | h'
        · exact Or.inl (Or.inr (Or.inr h'))
        · exact Or.inr ((Val.occ_shift 1 0 s).mp h')

end BoCa

namespace BoCa.Purity
open BoCa
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-- A location of `K[a]` is one of `K`'s (a location of `K[()]`) or one of `a`'s. -/
theorem Kont.occ_plug_iff {ℓ : Loc} {a : Expr} (K : Kont) :
    (K.plug a).Occ ℓ ↔ (K.plug .unit).Occ ℓ ∨ a.Occ ℓ := by
  induction K with
  | hole => simp [Kont.plug, Expr.Occ]
  | pairL K _ ih | letpair K _ ih | seq K _ ih | appL K _ ih | case K _ _ ih =>
      simp only [Kont.plug, Expr.Occ, ih]; tauto
  | pairR _ K ih | appR _ K ih =>
      simp only [Kont.plug, Expr.Occ, ih]; tauto
  | inj₁ K ih | inj₂ K ih => simp only [Kont.plug, Expr.Occ, ih]

/-! ### Reachability -/

/-- `ℓ` is reachable from `A` through `μ`: it is in `A`, or a value stored at a reachable
location mentions it. -/
inductive Reach (μ : Heap) (A : Loc → Prop) : Loc → Prop where
  | base {ℓ : Loc} : A ℓ → Reach μ A ℓ
  | step {ℓ k : Loc} {v : Val} : Reach μ A ℓ → μ ℓ = some v → v.1.Occ k → Reach μ A k

/-- `S` contains the locations of `e`, and every location a cell of `μ` in `S` mentions. -/
def Closed (S : Loc → Prop) (μ : Heap) (e : Expr) : Prop :=
  (∀ ℓ, e.Occ ℓ → S ℓ) ∧ ∀ x v, S x → μ x = some v → ∀ k, v.1.Occ k → S k

theorem closed_reach (μ : Heap) (e : Expr) : Closed (Reach μ (fun ℓ => e.Occ ℓ)) μ e :=
  ⟨fun _ h => .base h, fun _ _ hx hv _ hk => .step hx hv hk⟩

/-- `Reach μ (Occ e)` is the least closed set. -/
theorem reach_sub {S : Loc → Prop} {μ : Heap} {e : Expr} (hS : Closed S μ e) :
    ∀ {ℓ}, Reach μ (fun ℓ => e.Occ ℓ) ℓ → S ℓ := by
  intro ℓ h
  induction h with
  | base h => exact hS.1 _ h
  | step _ hv hk ih => exact hS.2 _ _ ih hv _ hk

/-! ### The relation between the two runs -/

/-- `S` is closed in `μB`; `g` sends every allocated location of `S` to an allocated location
of `μA` holding the renamed value, injectively. -/
def LocRel (g : Loc → Loc) (S : Loc → Prop) (μB μA : Heap) : Prop :=
  (∀ x v, S x → μB x = some v → ∀ k, v.1.Occ k → S k) ∧
  (∀ x, S x → μB x ≠ none → μA (g x) = (μB x).map (Val.rename g)) ∧
  (∀ x y, S x → S y → μB x ≠ none → μB y ≠ none → g x = g y → x = y)

/-- **A head step that is not an allocation, followed.**  If `B` takes it on a redex whose
locations lie in `S`, `A` takes it at the image under `g`; the result's locations lie in `S`,
and the heaps stay related. -/
theorem head_sim_loc {g : Loc → Loc} {S : Loc → Prop} {μB μB' μA : Heap} {b b' : Expr}
    (hB : Head μB b μB' b') (hR : LocRel g S μB μA) (hb : ∀ ℓ, b.Occ ℓ → S ℓ)
    (hna : ∀ v : Val, b ≠ allocRedex v) :
    ∃ μA', Head μA (b.rename g) μA' (b'.rename g) ∧ LocRel g S μB' μA' ∧
      ∀ ℓ, b'.Occ ℓ → S ℓ := by
  obtain ⟨h₁, h₂, h₃⟩ := hR
  have sub : ∀ {e : Expr} {s : Val} {j : Nat}, (∀ ℓ, e.Occ ℓ → S ℓ) → (∀ ℓ, s.1.Occ ℓ → S ℓ) →
      ∀ ℓ, (e.subst j s).Occ ℓ → S ℓ := fun he hs ℓ o => by
    rcases Expr.occ_subst _ _ _ o with o | o
    · exact he ℓ o
    · exact hs ℓ o
  cases hB with
  | alloc v _ _ => exact absurd rfl (hna v)
  | beta b v =>
      rw [Expr.rename_subst]
      exact ⟨μA, .beta _ (b.rename g) (v.rename g), ⟨h₁, h₂, h₃⟩,
        sub (fun ℓ o => hb ℓ (Or.inl o)) (fun ℓ o => hb ℓ (Or.inr o))⟩
  | seq => exact ⟨μA, .seq _ _, ⟨h₁, h₂, h₃⟩, fun ℓ o => hb ℓ (Or.inr o)⟩
  | letpair v₁ v₂ e =>
      rw [Expr.rename_subst, Expr.rename_subst, Val.rename_shift]
      refine ⟨μA, .letpair _ (v₁.rename g) (v₂.rename g) (e.rename g), ⟨h₁, h₂, h₃⟩, ?_⟩
      refine sub (sub (fun ℓ o => hb ℓ (Or.inr o)) (fun ℓ o => ?_)) (fun ℓ o => hb ℓ (Or.inl (Or.inl o)))
      exact hb ℓ (Or.inl (Or.inr ((Val.occ_shift 1 0 v₂).mp o)))
  | case₁ v e₁ e₂ =>
      rw [Expr.rename_subst]
      exact ⟨μA, .case₁ _ (v.rename g) (e₁.rename g) (e₂.rename g), ⟨h₁, h₂, h₃⟩,
        sub (fun ℓ o => hb ℓ (Or.inr (Or.inl o))) (fun ℓ o => hb ℓ (Or.inl o))⟩
  | case₂ v e₁ e₂ =>
      rw [Expr.rename_subst]
      exact ⟨μA, .case₂ _ (v.rename g) (e₁.rename g) (e₂.rename g), ⟨h₁, h₂, h₃⟩,
        sub (fun ℓ o => hb ℓ (Or.inr (Or.inr o))) (fun ℓ o => hb ℓ (Or.inl o))⟩
  | load ℓ v h =>
      have hS : S ℓ := hb ℓ (Or.inr rfl)
      have hA : μA (g ℓ) = some (v.rename g) := by rw [h₂ ℓ hS (by simp [h]), h]; rfl
      exact ⟨μA, .load _ (g ℓ) (v.rename g) hA, ⟨h₁, h₂, h₃⟩, fun k o => h₁ ℓ v hS h k o⟩
  | store ℓ v w h =>
      have hS : S ℓ := hb ℓ (Or.inl (Or.inr rfl))
      have hℓ : μB ℓ ≠ none := by simp [h]
      have hA : μA (g ℓ) = some (w.rename g) := by rw [h₂ ℓ hS hℓ, h]; rfl
      have dom : ∀ x, (μB.upd ℓ v) x ≠ none ↔ μB x ≠ none := fun x => by
        by_cases e : x = ℓ
        · subst e; simp [h]
        · rw [Heap.upd_other e]
      refine ⟨μA.upd (g ℓ) (v.rename g), .store _ (g ℓ) (v.rename g) (w.rename g) hA,
        ⟨fun x u hx hu k o => ?_, fun x hx hx' => ?_,
          fun x y hx hy hx' hy' => h₃ x y hx hy ((dom x).mp hx') ((dom y).mp hy')⟩,
        fun _ o => by simp [Expr.Occ] at o⟩
      · by_cases e : x = ℓ
        · subst e; rw [Heap.upd_same] at hu; cases hu; exact hb k (Or.inr o)
        · rw [Heap.upd_other e] at hu; exact h₁ x u hx hu k o
      · by_cases e : x = ℓ
        · subst e; simp
        · have hx'' := (dom x).mp hx'
          rw [Heap.upd_other e, Heap.upd_other fun e' => e (h₃ x ℓ hx hS hx'' hℓ e')]
          exact h₂ x hx hx''
  | free ℓ v h =>
      have hS : S ℓ := hb ℓ (Or.inr rfl)
      have hℓ : μB ℓ ≠ none := by simp [h]
      have hA : μA (g ℓ) = some (v.rename g) := by rw [h₂ ℓ hS hℓ, h]; rfl
      have dom : ∀ x, (μB.del ℓ) x ≠ none ↔ μB x ≠ none ∧ x ≠ ℓ := fun x => by
        by_cases e : x = ℓ
        · subst e; simp
        · rw [Heap.del_other e]; exact ⟨fun h => ⟨h, e⟩, fun h => h.1⟩
      refine ⟨μA.del (g ℓ), .free _ (g ℓ) (v.rename g) hA,
        ⟨fun x u hx hu k o => ?_, fun x hx hx' => ?_,
          fun x y hx hy hx' hy' => h₃ x y hx hy ((dom x).mp hx').1 ((dom y).mp hy').1⟩,
        fun k o => h₁ ℓ v hS h k o⟩
      · by_cases e : x = ℓ
        · subst e; simp at hu
        · rw [Heap.del_other e] at hu; exact h₁ x u hx hu k o
      · obtain ⟨hx'', e⟩ := (dom x).mp hx'
        rw [Heap.del_other e, Heap.del_other fun e' => e (h₃ x ℓ hx hS hx'' hℓ e')]
        exact h₂ x hx hx''

/-- **One step of a fresh run, followed.**  From configurations related along `g` and `S`,
where `S` holds the fresh run's term's locations, `A`'s step is `B`'s at the image, and the
resulting configurations are related along an update of `g` and an extension of `S`. -/
theorem step_sim_loc {g : Loc → Loc} {S : Loc → Prop} {μB μB' μA μA' : Heap}
    {eB eB' eA' : Expr} (hB : Step1F μB eB μB' eB') (hR : LocRel g S μB μA)
    (hS : ∀ ℓ, eB.Occ ℓ → S ℓ) (hA : Step1 μA (eB.rename g) μA' eA') :
    ∃ g' S', eA' = eB'.rename g' ∧ LocRel g' S' μB' μA' ∧ ∀ ℓ, eB'.Occ ℓ → S' ℓ := by
  obtain ⟨⟨K, b, b', rfl, rfl, hhB⟩, hfB⟩ := hB
  obtain ⟨K', a, a', hE, rfl, hhA⟩ := hA
  rw [BoLo.Kont.rename_plug] at hE
  have hnv : ¬ IsVal (b.rename g) := fun h => hhB.not_isVal (isVal_of_rename g h)
  obtain ⟨K'', hb, rfl⟩ := plug_decomp hhA (K.rename g) K' hnv hE
  rw [BoLo.Kont.plug_comp]
  have hK : ∀ ℓ, (K.plug .unit).Occ ℓ → S ℓ :=
    fun ℓ o => hS ℓ ((Kont.occ_plug_iff K).mpr (Or.inl o))
  have hbS : ∀ ℓ, b.Occ ℓ → S ℓ := fun ℓ o => hS ℓ ((Kont.occ_plug_iff K).mpr (Or.inr o))
  by_cases hal : ∃ v, b = allocRedex v
  · obtain ⟨v, rfl⟩ := hal
    have hh₀ : Head (fun _ => none) ((allocRedex v).rename g)
        (BoLo.Heap.upd (fun _ => none) 0 (v.rename g)) (.val (.loc 0)) := by
      simp only [allocRedex, Expr.rename]; exact .alloc _ (v.rename g) 0 rfl
    obtain rfl : K'' = .hole := head_plug hh₀ K'' hhA.not_isVal hb
    simp only [Kont.plug] at hb
    subst hb
    obtain ⟨ℓB, hℓB, rfl, rfl⟩ := head_alloc_inv hhB rfl
    obtain ⟨ℓA, hℓA, rfl, rfl⟩ := head_alloc_inv hhA (v := v.rename g) rfl
    have nB := hfB ℓB (by simp) hℓB
    have oK : ∀ k, (K.plug (allocRedex v)).Occ k → k ≠ ℓB :=
      fun k o e => nB (.inr (.inl (e ▸ o)))
    have hvS : ∀ k, v.1.Occ k → S k := fun k o => hbS k (Or.inr o)
    have hv : v.rename (Function.update g ℓB ℓA) = v.rename g :=
      Subtype.ext (rename_update_eq fun o =>
        oK ℓB (Kont.occ_plug K (show (Expr.app _ _).Occ ℓB from Or.inr o)) rfl)
    obtain ⟨h₁, h₂, h₃⟩ := hR
    have ne : ∀ x, μB x ≠ none → x ≠ ℓB := fun x hx e => hx (e ▸ hℓB)
    have neA : ∀ x, S x → μB x ≠ none → g x ≠ ℓA := fun x hS' hx e => by
      have := h₂ x hS' hx; rw [e, hℓA] at this
      cases h : μB x with
      | none => exact hx h
      | some w => rw [h] at this; cases this
    refine ⟨Function.update g ℓB ℓA, fun x => S x ∨ x = ℓB, ?_,
      ⟨fun x u hx hu k o => ?_, fun x hx hx' => ?_, fun x y hx hy hx' hy' e => ?_⟩,
      fun ℓ o => ?_⟩
    · rw [BoLo.Kont.rename_plug, Kont.rename_congr (σ := Function.update g ℓB ℓA) (τ := g) K
        (allocRedex v) (fun k o => Function.update_of_ne (oK k o) _ _)]
      simp only [Kont.plug, Expr.rename, Expr.val, Val.loc, Function.update_self]
    · by_cases ex : x = ℓB
      · subst ex; rw [Heap.upd_same] at hu; cases hu; exact Or.inl (hvS k o)
      · rw [Heap.upd_other ex] at hu
        exact Or.inl (h₁ x u (hx.resolve_right ex) hu k o)
    · by_cases ex : x = ℓB
      · rw [ex, Function.update_self, Heap.upd_same, Heap.upd_same, Option.map_some, hv]
      · have hSx : S x := hx.resolve_right ex
        have hx'' : μB x ≠ none := by rwa [Heap.upd_other ex] at hx'
        rw [Function.update_of_ne ex, Heap.upd_other (neA x hSx hx''), Heap.upd_other ex,
          h₂ x hSx hx'']
        cases hμ : μB x with
        | none => exact absurd hμ hx''
        | some w =>
            refine congrArg some (Subtype.ext (rename_update_eq fun o => nB ?_).symm)
            exact .inr (.inr ⟨x, w, hμ, o⟩)
    · by_cases ex : x = ℓB <;> by_cases ey : y = ℓB
      · exact ex.trans ey.symm
      · have hSy : S y := hy.resolve_right ey
        have hy'' : μB y ≠ none := by rwa [Heap.upd_other ey] at hy'
        rw [ex, Function.update_self, Function.update_of_ne ey] at e
        exact absurd e.symm (neA y hSy hy'')
      · have hSx : S x := hx.resolve_right ex
        have hx'' : μB x ≠ none := by rwa [Heap.upd_other ex] at hx'
        rw [ey, Function.update_self, Function.update_of_ne ex] at e
        exact absurd e (neA x hSx hx'')
      · have hx'' : μB x ≠ none := by rwa [Heap.upd_other ex] at hx'
        have hy'' : μB y ≠ none := by rwa [Heap.upd_other ey] at hy'
        rw [Function.update_of_ne ex, Function.update_of_ne ey] at e
        exact h₃ x y (hx.resolve_right ex) (hy.resolve_right ey) hx'' hy'' e
    · rcases (Kont.occ_plug_iff K).mp o with o | o
      · exact Or.inl (hK ℓ o)
      · simp only [Expr.val, Val.loc, Expr.Occ] at o; exact Or.inr o.symm
  · push Not at hal
    obtain ⟨μA'', hA'', hR'', hb'⟩ := head_sim_loc hhB hR hbS hal
    obtain rfl : K'' = .hole := head_plug hA'' K'' hhA.not_isVal hb
    simp only [Kont.plug] at hb
    subst hb
    obtain ⟨rfl, rfl⟩ := head_det hA'' hhA (not_allocRedex_rename g hal)
    refine ⟨g, S, (BoLo.Kont.rename_plug g K b').symm, hR'', fun ℓ o => ?_⟩
    rcases (Kont.occ_plug_iff K).mp o with o | o
    · exact hK ℓ o
    · exact hb' ℓ o

/-- **A fresh run, followed by every run, relative to a closed set.** -/
theorem run_sim_loc {μB μB' : Heap} {eB eB' : Expr} (hB : FreshRun μB eB μB' eB') :
    IsVal eB' → ∀ {g : Loc → Loc} {S : Loc → Prop} {μA μA' : Heap} {eA' : Expr},
      LocRel g S μB μA → (∀ ℓ, eB.Occ ℓ → S ℓ) →
      Steps μA (eB.rename g) μA' eA' → IsVal eA' → ∃ g', eA' = eB'.rename g' := by
  induction hB with
  | refl μ e =>
      intro hv g S μA μA' eA' _ _ hA _
      cases hA with
      | refl => exact ⟨g, rfl⟩
      | more h _ => exact absurd h (not_step1_of_isVal (hv.rename g))
  | more hs _ ih =>
      intro hv g S μA μA' eA' hR hS hA hvA
      cases hA with
      | refl => exact absurd hs.1 (not_step1_of_isVal (isVal_of_rename g hvA))
      | more h t =>
          obtain ⟨g₁, S₁, rfl, hR₁, hS₁⟩ := step_sim_loc hs hR hS h
          exact ih hv hR₁ hS₁ t hvA

/-- **Locality.**  A fresh run from `(μ₁, e)` to `v₁` and any run from `(μ₂, e)` to `v₂`, where
`μ₂` agrees with `μ₁` on every allocated location of a set closed for `(μ₁, e)`: `v₂` is `v₁`
with its locations renamed. -/
theorem fresh_run_local_closed {S : Loc → Prop} {μ₁ μ₂ μ₁' μ₂' : Heap} {e : Expr} {v₁ v₂ : Val}
    (hS : Closed S μ₁ e) (hag : ∀ x, S x → μ₁ x ≠ none → μ₂ x = μ₁ x)
    (h₁ : FreshRun μ₁ e μ₁' v₁.1) (h₂ : Steps μ₂ e μ₂' v₂.1) : ∃ g, v₂ = v₁.rename g := by
  have hR : LocRel id S μ₁ μ₂ := by
    refine ⟨hS.2, fun x hx hx' => ?_, fun _ _ _ _ _ _ h => h⟩
    rw [id, hag x hx hx']
    cases μ₁ x with
    | none => rfl
    | some v => exact congrArg some (Val.rename_id v).symm
  obtain ⟨g, hg⟩ := run_sim_loc h₁ v₁.2 hR hS.1 (by rwa [Expr.rename_id]) v₂.2
  exact ⟨g, Subtype.ext hg⟩

/-- **Locality**, at the least closed set: two heaps that agree on what `e` can reach. -/
theorem fresh_run_local {μ₁ μ₂ μ₁' μ₂' : Heap} {e : Expr} {v₁ v₂ : Val}
    (hag : ∀ x, Reach μ₁ (fun ℓ => e.Occ ℓ) x → μ₁ x ≠ none → μ₂ x = μ₁ x)
    (h₁ : FreshRun μ₁ e μ₁' v₁.1) (h₂ : Steps μ₂ e μ₂' v₂.1) : ∃ g, v₂ = v₁.rename g :=
  fresh_run_local_closed (closed_reach μ₁ e) hag h₁ h₂

/-- A value that mentions no location. -/
def LocFree (e : Expr) : Prop := ∀ ℓ, ¬ e.Occ ℓ

theorem Val.rename_locFree {v : Val} (h : LocFree v.1) (g : Loc → Loc) : v.rename g = v :=
  Subtype.ext (Expr.rename_eq_self _ fun ℓ o => absurd o (h ℓ))

theorem locFree_of_rename {e : Expr} {g : Loc → Loc} (h : LocFree (e.rename g)) : LocFree e :=
  fun ℓ o => h (g ℓ) ((Expr.occ_rename e).mpr ⟨ℓ, o, rfl⟩)

/-- **Locality, at a result that mentions no location**: the two results are equal. -/
theorem fresh_run_local_eq {μ₁ μ₂ μ₁' μ₂' : Heap} {e : Expr} {v₁ v₂ : Val}
    (hag : ∀ x, Reach μ₁ (fun ℓ => e.Occ ℓ) x → μ₁ x ≠ none → μ₂ x = μ₁ x)
    (h₁ : FreshRun μ₁ e μ₁' v₁.1) (h₂ : Steps μ₂ e μ₂' v₂.1) (hv : LocFree v₁.1) : v₂ = v₁ := by
  obtain ⟨g, rfl⟩ := fresh_run_local hag h₁ h₂
  exact Val.rename_locFree hv g

end BoCa.Purity

end
