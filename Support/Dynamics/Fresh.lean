import Paper.S1_Syntax.Definitions
import Paper.S3_Dynamics.Definitions
import Support.Dynamics.Machine
import Support.Model.Prelude

/-!
# Support — Dynamics — Fresh

`[about ours]`.  Runs whose allocations avoid a finite set of locations.  A configuration
`(μ, e)` *names* a location when the memory holds it, the term mentions it, or a value the
memory holds mentions it; with a finite list `N`, a location is named when it is also in `N`
(`NamedBy`).  A fresh step allocates only locations its configuration does not name
(`FreshStepN`); a fresh run takes only fresh steps (`FreshRunN`).

Fresh runs are closed under the operations `wp`'s rules build runs with, provided the list is
enlarged when a run is plugged into an evaluation context: a run of `e` avoiding `N` and the
locations of `K` is, plugged, a run of `K[e]` avoiding `N` (`FreshRunN.plug`).
(docs/adjudications.md §12.74.)
-/

noncomputable section

namespace BoCa

/-- `ℓ` occurs in `e`. -/
def Expr.Occ (ℓ : Loc) : Expr → Prop
  | .var _ | .unit | .prim _ => False
  | .loc k         => k = ℓ
  | .pair a b | .seq a b | .letpair a b | .app a b => a.Occ ℓ ∨ b.Occ ℓ
  | .inj₁ a | .inj₂ a | .lam a => a.Occ ℓ
  | .case a b c    => a.Occ ℓ ∨ b.Occ ℓ ∨ c.Occ ℓ

/-- The locations of `e`, as a list. -/
def Expr.locs : Expr → List Loc
  | .var _ | .unit | .prim _ => []
  | .loc k         => [k]
  | .pair a b | .seq a b | .letpair a b | .app a b => a.locs ++ b.locs
  | .inj₁ a | .inj₂ a | .lam a => a.locs
  | .case a b c    => a.locs ++ b.locs ++ c.locs

theorem Expr.occ_iff_mem_locs {ℓ : Loc} : ∀ e : Expr, e.Occ ℓ ↔ ℓ ∈ e.locs
  | .var _ | .unit | .prim _ => by simp [Expr.Occ, Expr.locs]
  | .loc k => by simp [Expr.Occ, Expr.locs, eq_comm]
  | .pair a b | .seq a b | .letpair a b | .app a b => by
      simp [Expr.Occ, Expr.locs, Expr.occ_iff_mem_locs a, Expr.occ_iff_mem_locs b]
  | .inj₁ a | .inj₂ a | .lam a => by simp [Expr.Occ, Expr.locs, Expr.occ_iff_mem_locs a]
  | .case a b c => by
      simp [Expr.Occ, Expr.locs, Expr.occ_iff_mem_locs a, Expr.occ_iff_mem_locs b,
        Expr.occ_iff_mem_locs c]

end BoCa

namespace BoCa.BoLo

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

/-- `(μ, e)` names `ℓ`, or `ℓ ∈ N`. -/
def NamedBy (N : List Loc) (μ : Heap) (e : Expr) (ℓ : Loc) : Prop :=
  ℓ ∈ N ∨ μ ℓ ≠ none ∨ e.Occ ℓ ∨ ∃ k v, μ k = some v ∧ v.1.Occ ℓ

/-- A step whose allocation, if any, is of a location `(μ, e)` and `N` do not name. -/
def FreshStepN (N : List Loc) (μ : Heap) (e : Expr) (μ' : Heap) (e' : Expr) : Prop :=
  Step1 μ e μ' e' ∧ ∀ ℓ, μ' ℓ ≠ none → μ ℓ = none → ¬ NamedBy N μ e ℓ

/-- A run of fresh steps, avoiding `N`. -/
inductive FreshRunN (N : List Loc) : Heap → Expr → Heap → Expr → Prop where
  | refl (μ : Heap) (e : Expr) : FreshRunN N μ e μ e
  | more {μ μ₁ μ' : Heap} {e e₁ e' : Expr}
      (h : FreshStepN N μ e μ₁ e₁) (t : FreshRunN N μ₁ e₁ μ' e') : FreshRunN N μ e μ' e'

namespace FreshRunN

theorem toSteps {N : List Loc} {μ μ' : Heap} {e e' : Expr} (h : FreshRunN N μ e μ' e') :
    Steps μ e μ' e' := by
  induction h with
  | refl => exact .refl _ _
  | more h _ ih => exact .more h.1 ih

/-- A step that allocates no location, then a fresh run. -/
theorem cons {N : List Loc} {μ μ₁ μ' : Heap} {e e₁ e' : Expr} (h : Step1 μ e μ₁ e₁)
    (hdom : ∀ ℓ, μ₁ ℓ ≠ none → μ ℓ ≠ none) (t : FreshRunN N μ₁ e₁ μ' e') :
    FreshRunN N μ e μ' e' :=
  .more ⟨h, fun ℓ h₁ h₀ => absurd h₀ (hdom ℓ h₁)⟩ t

theorem trans {N : List Loc} {μ μ₁ μ' : Heap} {e e₁ e' : Expr} (h₁ : FreshRunN N μ e μ₁ e₁)
    (h₂ : FreshRunN N μ₁ e₁ μ' e') : FreshRunN N μ e μ' e' := by
  induction h₁ with
  | refl => exact h₂
  | more h _ ih => exact .more h (ih h₂)

/-- A run of `e` avoiding `N` and the locations of `K` is, plugged, a run of `K[e]` avoiding
`N`. -/
theorem plug {N : List Loc} (K : Kont) {μ μ' : Heap} {e e' : Expr}
    (h : FreshRunN (N ++ (K.plug .unit).locs) μ e μ' e') :
    FreshRunN N μ (K.plug e) μ' (K.plug e') := by
  induction h with
  | refl => exact .refl _ _
  | more h _ ih =>
      refine .more ⟨Step1.plug K h.1, fun ℓ h₁ h₀ hn => h.2 ℓ h₁ h₀ ?_⟩ ih
      rcases hn with hN | hd | ho | hv
      · exact .inl (List.mem_append_left _ hN)
      · exact .inr (.inl hd)
      · rcases (Kont.occ_plug_iff K).mp ho with hK | he
        · exact .inl (List.mem_append_right _ ((Expr.occ_iff_mem_locs _).mp hK))
        · exact .inr (.inr (.inl he))
      · exact .inr (.inr (.inr hv))

/-- The locations a finite memory holds or its values mention, with `N` and those of `e`. -/
theorem named_finite (N : List Loc) {μ : Heap} (hfin : Fig16.FinDom μ) (e : Expr) :
    ∃ L : List Loc, ∀ ℓ, NamedBy N μ e ℓ → ℓ ∈ L := by
  obtain ⟨d, hd⟩ := hfin
  refine ⟨N ++ d ++ e.locs ++ d.flatMap (fun k => ((μ k).map (fun v => v.1.locs)).getD []),
    fun ℓ hn => ?_⟩
  rcases hn with hN | hdom | ho | ⟨k, v, hk, hv⟩
  · simp [hN]
  · simp [hd ℓ hdom]
  · simp [(Expr.occ_iff_mem_locs e).mp ho]
  · have hkd : k ∈ d := hd k (by simp [hk])
    simp only [List.mem_append, List.mem_flatMap]
    exact .inr ⟨k, hkd, by simp [hk, (Expr.occ_iff_mem_locs _).mp hv]⟩

/-- An allocation at a location nothing names. -/
theorem alloc (N : List Loc) (μ : Heap) (v : Val) (hfin : Fig16.FinDom μ) :
    ∃ l, μ l = none ∧ FreshRunN N μ (.app (.val (.prim .alloc)) (.val v)) (μ.upd l v)
      (.val (.loc l)) := by
  obtain ⟨L, hL⟩ := named_finite N hfin (.app (.val (.prim .alloc)) (.val v))
  have hl : L.sum + 1 ∉ L := fun h => Nat.not_succ_le_self _ (List.le_sum_of_mem h)
  have hn : ¬ NamedBy N μ (.app (.val (.prim .alloc)) (.val v)) (L.sum + 1) :=
    fun h => hl (hL _ h)
  have hμ : μ (L.sum + 1) = none := by
    by_contra h; exact hn (.inr (.inl h))
  refine ⟨L.sum + 1, hμ, .more ⟨Step1.head (Head.alloc μ v _ hμ), fun ℓ h₁ h₀ => ?_⟩ (.refl _ _)⟩
  by_cases e : ℓ = L.sum + 1
  · subst e; exact hn
  · exact absurd (by rw [Heap.upd_other e, h₀]) h₁

end FreshRunN

end BoCa.BoLo

end
