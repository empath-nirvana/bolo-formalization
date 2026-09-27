import Purity.FreshExistence
import Support.Model.CellFacts

/-!
# Purity — where the freedom in allocation comes from

`[TR]` p. 4's `alloc↦` allocates any location the memory misses.  The question here is whether
the logical relation needs that freedom — whether its runs could be fixed by a deterministic
allocation policy.

**The allocation rule is demonic.**  `Typed.wpTS_alloc` (`Support/TypedWorld/Wp.lean`, `[TR]`
6.141) picks its location with `PMap.exists_fresh` from the flattening `⦇ρf ● ρ⦈`, and a
location is missing from the flattening exactly when it is missing from the heap
(`lower_eq_none_iff`).  Nothing else in the proof depends on which location it is.
`wpTS_alloc_any` restates the rule for every heap-fresh location: from every tagged typed
world, the step to *any* location the heap misses satisfies all of row 5.33's post-conditions.

**The freedom is in `wpTS` itself** (`Support/TypedWorld/World.lean`, row 5.33): it asks for
*some* run (`Steps`, existentially).  Every run the Fundamental Property builds is assembled by
`wpTS_val`, `wpTS_head`, `wpTS_alloc`, `wpTS_free`, the two load rules, `wpTS_store` (one head
step each) and `wpTS_bind` (`Steps.plug`, `Steps.trans`); the other rules pass the run through
(by inspection of the run constructors in `Support/TypedWorld/`).  So a `wpTS` whose run is
restricted to a policy (`PolRun`) would satisfy the same rules — but in this repository that
means re-running the typed world at a different `wpTS`, since its definition fixes `Steps`.

**A term of the semantic relation can need the freedom.**  `peek 1` is in the relation at
`∅; ∅ ⊨ peek 1 : 1`, and from the empty world it has no run under the least-free policy
(`not_semPolicyRuns`): the policy allocates `0`, and `load 1` is stuck.  Its semantic proof
allocates `1` when the heap misses it, a choice the policy does not make.

`[about ours]`: an extension, not a transcription.
-/

noncomputable section

namespace BoCa.Purity
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Fig16.LogRel.Typed
open BoCa.Lifetime (LifeCtx LSub)

/-! ### The allocation rule, at every heap-fresh location -/

/-- Row 5.33's post-conditions, for a run from `μ` to `μ'` returning `v`. -/
def PostAt (ls : List SRec) (ρ ρf fρ : WRes) (ps : List FrameRec) (Q : List SRec → Val → WProp)
    (μ μ' : Heap) (v : Val) : Prop :=
  ∃ (ρ' ρp fρ' fρ'p π : WRes) (ps' : List FrameRec) (ls' : List SRec),
    ResU.Hash ρ' ρf ∧ ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧ ResU.Lower fρ μ ∧
    ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧ ResU.CompS ρ' ρp π ∧ ResU.UpdV ρ π ∧
    NoOwn ρp ∧ TW fρ'p ps' (rsOf ls') ∧ Tagged fρ'p ps' ls' ∧ (∀ p, p ∈ ps' ↔ p ∈ ps) ∧
    (∀ x, x ∈ ls' ↔ x ∈ ls) ∧ Q ls' v ρ'

/-- `wpTS` is "some run, and `PostAt`". -/
theorem wpTS_iff_postAt {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp} {ρ : WRes} :
    wpTS ls e Q ρ ↔ ∀ (ρf fρ : WRes) (ps : List FrameRec), ResU.Hash ρf ρ →
      ResU.CompS ρf ρ fρ → TW fρ ps (rsOf ls) → Tagged fρ ps ls →
      ∃ (μ μ' : Heap) (v : Val), Steps μ e μ' (.val v) ∧ PostAt ls ρ ρf fρ ps Q μ μ' v := by
  constructor
  · intro h ρf fρ ps hf hc hT htg
    obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, h₈, h₉, hA, hB,
      hT', htg', hps, hls, hC⟩ := h ρf fρ ps hf hc hT htg
    exact ⟨μ, μ', v, h₈, ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, h₉, hA, hB,
      hT', htg', hps, hls, hC⟩
  · intro h ρf fρ ps hf hc hT htg
    obtain ⟨μ, μ', v, h₈, ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, h₉, hA, hB,
      hT', htg', hps, hls, hC⟩ := h ρf fρ ps hf hc hT htg
    exact ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, h₈, h₉, hA, hB,
      hT', htg', hps, hls, hC⟩

/-- **`[TR]` 6.141 at every heap-fresh location.**  Under `wp-alloc`'s premise, from every tagged
typed world with heap `μ`, the step allocating any `l` that `μ` misses satisfies row 5.33's
post-conditions.  The proof is `Typed.wpTS_alloc`'s with its choice of `l` made a parameter. -/
theorem wpTS_alloc_any (ls : List SRec) (v : Val) (Q : List SRec → Val → WProp) {ρ : WRes}
    (h : all (fun l : BoCa.Loc => wand (ptoOwn l v) (Q ls (.loc l))) ρ) {ρf σ : WRes}
    {ps : List FrameRec} (hf : ResU.Hash ρf ρ) (hσ : ResU.CompS ρf ρ σ) (hT : TW σ ps (rsOf ls))
    (htg : Tagged σ ps ls) {μ : Heap} (hμ : ResU.Lower σ μ) {l : Loc} (hμl : μ l = none) :
    Head μ (.app (.val (.prim .alloc)) (.val v)) (μ.upd l v) (.val (.loc l)) ∧
      PostAt ls ρ ρf σ ps Q μ (μ.upd l v) (.loc l) := by
  obtain ⟨τ, hτ, hval⟩ := id hμ
  have hl : τ.get l = none := (lower_eq_none_iff hval).mp hμl
  have hρl : ρ.get l = none :=
    ((ResU.Comp.eq_none_iff hσ l).mp (get_eq_none_of_flat hτ hl)).2
  obtain ⟨x, hx⟩ := (ResU.compS_defined_iff ρ (ResU.single l (CellU.ownOf v))).mpr
    (compatS_single_of_get_none hρl)
  obtain ⟨σ', hσ'x, hfx, hlow'⟩ := hash_compS_own hσ hμ hμl hx
  obtain ⟨y, hy, hyσ'⟩ := (ResU.CompS.assoc ρf ρ (ResU.single l (CellU.ownOf v)) σ').mp
    ⟨x, hx, hσ'x⟩
  cases ResU.CompS.functional hy hσ
  have hT' : TW σ' ps (rsOf ls) := TW.alloc hT hμ hμl hyσ' (hash_valid_comp hfx hσ'x)
  exact ⟨Head.alloc μ v l hμl, x, PMap.empty, σ', σ', x, ps, ls,
    ResU.hash_symm hfx, hσ'x,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hfx hσ'x)),
    hμ, ResU.comp_empty_right σ', hlow', ResU.comp_empty_right x,
    updV_compS_own hx (hash_valid hf).2 (hash_valid hfx).2,
    noOwn_empty, hT', tagged_of_ag (fun a ha => alloc_ag hyσ' ha) htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, h l _ x rfl hx⟩

/-! ### Runs under an allocation policy -/

/-- A step whose allocation, if any, is at `pol μ`. -/
def PolStep (pol : Heap → Loc) (μ : Heap) (e : Expr) (μ' : Heap) (e' : Expr) : Prop :=
  Step1 μ e μ' e' ∧ ∀ ℓ, μ' ℓ ≠ none → μ ℓ = none → ℓ = pol μ

/-- A run under the allocation policy `pol`. -/
inductive PolRun (pol : Heap → Loc) : Heap → Expr → Heap → Expr → Prop where
  | refl (μ : Heap) (e : Expr) : PolRun pol μ e μ e
  | more {μ μ₁ μ' : Heap} {e e₁ e' : Expr}
      (h : PolStep pol μ e μ₁ e₁) (t : PolRun pol μ₁ e₁ μ' e') : PolRun pol μ e μ' e'

theorem PolRun.toSteps {pol : Heap → Loc} {μ μ' : Heap} {e e' : Expr}
    (h : PolRun pol μ e μ' e') : Steps μ e μ' e' := by
  induction h with
  | refl => exact .refl _ _
  | more h _ ih => exact .more h.1 ih

open Classical in
/-- The least location the heap misses (`0` if it misses none). -/
def leastFree (μ : Heap) : Loc := if h : ∃ l, μ l = none then Nat.find h else 0

theorem leastFree_fresh {μ : Heap} (h : ∃ l, μ l = none) : μ (leastFree μ) = none := by
  classical
  simp only [leastFree, dif_pos h]
  exact Nat.find_spec h

theorem leastFree_empty : leastFree (fun _ => none) = 0 := by
  classical
  have h : ∃ l : Loc, (fun _ => none : Heap) l = none := ⟨0, rfl⟩
  unfold leastFree
  rw [dif_pos h]
  exact (Nat.find_eq_zero h).mpr rfl

/-- **Runs under a policy, at the semantic judgment**: every closed plain program of the
semantic relation has, from every tagged typed world completing `∅`, a run under `pol` to a
value. -/
def SemPolicyRuns (pol : Heap → Loc) : Prop :=
  ∀ (e : Expr) (T : Ty), SemX LifeCtx.empty ([] : Ctx Ty) e T →
    ∀ (ρf fρ : WRes) (ps : List FrameRec) (μ : Heap),
      ResU.Hash ρf PMap.empty → ResU.CompS ρf PMap.empty fρ → TW fρ ps (rsOf []) →
      Tagged fρ ps [] → ResU.Lower fρ μ → ∃ (μ' : Heap) (v : Val), PolRun pol μ e μ' v.1

/-- **`SemPolicyRuns leastFree` does not hold**, at `peek 1` from the empty world. -/
theorem not_semPolicyRuns : ¬ SemPolicyRuns leastFree := by
  intro h
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  obtain ⟨μ', v, hR⟩ := h (peek 1) .unit (peek_sem 1) PMap.empty PMap.empty [] (fun _ => none)
    Fig16.LogRel.hash_empty (ResU.comp_empty_right _) TW.empty htg Fig16.BoLo.lower_empty
  generalize hp : peek 1 = e at hR
  cases hR with
  | refl => exact absurd (hp ▸ v.2 : IsVal (peek 1)) (by simp [peek, elet, allocE])
  | more hs t =>
      subst hp
      obtain ⟨l, -, rfl, rfl⟩ := peek_first_step hs.1
      have hl0 : l = 0 := by
        rw [← leastFree_empty]; exact hs.2 l (by simp) rfl
      have hl1 : l = 1 := peek_allocates_k t.toSteps
      rw [hl0] at hl1
      exact absurd hl1 (by decide)

end BoCa.Purity

end
