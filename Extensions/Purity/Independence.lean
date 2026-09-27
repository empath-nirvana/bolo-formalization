import Purity.FreshRuns

/-!
# Purity — where the relation does not depend on the class of runs

`vX wpX b T` mentions `wpX` only at `⊸` and `∀` in the program's view (`b = true`); the
observable view (`b = false`), which an `Imm` payload is read at, relaxes both to `True`
([CONF] 415:10, 415:15; docs/adjudications.md §12.69).  But a `Mut` cell's stored predicate is
read at the program's view, wherever the cell sits.  `Ind b T` says that no `⊸` or `∀` is read
at the program's view in `T` at view `b`; at such types the relation is the same at every `wp`
(`vX_indep`), so at every class of runs.

So for the pure fragment with such argument types (`PureTypingInd`), the arguments in the
relation at every run are in the relation at the fresh runs (`gDenXR_indep`), and:

* `freshRunsExistPureInd`: fresh runs exist;
* `pure_result_every_run_ind`: every run from the world's heap, and every run from any heap
  agreeing on what the arguments reach, returns the exhibited plain-data value.

Outside `Ind`, the relation at the program's view of a function type does depend on the class
of runs: `λ_. staleL` is in the relation at `1 ⊸ 1` at every run and not at the fresh runs
(`vX_lolli_depends`).  An argument `Imm @a (Mut @b (1 ⊸ 1))` stores such a predicate in its
`Mut` cell.  For those argument types `FreshRunsExistPure` is not derived, and no obstruction is
verified: the step that does not go through is `gDenXR_indep`'s, at the `Mut` cell's stored
predicate (`ptoMutS`'s `ofS Q = P ls₀`).  Arguments that arise from a well-typed program run
at the fresh runs are in the relation at the fresh runs, and there `pure_result_every_run_fresh`
applies.

`[about ours]`: an extension, not a transcription.
-/

noncomputable section

namespace BoCa.Purity
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont FreshRunN)
open BoCa.Fig16.LogRel.Typed
open BoCa.Lifetime (LifeCtx LSub)

/-- No `⊸` or `∀` of `T` is read at the program's view, starting at view `b`. -/
def Ind : Bool → Ty → Prop
  | _, .unit => True
  | b, .tensor T₁ T₂ => Ind b T₁ ∧ Ind b T₂
  | b, .sum T₁ T₂ => Ind b T₁ ∧ Ind b T₂
  | true, .lolli _ _ => False
  | false, .lolli _ _ => True
  | true, .all _ _ _ => False
  | false, .all _ _ _ => True
  | b, .box _ T => Ind b T
  | b, .ref T => Ind b T
  | _, .imm _ T => Ind false T
  | _, .mut _ T => Ind true T
  | _, .unk => True

/-- **At `Ind` types the relation does not depend on `wp`.** -/
theorem vX_indep (w₁ w₂ : WpOp) : ∀ (T : Ty) (b : Bool), Ind b T → vX w₁ b T = vX w₂ b T
  | .unit, b, _ => by cases b <;> rfl
  | .tensor T₁ T₂, b, h => by
      have e₁ := vX_indep w₁ w₂ T₁ b h.1
      have e₂ := vX_indep w₁ w₂ T₂ b h.2
      cases b <;> (funext ls δ v; simp only [vX, e₁, e₂])
  | .sum T₁ T₂, b, h => by
      have e₁ := vX_indep w₁ w₂ T₁ b h.1
      have e₂ := vX_indep w₁ w₂ T₂ b h.2
      cases b <;> (funext ls δ v; simp only [vX, e₁, e₂])
  | .lolli _ _, false, _ => rfl
  | .lolli _ _, true, h => h.elim
  | .all _ _ _, false, _ => rfl
  | .all _ _ _, true, h => h.elim
  | .box a T, b, h => by
      have e := vX_indep w₁ w₂ T b h
      cases b <;> (funext ls δ v; simp only [vX, e])
  | .ref T, b, h => by
      have e := vX_indep w₁ w₂ T b h
      cases b <;> (funext ls δ v; simp only [vX, e])
  | .imm a T, b, h => by
      have e := vX_indep w₁ w₂ T false h
      cases b <;> (funext ls δ v; simp only [vX, e])
  | .mut a T, b, h => by
      have e := vX_indep w₁ w₂ T true h
      cases b <;> (funext ls δ v; simp only [vX, e])
  | .unk, b, _ => by cases b <;> rfl

/-- A context all of whose live slots are `Ind` at the program's view. -/
def CtxInd (Γ : Ctx Ty) : Prop := ∀ s ∈ Γ, s.live = true → Ind true s.ty

theorem gSepXR_indep (RR₁ RR₂ : RunRel) (ls : List SRec) (δ : LSub) :
    ∀ (Γ : Ctx Ty) (γ : List Val), CtxInd Γ → gSepXR RR₁ ls δ Γ γ = gSepXR RR₂ ls δ Γ γ
  | [], _, _ => by simp only [gSepXR]
  | _ :: _, [], _ => by simp only [gSepXR]
  | s :: Γ, v :: γ, hΓ => by
      have ih := gSepXR_indep RR₁ RR₂ ls δ Γ γ
        (fun s' hs' => hΓ s' (List.mem_cons_of_mem _ hs'))
      simp only [gSepXR]
      split
      · rename_i hl
        have e := vX_indep (wpTSR RR₁) (wpTSR RR₂) s.ty true (hΓ s (List.mem_cons_self ..) hl)
        simp only [vPR, e, ih]
      · exact ih

/-- **At `Ind` contexts the context relation does not depend on the class of runs.** -/
theorem gDenXR_indep (RR₁ RR₂ : RunRel) {ls : List SRec} {δ : LSub} {Γ : Ctx Ty}
    {γ : List Val} (hΓ : CtxInd Γ) : gDenXR RR₁ ls δ Γ γ = gDenXR RR₂ ls δ Γ γ := by
  simp only [gDenXR, gSepXR_indep RR₁ RR₂ ls δ Γ γ hΓ]

/-- The pure fragment with `Ind` argument types. -/
structure PureTypingInd (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty) : Prop where
  pure : PureTyping Δ Γ e T
  ind : CtxInd Γ

/-- **Fresh runs exist for the pure fragment at `Ind` argument types**, the arguments in the
relation at every run. -/
theorem freshRunsExistPureInd {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty}
    (hP : PureTypingInd Δ Γ e T) {δ : LSub} {γ : List Val} {ls : List SRec} {ρ ρf fρ : WRes}
    {ps : List FrameRec} {μ : Heap} (hδ : Δ.Models δ) (hγ : gDenX ls δ Γ γ ρ)
    (hf : ResU.Hash ρf ρ) (hc : ResU.CompS ρf ρ fρ) (hT : TW fρ ps (rsOf ls))
    (htg : Tagged fρ ps ls) (hμ : ResU.Lower fρ μ) :
    ∃ (μ' : Heap) (v : Val), FreshRun μ (LogRel.substAll γ e) μ' v.1 := by
  have hγ' : gDenXR freshRel ls δ Γ γ ρ := by
    rw [← gDenXR_indep stepsRel freshRel hP.ind]; exact hγ
  exact freshRunsExistPureF Δ Γ e T hP.pure δ γ ls ρ ρf fρ ps μ hδ hγ' hf hc hT htg hμ

/-- **The pure fragment at `Ind` argument types, on every run.**  With the arguments in the
relation at every run, from every tagged typed world's heap `μ`: a fresh run gives `μ` back and
returns a plain-data value `v`; every run from `μ` returns `v`; and every run from any heap
agreeing with `μ` on what the arguments reach returns `v`. -/
theorem pure_result_every_run_ind {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty}
    (hP : PureTypingInd Δ Γ e T) {δ : LSub} {γ : List Val} {ls : List SRec} {ρ : WRes}
    (hδ : Δ.Models δ) (hγ : gDenX ls δ Γ γ ρ) {ρf fρ : WRes} {ps : List FrameRec}
    (hf : ResU.Hash ρf ρ) (hc : ResU.CompS ρf ρ fρ) (hT : TW fρ ps (rsOf ls))
    (htg : Tagged fρ ps ls) {μ : Heap} (hμ : ResU.Lower fρ μ) :
    ∃ v : Val, LocFree v.1 ∧ FreshRun μ (LogRel.substAll γ e) μ (.val v) ∧
      (∀ (μ' : Heap) (w : Val), Steps μ (LogRel.substAll γ e) μ' w.1 → w = v) ∧
      ∀ (μ₂ μ₂' : Heap) (w : Val),
        (∀ x, Reach μ (ArgLocs γ) x → μ x ≠ none → μ₂ x = μ x) →
        Steps μ₂ (LogRel.substAll γ e) μ₂' w.1 → w = v := by
  have hγ' : gDenXR freshRel ls δ Γ γ ρ := by
    rw [← gDenXR_indep stepsRel freshRel hP.ind]; exact hγ
  exact pure_result_every_run_fresh hP.pure hδ hγ' hf hc hT htg hμ

/-! ### Outside `Ind` -/

/-- `λ_. staleL` is not in the relation at `1 ⊸ 1` at the fresh runs: from the empty world,
`staleL` has no fresh run. -/
theorem staleClosure_outside_fresh (δ : LSub) :
    ¬ vPR freshRel (.lolli .unit .unit) [] δ staleClosure PMap.empty := by
  intro h
  have hw := h [] (Ext.refl [] _) Val.unit PMap.empty PMap.empty ⟨rfl, rfl⟩
    (ResU.comp_empty_right _)
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  obtain ⟨-, -, -, -, -, v, μ₀, μ', -, -, -, -, -, h₅, -, -, h₈, -⟩ :=
    hw PMap.empty PMap.empty [] Fig16.LogRel.hash_empty (ResU.comp_empty_right _) TW.empty
      htg []
  cases ResU.Lower.functional h₅ Fig16.BoLo.lower_empty
  have hB := FreshRunN.toFreshRun h₈
  have h := fresh_peel_det (K := .hole) hB rfl (Head.beta _ staleL Val.unit)
    (by intro w e; simp [allocRedex, staleClosure, Expr.val, Val.lam, Val.unit] at e)
  simp only [Kont.plug] at h
  rw [staleL_subst] at h
  exact staleL_no_fresh h

/-- **The relation at the program's view of `1 ⊸ 1` depends on the class of runs**: it differs
at every run and at the fresh runs. -/
theorem vX_lolli_depends :
    vX (wpTSR stepsRel) true (.lolli .unit .unit) ≠ vX (wpTSR freshRel) true (.lolli .unit .unit) :=
  fun e => staleClosure_outside_fresh LSub.empty (by
    have h := staleClosure_vP [] LSub.empty
    simp only [vP, vPR] at h ⊢
    rwa [e] at h)

end BoCa.Purity

end
