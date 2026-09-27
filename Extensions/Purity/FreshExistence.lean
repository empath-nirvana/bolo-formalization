import Purity.Boundary

/-!
# Purity — does a well-typed program have a fresh run?

The "every run" halves of `pure_heap`, `pure_result` and `closed_pure` quantify over *fresh*
runs (`Fresh.lean`): runs whose allocations pick locations the configuration does not name.
The run the Fundamental Property exhibits need not be fresh.  This file states the missing
fact and settles how far the semantic relation goes toward it.

* `FreshRunsExistSyn`: from every tagged typed world, a program `DerivesWf` types, closed by
  values in the relation, has a fresh run to a value.  **Not derived**; no obstruction to it
  is verified.
* `FreshRunsExistSem`: the same with `SemX` in place of `DerivesWf`.  **It does not hold**
  (`not_freshRunsExistSem`), at `peek 0`: from the empty world every run of `peek 0` to a
  value allocates the location `0` that the term itself names.
* `pure_result_every_run`: under `FreshRunsExistSyn`, every run of a program of the pure
  fragment from the world's heap, and every run from any heap agreeing on what the arguments
  reach, returns the exhibited value.  This is what the missing fact would buy.

The two columns differ, as for the read footprint, by the locations a term names.  What a
proof of `FreshRunsExistSyn` would need is that a well-typed program never reads through a
name whose location it freed and reallocated; that is a property of the states along a run.
The semantic relation constrains a run only through its final world, and `DerivesWf` does not
type the run's intermediate terms: they contain locations (`derivesWf_locFree`), and the axiom
terms' reducts duplicate a lent location (`withbor ≜ λx.λf.(x, f () x)`).  So the development
has no invariant of intermediate states to draw on.

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

/-- **Fresh runs exist, at the syntactic judgment.**  Not derived. -/
def FreshRunsExistSyn : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty), DerivesWf Δ Γ e T → Δ.Ok →
    Ctx.ScopedB Δ Γ → ∀ (δ : LSub) (γ : List Val) (ls : List SRec) (ρ ρf fρ : WRes)
      (ps : List FrameRec) (μ : Heap), Δ.Models δ → gDenX ls δ Γ γ ρ →
      ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → TW fρ ps (rsOf ls) → Tagged fρ ps ls →
      ResU.Lower fρ μ → ∃ (μ' : Heap) (v : Val), FreshRun μ (LogRel.substAll γ e) μ' v.1

/-- **Fresh runs exist, at the semantic judgment**: `FreshRunsExistSyn` with `SemX` in place of
`DerivesWf`. -/
def FreshRunsExistSem : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty), SemX Δ Γ e T →
    ∀ (δ : LSub) (γ : List Val) (ls : List SRec) (ρ ρf fρ : WRes)
      (ps : List FrameRec) (μ : Heap), Δ.Models δ → gDenX ls δ Γ γ ρ →
      ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → TW fρ ps (rsOf ls) → Tagged fρ ps ls →
      ResU.Lower fρ μ → ∃ (μ' : Heap) (v : Val), FreshRun μ (LogRel.substAll γ e) μ' v.1

/-- The first step of `peek k` allocates, at a location the heap misses. -/
theorem peek_first_step {μ μ₁ : Heap} {k : Loc} {e₁ : Expr} (h : Step1 μ (peek k) μ₁ e₁) :
    ∃ l, μ l = none ∧ μ₁ = μ.upd l .unit ∧
      e₁ = Kont.plug (.appR (.val (.lam (peekBody k))) .hole) (.val (.loc l)) := by
  obtain ⟨K', b, b', hE, rfl, hh⟩ := h
  have h₀ : Head (fun _ => none) (allocE unit') (BoLo.Heap.upd (fun _ => none) 0 .unit)
      (.val (.loc 0)) := Head.alloc _ .unit 0 rfl
  obtain ⟨K'', hb, rfl⟩ := plug_decomp hh (.appR (.val (.lam (peekBody k))) .hole) K'
    h₀.not_isVal hE
  obtain rfl : K'' = .hole := head_plug h₀ K'' hh.not_isVal hb
  simp only [Kont.plug] at hb
  subst hb
  obtain ⟨l, hl, rfl, rfl⟩ := head_alloc_inv hh (v := .unit) rfl
  exact ⟨l, hl, rfl, by rw [BoLo.Kont.plug_comp]; rfl⟩

/-- From a heap lacking `k`, a run of `peek k` to a value allocates `k` first. -/
theorem peek_allocates_k {k : Loc} {μ' : Heap} {v : Val} {l : Loc}
    (t : Steps (BoLo.Heap.upd (fun _ => none) l .unit)
      (Kont.plug (.appR (.val (.lam (peekBody k))) .hole) (.val (.loc l))) μ' v.1) :
    l = k := by
  have hr := steps_runIn (S := fun _ => True) ⟨fun _ _ => trivial, fun _ _ _ _ _ _ => trivial⟩ t
  obtain ⟨μ₂, a₂, hh₂, -, t₂⟩ := runIn_head_inv (K := .hole)
    (Head.beta (fun _ => none) (peekBody k) (Val.loc l)) hr v.2
  obtain ⟨rfl, rfl⟩ := head_det (Head.beta _ _ (Val.loc l)) hh₂
    (by intro w e; simp [allocRedex, Expr.val, Val.lam, Val.loc] at e)
  rw [peekBody_subst] at t₂
  simp only [Kont.plug] at t₂
  obtain ⟨μ₃, a₃, hh₃, -, -⟩ := runIn_head_inv
    (K := .seq (.appR (.val (.lam unit')) .hole) (freeE (.val (.loc l))))
    (a := loadE (.val (.loc k)))
    (Head.load (BoLo.Heap.upd (fun _ => none) k .unit) k .unit (BoLo.Heap.upd_same _ _ _))
    (by exact t₂) v.2
  cases hh₃ with
  | load _ w hw =>
      by_contra hne
      rw [BoLo.Heap.upd_other (Ne.symm hne)] at hw
      cases hw

/-- **`FreshRunsExistSem` does not hold**, at `peek 0` from the empty world: a fresh run may not
allocate `0`, which `peek 0` names, and every run to a value does. -/
theorem not_freshRunsExistSem : ¬ FreshRunsExistSem := by
  intro h
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  obtain ⟨μ', v, hR⟩ := h LifeCtx.empty [] (peek 0) .unit (peek_sem 0) LSub.empty [] []
    PMap.empty PMap.empty PMap.empty [] (fun _ => none) Adequacy.models_empty
    (gDenX_nil [] LSub.empty) Fig16.LogRel.hash_empty (ResU.comp_empty_right _) TW.empty htg
    Fig16.BoLo.lower_empty
  rw [substAll_peek] at hR
  generalize hp : peek 0 = e at hR
  cases hR with
  | refl => exact absurd (hp ▸ v.2 : IsVal (peek 0)) (by simp [peek, elet, allocE])
  | more hs t =>
      subst hp
      obtain ⟨l, -, rfl, rfl⟩ := peek_first_step hs.1
      have hl : l = 0 := peek_allocates_k t.toSteps
      subst hl
      exact hs.2 0 (by simp) rfl
        (.inr (.inl (by simp [peek, elet, peekBody, loadE, Expr.Occ, Expr.val, Val.loc])))

/-- **What fresh-run existence would buy.**  Under `FreshRunsExistSyn`, every run of a program
of the pure fragment from the world's heap `μ`, and every run from any heap agreeing with `μ`
on what the arguments reach, returns the exhibited value. -/
theorem pure_result_every_run (hex : FreshRunsExistSyn) {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr}
    {T : Ty} (hP : PureTyping Δ Γ e T) {δ : LSub} {γ : List Val} {ls : List SRec} {ρ : WRes}
    (hδ : Δ.Models δ) (hγ : gDenX ls δ Γ γ ρ) {ρf fρ : WRes} {ps : List FrameRec}
    (hf : ResU.Hash ρf ρ) (hc : ResU.CompS ρf ρ fρ) (hT : TW fρ ps (rsOf ls))
    (htg : Tagged fρ ps ls) {μ : Heap} (hμ : ResU.Lower fρ μ) :
    ∃ v : Val, LocFree v.1 ∧ Steps μ (LogRel.substAll γ e) μ (.val v) ∧
      ∀ (μ₂ μ₂' : Heap) (w : Val),
        (∀ x, Reach μ (ArgLocs γ) x → μ x ≠ none → μ₂ x = μ x) →
        Steps μ₂ (LogRel.substAll γ e) μ₂' w.1 → w = v := by
  obtain ⟨v, hlf, -, hrun, hall⟩ := pure_result hP hδ hγ hf hc hT htg hμ
  obtain ⟨μ₁, w₁, hR⟩ := hex Δ Γ e T hP.derives hP.ok hP.wfCtx δ γ ls ρ ρf fρ ps μ hδ hγ
    hf hc hT htg hμ
  exact ⟨v, hlf, hrun, fun μ₂ μ₂' w hag h₂ => (hall μ₁ μ₂ μ₂' w₁ w hR hag h₂).2⟩

end BoCa.Purity

end
