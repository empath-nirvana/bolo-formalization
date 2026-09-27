import Purity.PolicyRuns

/-!
# Purity — fresh runs of well-typed programs

The Fundamental Property holds at `Typed.freshRel` (docs/adjudications.md §12.74): the class of
runs whose every allocation avoids a given finite list `N` and every location its configuration
names.  At `N = []` such a run is a fresh run of `Fresh.lean` (`FreshRunN.toFreshRun`).  So:

* `freshRunsExistClosed`: `FreshRunsExistClosed` holds.  A closed well-typed program has a fresh
  run from the heap of every tagged typed world.
* `closed_pure_every_run`: a closed program of plain-data type returns one value `v` on *every*
  run from *every* heap: whatever the allocator, whatever the memory around it.  This is purity
  in Pure Borrow's sense (§1), with no condition on the runs.
* `freshRunsExistPureF`, `pure_result_every_run_fresh`: the same for the pure fragment, with its
  arguments in the relation at the fresh runs.  Every run of `γ(e)` from `μ`, and every run from
  any heap agreeing with `μ` on what `γ` reaches, returns the exhibited value.

`FreshRunsExistPure` itself, with the arguments in the relation at every run, is not derived:
the relation at a `Mut` cell inside a borrowed payload stores a predicate that mentions `wp`
(`vX`'s `Mut` clause), so the relations at the two classes of runs need not agree there.

`[about ours]`: an extension, not a transcription.
-/

noncomputable section

namespace BoCa.Purity
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont FreshRunN NamedBy)
open BoCa.Fig16.LogRel.Typed
open BoCa.Lifetime (LifeCtx LSub)

/-- A fresh run avoiding the empty list is a fresh run. -/
theorem FreshRunN.toFreshRun {μ μ' : Heap} {e e' : Expr} (h : FreshRunN [] μ e μ' e') :
    FreshRun μ e μ' e' := by
  induction h with
  | refl => exact .refl _ _
  | more h _ ih => exact .more ⟨h.1, fun ℓ h₁ h₀ hn => h.2 ℓ h₁ h₀ (.inr hn)⟩ ih

/-- **`FreshRunsExistClosed` holds.** -/
theorem freshRunsExistClosed : FreshRunsExistClosed := by
  intro e T hD ls ρf fρ ps μ hf hc hTW htg hμ
  have hsem := fundamentalR freshRel LifeCtx.empty [] e T hD ok_empty
    (fun s hs => absurd hs (by simp))
  have hw := hsem LSub.empty [] ls PMap.empty Adequacy.models_empty
    (gDenX_nil (RR := freshRel) ls LSub.empty)
  rw [LogRel.substAll, Adequacy.psub_nil] at hw
  obtain ⟨-, -, -, -, -, v, μ₀, μ', -, -, -, -, -, h₅, -, -, h₈, -⟩ :=
    hw ρf fρ ps hf hc hTW htg []
  cases ResU.Lower.functional h₅ hμ
  exact ⟨μ', v, FreshRunN.toFreshRun h₈⟩

/-- **A closed program of plain-data type is pure.**  It returns one plain-data value `v` on
every run from every heap; from the empty memory it has a run that frees everything it
allocates. -/
theorem closed_pure_every_run {e : Expr} {T : Ty} (hD : DerivesWf LifeCtx.empty [] e T)
    (hT : PlainTy T) :
    ∃ v : Val, LocFree v.1 ∧ Steps Adequacy.emptyMem e Adequacy.emptyMem (.val v) ∧
      ∀ (μ μ' : Heap) (w : Val), Steps μ e μ' w.1 → w = v := by
  obtain ⟨v, hlf, hrun, hfresh, -⟩ := closed_pure hD hT
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  obtain ⟨μB, vB, hB⟩ := freshRunsExistClosed e T hD [] PMap.empty PMap.empty [] _
    Fig16.LogRel.hash_empty (ResU.comp_empty_right _) TW.empty htg Fig16.BoLo.lower_empty
  obtain rfl := hfresh _ _ _ hB
  refine ⟨vB, hlf, hrun, fun μ μ' w h => ?_⟩
  exact fresh_run_local_eq (μ₁ := Adequacy.emptyMem) (fun x _ hx => absurd rfl hx) hB h hlf

/-- **Fresh runs exist for the pure fragment**, its arguments in the relation at the fresh
runs. -/
def FreshRunsExistPureF : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty), PureTyping Δ Γ e T →
    ∀ (δ : LSub) (γ : List Val) (ls : List SRec) (ρ ρf fρ : WRes)
      (ps : List FrameRec) (μ : Heap), Δ.Models δ → gDenXR freshRel ls δ Γ γ ρ →
      ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → TW fρ ps (rsOf ls) → Tagged fρ ps ls →
      ResU.Lower fρ μ → ∃ (μ' : Heap) (v : Val), FreshRun μ (LogRel.substAll γ e) μ' v.1

theorem freshRunsExistPureF : FreshRunsExistPureF := by
  intro Δ Γ e T hP δ γ ls ρ ρf fρ ps μ hδ hγ hf hc hT htg hμ
  obtain ⟨v, hrun, -, -⟩ := pure_exhibited (RR := freshRel) hP hδ hγ hf hc hT htg hμ []
  exact ⟨μ, v, FreshRunN.toFreshRun hrun⟩

/-- **The pure fragment, on every run.**  With the arguments in the relation at the fresh runs,
from the heap `μ` of every tagged typed world completing their resource: there is a fresh run
that gives `μ` back and returns a plain-data value `v`; every run of `γ(e)` from `μ` returns
`v`; and every run from any heap `μ₂` agreeing with `μ` on what `γ` reaches returns `v`. -/
theorem pure_result_every_run_fresh {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty}
    (hP : PureTyping Δ Γ e T) {δ : LSub} {γ : List Val} {ls : List SRec} {ρ : WRes}
    (hδ : Δ.Models δ) (hγ : gDenXR freshRel ls δ Γ γ ρ) {ρf fρ : WRes} {ps : List FrameRec}
    (hf : ResU.Hash ρf ρ) (hc : ResU.CompS ρf ρ fρ) (hT : TW fρ ps (rsOf ls))
    (htg : Tagged fρ ps ls) {μ : Heap} (hμ : ResU.Lower fρ μ) :
    ∃ v : Val, LocFree v.1 ∧ FreshRun μ (LogRel.substAll γ e) μ (.val v) ∧
      (∀ (μ' : Heap) (w : Val), Steps μ (LogRel.substAll γ e) μ' w.1 → w = v) ∧
      ∀ (μ₂ μ₂' : Heap) (w : Val),
        (∀ x, Reach μ (ArgLocs γ) x → μ x ≠ none → μ₂ x = μ x) →
        Steps μ₂ (LogRel.substAll γ e) μ₂' w.1 → w = v := by
  obtain ⟨v, hrun, hlf, -⟩ := pure_exhibited (RR := freshRel) hP hδ hγ hf hc hT htg hμ []
  have hB := FreshRunN.toFreshRun hrun
  have hagr : ∀ (μ₂ : Heap),
      (∀ x, Reach μ (ArgLocs γ) x → μ x ≠ none → μ₂ x = μ x) →
      ∀ x, Reach μ (fun ℓ => (LogRel.substAll γ e).Occ ℓ) x → μ x ≠ none → μ₂ x = μ x :=
    fun μ₂ hag x hx =>
      hag x (Reach.mono (fun _ o => occ_substAll_of_locFree (derivesWf_locFree hP.derives) o) hx)
  refine ⟨v, hlf, hB, fun μ' w h => ?_, fun μ₂ μ₂' w hag h => ?_⟩
  · exact fresh_run_local_eq (hagr μ fun _ _ _ => rfl) hB h hlf
  · exact fresh_run_local_eq (hagr μ₂ hag) hB h hlf

end BoCa.Purity

end
