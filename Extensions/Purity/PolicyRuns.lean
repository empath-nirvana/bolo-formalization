import Purity.Pure
import Purity.Closures

/-!
# Purity — every run under a policy

The Fundamental Property holds at every class of runs (`Typed.fundamentalR`,
docs/adjudications.md §12.74), in particular at the runs of any allocation policy
(`BoLo.PolRun`, `Typed.polRel`).  A policy makes the machine deterministic: a policy step is
the only one from its configuration (`polStep_det`), so a policy run to a value is the only one
(`polRun_det`).  Hence:

* `closed_policy_adequacy`: for every policy, the run of a closed program of type `1` from the
  empty memory ends at `()` and the empty memory, and every run under that policy that reaches
  a value is this run.  Adequacy (`[CONF]` Corollary 3.3) is its instance at "some run".
* `closed_policy_pure`: for a closed program of plain-data type, from the heap of every tagged
  typed world, the policy's run gives the heap back and returns a plain-data value; every run
  under the policy that reaches a value does the same.
* `pure_policy_heap`: the pure fragment's heap preservation, for the unique policy run.

What is not derived here: that runs under *different* policies, or from heaps that agree only on
what the arguments reach, return the same value.  That comparison is `Local.lean`'s, and needs
one of the runs fresh.  A policy sees only the memory; a fresh choice must also avoid the
locations the term names, and a choice that looks at the term is not preserved by plugging
into an evaluation context (`RunRel.plug`).  So `FreshRunsExistClosed` does not follow from
the policy results, and remains open.

`[about ours]`: an extension, not a transcription.
-/

noncomputable section

namespace BoCa.Purity
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Policy PolStep PolRun)
open BoCa.Fig16.LogRel.Typed
open BoCa.Lifetime (LifeCtx LSub)

/-- **A policy step is the only one from its configuration.** -/
theorem polStep_det {pol : Policy} {μ μ₁ μ₂ : Heap} {e e₁ e₂ : Expr}
    (h₁ : PolStep pol μ e μ₁ e₁) (h₂ : PolStep pol μ e μ₂ e₂) : μ₂ = μ₁ ∧ e₂ = e₁ := by
  obtain ⟨⟨K, a, a', rfl, rfl, hh₁⟩, hp₁⟩ := h₁
  obtain ⟨⟨K', b, b', hE, rfl, hh₂⟩, hp₂⟩ := h₂
  obtain ⟨K'', ha, rfl⟩ := plug_decomp hh₂ K K' hh₁.not_isVal hE
  obtain rfl : K'' = .hole := head_plug hh₁ K'' hh₂.not_isVal ha
  simp only [Kont.plug] at ha
  subst ha
  by_cases hal : ∃ v, a = allocRedex v
  · obtain ⟨v, rfl⟩ := hal
    obtain ⟨l₁, hl₁, rfl, rfl⟩ := head_alloc_inv hh₁ rfl
    obtain ⟨l₂, hl₂, rfl, rfl⟩ := head_alloc_inv hh₂ rfl
    have e₁ := hp₁ l₁ (by simp) hl₁
    have e₂ := hp₂ l₂ (by simp) hl₂
    rw [e₁, ← e₂]
    exact ⟨rfl, by rw [BoLo.Kont.plug_comp]; rfl⟩
  · push Not at hal
    obtain ⟨rfl, rfl⟩ := head_det hh₁ hh₂ hal
    exact ⟨rfl, by rw [BoLo.Kont.plug_comp]; rfl⟩

/-- **A policy run to a value is the only one.** -/
theorem polRun_det {pol : Policy} {μ μ₁ : Heap} {e e₁ : Expr} (h₁ : PolRun pol μ e μ₁ e₁) :
    ∀ {v₁ : Val} {μ₂ : Heap} {v₂ : Val}, e₁ = v₁.1 → PolRun pol μ e μ₂ v₂.1 →
      μ₂ = μ₁ ∧ v₂ = v₁ := by
  induction h₁ with
  | refl μ e =>
      intro v₁ μ₂ v₂ he h₂
      subst he
      exact steps_from_val h₂.toSteps
  | more hs _ ih =>
      intro v₁ μ₂ v₂ he h₂
      cases h₂ with
      | refl => exact absurd hs.1 (BoCa.BoLo.no_step_val (w := v₂))
      | more h t =>
          obtain ⟨rfl, rfl⟩ := polStep_det hs h
          exact ih he t

/-- **Adequacy under every policy, and uniqueness.**  For a closed program of type `1` and any
policy, the policy's run from the empty memory ends at `()` and the empty memory, and it is the
only run under the policy that reaches a value. -/
theorem closed_policy_adequacy {e : Expr} (hD : DerivesWf LifeCtx.empty [] e .unit)
    (pol : Policy) :
    PolRun pol Adequacy.emptyMem e Adequacy.emptyMem (.val .unit) ∧
      ∀ (μ' : Heap) (v : Val), PolRun pol Adequacy.emptyMem e μ' v.1 →
        μ' = Adequacy.emptyMem ∧ v = .unit :=
  ⟨adequacyPol pol e hD, fun _ _ h => polRun_det (adequacyPol pol e hD) rfl h⟩

/-- **A closed program of plain-data type, under every policy.**  From the heap `μ` of every
tagged typed world completing `∅`, the policy's run gives `μ` back and returns a plain-data
value, and every run under the policy that reaches a value is that run. -/
theorem closed_policy_pure {e : Expr} {T : Ty} (hD : DerivesWf LifeCtx.empty [] e T)
    (hT : PlainTy T) (pol : Policy) {ls : List SRec} {ρf fρ : WRes} {ps : List FrameRec}
    {μ : Heap} (hf : ResU.Hash ρf PMap.empty) (hc : ResU.CompS ρf PMap.empty fρ)
    (hTW : TW fρ ps (rsOf ls)) (htg : Tagged fρ ps ls) (hμ : ResU.Lower fρ μ) :
    ∃ v : Val, LocFree v.1 ∧ PolRun pol μ e μ (.val v) ∧
      ∀ (μ' : Heap) (w : Val), PolRun pol μ e μ' w.1 → μ' = μ ∧ w = v := by
  have hP : PureTyping LifeCtx.empty [] e T :=
    ⟨hD, ok_empty, fun s hs => absurd hs (by simp), fun s hs => absurd hs (by simp), hT⟩
  have hsub : LogRel.substAll [] e = e := by rw [LogRel.substAll, Adequacy.psub_nil]
  obtain ⟨v, hrun, hlf, -⟩ := pure_exhibited (RR := polRel pol) hP Adequacy.models_empty
    (gDenX_nil ls LSub.empty) hf hc hTW htg hμ
  rw [hsub] at hrun
  exact ⟨v, hlf, hrun, fun _ _ h => polRun_det hrun rfl h⟩

/-- **The pure fragment under a policy**: from every tagged typed world completing the
arguments' resource (in the relation at the policy's runs), the policy's run gives the heap
back and returns a plain-data value, and it is the only run under the policy that reaches a
value. -/
theorem pure_policy_heap {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty}
    (hP : PureTyping Δ Γ e T) (pol : Policy) {δ : LSub} {γ : List Val} {ls : List SRec}
    {ρ : WRes} (hδ : Δ.Models δ) (hγ : gDenXR (polRel pol) ls δ Γ γ ρ) {ρf fρ : WRes}
    {ps : List FrameRec} (hf : ResU.Hash ρf ρ) (hc : ResU.CompS ρf ρ fρ)
    (hT : TW fρ ps (rsOf ls)) (htg : Tagged fρ ps ls) {μ : Heap} (hμ : ResU.Lower fρ μ) :
    ∃ v : Val, LocFree v.1 ∧ PolRun pol μ (LogRel.substAll γ e) μ (.val v) ∧
      ∀ (μ' : Heap) (w : Val), PolRun pol μ (LogRel.substAll γ e) μ' w.1 → μ' = μ ∧ w = v := by
  obtain ⟨v, hrun, hlf, -⟩ := pure_exhibited (RR := polRel pol) hP hδ hγ hf hc hT htg hμ
  exact ⟨v, hlf, hrun, fun _ _ h => polRun_det hrun rfl h⟩

end BoCa.Purity

end
