import Purity.Invariant

/-!
# Purity — `FreshRunsExistSyn` does not hold as stated: closing values are semantic

`FreshRunsExistSyn` (`FreshExistence.lean`) closes a `DerivesWf` program by values `γ` in the
*semantic* relation.  A value at a function type there is any closure the relation admits,
typed or not.  `f () ` with `f : 1 ⊸ 1` is well typed, and `λ_. staleL` is in the relation at
`1 ⊸ 1` (`staleClosure_vP`); so `(λ_. staleL) ()` is an instance of the statement, and from
the empty world it has no fresh run (`not_freshRunsExistSyn`).

The statement that remains open restricts what the program can reach to syntactically typed
code.  Two forms of it are stated:

* `FreshRunsExistClosed`: a closed program `∅; ∅ ⊢ e : T` from every tagged typed world
  completing `∅`.  The frame's cells, whatever closures they hold, are unreachable from a term
  that names no location.
* `FreshRunsExistPure`: a program of the pure fragment.  Its arguments are plain data and
  `Imm` borrows; a closure behind an `Imm` borrow is reachable but reaches the program only at
  `Unk` (`[TR]` p. 3's `Imm̲`), and cannot be called.

Neither is derived; no obstruction to either is verified.  `pure_result_every_run` records what
the second would give.

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

theorem staleL_subst (j : Nat) (v : Val) : staleL.subst j v = staleL := by
  simp [staleL, staleBody, staleInner, staleTail, elet, allocE, freeE, loadE, unit', Expr.subst,
    Expr.val, Val.lam, Val.unit, Val.prim, Val.inj₁]

/-- `λ_. staleL`. -/
def staleClosure : Val := Val.lam staleL

/-- `λ_. staleL` is in the relation at `1 ⊸ 1`, at `∅`. -/
theorem staleClosure_vP (ls : List SRec) (δ : LSub) :
    vP (.lolli .unit .unit) ls δ staleClosure PMap.empty := by
  intro ls' _ v' ρ₁ ρ₂ h₁ hc
  obtain ⟨rfl, rfl⟩ := h₁
  obtain rfl : (PMap.empty : WRes) = ρ₂ := ResU.eq_of_comp_empty_left hc
  refine wpTS_restore (v := .unit) (fun ρf fρ μ _ _ hμ => ?_) ⟨rfl, rfl⟩
  obtain ⟨d, hd⟩ := lower_finite hμ
  obtain ⟨l, hl⟩ := loc_infinite d
  refine .more (Step1.head (Head.beta μ staleL Val.unit)) ?_
  rw [staleL_subst]
  exact staleL_runs (l := l) (by by_contra h; exact hl (hd l h))

/-- `f ()`, at `f : 1 ⊸ 1`. -/
def callF : Expr := .app (.var 0) (.val .unit)

theorem d_callF : DerivesWf LifeCtx.empty [⟨.lolli .unit .unit, true⟩] callF .unit :=
  .lolliE (.right .nil) (.unitI (.cons .nil)) (.var (.here .nil))

/-- **`FreshRunsExistSyn` does not hold**, at `f ()` closed by `f = λ_. staleL`. -/
theorem not_freshRunsExistSyn : ¬ FreshRunsExistSyn := by
  intro h
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  have hγ : gDenX [] LSub.empty [⟨.lolli .unit .unit, true⟩] [staleClosure] PMap.empty := by
    refine gDenX_mk (by simp [Ctx.LiveWithin]) ?_
    simp only [gSepX, gSepXR, if_pos]
    exact ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, staleClosure_vP [] LSub.empty,
      ⟨rfl, trivial⟩⟩
  obtain ⟨μ', v, hR⟩ := h LifeCtx.empty _ callF .unit d_callF ok_empty
    (fun s hs _ => by simp at hs; subst hs; rfl) LSub.empty [staleClosure] [] PMap.empty
    PMap.empty PMap.empty [] (fun _ => none) Adequacy.models_empty hγ
    Fig16.LogRel.hash_empty (ResU.comp_empty_right _) TW.empty htg Fig16.BoLo.lower_empty
  have hsub : LogRel.substAll [staleClosure] callF = .app (.val staleClosure) (.val .unit) := by
    simp [LogRel.substAll, callF, Expr.psub, staleClosure, Val.shift, Expr.shift, staleL,
      staleBody, staleInner, staleTail, elet, allocE, freeE, loadE, unit', Expr.val, Val.lam,
      Val.unit, Val.prim, Val.inj₁]
  rw [hsub] at hR
  have h := fresh_peel_det (K := .hole) hR rfl (Head.beta _ staleL Val.unit)
    (by intro w e; simp [allocRedex, staleClosure, Expr.val, Val.lam, Val.unit] at e)
  simp only [Kont.plug] at h
  rw [staleL_subst] at h
  exact staleL_no_fresh h

/-! ### The forms that remain open -/

/-- **Fresh runs exist for closed well-typed programs.**  Not derived. -/
def FreshRunsExistClosed : Prop :=
  ∀ (e : Expr) (T : Ty), DerivesWf LifeCtx.empty ([] : Ctx Ty) e T →
    ∀ (ls : List SRec) (ρf fρ : WRes) (ps : List FrameRec) (μ : Heap),
      ResU.Hash ρf PMap.empty → ResU.CompS ρf PMap.empty fρ → TW fρ ps (rsOf ls) →
      Tagged fρ ps ls → ResU.Lower fρ μ → ∃ (μ' : Heap) (v : Val), FreshRun μ e μ' v.1

/-- **Fresh runs exist for the pure fragment.**  Not derived. -/
def FreshRunsExistPure : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty), PureTyping Δ Γ e T →
    ∀ (δ : LSub) (γ : List Val) (ls : List SRec) (ρ ρf fρ : WRes)
      (ps : List FrameRec) (μ : Heap), Δ.Models δ → gDenX ls δ Γ γ ρ →
      ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → TW fρ ps (rsOf ls) → Tagged fρ ps ls →
      ResU.Lower fρ μ → ∃ (μ' : Heap) (v : Val), FreshRun μ (LogRel.substAll γ e) μ' v.1

/-- **What `FreshRunsExistPure` would buy**: every run of a program of the pure fragment, from
the world's heap or from any heap agreeing on what the arguments reach, returns the exhibited
value. -/
theorem pure_result_every_run (hex : FreshRunsExistPure) {Δ : LifeCtx} {Γ : Ctx Ty}
    {e : Expr} {T : Ty} (hP : PureTyping Δ Γ e T) {δ : LSub} {γ : List Val} {ls : List SRec}
    {ρ : WRes} (hδ : Δ.Models δ) (hγ : gDenX ls δ Γ γ ρ) {ρf fρ : WRes} {ps : List FrameRec}
    (hf : ResU.Hash ρf ρ) (hc : ResU.CompS ρf ρ fρ) (hT : TW fρ ps (rsOf ls))
    (htg : Tagged fρ ps ls) {μ : Heap} (hμ : ResU.Lower fρ μ) :
    ∃ v : Val, LocFree v.1 ∧ Steps μ (LogRel.substAll γ e) μ (.val v) ∧
      ∀ (μ₂ μ₂' : Heap) (w : Val),
        (∀ x, Reach μ (ArgLocs γ) x → μ x ≠ none → μ₂ x = μ x) →
        Steps μ₂ (LogRel.substAll γ e) μ₂' w.1 → w = v := by
  obtain ⟨v, hlf, -, hrun, hall⟩ := pure_result hP hδ hγ hf hc hT htg hμ
  obtain ⟨μ₁, w₁, hR⟩ := hex Δ Γ e T hP δ γ ls ρ ρf fρ ps μ hδ hγ hf hc hT htg hμ
  exact ⟨v, hlf, hrun, fun μ₂ μ₂' w hag h₂ => (hall μ₁ μ₂ μ₂' w₁ w hR hag h₂).2⟩

end BoCa.Purity

end
