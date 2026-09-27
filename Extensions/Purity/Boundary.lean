import Purity.Pure
import Support.LogicalRelation.Compatibility
import Support.Model.Empty
import Support.Model.Entailments
import Support.Model.Singletons
import Support.Model.UpdateSymmetry
import Support.TypedWorld.Invariant

/-!
# Purity — the boundary: the semantic judgment alone does not bound what a program reads

`Read.lean` proves that every run of a program `[TR]` p. 2 types reads only what its arguments
reach (`derivesWf_runIn`).  The same statement at the semantic judgment `SemX` — the conclusion
of the Fundamental Property — does not hold.

* `ReadFootprintSyn`: from every tagged typed world completing the empty resource, a closed
  program of plain-data type that `DerivesWf` types has a run to a value that touches only
  locations it allocated itself.  Proved (`readFootprintSyn`).
* `ReadFootprintSem`: the same, for a closed program `SemX` types.  It does not hold
  (`not_readFootprintSem`), at `peek k`.

`peek k = let x = alloc () in ((λ_. ()) (load k); free x)` returns `()` and gives the heap back.
It satisfies `SemX` at `∅; ∅ ⊨ peek k : 1` (`peek_sem`): in a world whose heap lacks `k` its run
allocates `k` itself and loads it; in a world whose heap holds `k` it allocates elsewhere and
loads the cell `k` of the frame.  In the world whose frame owns `k`, every run of `peek k` to a
value loads `k`, which the run did not allocate.

Two features of `wp` meet here: a load leaves no trace in the post-world, so `↭` constrains
what a run changes and never what it reads; and `wp` exhibits a run per world, whose `alloc↦`
may pick a location that depends on the frame.  `peek k` mentions the location `k`, and no
typing rule types a location; that is the difference `derivesWf_locFree` records.

`peek k`'s *result* does not depend on the frame; what this bounds is the read footprint.
Whether the semantic judgment alone bounds the result of a plain-data program is not settled
here: not derived, and no obstruction verified.

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

/-! ### The two statements -/

/-- **The read footprint at the syntactic judgment**: from every tagged typed world completing
`∅`, a closed program of plain-data type has a run to a value that touches only locations it
allocated itself. -/
def ReadFootprintSyn : Prop :=
  ∀ (e : Expr) (T : Ty), PlainTy T → DerivesWf LifeCtx.empty ([] : Ctx Ty) e T →
    ∀ (ρf fρ : WRes) (ps : List FrameRec) (μ : Heap),
      ResU.Hash ρf PMap.empty → ResU.CompS ρf PMap.empty fρ → TW fρ ps (rsOf []) →
      Tagged fρ ps [] → ResU.Lower fρ μ →
      ∃ (μ' : Heap) (v : Val), RunIn (fun _ => False) μ e μ' (.val v)

/-- **The read footprint at the semantic judgment**: `ReadFootprintSyn` with `SemX` in place of
`DerivesWf`. -/
def ReadFootprintSem : Prop :=
  ∀ (e : Expr) (T : Ty), PlainTy T → SemX LifeCtx.empty ([] : Ctx Ty) e T →
    ∀ (ρf fρ : WRes) (ps : List FrameRec) (μ : Heap),
      ResU.Hash ρf PMap.empty → ResU.CompS ρf PMap.empty fρ → TW fρ ps (rsOf []) →
      Tagged fρ ps [] → ResU.Lower fρ μ →
      ∃ (μ' : Heap) (v : Val), RunIn (fun _ => False) μ e μ' (.val v)

theorem reach_nil {μ : Heap} {ℓ : Loc} (h : Reach μ (ArgLocs []) ℓ) : False := by
  induction h with
  | base h => obtain ⟨v, hv, -⟩ := h; simp at hv
  | step _ _ _ ih => exact ih

theorem RunIn.mono {S S' : Loc → Prop} (hS : ∀ ℓ, S ℓ → S' ℓ) {μ μ' : Heap} {e e' : Expr}
    (h : RunIn S μ e μ' e') : RunIn S' μ e μ' e' := by
  induction h generalizing S' with
  | refl => exact .refl _ _ _
  | more K a a' he he₁ hh ht _ ih =>
      refine .more K a a' he he₁ hh (fun ℓ h => hS ℓ (ht ℓ h)) (ih fun ℓ h => ?_)
      rcases h with h | h
      · exact Or.inl (hS ℓ h)
      · exact Or.inr h

/-- **`ReadFootprintSyn` holds.** -/
theorem readFootprintSyn : ReadFootprintSyn := by
  intro e T hT hD ρf fρ ps μ hf hc hTW htg hμ
  have hP : PureTyping LifeCtx.empty [] e T :=
    ⟨hD, ok_empty, fun s hs => absurd hs (by simp), fun s hs => absurd hs (by simp), hT⟩
  obtain ⟨v, hrun, -, -⟩ := pure_exhibited (RR := stepsRel) hP Adequacy.models_empty (gDenX_nil [] LSub.empty)
    hf hc hTW htg hμ ()
  have hsub : LogRel.substAll [] e = e := by rw [LogRel.substAll, Adequacy.psub_nil]
  refine ⟨μ, v, ?_⟩
  have := derivesWf_runIn hD [] hrun
  rw [hsub] at this
  exact this.mono fun ℓ h => reach_nil h

/-! ### `peek k` -/

/-- `alloc e`. -/
def allocE (e : Expr) : Expr := .app (.val (.prim .alloc)) e
/-- `free e`. -/
def freeE (e : Expr) : Expr := .app (.val (.prim .free)) e
/-- `load e`. -/
def loadE (e : Expr) : Expr := .app (.val (.prim .load)) e

/-- `peek k = let x = alloc () in ((λ_. ()) (load k); free x)`. -/
def peekBody (k : Loc) : Expr :=
  .seq (.app (.val (.lam unit')) (loadE (.val (.loc k)))) (freeE (.var 0))

def peek (k : Loc) : Expr := elet (allocE unit') (peekBody k)

theorem peekBody_subst (k l : Loc) :
    (peekBody k).subst 0 (Val.loc l) =
      .seq (.app (.val (.lam unit')) (loadE (.val (.loc k)))) (freeE (.val (.loc l))) := by
  simp [peekBody, Expr.subst, loadE, freeE, unit', Expr.val, Val.lam, Val.loc, Val.unit,
    Val.prim]

theorem steps_head {μ μ' : Heap} {a a' : Expr} (h : Head μ a μ' a') : Steps μ a μ' a' :=
  .one (Step1.head h)

/-- The run of `peek k` that allocates `l`. -/
theorem peek_runs {μ : Heap} {k l : Loc} (hl : μ l = none) {w : Val}
    (hk : BoLo.Heap.upd μ l .unit k = some w) : Steps μ (peek k) μ (.val .unit) := by
  have hfree : (BoLo.Heap.upd μ l Val.unit).del l = μ := by
    funext x
    by_cases e : x = l
    · subst e; rw [BoLo.Heap.del_same, hl]
    · rw [BoLo.Heap.del_other e, BoLo.Heap.upd_other e]
  -- `alloc ()`
  refine .more (μ₁ := BoLo.Heap.upd μ l .unit)
    (e₁ := .app (.val (.lam (peekBody k))) (.val (.loc l)))
    ⟨.appR (.val (.lam (peekBody k))) .hole, _, _, rfl, rfl, Head.alloc μ .unit l hl⟩ ?_
  -- `β`
  refine .more (μ₁ := BoLo.Heap.upd μ l .unit) (e₁ := (peekBody k).subst 0 (Val.loc l))
    (Step1.head (Head.beta _ (peekBody k) (Val.loc l))) ?_
  rw [peekBody_subst]
  -- `load k`
  refine .more (μ₁ := BoLo.Heap.upd μ l .unit)
    (e₁ := .seq (.app (.val (.lam unit')) (.val w)) (freeE (.val (.loc l))))
    ⟨.seq (.appR (.val (.lam unit')) .hole) (freeE (.val (.loc l))), _, _, rfl, rfl,
      Head.load _ k w hk⟩ ?_
  -- `(λ_. ()) w`
  refine .more (μ₁ := BoLo.Heap.upd μ l .unit) (e₁ := .seq unit' (freeE (.val (.loc l))))
    ⟨.seq .hole (freeE (.val (.loc l))), _, _, rfl, rfl, Head.beta _ unit' w⟩ ?_
  -- `(); free l`
  refine .more (μ₁ := BoLo.Heap.upd μ l .unit) (e₁ := freeE (.val (.loc l)))
    (Step1.head (Head.seq _ _)) ?_
  -- `free l`
  have := steps_head (Head.free (BoLo.Heap.upd μ l Val.unit) l Val.unit (BoLo.Heap.upd_same _ _ _))
  rwa [hfree] at this

/-- The heap of a world is finite. -/
theorem lower_finite {Z : WRes} {μ : Heap} (hμ : ResU.Lower Z μ) :
    ∃ d : List Loc, ∀ l, μ l ≠ none → l ∈ d := by
  obtain ⟨σ, -, hval⟩ := hμ
  obtain ⟨d, hd⟩ := σ.finite
  exact ⟨d, fun l hl => hd l fun h => hl (by rw [hval l, h]; rfl)⟩

/-- A term that runs from every heap of every world completing `ρ` back to that heap satisfies
`wpTS` at every post-condition holding of `ρ`. -/
theorem wpTS_restore {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp} {ρ : WRes}
    {v : Val}
    (hrun : ∀ ρf fρ μ, ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → ResU.Lower fρ μ →
      Steps μ e μ (.val v))
    (hQ : Q ls v ρ) : wpTS ls e Q ρ := by
  intro ρf fρ ps hf hc hT htg _
  obtain ⟨μ, hμ⟩ := lower_of_hash hf hc
  exact ⟨ρ, PMap.empty, fρ, fρ, ρ, v, μ, μ, ps, ls, ResU.hash_symm hf, hc,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hf hc)), hμ,
    ResU.comp_empty_right fρ, hμ, hrun ρf fρ μ hf hc hμ, ResU.comp_empty_right ρ,
    (ResU.updV_self_iff ρ).mpr (hash_valid hf).2, noOwn_empty, hT, htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, hQ⟩

theorem substAll_peek (γ : List Val) (k : Loc) : LogRel.substAll γ (peek k) = peek k := by
  simp [LogRel.substAll, peek, peekBody, elet, allocE, freeE, loadE, unit', Expr.psub,
    Expr.val, Val.lam, Val.loc, Val.unit, Val.prim]

/-- **`peek k` is in the semantic relation** at `∅; ∅ ⊨ peek k : 1`. -/
theorem peek_sem (k : Loc) : SemX LifeCtx.empty ([] : Ctx Ty) (peek k) .unit := by
  intro δ γ ls ρ _ hγ
  obtain ⟨ρ₁, ρ₂, hc, ⟨rfl, -⟩, h₂⟩ := hγ
  have hρ₂ : ρ₂ = PMap.empty := by
    cases γ with
    | nil => exact h₂.1
    | cons _ _ => exact h₂.1
  subst hρ₂
  obtain rfl : (PMap.empty : WRes) = ρ := ResU.eq_of_comp_empty_left hc
  rw [substAll_peek]
  refine wpTS_restore (v := .unit) (fun ρf fρ μ _ _ hμ => ?_) ⟨rfl, rfl⟩
  by_cases hk : μ k = none
  · exact peek_runs hk (w := .unit) (BoLo.Heap.upd_same _ _ _)
  · obtain ⟨d, hd⟩ := lower_finite hμ
    obtain ⟨l, hl⟩ := loc_infinite d
    have hμl : μ l = none := by by_contra h; exact hl (hd l h)
    have hne : k ≠ l := fun e => hk (e ▸ hμl)
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hk
    exact peek_runs hμl (w := w) (by rw [BoLo.Heap.upd_other hne, hw])

/-! ### Every run of `peek 0` from the world whose frame owns `0` loads `0` -/

/-- A run from `K[a]`, `a` a redex, to a value takes a head step of `a` first. -/
theorem runIn_head_inv {S : Loc → Prop} {μ μ' : Heap} {K : Kont} {a e' : Expr}
    {μ₀ μ₀' : Heap} {a₀' : Expr} (h₀ : Head μ₀ a μ₀' a₀') (h : RunIn S μ (K.plug a) μ' e')
    (hv : IsVal e') :
    ∃ μ₁ a₁, Head μ a μ₁ a₁ ∧ (∀ ℓ, Touch a ℓ → S ℓ) ∧
      RunIn (Grow S μ μ₁) μ₁ (K.plug a₁) μ' e' := by
  cases h with
  | refl => exact absurd (K.isVal_of_plug hv) h₀.not_isVal
  | more K' b b' he he₁ hh ht t =>
      obtain ⟨K'', hb, rfl⟩ := plug_decomp hh K K' h₀.not_isVal he
      obtain rfl : K'' = .hole := head_plug h₀ K'' hh.not_isVal hb
      simp only [Kont.plug] at hb
      subst hb
      subst he₁
      rw [BoLo.Kont.plug_comp] at t
      exact ⟨_, _, hh, ht, t⟩

/-- The world whose frame owns `k`, holding `()`, and whose computation's resource is `∅`. -/
theorem frame_world (k : Loc) :
    ResU.Hash (ResU.single k (CellU.ownOf Val.unit)) (PMap.empty : WRes) ∧
      ResU.CompS (ResU.single k (CellU.ownOf Val.unit)) PMap.empty
        (ResU.single k (CellU.ownOf Val.unit)) ∧
      TW (ResU.single k (CellU.ownOf Val.unit)) [] (rsOf []) ∧
      Tagged (ResU.single k (CellU.ownOf Val.unit)) [] [] ∧
      ResU.Lower (ResU.single k (CellU.ownOf Val.unit))
        (BoLo.Heap.upd (fun _ => none) k Val.unit) := by
  have hv := ResU.valid_single_own k Val.unit
  have hc : ResU.CompS PMap.empty (ResU.single k (CellU.ownOf Val.unit))
      (ResU.single k (CellU.ownOf Val.unit)) := ResU.comp_empty_left _
  obtain ⟨σ', hσ', -, hlow⟩ := hash_compS_own (ResU.comp_empty_left PMap.empty)
    Fig16.BoLo.lower_empty rfl hc
  cases ResU.CompS.functional hσ' (ResU.comp_empty_left _)
  exact ⟨ResU.hash_empty_right hv, ResU.comp_empty_right _,
    .alloc .empty Fig16.BoLo.lower_empty rfl (ResU.comp_empty_left _) hv,
    fun x hx => absurd hx (by simp), hlow⟩

/-- **`ReadFootprintSem` does not hold**, at `peek 0`: from the world whose frame owns `0`, every
run of `peek 0` to a value loads `0`, which it did not allocate. -/
theorem not_readFootprintSem : ¬ ReadFootprintSem := by
  intro h
  obtain ⟨hf, hc, hT, htg, hμ⟩ := frame_world 0
  obtain ⟨μ', v, hrun⟩ := h (peek 0) .unit .unit (peek_sem 0) _ _ _ _ hf hc hT htg hμ
  -- the allocation
  obtain ⟨μ₁, a₁, hh₁, -, t₁⟩ := runIn_head_inv (K := .appR (.val (.lam (peekBody 0))) .hole)
    (a := allocE unit') (Head.alloc (fun _ => none) .unit 0 rfl) hrun v.2
  obtain ⟨l, hl, rfl, rfl⟩ := head_alloc_inv hh₁ (v := .unit) rfl
  have hl0 : l ≠ 0 := fun e => by subst e; simp at hl
  -- the application of the continuation
  obtain ⟨μ₂, a₂, hh₂, -, t₂⟩ := runIn_head_inv (K := .hole)
    (Head.beta (fun _ => none) (peekBody 0) (Val.loc l)) t₁ v.2
  obtain ⟨rfl, rfl⟩ := head_det (Head.beta _ _ (Val.loc l)) hh₂
    (by intro w e; simp [allocRedex, Expr.val, Val.lam, Val.loc] at e)
  rw [peekBody_subst] at t₂
  -- the load of the frame's cell
  obtain ⟨-, -, -, ht, -⟩ := runIn_head_inv
    (K := .seq (.appR (.val (.lam unit')) .hole) (freeE (.val (.loc l))))
    (a := loadE (.val (.loc 0)))
    (Head.load (BoLo.Heap.upd (fun _ => none) 0 .unit) 0 .unit (BoLo.Heap.upd_same _ _ _))
    t₂ v.2
  rcases ht 0 (.load 0) with ((h0 | ⟨h0, -⟩) | ⟨h0, -⟩)
  · exact h0
  · simp [BoLo.Heap.upd] at h0
  · rw [BoLo.Heap.upd_other (Ne.symm hl0)] at h0
    simp [BoLo.Heap.upd] at h0

end BoCa.Purity

end
