import Purity.FreshExistence

/-!
# Purity — a location-free term in the semantic relation with no fresh run

`FreshExistence.lean` refutes fresh-run existence at `SemX` with `peek 0`, a term that names a
location.  A nominal argument would exclude such terms: the model compares locations only by
equality, so the relation should be invariant under permutations of locations, and a term
that names no location (`LocFree`, which `derivesWf_locFree` gives every `DerivesWf` term) is
fixed by every permutation.

That exclusion is not enough.  `staleL` names no location and is in the semantic relation at
`∅; ∅ ⊨ staleL : 1` (`staleL_sem`), yet from the empty world it has no fresh run to a value
(`staleL_no_fresh`).  So `FreshRunsExistSemLocFree` — fresh runs exist for every location-free
term of the semantic relation — does not hold (`not_freshRunsExistSemLocFree`).

    staleL = let x = alloc () in free x;
             let y = alloc (inj₁ ()) in (λ_. ()) (load x); case (free y) {_ ⇒ () | _ ⇒ ()}

It reads `x` after freeing it.  The run that reallocates `x`'s location for `y` reads
`inj₁ ()` there and gives the heap back, from every world, so `wp` holds.  A fresh run may not
reallocate that location, since the term still names it, and then `load x` is stuck.

Consequence for the nominal route.  Every fact such a proof uses about the program — its
membership in the relation, and that it names no location — holds of `staleL`, and so does
every fact about the model, which does not depend on the program.  An argument from those
facts alone would prove `FreshRunsExistSemLocFree`.  A proof of fresh-run existence for well-typed programs (`FreshRunsExistClosed`,
`FreshRunsExistPure`, `Closures.lean`) has to use
more of `DerivesWf` than `derivesWf_locFree`: here, that `staleL` uses `x` twice.

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

/-- **Fresh runs exist for every location-free term of the semantic relation.** -/
def FreshRunsExistSemLocFree : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty), LocFree e → SemX Δ Γ e T →
    ∀ (δ : LSub) (γ : List Val) (ls : List SRec) (ρ ρf fρ : WRes)
      (ps : List FrameRec) (μ : Heap), Δ.Models δ → gDenX ls δ Γ γ ρ →
      ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → TW fρ ps (rsOf ls) → Tagged fρ ps ls →
      ResU.Lower fρ μ → ∃ (μ' : Heap) (v : Val), FreshRun μ (LogRel.substAll γ e) μ' v.1

/-! ### The term -/

/-- `(λ_. ()) (load x); case (free y) {_ ⇒ () | _ ⇒ ()}`, with `y` at index 0. -/
def staleTail (x : Expr) : Expr :=
  .seq (.app (.val (.lam unit')) (loadE x)) (.case (freeE (.var 0)) unit' unit')

/-- `let y = alloc (inj₁ ()) in staleTail x`. -/
def staleInner (x : Expr) : Expr := elet (allocE (.val (.inj₁ .unit))) (staleTail x)

/-- `free x; staleInner x`, with `x` at index 0. -/
def staleBody : Expr := .seq (freeE (.var 0)) (staleInner (.var 1))

def staleL : Expr := elet (allocE unit') staleBody

theorem staleL_locFree : LocFree staleL := by
  intro ℓ o
  simp [staleL, staleBody, staleInner, staleTail, elet, allocE, freeE, loadE, unit', Expr.Occ,
    Expr.val, Val.lam, Val.unit, Val.prim, Val.inj₁] at o

theorem staleBody_subst (l : Loc) :
    staleBody.subst 0 (Val.loc l) = .seq (freeE (.val (.loc l))) (staleInner (.val (.loc l))) := by
  simp [staleBody, staleInner, staleTail, elet, allocE, freeE, loadE, unit', Expr.subst,
    Expr.shift, Val.shift, Expr.val, Val.lam, Val.unit, Val.prim, Val.inj₁, Val.loc]

theorem staleTail_subst (l l' : Loc) :
    (staleTail (.val (.loc l))).subst 0 (Val.loc l') =
      .seq (.app (.val (.lam unit')) (loadE (.val (.loc l))))
        (.case (freeE (.val (.loc l'))) unit' unit') := by
  simp [staleTail, freeE, loadE, unit', Expr.subst, Expr.val, Val.lam, Val.unit, Val.prim,
    Val.loc]

/-- The run that allocates `x` and `y` at the same location `l`, and gives the heap back. -/
theorem staleL_runs {μ : Heap} {l : Loc} (hl : μ l = none) : Steps μ staleL μ (.val .unit) := by
  have hdel : (μ.upd l Val.unit).del l = μ := by
    funext x
    by_cases e : x = l
    · subst e; rw [BoLo.Heap.del_same, hl]
    · rw [BoLo.Heap.del_other e, BoLo.Heap.upd_other e]
  have hdel' : (μ.upd l (Val.inj₁ Val.unit)).del l = μ := by
    funext x
    by_cases e : x = l
    · subst e; rw [BoLo.Heap.del_same, hl]
    · rw [BoLo.Heap.del_other e, BoLo.Heap.upd_other e]
  -- `alloc ()`
  refine .more (μ₁ := μ.upd l .unit) (e₁ := .app (.val (.lam staleBody)) (.val (.loc l)))
    ⟨.appR (.val (.lam staleBody)) .hole, _, _, rfl, rfl, Head.alloc μ .unit l hl⟩ ?_
  refine .more (μ₁ := μ.upd l .unit) (e₁ := staleBody.subst 0 (Val.loc l))
    (Step1.head (Head.beta _ staleBody (Val.loc l))) ?_
  rw [staleBody_subst]
  -- `free x`
  refine .more (μ₁ := μ) (e₁ := .seq (.val .unit) (staleInner (.val (.loc l))))
    ⟨.seq .hole (staleInner (.val (.loc l))), _, _, rfl, rfl, by
      have := Head.free (μ.upd l Val.unit) l Val.unit (BoLo.Heap.upd_same _ _ _)
      rwa [hdel] at this⟩ ?_
  refine .more (μ₁ := μ) (e₁ := staleInner (.val (.loc l))) (Step1.head (Head.seq _ _)) ?_
  -- `alloc (inj₁ ())`, at `l` again
  refine .more (μ₁ := μ.upd l (.inj₁ .unit))
    (e₁ := .app (.val (.lam (staleTail (.val (.loc l))))) (.val (.loc l)))
    ⟨.appR (.val (.lam (staleTail (.val (.loc l))))) .hole, _, _, rfl, rfl,
      Head.alloc μ (.inj₁ .unit) l hl⟩ ?_
  refine .more (μ₁ := μ.upd l (.inj₁ .unit))
    (e₁ := (staleTail (.val (.loc l))).subst 0 (Val.loc l))
    (Step1.head (Head.beta _ _ (Val.loc l))) ?_
  rw [staleTail_subst]
  -- `load x`, reading `y`'s cell
  refine .more (μ₁ := μ.upd l (.inj₁ .unit))
    (e₁ := .seq (.app (.val (.lam unit')) (.val (.inj₁ .unit)))
      (.case (freeE (.val (.loc l))) unit' unit'))
    ⟨.seq (.appR (.val (.lam unit')) .hole) (.case (freeE (.val (.loc l))) unit' unit'), _, _,
      rfl, rfl, Head.load _ l (.inj₁ .unit) (BoLo.Heap.upd_same _ _ _)⟩ ?_
  refine .more (μ₁ := μ.upd l (.inj₁ .unit))
    (e₁ := .seq unit' (.case (freeE (.val (.loc l))) unit' unit'))
    ⟨.seq .hole (.case (freeE (.val (.loc l))) unit' unit'), _, _, rfl, rfl,
      Head.beta _ unit' (.inj₁ .unit)⟩ ?_
  refine .more (μ₁ := μ.upd l (.inj₁ .unit)) (e₁ := .case (freeE (.val (.loc l))) unit' unit')
    (Step1.head (Head.seq _ _)) ?_
  -- `free y`
  refine .more (μ₁ := μ) (e₁ := .case (.val (.inj₁ .unit)) unit' unit')
    ⟨.case .hole unit' unit', _, _, rfl, rfl, by
      have := Head.free (μ.upd l (Val.inj₁ Val.unit)) l (Val.inj₁ Val.unit)
        (BoLo.Heap.upd_same _ _ _)
      rwa [hdel'] at this⟩ ?_
  exact .one (Step1.head (Head.case₁ μ Val.unit unit' unit'))

theorem substAll_staleL (γ : List Val) : LogRel.substAll γ staleL = staleL := by
  simp [LogRel.substAll, staleL, staleBody, staleInner, staleTail, elet, allocE, freeE, loadE,
    unit', Expr.psub, Expr.val, Val.lam, Val.unit, Val.prim, Val.inj₁]

/-- **`staleL` is in the semantic relation** at `∅; ∅ ⊨ staleL : 1`. -/
theorem staleL_sem : SemX LifeCtx.empty ([] : Ctx Ty) staleL .unit := by
  intro δ γ ls ρ _ hγ
  obtain ⟨ρ₁, ρ₂, hc, ⟨rfl, -⟩, h₂⟩ := hγ
  have hρ₂ : ρ₂ = PMap.empty := by
    cases γ with
    | nil => exact h₂.1
    | cons _ _ => exact h₂.1
  subst hρ₂
  obtain rfl : (PMap.empty : WRes) = ρ := ResU.eq_of_comp_empty_left hc
  rw [substAll_staleL]
  refine wpTS_restore (v := .unit) (fun ρf fρ μ _ _ hμ => ?_) ⟨rfl, rfl⟩
  obtain ⟨d, hd⟩ := lower_finite hμ
  obtain ⟨l, hl⟩ := loc_infinite d
  exact staleL_runs (l := l) (by by_contra h; exact hl (hd l h))

/-! ### No fresh run from the empty world -/

/-- A fresh run through a step that is not an allocation continues from that step's result. -/
theorem fresh_peel_det {μ μ' μ₀ : Heap} {e a a₀ : Expr} {K : Kont} {v : Val}
    (h : FreshRun μ e μ' v.1) (he : e = K.plug a) (hh : Head μ a μ₀ a₀)
    (hna : ∀ w : Val, a ≠ allocRedex w) : FreshRun μ₀ (K.plug a₀) μ' v.1 := by
  cases h with
  | refl => exact absurd (K.isVal_of_plug (he ▸ v.2)) hh.not_isVal
  | more hs t =>
      obtain ⟨rfl, rfl⟩ := step1_det ⟨K, a, a₀, he, rfl, hh, hna⟩ hs.1
      exact t

/-- A fresh run through an allocation picks a location the configuration does not name. -/
theorem fresh_peel_alloc {μ μ' : Heap} {e : Expr} {K : Kont} {w v : Val}
    (h : FreshRun μ e μ' v.1) (he : e = K.plug (allocRedex w)) :
    ∃ l, μ l = none ∧ ¬ Named μ e l ∧ FreshRun (μ.upd l w) (K.plug (.val (.loc l))) μ' v.1 := by
  have h₀ : Head (fun _ => none) (allocRedex w) (BoLo.Heap.upd (fun _ => none) 0 w)
      (.val (.loc 0)) := Head.alloc _ w 0 rfl
  cases h with
  | refl => exact absurd (K.isVal_of_plug (he ▸ v.2)) h₀.not_isVal
  | more hs t =>
      obtain ⟨⟨K', b, b', hE, rfl, hh⟩, hfr⟩ := hs
      rw [he] at hE
      obtain ⟨K'', hb, rfl⟩ := plug_decomp hh K K' h₀.not_isVal hE
      obtain rfl : K'' = .hole := head_plug h₀ K'' hh.not_isVal hb
      simp only [Kont.plug] at hb
      subst hb
      obtain ⟨l, hl, rfl, rfl⟩ := head_alloc_inv hh (v := w) rfl
      refine ⟨l, hl, he ▸ hfr l (by simp) hl, ?_⟩
      rwa [BoLo.Kont.plug_comp] at t

/-- A fresh run cannot load a location the heap lacks. -/
theorem fresh_stuck_load {μ μ' : Heap} {K : Kont} {l : Loc} {v : Val} (hl : μ l = none)
    (h : FreshRun μ (K.plug (loadE (.val (.loc l)))) μ' v.1) : False := by
  generalize hE₀ : K.plug (loadE (.val (.loc l))) = E at h
  have h₀ : Head (BoLo.Heap.upd (fun _ => none) l Val.unit) (loadE (.val (.loc l)))
      (BoLo.Heap.upd (fun _ => none) l Val.unit) (.val Val.unit) :=
    Head.load _ l .unit (BoLo.Heap.upd_same _ _ _)
  cases h with
  | refl => exact h₀.not_isVal (K.isVal_of_plug (hE₀ ▸ v.2))
  | more hs _ =>
      obtain ⟨⟨K', b, b', hE, -, hh⟩, -⟩ := hs
      rw [← hE₀] at hE
      obtain ⟨K'', hb, rfl⟩ := plug_decomp hh K K' h₀.not_isVal hE
      obtain rfl : K'' = .hole := head_plug h₀ K'' hh.not_isVal hb
      simp only [Kont.plug] at hb
      subst hb
      cases hh with
      | load _ _ hw => rw [hl] at hw; cases hw

/-- **`staleL` has no fresh run to a value from the empty heap.** -/
theorem staleL_no_fresh {μ' : Heap} {v : Val} (h : FreshRun (fun _ => none) staleL μ' v.1) :
    False := by
  -- `alloc ()` at some `l`
  obtain ⟨l, -, -, h⟩ := fresh_peel_alloc (K := .appR (.val (.lam staleBody)) .hole)
    (w := .unit) h rfl
  have h := fresh_peel_det (K := .hole) h rfl (Head.beta _ staleBody (Val.loc l))
    (by intro w e; simp [allocRedex, Expr.val, Val.lam, Val.loc] at e)
  simp only [Kont.plug] at h
  rw [staleBody_subst] at h
  -- `free x`
  have h := fresh_peel_det (K := .seq .hole (staleInner (.val (.loc l)))) h rfl
    (Head.free _ l .unit (BoLo.Heap.upd_same _ _ _))
    (by intro w e; simp [allocRedex, Expr.val, Val.prim, Val.loc] at e)
  have h := fresh_peel_det (K := .hole) h rfl (Head.seq _ _)
    (by intro w e; simp [allocRedex] at e)
  simp only [Kont.plug] at h
  -- `alloc (inj₁ ())` at some `l'`, which the term's `load x` forbids from being `l`
  obtain ⟨l', hl', hnamed, h⟩ :=
    fresh_peel_alloc (K := .appR (.val (.lam (staleTail (.val (.loc l))))) .hole)
      (w := .inj₁ .unit) h rfl
  have hne : l' ≠ l := fun e => hnamed (.inr (.inl (by
    subst e; simp [staleInner, staleTail, elet, loadE, Expr.Occ, Expr.val, Val.loc])))
  have h := fresh_peel_det (K := .hole) h rfl (Head.beta _ _ (Val.loc l'))
    (by intro w e; simp [allocRedex, Expr.val, Val.lam, Val.loc] at e)
  simp only [Kont.plug] at h
  rw [staleTail_subst] at h
  -- `load x`: `l` is no longer allocated
  refine fresh_stuck_load (K := .seq (.appR (.val (.lam unit')) .hole)
    (.case (freeE (.val (.loc l'))) unit' unit')) ?_ h
  rw [BoLo.Heap.upd_other (Ne.symm hne), BoLo.Heap.del_same]

/-- **`FreshRunsExistSemLocFree` does not hold**, at `staleL` from the empty world. -/
theorem not_freshRunsExistSemLocFree : ¬ FreshRunsExistSemLocFree := by
  intro h
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  obtain ⟨μ', v, hR⟩ := h LifeCtx.empty [] staleL .unit staleL_locFree staleL_sem LSub.empty []
    [] PMap.empty PMap.empty PMap.empty [] (fun _ => none) Adequacy.models_empty
    (gDenX_nil [] LSub.empty) Fig16.LogRel.hash_empty (ResU.comp_empty_right _) TW.empty htg
    Fig16.BoLo.lower_empty
  rw [substAll_staleL] at hR
  exact staleL_no_fresh hR

end BoCa.Purity

end
