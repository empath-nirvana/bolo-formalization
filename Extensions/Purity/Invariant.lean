import Purity.Stale

/-!
# Purity — invariants along runs: what a name-level invariant can and cannot do

`FreshRunsExistClosed` and `FreshRunsExistPure` (`Closures.lean`) ask for a fresh run of a
well-typed program.  `Stale.lean` shows the
proof must use linearity: `staleL` reads `x` after `free x`.  This file tests the two
invariants on names that would express that without types.

**Term liveness** (`TermLive μ e`): every location the term mentions is allocated.  It is what
`staleL` breaks: after `free x` the term still mentions `x`'s location.  But a run all of
whose states satisfy it need not have a fresh counterpart (`not_termLiveSuffices`, at
`staleH`): a value stored in a cell can go stale without the term mentioning it, and be read
back after its location is reallocated.

    staleH = let r = alloc () in let c = alloc r in free (load c);
             let s = alloc (inj₁ ()) in (λ_. ()) (load (load c)); case (free s) {_ ⇒ () | _ ⇒ ()};
             (λ_. ()) (free c)

`staleH` names no location and is in the semantic relation at `∅; ∅ ⊨ staleH : 1`
(`staleH_sem`).  Its run from the empty heap that reallocates `r`'s location for `s`
satisfies `TermLive` at every state (`staleH_live_run`).  It has no fresh run from the empty
heap (`staleH_no_fresh`): the cell `c` still names `r`'s location, so a fresh `s` lands
elsewhere, and `load (load c)` is stuck.

**Reach liveness** — every location reachable from the term through the heap is allocated —
rules `staleH` out.  It is what `withswap` breaks on the runs of well-typed programs: during
the callback, the lent cell still holds the payload that the callback owns, and may free.
That is not machine-checked here; `withswapWindow` below records the program.

So an invariant sufficient for fresh runs must constrain the heap's contents, and must exempt
exactly the cells whose contents are moved out, as `withswap`'s is during its callback.
Which cells those are is a fact about types, not names.

`[about ours]`: an extension, not a transcription.
-/

noncomputable section

set_option linter.unusedSimpArgs false

namespace BoCa.Purity
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Fig16.LogRel.Typed
open BoCa.Lifetime (LifeCtx LSub)

/-! ### Term liveness -/

/-- Every location the term mentions is allocated. -/
def TermLive (μ : Heap) (e : Expr) : Prop := ∀ ℓ, e.Occ ℓ → μ ℓ ≠ none

/-- A run all of whose states satisfy `TermLive`. -/
inductive LiveSteps : Heap → Expr → Heap → Expr → Prop where
  | refl {μ : Heap} {e : Expr} (h : TermLive μ e) : LiveSteps μ e μ e
  | more {μ μ₁ μ' : Heap} {e e₁ e' : Expr} (h : TermLive μ e) (s : Step1 μ e μ₁ e₁)
      (t : LiveSteps μ₁ e₁ μ' e') : LiveSteps μ e μ' e'

theorem LiveSteps.toSteps {μ μ' : Heap} {e e' : Expr} (h : LiveSteps μ e μ' e') :
    Steps μ e μ' e' := by
  induction h with
  | refl => exact .refl _ _
  | more _ s _ ih => exact .more s ih

/-- **Term liveness along a run is enough for a fresh run.**  Refuted by `staleH`. -/
def TermLiveSuffices : Prop :=
  ∀ (μ μ' : Heap) (e : Expr) (v : Val), LiveSteps μ e μ' v.1 →
    ∃ (μ'' : Heap) (w : Val), FreshRun μ e μ'' w.1

/-! ### `staleH` -/

/-- `store c ()`; `(λ_. ()) (free c)`. -/
def hEnd (c : Expr) : Expr := .seq (.app (.app (.val (.prim .store)) c) unit') (.app (.val (.lam unit')) (freeE c))

/-- `(λ_. ()) (load (load c)); case (free s) {…}; store c (); (λ_. ()) (free c)`, with `s` at
index 0. -/
def hTail (c : Expr) : Expr :=
  .seq (.app (.val (.lam unit')) (loadE (loadE c)))
    (.seq (.case (freeE (.var 0)) unit' unit') (hEnd c))

/-- `free (load c); let s = alloc (inj₁ ()) in hTail c`, with `c` at index 0. -/
def hMid : Expr :=
  .seq (freeE (loadE (.var 0))) (elet (allocE (.val (.inj₁ .unit))) (hTail (.var 1)))

def staleH : Expr := elet (allocE unit') (elet (allocE (.var 0)) hMid)

theorem staleH_locFree : LocFree staleH := by
  intro ℓ o
  simp [staleH, hMid, hTail, hEnd, hEnd, elet, allocE, freeE, loadE, unit', Expr.Occ, Expr.val, Val.lam,
    Val.unit, Val.prim, Val.inj₁] at o

theorem substAll_staleH (γ : List Val) : LogRel.substAll γ staleH = staleH := by
  simp [LogRel.substAll, staleH, hMid, hTail, hEnd, hEnd, elet, allocE, freeE, loadE, unit', Expr.psub,
    Expr.val, Val.lam, Val.unit, Val.prim, Val.inj₁]

theorem hsub₁ (l : Loc) :
    (elet (allocE (.var 0)) hMid).subst 0 (Val.loc l) = elet (allocE (.val (.loc l))) hMid := by
  simp [hMid, hTail, hEnd, elet, allocE, freeE, loadE, unit', Expr.subst, Expr.shift, Val.shift,
    Expr.val, Val.lam, Val.unit, Val.prim, Val.inj₁, Val.loc]

theorem hsub₂ (c : Loc) :
    hMid.subst 0 (Val.loc c) = .seq (freeE (loadE (.val (.loc c))))
      (elet (allocE (.val (.inj₁ .unit))) (hTail (.val (.loc c)))) := by
  simp [hMid, hTail, hEnd, elet, allocE, freeE, loadE, unit', Expr.subst, Expr.shift, Val.shift,
    Expr.val, Val.lam, Val.unit, Val.prim, Val.inj₁, Val.loc]

/-- `hTail c` with `s` substituted. -/
def hTail' (c s : Loc) : Expr :=
  .seq (.app (.val (.lam unit')) (loadE (loadE (.val (.loc c)))))
    (.seq (.case (freeE (.val (.loc s))) unit' unit') (hEnd (.val (.loc c))))

theorem hsub₃ (c s : Loc) : (hTail (.val (.loc c))).subst 0 (Val.loc s) = hTail' c s := by
  simp [hTail, hEnd, hTail', hEnd, freeE, loadE, unit', Expr.subst, Expr.val, Val.lam, Val.unit, Val.prim,
    Val.loc]

/-- One step of `staleH`, at the frame `K`. -/
theorem stepK (K : Kont) {μ μ₁ : Heap} {a a' : Expr} (h : Head μ a μ₁ a') :
    Step1 μ (K.plug a) μ₁ (K.plug a') := ⟨K, a, a', rfl, rfl, h⟩

theorem cov1 {μ : Heap} {a : Loc} (h : μ a ≠ none) : ∀ ℓ ∈ [a], μ ℓ ≠ none := by
  intro ℓ hℓ; simp at hℓ; subst hℓ; exact h

theorem cov2 {μ : Heap} {a b : Loc} (ha : μ a ≠ none) (hb : μ b ≠ none) :
    ∀ ℓ ∈ [a, b], μ ℓ ≠ none := by
  intro ℓ hℓ; simp at hℓ; rcases hℓ with rfl | rfl
  · exact ha
  · exact hb

/-- Liveness from a covering list of allocated locations. -/
theorem termLive_of {μ : Heap} {e : Expr} (L : List Loc) (hs : ∀ ℓ, e.Occ ℓ → ℓ ∈ L)
    (hL : ∀ ℓ ∈ L, μ ℓ ≠ none) : TermLive μ e := fun ℓ o => hL ℓ (hs ℓ o)

set_option maxHeartbeats 1000000 in
/-- **The run of `staleH` that reallocates `r`'s location for `s`**, with every state
term-live, back to the heap it started from. -/
theorem staleH_live_run {μ : Heap} {l c : Loc} (hl : μ l = none) (hc : μ c = none)
    (hlc : l ≠ c) : LiveSteps μ staleH μ (.val .unit) := by
  have hcl : c ≠ l := Ne.symm hlc
  -- the heaps
  let μ₁ := μ.upd l Val.unit
  let μ₂ := μ₁.upd c (Val.loc l)
  let μ₃ := μ₂.del l
  let μ₄ := μ₃.upd l (Val.inj₁ Val.unit)
  let μ₅ := μ₄.del l
  have e₂c : μ₂ c = some (Val.loc l) := BoLo.Heap.upd_same _ _ _
  have e₂l : μ₂ l = some Val.unit := by
    simp only [μ₂, μ₁]; rw [BoLo.Heap.upd_other hlc, BoLo.Heap.upd_same]
  have e₃c : μ₃ c = some (Val.loc l) := by simp only [μ₃]; rw [BoLo.Heap.del_other hcl, e₂c]
  have e₃l : μ₃ l = none := BoLo.Heap.del_same _ _
  have e₄c : μ₄ c = some (Val.loc l) := by simp only [μ₄]; rw [BoLo.Heap.upd_other hcl, e₃c]
  have e₄l : μ₄ l = some (Val.inj₁ Val.unit) := BoLo.Heap.upd_same _ _ _
  have e₅c : μ₅ c = some (Val.loc l) := by simp only [μ₅]; rw [BoLo.Heap.del_other hcl, e₄c]
  have e₅ : μ₅.del c = μ := by
    funext x
    simp only [μ₅, μ₄, μ₃, μ₂, μ₁]
    by_cases hx : x = c
    · subst hx; rw [BoLo.Heap.del_same, hc]
    · by_cases hx' : x = l
      · subst hx'; rw [BoLo.Heap.del_other hx, BoLo.Heap.del_same, hl]
      · rw [BoLo.Heap.del_other hx, BoLo.Heap.del_other hx', BoLo.Heap.upd_other hx',
          BoLo.Heap.del_other hx', BoLo.Heap.upd_other hx, BoLo.Heap.upd_other hx']
  have nn : ∀ {x : Loc} {v : Val} {m : Heap}, m x = some v → m x ≠ none := fun h => by simp [h]
  -- the live-location covers
  have noLoc : ∀ {m : Heap} {e : Expr}, (∀ ℓ, ¬ e.Occ ℓ) → TermLive m e :=
    fun h ℓ o => absurd o (h ℓ)
  refine .more (noLoc fun ℓ o => staleH_locFree ℓ o)
    (stepK (.appR (.val (.lam (elet (allocE (.var 0)) hMid))) .hole)
      (Head.alloc μ .unit l hl)) ?_
  refine .more (termLive_of [l] (fun ℓ o => by
      simp [Kont.plug, elet, allocE, hMid, hTail, hEnd, freeE, loadE, unit', Expr.Occ, Expr.val,
        Val.lam, Val.loc, Val.unit, Val.prim, Val.inj₁] at o; aesop)
      (by simp [μ₁]))
    (Step1.head (Head.beta _ _ (Val.loc l))) ?_
  rw [hsub₁]
  refine .more (termLive_of [l] (fun ℓ o => by
      simp [elet, allocE, hMid, hTail, hEnd, freeE, loadE, unit', Expr.Occ, Expr.val, Val.lam,
        Val.loc, Val.unit, Val.prim, Val.inj₁] at o; aesop)
      (by simp [μ₁]))
    (stepK (.appR (.val (.lam hMid)) .hole) (Head.alloc μ₁ (.loc l) c (by
      simp only [μ₁]; rw [BoLo.Heap.upd_other hcl, hc]))) ?_
  refine .more (termLive_of [c] (fun ℓ o => by
      simp [Kont.plug, hMid, hTail, hEnd, elet, allocE, freeE, loadE, unit', Expr.Occ, Expr.val,
        Val.lam, Val.loc, Val.unit, Val.prim, Val.inj₁] at o; aesop)
      (cov1 (nn e₂c)))
    (Step1.head (Head.beta μ₂ hMid (Val.loc c))) ?_
  rw [hsub₂]
  -- `load c`
  refine .more (termLive_of [c] (fun ℓ o => by
      simp [hTail, hEnd, elet, allocE, freeE, loadE, unit', Expr.Occ, Expr.val, Val.lam, Val.loc,
        Val.unit, Val.prim, Val.inj₁] at o; aesop)
      (cov1 (nn e₂c)))
    (stepK (.seq (.appR (.val (.prim .free)) .hole)
      (elet (allocE (.val (.inj₁ .unit))) (hTail (.val (.loc c)))))
      (Head.load μ₂ c (.loc l) e₂c)) ?_
  -- `free l`
  refine .more (termLive_of [l, c] (fun ℓ o => by
      simp [Kont.plug, hTail, hEnd, elet, allocE, freeE, loadE, unit', Expr.Occ, Expr.val, Val.lam,
        Val.loc, Val.unit, Val.prim, Val.inj₁] at o; aesop)
      (cov2 (nn e₂l) (nn e₂c)))
    (stepK (.seq .hole (elet (allocE (.val (.inj₁ .unit))) (hTail (.val (.loc c)))))
      (Head.free μ₂ l .unit e₂l)) ?_
  refine .more (termLive_of [c] (fun ℓ o => by
      simp [Kont.plug, hTail, hEnd, elet, allocE, freeE, loadE, unit', Expr.Occ, Expr.val, Val.lam,
        Val.loc, Val.unit, Val.prim, Val.inj₁] at o; aesop)
      (cov1 (nn e₃c)))
    (Step1.head (Head.seq μ₃ _)) ?_
  -- `alloc (inj₁ ())`, at `l` again
  refine .more (termLive_of [c] (fun ℓ o => by
      simp [hTail, hEnd, elet, allocE, freeE, loadE, unit', Expr.Occ, Expr.val, Val.lam, Val.loc,
        Val.unit, Val.prim, Val.inj₁] at o; aesop)
      (cov1 (nn e₃c)))
    (stepK (.appR (.val (.lam (hTail (.val (.loc c))))) .hole)
      (Head.alloc μ₃ (.inj₁ .unit) l e₃l)) ?_
  refine .more (termLive_of [l, c] (fun ℓ o => by
      simp [Kont.plug, hTail, hEnd, elet, allocE, freeE, loadE, unit', Expr.Occ, Expr.val, Val.lam,
        Val.loc, Val.unit, Val.prim, Val.inj₁] at o; aesop)
      (cov2 (nn e₄l) (nn e₄c)))
    (Step1.head (Head.beta μ₄ _ (Val.loc l))) ?_
  rw [hsub₃]
  -- `load c`, then `load l`
  refine .more (termLive_of [l, c] (fun ℓ o => by
      simp [hTail', hEnd, freeE, loadE, unit', Expr.Occ, Expr.val, Val.lam, Val.loc, Val.unit,
        Val.prim] at o; aesop)
      (cov2 (nn e₄l) (nn e₄c)))
    (stepK (.seq (.appR (.val (.lam unit')) (.appR (.val (.prim .load)) .hole))
      (.seq (.case (freeE (.val (.loc l))) unit' unit') (hEnd (.val (.loc c)))))
      (Head.load μ₄ c (.loc l) e₄c)) ?_
  refine .more (termLive_of [l, c] (fun ℓ o => by
      simp [hEnd, Kont.plug, freeE, loadE, unit', Expr.Occ, Expr.val, Val.lam, Val.loc, Val.unit,
        Val.prim] at o; aesop)
      (cov2 (nn e₄l) (nn e₄c)))
    (stepK (.seq (.appR (.val (.lam unit')) .hole)
      (.seq (.case (freeE (.val (.loc l))) unit' unit') (hEnd (.val (.loc c)))))
      (Head.load μ₄ l (.inj₁ .unit) e₄l)) ?_
  refine .more (termLive_of [l, c] (fun ℓ o => by
      simp [hEnd, Kont.plug, freeE, loadE, unit', Expr.Occ, Expr.val, Val.lam, Val.loc, Val.unit,
        Val.prim, Val.inj₁] at o; aesop)
      (cov2 (nn e₄l) (nn e₄c)))
    (stepK (.seq .hole
      (.seq (.case (freeE (.val (.loc l))) unit' unit') (hEnd (.val (.loc c)))))
      (Head.beta μ₄ unit' (.inj₁ .unit))) ?_
  refine .more (termLive_of [l, c] (fun ℓ o => by
      simp [hEnd, Kont.plug, freeE, loadE, unit', Expr.Occ, Expr.val, Val.lam, Val.loc, Val.unit,
        Val.prim, Expr.subst] at o; aesop)
      (cov2 (nn e₄l) (nn e₄c)))
    (Step1.head (Head.seq μ₄ _)) ?_
  -- `free s`
  refine .more (termLive_of [l, c] (fun ℓ o => by
      simp [hEnd, freeE, loadE, unit', Expr.Occ, Expr.val, Val.lam, Val.loc, Val.unit,
        Val.prim] at o; aesop)
      (cov2 (nn e₄l) (nn e₄c)))
    (stepK (.seq (.case .hole unit' unit') (hEnd (.val (.loc c))))
      (Head.free μ₄ l (.inj₁ .unit) e₄l)) ?_
  refine .more (termLive_of [c] (fun ℓ o => by
      simp [Kont.plug, hEnd, freeE, unit', Expr.Occ, Expr.val, Val.lam, Val.loc, Val.unit,
        Val.prim, Val.inj₁] at o; aesop)
      (cov1 (nn e₅c)))
    (stepK (.seq .hole (hEnd (.val (.loc c)))) (Head.case₁ μ₅ Val.unit unit' unit')) ?_
  refine .more (termLive_of [c] (fun ℓ o => by
      simp [Kont.plug, hEnd, freeE, unit', Expr.Occ, Expr.val, Val.lam, Val.loc, Val.unit,
        Val.prim, Expr.subst] at o; aesop)
      (cov1 (nn e₅c)))
    (Step1.head (Head.seq μ₅ _)) ?_
  -- `store c ()`
  refine .more (termLive_of [c] (fun ℓ o => by
      simp [hEnd, freeE, unit', Expr.Occ, Expr.val, Val.lam, Val.loc, Val.unit,
        Val.prim] at o; aesop)
      (cov1 (nn e₅c)))
    (stepK (.seq .hole (.app (.val (.lam unit')) (freeE (.val (.loc c)))))
      (Head.store μ₅ c .unit (.loc l) e₅c)) ?_
  have e₆c : (μ₅.upd c Val.unit) c = some Val.unit := BoLo.Heap.upd_same _ _ _
  refine .more (termLive_of [c] (fun ℓ o => by
      simp [hEnd, Kont.plug, freeE, unit', Expr.Occ, Expr.val, Val.lam, Val.loc, Val.unit,
        Val.prim] at o; aesop)
      (cov1 (nn e₆c)))
    (Step1.head (Head.seq _ _)) ?_
  -- `free c`
  refine .more (termLive_of [c] (fun ℓ o => by
      simp [hEnd, freeE, unit', Expr.Occ, Expr.val, Val.lam, Val.loc, Val.unit, Val.prim] at o
       ; aesop)
      (cov1 (nn e₆c)))
    (stepK (.appR (.val (.lam unit')) .hole) (Head.free _ c .unit e₆c)) ?_
  have e₆ : (μ₅.upd c Val.unit).del c = μ := by
    funext x
    by_cases hx : x = c
    · subst hx; rw [BoLo.Heap.del_same, hc]
    · rw [BoLo.Heap.del_other hx, BoLo.Heap.upd_other hx, ← e₅, BoLo.Heap.del_other hx]
  rw [e₆]
  refine .more (termLive_of [] (fun ℓ o => by
      simp [hEnd, Kont.plug, unit', Expr.Occ, Expr.val, Val.lam, Val.loc, Val.unit] at o)
      (by simp))
    (Step1.head (Head.beta μ unit' Val.unit)) ?_
  exact .refl (termLive_of [] (fun ℓ o => by
    simp [hEnd, unit', Expr.Occ, Expr.val, Val.unit, Expr.subst] at o) (by simp))

/-- **`staleH` is in the semantic relation** at `∅; ∅ ⊨ staleH : 1`. -/
theorem staleH_sem : SemX LifeCtx.empty ([] : Ctx Ty) staleH .unit := by
  intro δ γ ls ρ _ hγ
  obtain ⟨ρ₁, ρ₂, hc, ⟨rfl, -⟩, h₂⟩ := hγ
  have hρ₂ : ρ₂ = PMap.empty := by
    cases γ with
    | nil => exact h₂.1
    | cons _ _ => exact h₂.1
  subst hρ₂
  obtain rfl : (PMap.empty : WRes) = ρ := ResU.eq_of_comp_empty_left hc
  rw [substAll_staleH]
  refine wpTS_restore (v := .unit) (fun ρf fρ μ _ _ hμ => ?_) ⟨rfl, rfl⟩
  obtain ⟨d, hd⟩ := lower_finite hμ
  obtain ⟨l, hl⟩ := loc_infinite d
  obtain ⟨c, hc⟩ := loc_infinite (l :: d)
  have hμl : μ l = none := by by_contra h; exact hl (hd l h)
  have hμc : μ c = none := by by_contra h; exact hc (List.mem_cons_of_mem _ (hd c h))
  have hlc : l ≠ c := fun e => hc (e ▸ List.mem_cons_self ..)
  exact (staleH_live_run hμl hμc hlc).toSteps

/-- **`staleH` has no fresh run to a value from the empty heap.** -/
theorem staleH_no_fresh {μ' : Heap} {v : Val} (h : FreshRun (fun _ => none) staleH μ' v.1) :
    False := by
  obtain ⟨l, -, -, h⟩ := fresh_peel_alloc
    (K := .appR (.val (.lam (elet (allocE (.var 0)) hMid))) .hole) (w := .unit) h rfl
  have h := fresh_peel_det (K := .hole) h rfl (Head.beta _ _ (Val.loc l))
    (by intro w e; simp [allocRedex, Expr.val, Val.lam, Val.loc] at e)
  simp only [Kont.plug] at h
  rw [hsub₁] at h
  obtain ⟨c, hc, -, h⟩ := fresh_peel_alloc (K := .appR (.val (.lam hMid)) .hole)
    (w := .loc l) h rfl
  have hlc : c ≠ l := fun e => by subst e; simp at hc
  have h := fresh_peel_det (K := .hole) h rfl (Head.beta _ hMid (Val.loc c))
    (by intro w e; simp [allocRedex, Expr.val, Val.lam, Val.loc] at e)
  simp only [Kont.plug] at h
  rw [hsub₂] at h
  have e₂c : BoLo.Heap.upd (BoLo.Heap.upd (fun _ => none) l Val.unit) c (Val.loc l) c =
      some (Val.loc l) := BoLo.Heap.upd_same _ _ _
  have e₂l : BoLo.Heap.upd (BoLo.Heap.upd (fun _ => none) l Val.unit) c (Val.loc l) l =
      some Val.unit := by rw [BoLo.Heap.upd_other (Ne.symm hlc), BoLo.Heap.upd_same]
  have h := fresh_peel_det (K := .seq (.appR (.val (.prim .free)) .hole)
      (elet (allocE (.val (.inj₁ .unit))) (hTail (.val (.loc c))))) h rfl
    (Head.load _ c (.loc l) e₂c)
    (by intro w e; simp [allocRedex, loadE, Expr.val, Val.prim, Val.loc] at e)
  have h := fresh_peel_det (K := .seq .hole
      (elet (allocE (.val (.inj₁ .unit))) (hTail (.val (.loc c))))) h rfl
    (Head.free _ l .unit e₂l)
    (by intro w e; simp [allocRedex, Expr.val, Val.prim, Val.loc] at e)
  have h := fresh_peel_det (K := .hole) h rfl (Head.seq _ _)
    (by intro w e; simp [allocRedex] at e)
  simp only [Kont.plug] at h
  -- the fresh `s` avoids `l`, which the cell `c` still names
  obtain ⟨s, hs, hnamed, h⟩ :=
    fresh_peel_alloc (K := .appR (.val (.lam (hTail (.val (.loc c))))) .hole)
      (w := .inj₁ .unit) h rfl
  have hsl : s ≠ l := fun e => hnamed (.inr (.inr ⟨c, Val.loc l,
    by rw [BoLo.Heap.del_other hlc, e₂c], by subst e; simp [hEnd, Expr.Occ, Expr.val, Val.loc]⟩))
  have h := fresh_peel_det (K := .hole) h rfl (Head.beta _ _ (Val.loc s))
    (by intro w e; simp [allocRedex, Expr.val, Val.lam, Val.loc] at e)
  simp only [Kont.plug] at h
  rw [hsub₃] at h
  have e₄c : BoLo.Heap.upd ((BoLo.Heap.upd (BoLo.Heap.upd (fun _ => none) l Val.unit) c
      (Val.loc l)).del l) s (Val.inj₁ Val.unit) c = some (Val.loc l) := by
    have hcs : c ≠ s := fun e => by
      subst e; rw [BoLo.Heap.del_other hlc, e₂c] at hs; cases hs
    rw [BoLo.Heap.upd_other hcs, BoLo.Heap.del_other hlc, e₂c]
  have h := fresh_peel_det (K := .seq (.appR (.val (.lam unit')) (.appR (.val (.prim .load)) .hole))
      (.seq (.case (freeE (.val (.loc s))) unit' unit') (hEnd (.val (.loc c))))) h rfl
    (Head.load _ c (.loc l) e₄c)
    (by intro w e; simp [allocRedex, loadE, Expr.val, Val.prim, Val.loc] at e)
  refine fresh_stuck_load (K := .seq (.appR (.val (.lam unit')) .hole)
    (.seq (.case (freeE (.val (.loc s))) unit' unit') (hEnd (.val (.loc c))))) ?_ h
  rw [BoLo.Heap.upd_other (Ne.symm hsl), BoLo.Heap.del_same]

/-- **`TermLiveSuffices` does not hold**, at `staleH` from the empty heap. -/
theorem not_termLiveSuffices : ¬ TermLiveSuffices := by
  intro h
  obtain ⟨μ'', w, hR⟩ := h (fun _ => none) (fun _ => none) staleH Val.unit
    (staleH_live_run (l := 0) (c := 1) rfl rfl (by decide))
  exact staleH_no_fresh hR

/-! ### `withswap`'s window -/

/-- A well-typed use of `withswap` whose callback frees the payload it was handed, while the
lent cell still holds it: `let (r, u) = withbor (alloc (alloc ())) (Λ. λm. let (m′, v) =
withswap m (λz. free z; (alloc (), ())); v; forget m′; ()); u; free (free r)`.  During the
callback the cell `r` names a freed location, and `r` is reachable from the term (the pending
`store` and `withbor`'s pair).  Recorded, not machine-checked: its typing and that run are not
built here. -/
def withswapWindow : Expr :=
  .letpair
    (.app (.app withbor (allocE (allocE unit')))
      (.val (.lam (.val (.lam (.letpair
        (.app (.app withswap (.var 0))
          (.val (.lam (.seq (freeE (.var 0)) (.pair (allocE unit') unit')))))
        (.seq (.var 0) (.seq (.app forget (.var 1)) unit'))))))))
    (.seq (.var 0) (freeE (freeE (.var 1))))

end BoCa.Purity

end
