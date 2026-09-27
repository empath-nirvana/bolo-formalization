import Purity.Local
import Support.Statics.Presupposed
import Support.LogicalRelation.ClosingSubstitutions

/-!
# Purity — a well-typed term names no location

`[TR]` p. 1's `Val` has the production `ℓ`, but no rule of p. 2's typing judgment types a
location, and the axiom terms of p. 3 mention none.  So a term `DerivesWf` types mentions no
location (`derivesWf_locFree`), and every location of the closed program `γ(e)` comes from the
closing values `γ` (`occ_substAll_of_locFree`).

This is where typing enters the read footprint: by `Local.lean`, a run of `γ(e)` touches only
locations reachable from `γ` through the heap, or allocated by the run itself.

`[about ours]`: an extension, not a transcription.
-/

noncomputable section

namespace BoCa.Purity
open BoCa
open BoCa.Lifetime (LifeCtx)

/-- A location of `γ(e)` under `k` binders is a location of `e` or of a value of `γ`. -/
theorem occ_psub {ℓ : Loc} :
    ∀ (k : Nat) (γ : List Val) (e : Expr),
      (Expr.psub k γ e).Occ ℓ → e.Occ ℓ ∨ ∃ v ∈ γ, v.1.Occ ℓ
  | k, γ, .var i, h => by
      simp only [Expr.psub] at h
      split at h
      · simp [Expr.Occ] at h
      · split at h
        · rename_i v hv
          exact Or.inr ⟨v, List.mem_of_getElem? hv, (Val.occ_shift k 0 v).mp h⟩
        · simp [Expr.Occ] at h
  | _, _, .unit, h | _, _, .prim _, h => h.elim
  | _, _, .loc _, h => Or.inl h
  | k, γ, .pair a b, h | k, γ, .seq a b, h | k, γ, .app a b, h => by
      simp only [Expr.psub, Expr.Occ] at h
      rcases h with h | h
      · rcases occ_psub k γ a h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases occ_psub k γ b h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | k, γ, .letpair a b, h => by
      simp only [Expr.psub, Expr.Occ] at h
      rcases h with h | h
      · rcases occ_psub k γ a h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases occ_psub (k + 2) γ b h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | k, γ, .inj₁ a, h | k, γ, .inj₂ a, h => by
      simp only [Expr.psub, Expr.Occ] at h
      exact occ_psub k γ a h
  | k, γ, .lam a, h => by
      simp only [Expr.psub, Expr.Occ] at h
      exact occ_psub (k + 1) γ a h
  | k, γ, .case a b c, h => by
      simp only [Expr.psub, Expr.Occ] at h
      rcases h with h | h | h
      · rcases occ_psub k γ a h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases occ_psub (k + 1) γ b h with h' | h'
        · exact Or.inl (Or.inr (Or.inl h'))
        · exact Or.inr h'
      · rcases occ_psub (k + 1) γ c h with h' | h'
        · exact Or.inl (Or.inr (Or.inr h'))
        · exact Or.inr h'

/-- The locations the closing values `γ` mention. -/
def ArgLocs (γ : List Val) (ℓ : Loc) : Prop := ∃ v ∈ γ, v.1.Occ ℓ

/-- Every location of `γ(e)`, for `e` naming none, is a location of `γ`. -/
theorem occ_substAll_of_locFree {γ : List Val} {e : Expr} (he : LocFree e) {ℓ : Loc}
    (h : (Fig16.LogRel.substAll γ e).Occ ℓ) : ArgLocs γ ℓ :=
  (occ_psub 0 γ e h).resolve_left (he ℓ)

/-- **A term `[TR]` p. 2 types mentions no location.** -/
theorem derivesWf_locFree {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty}
    (h : DerivesWf Δ Γ e T) : LocFree e := by
  induction h with
  | var | unitI | allocAx | freeAx | forgetImmAx | forgetMutAx | forgetUnkAx =>
      intro ℓ o; simp [Expr.Occ, forget, unit'] at o
  | swapAx | copyAx | withbor1Ax | withbor2Ax | withbor3Ax | withloadAx | withswapAx =>
      intro ℓ o
      simp [Expr.Occ, swap, copy, withbor, withload, withswap, lam2, elet, load', store',
        unit', v0, v1, v2, v3] at o
  | unitE _ _ _ ih₁ ih₂ | tensorI _ _ _ ih₁ ih₂ | tensorE _ _ _ _ ih₁ ih₂ =>
      intro ℓ o; rcases o with o | o
      · exact ih₁ ℓ o
      · exact ih₂ ℓ o
  | lolliE _ _ _ ih₁ ih₂ =>
      intro ℓ o; rcases o with o | o
      · exact ih₂ ℓ o
      · exact ih₁ ℓ o
  | sumI₁ _ ih | sumI₂ _ ih => exact ih
  | sumE _ _ _ _ _ ih₀ ih₁ ih₂ =>
      intro ℓ o; rcases o with o | o | o
      · exact ih₀ ℓ o
      · exact ih₁ ℓ o
      · exact ih₂ ℓ o
  | lolliI _ _ ih => exact ih
  | allI _ _ _ _ ih => exact ih
  | allE _ _ ih =>
      intro ℓ o; rcases o with o | o
      · exact ih ℓ o
      · simp [Expr.Occ, Expr.val, Val.unit] at o
  | boxIctx _ _ ih | boxE _ ih | immSub _ _ ih | mutSub _ _ ih => exact ih

end BoCa.Purity

end
