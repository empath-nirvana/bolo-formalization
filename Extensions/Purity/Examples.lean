import Purity.Boundary
import Paper.Examples.Programs

/-!
# Purity — examples

Two programs of the pure fragment, each negating a boolean `1 ⊕ 1` read through an immutable
borrow, through a temporary cell it allocates and frees.

* `negB`, open: `Δ = ['a ⊏ ⊤]`, `Γ = b : Imm 'a (1 ⊕ 1)`,

      withload b (Λ. λy. let t = alloc y in case (free t) {x ⇒ inj₂ x | x ⇒ inj₁ x})

  typed at `1 ⊕ 1` (`d_negB`), so in the fragment (`negB_pure`).  Its instances: the heap is
  given back (`negB_heap`), the result is a function of `b` and what `b` reaches
  (`negB_result`), and every run reads only what `b` reaches or what it allocates
  (`negB_reads`).
* `negClosed`, closed: it allocates the cell `r ↦ inj₁ ()` itself, borrows it immutably with
  `withbor`, runs the same loader, and frees `r`.  `closed_pure` applies (`negClosed_pure`):
  every fresh run from every heap returns one value.  The executable interpreter
  (`Support/Dynamics/Interpreter.lean`, not proved to agree with `BoLo.Steps`,
  `docs/adjudications.md` D8) returns `inj₂ ()` with no cell left (`negClosed_eval`).

`[about ours]`: an extension, not a transcription.
-/

noncomputable section

namespace BoCa.Purity.Examples
open BoCa BoCa.Lifetime BoCa.Programs
open BoCa.Fig16.LogRel.Typed

/-- `let t = alloc y in case (free t) {x ⇒ inj₂ x | x ⇒ inj₁ x}`, at `y` of index 0. -/
def negBody : Expr :=
  elet (.app alloc' (.var 0)) (.case (.app free' (.var 0)) (.inj₂ (.var 0)) (.inj₁ (.var 0)))

theorem d_negBody {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ (⟨B, true⟩ :: Γ) negBody B :=
  .lolliE (.left hΓ.split)
    (.lolliE (.left hΓ.split) (.var (.here hΓ)) (.allocAx (.cons hΓ)))
    (.lolliI rfl
      (.sumE (.left (.dead hΓ.split)) rfl
        (.lolliE (.left (.dead hΓ.split)) (.var (.here (.cons hΓ))) (.freeAx (.cons (.cons hΓ))))
        (.sumI₂ (.var (.here (.cons (.cons hΓ)))))
        (.sumI₁ (.var (.here (.cons (.cons hΓ)))))))

/-! ### `negB`, with the borrow in its interface -/

/-- The loader `Λ. λy. negBody`, returning `['b] (1 ⊕ 1)`. -/
def negLoader : Expr := lam (lam negBody)

theorem d_negLoader {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf D1 Γ negLoader
      (.all 1 D1.meetOfDom (.lolli (Ty.immReborrow (.var 1) B) (.box (.var 1) B))) :=
  .allI (S := .unit) rfl rfl (Ctx.Dead.noBinds hΓ 1)
    (.lolliI rfl (.boxIctx (d_negBody (.cons hΓ))
      (Ctx.Outlives.solo (LifeCtx.defines_of_wf rfl) (.sum .unit .unit) (.cons hΓ))))

/-- `withload b negLoader`, at `b : Imm 'a (1 ⊕ 1)`. -/
def negB : Expr := app2 withload (.var 0) negLoader

theorem d_negB : DerivesWf D1 [⟨.imm (.var 0) B, true⟩] negB B :=
  .lolliE (.right .nil) (d_negLoader (.cons .nil))
    (.lolliE (.left .nil) (.var (.here .nil))
      (.withloadAx (T₂ := B) (.cons .nil) 1 rfl rfl))

/-- `negB` is in the pure fragment. -/
theorem negB_pure : PureTyping D1 [⟨.imm (.var 0) B, true⟩] negB B where
  derives := d_negB
  ok := rfl
  wfCtx := fun s hs _ => by simp at hs; subst hs; rfl
  args := fun s hs _ => by simp at hs; subst hs; exact .imm _ _
  result := .sum .unit .unit

/-- **`negB` gives the heap back**, from every tagged typed world completing its argument's
resource. -/
theorem negB_heap {δ : LSub} {γ : List Val} {ls : List SRec} {ρ : Fig16.BoLo.WRes} (hδ : D1.Models δ)
    (hγ : gDenX ls δ [⟨.imm (.var 0) B, true⟩] γ ρ) {ρf fρ : Fig16.BoLo.WRes} {ps : List FrameRec}
    (hf : Fig16.ResU.Hash ρf ρ) (hc : Fig16.ResU.CompS ρf ρ fρ) (hT : TW fρ ps (rsOf ls))
    (htg : Tagged fρ ps ls) {μ : BoLo.Heap} (hμ : Fig16.ResU.Lower fρ μ) :
    ∃ v : Val, BoLo.Steps μ (Fig16.LogRel.substAll γ negB) μ (.val v) ∧ LocFree v.1 ∧
      (∃ ls', vP B ls' δ v Fig16.PMap.empty) ∧
      ∀ (μR : BoLo.Heap) (w : Val), FreshRun μ (Fig16.LogRel.substAll γ negB) μR w.1 →
        w = v ∧ ∃ g : Loc → Loc, Set.InjOn g {x | μR x ≠ none} ∧ μ = Heap.push g μR :=
  pure_heap negB_pure hδ hγ hf hc hT htg hμ

/-- **`negB`'s result is a function of `b` and what `b` reaches.** -/
theorem negB_result {δ : LSub} {γ : List Val} {ls : List SRec} {ρ : Fig16.BoLo.WRes} (hδ : D1.Models δ)
    (hγ : gDenX ls δ [⟨.imm (.var 0) B, true⟩] γ ρ) {ρf fρ : Fig16.BoLo.WRes} {ps : List FrameRec}
    (hf : Fig16.ResU.Hash ρf ρ) (hc : Fig16.ResU.CompS ρf ρ fρ) (hT : TW fρ ps (rsOf ls))
    (htg : Tagged fρ ps ls) {μ : BoLo.Heap} (hμ : Fig16.ResU.Lower fρ μ) :
    ∃ v : Val, LocFree v.1 ∧ (∃ ls', vP B ls' δ v Fig16.PMap.empty) ∧
      BoLo.Steps μ (Fig16.LogRel.substAll γ negB) μ (.val v) ∧
      ∀ (μ₁ μ₂ μ₂' : BoLo.Heap) (w₁ w₂ : Val),
        FreshRun μ (Fig16.LogRel.substAll γ negB) μ₁ w₁.1 →
        (∀ x, Reach μ (ArgLocs γ) x → μ x ≠ none → μ₂ x = μ x) →
        BoLo.Steps μ₂ (Fig16.LogRel.substAll γ negB) μ₂' w₂.1 → w₁ = v ∧ w₂ = v :=
  pure_result negB_pure hδ hγ hf hc hT htg hμ

/-- **`negB` reads only what `b` reaches**, on every run from every heap. -/
theorem negB_reads (γ : List Val) {μ μ' : BoLo.Heap} {e' : Expr}
    (h : BoLo.Steps μ (Fig16.LogRel.substAll γ negB) μ' e') :
    RunIn (Reach μ (ArgLocs γ)) μ (Fig16.LogRel.substAll γ negB) μ' e' :=
  derivesWf_runIn d_negB γ h

/-! ### `negClosed`, with the borrow taken inside -/

/-- The loader, returning `['b] ['a] (1 ⊕ 1)` for `withbor`'s borrower. -/
def negLoader' : Expr := lam (lam negBody)

theorem d_negLoader' {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf D1 Γ negLoader'
      (.all 1 D1.meetOfDom
        (.lolli (Ty.immReborrow (.var 1) B) (.box (.var 1) (.box (.var 0) B)))) :=
  .allI (S := .unit) rfl rfl (Ctx.Dead.noBinds hΓ 1)
    (.lolliI rfl
      (.boxIctx (.boxIctx (d_negBody (.cons hΓ))
          (Ctx.Outlives.solo (LifeCtx.defines_of_wf rfl) (.sum .unit .unit) (.cons hΓ)))
        (Ctx.Outlives.solo (LifeCtx.defines_of_wf rfl) (.sum .unit .unit) (.cons hΓ))))

/-- The borrower `Λ. λb. withload b negLoader'`. -/
def negBorrower : Expr := lam (lam (app2 withload (.var 0) negLoader'))

theorem d_negBorrower :
    DerivesWf LifeCtx.empty [] negBorrower
      (.all 0 LifeCtx.empty.meetOfDom (.lolli (.imm (.var 0) B) (.box (.var 0) B))) :=
  .allI (S := .unit) rfl rfl (Ctx.Dead.noBinds .nil 0)
    (.lolliI rfl
      (.lolliE (.right (.dead .nil)) (d_negLoader' (.cons (.cons .nil)))
        (.lolliE (.left (.dead .nil)) (.var (.here (.cons .nil)))
          (.withloadAx (T₂ := .box (.var 0) B) (.cons (.cons .nil)) 1 rfl rfl))))

/-- `let (r, v) = withbor (alloc (inj₁ ())) negBorrower; case (free r) {x ⇒ x | y ⇒ y}; v`. -/
def negClosed : Expr :=
  .letpair (app2 withbor (.app alloc' (.inj₁ unit')) negBorrower)
    (.seq (.case (.app free' (.var 1)) (.var 0) (.var 0)) (.var 0))

theorem d_negClosed : DerivesWf LifeCtx.empty [] negClosed B :=
  .tensorE (T₁ := .ref B) (T₂ := B) .nil rfl
    (.lolliE .nil d_negBorrower
      (.lolliE .nil (.lolliE .nil (.sumI₁ (.unitI .nil)) (.allocAx .nil))
        (.withbor1Ax .nil 0 rfl rfl)))
    (.unitE (.right (.left .nil))
      (.sumE (.dead (.left .nil)) rfl
        (.lolliE (.dead (.left .nil)) (.var (.there (.here .nil))) (.freeAx (.cons (.cons .nil))))
        (.var (.here (.cons (.cons .nil))))
        (.var (.here (.cons (.cons .nil)))))
      (.var (.here (.cons .nil))))

/-- **`negClosed` is pure outright.** -/
theorem negClosed_pure :
    ∃ v : Val, LocFree v.1 ∧
      BoLo.Steps Adequacy.emptyMem negClosed Adequacy.emptyMem (.val v) ∧
      (∀ (μ μ' : BoLo.Heap) (w : Val), FreshRun μ negClosed μ' w.1 → w = v) ∧
      ∀ (ρf fρ : Fig16.BoLo.WRes) (ps : List FrameRec) (ls : List SRec) (μ : BoLo.Heap),
        Fig16.ResU.Hash ρf Fig16.PMap.empty → Fig16.ResU.CompS ρf Fig16.PMap.empty fρ →
        TW fρ ps (rsOf ls) → Tagged fρ ps ls → Fig16.ResU.Lower fρ μ →
        ∃ v' : Val, LocFree v'.1 ∧ BoLo.Steps μ negClosed μ (.val v') :=
  closed_pure d_negClosed (.sum .unit .unit)

/-- The interpreter returns `inj₂ ()` and leaves no cell. -/
theorem negClosed_eval :
    (match eval negClosed with
      | .value ⟨.inj₂ .unit, _⟩ false => true
      | _ => false) = true := by decide

end BoCa.Purity.Examples

end
