import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S5_Model.Definitions
import Support.Lifetimes.Interpretation
import Support.LogicalRelation.ClosingSubstitutions
import Support.Model.Notation
import Support.Statics.Contexts

/-!
# [TR] §4 Logical Relation  (physical p. 4)

    𝒱⟦1⟧δ(v)             ≜ ⌜v = ()⌝
    𝒱⟦T₁ ⊗ T₂⟧δ(v)       ≜ ∃ v₁, v₂. ⌜v = (v₁, v₂)⌝ ⋆ 𝒱⟦T₁⟧δ(v₁) ⋆ 𝒱⟦T₂⟧δ(v₂)
    𝒱⟦T₁ ⊕ T₂⟧δ(v)       ≜ (∃ v₁. ⌜v = inj₁ v₁⌝ ⋆ 𝒱⟦T₁⟧δ(v₁)) ∨ (∃ v₂. ⌜v = inj₂ v₂⌝ ⋆ 𝒱⟦T₂⟧δ(v₂))
    𝒱⟦T₁ ⊸ T₂⟧δ(v)       ≜ ∀ v′. 𝒱⟦T₁⟧δ(v′) ─⋆ ℰ⟦T₂⟧δ(v v′)
    𝒱⟦∀ 'a ⊏ @b. T⟧δ(v)  ≜ ∀ α ⊏ @bδ. ℰ⟦T⟧δ(v ())
    𝒱⟦[@a] T⟧δ(v)        ≜ [@aδ] 𝒱⟦T⟧δ(v)
    𝒱⟦Ref T⟧δ(v)         ≜ ∃ ℓ, v′. ⌜v = ℓ⌝ ⋆ ℓ ↦ v′ ⋆ 𝒱⟦T⟧δ(v′)
    𝒱⟦Imm @a T⟧δ(v)      ≜ ∃ ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦ Imm @aδ 𝒱⟦T⟧δ
    𝒱⟦Mut @a T⟧δ(v)      ≜ ∃ ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦ Mut @aδ 𝒱⟦T⟧δ
    𝒱⟦Unk⟧δ(v)           ≜ emp
    ℰ⟦T⟧δ(e)             ≜ wp (e) {𝒱⟦T⟧δ}
    𝒟⟦Δ⟧(δ)              ≜ ⌜δ ∈ ⟦Δ⟧⌝
    𝒢⟦Γ⟧(γ)              ≜ ⌜dom(Γ) ⊆ dom(δ)⌝ ⋆ ⊛_{x ∈ dom(Γ)} 𝒱⟦Γ(x)⟧δ(γ(x))
    Δ; Γ ⊨ e : T         ≜ !∀ δ, γ. 𝒟⟦Δ⟧(δ) ─⋆ 𝒢⟦Γ⟧δ(γ) ─⋆ ℰ⟦T⟧δ(γ(e))

**This display has two readings, and both are kept.**  The literal one is in
this file: `Fig16.LogRel.vDen`, `eDen`, `gDen`, `SemTy`, each clause as printed,
over `[TR]` p. 6's `wp`.  The repaired one is the typed world, `Fig16.LogRel.Typed.vX`,
`wpTS`, `gDenX`, `SemX` (`docs/adjudications.md` §12.69–§12.72): an `Imm`
payload is read at its observable view, borrow payloads are stratified by a
record list, the `Imm` clause carries the type the world recorded at the cell,
`⊸`/`∀` are Kripke over the record list, and `wp` ranges over the tagged typed
worlds `TW` that the printed proofs' operations produce.  `[TR]` 6.151 holds at
the repaired judgment with no hypothesis; at the literal one it needs
`WithloadEscrow`, which the configuration `Fig16.LogRel.ViewWitness` refuses
(`Paper/LiteralReadings/S6_8_FundamentalProperty.lean`).
Each row below records both readings: its comment gives the printed clause,
the adjudication, and what the repair changes.  The repaired declarations are
not in this file.  They are in `Support/TypedWorld/`, which imports it:
`Records.lean` (frame records, positions, coherence, the Kripke order `Ext`),
`World.lean` (value shapes `vShape`, the typed worlds `TW`, tagging, and
`wpTS`, row 5.33's repair) and `Relation.lean` (`vX`, the repaired `Imm`/`Mut`
points-to `ptoImmS`/`ptoMutS`, and `gDenX`, `SemX`).  They come after this file
because the worlds are defined through value shapes, which read lifetimes
through this section's `atLife` (row 4.15).

**How this file reads.**  Each printed item is a row of `[TR]`'s section, in the
order the page prints it, as far as Lean's definition-before-use allows; a row
that has to come earlier than printed does so because something printed before
it is defined through it.  Each row opens with a comment giving its number, the
printed form, the page, a tag, and the reason the Lean has the shape it has:

* `[as printed]` — the Lean is the printed item, symbol for symbol;
* `[encoding]` — it differs only by a representation choice that changes nothing
  (de Bruijn indices, a graph for a partial function, a list for a finite map);
* `[repair]` — it deliberately differs, and the comment gives the adjudication
  and the sentences of the paper that ground it;
* `[about ours]` — a declaration the paper does not print, placed here only
  because Lean needs it before the next printed row.

Row numbers are those of `Paper/INDEX.md` (*Definitions*); `§N` citations are
to `docs/adjudications.md`.
-/

noncomputable section

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
### 4.6 · `𝒱⟦[@a] T⟧δ(v) ≜ [@aδ] 𝒱⟦T⟧δ(v)` · [TR] p. 4 · `[encoding]`

Named choice: `BoCa.Lifetime.Life.interp` is partial, so `@aδ` in an argument position is wrapped as `∃α. @aδ = α ∧ …`; `BoCa.Fig16.LogRel.atLife_eq` reduces that to the printed clause wherever `@aδ` is defined, which 𝒟⟦Δ⟧ plus `Δ ⊢ T` guarantee. An undefined `@aδ` is read as False — a case the print does not address

### 4.15 · — no printed counterpart — · [TR] p. 4 · `[repair]`

Forced by `BoCa.Lifetime.Life.interp` being partial: p. 3 prints `@aδ` as a partial function and never says what a clause means when it is undefined. `atLife` fixes the argument position to False, `LtLife` fixes the bound position to a vacuous quantifier. Adjudicated at `docs/adjudications.md` L3, corroborated by C14: `@aδ` is partial in the sources themselves ([CONF] Fig. 11 gives `aδ ≜ δ('a)`, undefined off `dom(δ)`) and neither document says what a clause means when it is undefined, so a total reading must be chosen and the grammatical position, not us, decides which. [TR]'s own proof of 6.161 (p. 42) introduces `α ⊏ @bδ` without first establishing `@bδ`, which only the `LtLife` reading allows
-/
/-- `@aδ` as a connective's ARGUMENT. -/
def atLife (δ : LSub) (a : Lifetime.Life) (F : Life → SPropU BoCa.Loc BoCa.Val) :
    WProp :=
  fun ρ => ∃ α, a.interp δ = some α ∧ F α ρ

/-!
### 4.12 · `𝒟⟦Δ⟧(δ) ≜ ⌜δ ∈ ⟦Δ⟧⌝` · [TR] p. 4, with ⟦Δ⟧ from p. 3 · `[encoding]`

Inherits row 2.52's two named choices (association list, first conjunct subsumed) and nothing else
-/
/-- **`𝒟⟦Δ⟧(δ) ≜ ⌜δ ∈ ⟦Δ⟧⌝`**  (`[TR]` p. 4).  `[as printed]` -/
def dDen (Δ : LifeCtx) (δ : LSub) : WProp := ⌜Δ.Models δ⌝

end BoCa.Fig16.LogRel

namespace BoCa
open BoCa.Lifetime

/-!
### 4.13 · `𝒢⟦Γ⟧(γ) ≜ ⌜dom(Γ) ⊆ dom(δ)⌝ ⋆ ⊛_{x∈dom(Γ)} 𝒱⟦Γ(x)⟧δ(γ(x))` · [TR] p. 4 · `[repair]`

Two differences, both adjudicated. (1) The print says `dom(δ)` where Lean says `dom(γ)`: since Γ maps term variables and δ lifetime variables, so the printed containment is not type-correct. (2) The printed left-hand side carries no `δ` subscript though its right-hand side uses δ free; Lean takes δ as a parameter, which is row 4.14's reading of the same page.
-/
/-- `dom(Γ) ⊆ dom(γ)`, at the `dom(Γ)` of convention L4 (`docs/adjudications.md`)
    declares: every LIVE slot of `Γ` has a value in `γ`.  `Γ` may run past the
    end of `γ` provided the slots that do are consumed, which a positional
    context reaches whenever a binder's slot has been used up. -/
def Ctx.LiveWithin {τ σ : Type} : Ctx τ → List σ → Prop
  | [],     _      => True
  | s :: Γ, []     => ¬ s.live ∧ Ctx.LiveWithin Γ ([] : List σ)
  | _ :: Γ, _ :: γ => Ctx.LiveWithin Γ γ

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
@[simp] theorem Ctx.liveWithin_nil {τ σ : Type} (γ : List σ) :
    Ctx.LiveWithin ([] : Ctx τ) γ := by cases γ <;> trivial

@[simp] theorem Ctx.liveWithin_cons {τ σ : Type} (s : Slot τ) (Γ : Ctx τ)
    (v : σ) (γ : List σ) : Ctx.LiveWithin (s :: Γ) (v :: γ) ↔ Ctx.LiveWithin Γ γ :=
  Iff.rfl

@[simp] theorem Ctx.liveWithin_cons_nil {τ σ : Type} (s : Slot τ) (Γ : Ctx τ) :
    Ctx.LiveWithin (s :: Γ) ([] : List σ) ↔ (¬ s.live ∧ Ctx.LiveWithin Γ ([] : List σ)) :=
  Iff.rfl

end BoCa

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
Row 4.15, continued.
-/
/-- `α ⊏ @bδ` as a proposition about the partial `@bδ`. -/
def LtLife (δ : LSub) (b : Lifetime.Life) (α : Life) : Prop :=
  ∃ β, b.interp δ = some β ∧ α ⊏ β

/-!
### 4.1 · `𝒱⟦1⟧δ(v) ≜ ⌜v = ()⌝` · [TR] p. 4 · `[as printed]`

`⌜v = .unit⌝` with `BoCa.Fig16.BoLo.pure` the printed `⌜−⌝` row of p. 6
-/
/-- **`𝒱⟦T⟧δ(v)`** — `[TR]` p. 4, `[as printed]`.  No covering list, no fuel,
and no code at `Mut`. -/
noncomputable def vDen : Ty → LSub → Val → WProp
  -- 𝒱⟦1⟧δ(v) ≜ ⌜v = ()⌝
  | .unit, _, v => ⌜v = .unit⌝
  -- 𝒱⟦T₁ ⊗ T₂⟧δ(v) ≜ ∃v₁,v₂. ⌜v = (v₁,v₂)⌝ ⋆ 𝒱⟦T₁⟧δ(v₁) ⋆ 𝒱⟦T₂⟧δ(v₂)
  | .tensor T₁ T₂, δ, v =>
      ex fun v₁ => ex fun v₂ =>
        ⌜v = .pair v₁ v₂⌝ ⋆ vDen T₁ δ v₁ ⋆ vDen T₂ δ v₂
  -- 𝒱⟦T₁ ⊕ T₂⟧δ(v) ≜ (∃v₁. ⌜v = inj₁ v₁⌝ ⋆ 𝒱⟦T₁⟧δ(v₁)) ∨ (∃v₂. …)
  | .sum T₁ T₂, δ, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vDen T₁ δ v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vDen T₂ δ v₂)
  -- 𝒱⟦T₁ ⊸ T₂⟧δ(v) ≜ ∀v′. 𝒱⟦T₁⟧δ(v′) ─⋆ ℰ⟦T₂⟧δ(v v′)
  | .lolli T₁ T₂, δ, v =>
      all fun v' => vDen T₁ δ v' ─⋆ wp (.app (.val v) (.val v')) (vDen T₂ δ)
  -- 𝒱⟦∀'x ⊏ @b. T⟧δ(v) ≜ ∀α. ⌜α ⊏ @bδ⌝ ─⋆ ℰ⟦T⟧_{δ['x↦α]}(v ())
  | .all x b T, δ, v =>
      all fun α =>
        ⌜LtLife δ b α⌝ ─⋆ wp (.app (.val v) (.val .unit)) (vDen T (δ.extend x α))
  -- 𝒱⟦[@a] T⟧δ(v) ≜ [@aδ] 𝒱⟦T⟧δ(v)
  | .box a T, δ, v => atLife δ a fun α => box α (vDen T δ v)
  -- 𝒱⟦Ref T⟧δ(v) ≜ ∃ℓ,v′. ⌜v = ℓ⌝ ⋆ ℓ ↦ v′ ⋆ 𝒱⟦T⟧δ(v′)
  | .ref T, δ, v =>
      ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vDen T δ v'
  -- 𝒱⟦Imm @a T⟧δ(v) ≜ ∃ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦ Imm @aδ 𝒱⟦T⟧δ
  | .imm a T, δ, v =>
      atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆ ptoImm ℓ α (vDen T δ)
  -- 𝒱⟦Mut @a T⟧δ(v) ≜ ∃ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦ Mut @aδ 𝒱⟦T⟧δ — the PREDICATE
  | .mut a T, δ, v =>
      atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆ ptoMut ℓ α (vDen T δ)
  -- 𝒱⟦Unk⟧δ(v) ≜ emp
  | .unk, _, _ => emp

end BoCa.Fig16.LogRel

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
variable (δ : LSub) (v : Val)

/-!
Row 4.1, continued.
-/
@[simp] theorem vDen_unit : vDen .unit δ v = ⌜v = .unit⌝ := rfl

/-!
### 4.10 · `𝒱⟦Unk⟧δ(v) ≜ emp` · [TR] p. 4 · `[as printed]`

Both `δ` and `v` ignored, as printed
-/
@[simp] theorem vDen_unk : vDen .unk δ v = emp := rfl

/-!
### 4.2 · `𝒱⟦T₁ ⊗ T₂⟧δ(v) ≜ ∃v₁,v₂. ⌜v = (v₁,v₂)⌝ ⋆ 𝒱⟦T₁⟧δ(v₁) ⋆ 𝒱⟦T₂⟧δ(v₂)` · [TR] p. 4 · `[as printed]`

`⋆` is infixr, and the print fixes no associativity for an associative connective
-/
theorem vDen_tensor (T₁ T₂ : Ty) :
    vDen (.tensor T₁ T₂) δ v =
      ex (fun v₁ => ex fun v₂ =>
        ⌜v = .pair v₁ v₂⌝ ⋆ vDen T₁ δ v₁ ⋆ vDen T₂ δ v₂) := rfl

/-!
### 4.3 · `𝒱⟦T₁ ⊕ T₂⟧δ(v) ≜ (∃v₁. ⌜v = inj₁ v₁⌝ ⋆ 𝒱⟦T₁⟧δ(v₁)) ∨ (∃v₂. ⌜v = inj₂ v₂⌝ ⋆ 𝒱⟦T₂⟧δ(v₂))` · [TR] p. 4 · `[as printed]`

`BoCa.Fig16.BoLo.or` is the pointwise ∨ of p. 6's display
-/
theorem vDen_sum (T₁ T₂ : Ty) :
    vDen (.sum T₁ T₂) δ v =
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vDen T₁ δ v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vDen T₂ δ v₂) := rfl

/-!
### 4.4 · `𝒱⟦T₁ ⊸ T₂⟧δ(v) ≜ ∀v′. 𝒱⟦T₁⟧δ(v′) ─⋆ ℰ⟦T₂⟧δ(v v′)` · [TR] p. 4 · `[repair]`

Two named choices: `ℰ⟦T₂⟧δ` is inlined as the `wp` it is defined to be (row 4.11), and the print's `v v′` — where values are a subset of expressions — becomes `.app (.val v) (.val v′)`. The cost of that injection is not here but in the machine (row 4.11)  **Repair (`docs/adjudications.md` §12.72).**  At the typed world the clause is Kripke over the record list: `BoCa.Fig16.LogRel.Typed.vX` quantifies over every list `BoCa.Fig16.LogRel.Typed.Ext`-above the current one at the closure's resource, and `ℰ` is `BoCa.Fig16.LogRel.Typed.wpTS` (row 5.33).  §12.72 argues it from the settled reading that §6 quantifies over resources that arise, with [CONF] 415:21 and 415:19; `BoCa.Fig16.LogRel.vDen_lolli` stays as the literal reading, which §12.68's configuration refuses
-/
theorem vDen_lolli (T₁ T₂ : Ty) :
    vDen (.lolli T₁ T₂) δ v =
      all (fun v' => vDen T₁ δ v' ─⋆ wp (.app (.val v) (.val v')) (vDen T₂ δ)) := rfl

/-!
### 4.5 · `𝒱⟦∀ 'a ⊏ @b. T⟧δ(v) ≜ ∀ α ⊏ @bδ. ℰ⟦T⟧δ(v ())` · [TR] p. 4 · `[repair]`

The print's subscript is a bare `δ`; Lean writes `ℰ⟦T⟧` at `δ` extended by `'a ↦ α`, which is [CONF] p. 415:12. As printed, `α` is bound and never used, so the clause degenerates and `T`'s occurrences of `'a` are read by the outer `δ`. Also encoding: the printed bounded `∀ α ⊏ @bδ.` becomes an unbounded ∀ guarded by a `⌜−⌝`, sound because a pure proposition holds only of ∅, and `BoCa.Fig16.LogRel.LtLife` makes an undefined `@bδ` empty the quantifier rather than the clause. Adjudicated here: the printed form cannot be right, since `α` would be bound and never used while `T`'s occurrences of `'a` are read by the outer δ, at which `'a` need not even be defined. [CONF] p. 415:12 prints `ℰ⟦T⟧δ['a↦α]` and its prose says the substitution is extended at each quantifier — corroboration only, since the argument is internal to [TR] p. 4  **And at the typed world (`docs/adjudications.md` §12.72)**, Kripke over the record list as row 4.4
-/
theorem vDen_all (x : LifeVar) (b : Lifetime.Life) (T : Ty) :
    vDen (.all x b T) δ v =
      all (fun α =>
        ⌜LtLife δ b α⌝ ─⋆
          wp (.app (.val v) (.val .unit)) (vDen T (δ.extend x α))) := rfl

/-!
Row 4.6, continued.
-/
theorem vDen_box (a : Lifetime.Life) (T : Ty) :
    vDen (.box a T) δ v = atLife δ a (fun α => box α (vDen T δ v)) := rfl

/-!
### 4.7 · `𝒱⟦Ref T⟧δ(v) ≜ ∃ℓ,v′. ⌜v = ℓ⌝ ⋆ ℓ ↦ v′ ⋆ 𝒱⟦T⟧δ(v′)` · [TR] p. 4 · `[as printed]`

`BoCa.Fig16.BoLo.ptoOwn` is [TR] p. 6's own `ℓ ↦ v` row; no lifetime, so no partiality to absorb
-/
theorem vDen_ref (T : Ty) :
    vDen (.ref T) δ v =
      ex (fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vDen T δ v') := rfl

/-!
### 4.8 · `𝒱⟦Imm @a T⟧δ(v) ≜ ∃ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦ Imm @aδ 𝒱⟦T⟧δ` · [TR] p. 4 · `[repair]`

The same `BoCa.Fig16.LogRel.atLife` choice as row 4.6, plus the `∃α` it introduces is hoisted OUTSIDE the printed `∃ℓ`; sound because `α` is a function of `δ` and `@a` alone. The payload is the predicate `𝒱⟦T⟧δ`, as printed  **Three repairs at the typed world.**  (i) The payload is held at its observable view — `⊸`/`∀` positions not under a `Mut` relaxed to `True` (`BoCa.Fig16.LogRel.Typed.vO_obs`: a weakening) — per [CONF] 415:9's *"no view at which it would be safe to access the payload"*, Fig. 8's `Imm̲` sending `⊸`/`∀` to `Unk`, 415:15's *"obfuscates any closures"* and [TR] 6.131's `⊸`/`∀` bullets (`docs/adjudications.md` §12.69). (ii) The payload holds at the records strictly longer-lived than the cell (§12.70). (iii) The clause carries `CohE`: the program's type is the type the world recorded at the cell, up to `BoCa.Fig16.LogRel.Typed.TyEq`, 6.150's H12/H19 read through [TR] p. 18's *"witnesses and values always stay the same"* and [CONF] 415:19's *"same witness"* (§12.71). `BoCa.Fig16.LogRel.vDen_imm` stays as the literal reading
-/
theorem vDen_imm (a : Lifetime.Life) (T : Ty) :
    vDen (.imm a T) δ v =
      atLife δ a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆ ptoImm ℓ α (vDen T δ)) := rfl

/-!
### 4.9 · `𝒱⟦Mut @a T⟧δ(v) ≜ ∃ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦ Mut @aδ 𝒱⟦T⟧δ` · [TR] p. 4 · `[repair]`

On the printed carrier the cell stores the PREDICATE, which is what Fig. 16 row 5 prints, and only the `atLife` hoist of row 4.8 is an encoding step. Note also that the printed clause silently carries Fig. 16 row 5's stratum typing, and row 4.17 proves it EMPTY at `Mut @a (Imm @b 1)` — `exact` here does not mean inhabited  **Repair at the typed world (`docs/adjudications.md` §12.70).**  The cell stores `𝒱⟦T⟧` at the records strictly longer-lived than its lifetime, and the family lies in `Res_b` at every list — [TR] p. 4's `P̂ : Val → SProp_β`, 6.65's `P̂ ⊧ [β]P̂`, [CONF] 415:20 and 415:25's stratification, lifted to the list — so the stored predicate stays equal along `BoCa.Fig16.LogRel.Typed.Ext`. `BoCa.Fig16.LogRel.vDen_mut` stays as the literal reading
-/
/-- **The `Mut` clause, on the nose.**  The cell holds `P̂` itself. -/
theorem vDen_mut (a : Lifetime.Life) (T : Ty) :
    vDen (.mut a T) δ v =
      atLife δ a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆ ptoMut ℓ α (vDen T δ)) := rfl

end BoCa.Fig16.LogRel

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
### 4.11 · `ℰ⟦T⟧δ(v) ≜ wp (e) {𝒱⟦T⟧δ}` · [TR] p. 4 · `[repair]`

The row's shape is exact — the printed left-hand side binds `v` where the right-hand side uses `e`, and Lean reads `e`, correctly. What diverges is the `wp` it names: `BoCa.Fig16.BoLo.wp` runs `BoCa.BoLo.Steps`, whose `Kont` has ten frames where p. 3 prints seven (rows 3.30, 3.31), its `Head` being the p. 4 box exactly. A larger step relation makes `wp` easier to satisfy, so Lean's ℰ is strictly LARGER than [TR]'s. `BoCa.TR3.wp` re-proves over the printed machine the §6.7 rules `docs/adjudications.md` D6 enumerates (6.135–6.149, all of them) and refutes the rest; `BoCa.TR3.wp_le_fig16` gives one direction only. Adjudicated at `docs/adjudications.md` §12.42 and D6: [TR] §3's box is elided, not exact — `inj₁ (free (alloc ()))` and `free (alloc ()); ()` are closed, typed by [TR] p. 2, and irreducible on the printed machine (`BoCa.TR3.stuck_wInj`, `BoCa.TR3.stuck_wSeq`) — and priced at the level of `wp` (`BoCa.TR3.wp_inj₁_false`, `BoCa.TR3.wp_seq_false`). The entry's narrowing of `BoCa.BoLo.Head.seq` to the printed `1↦` is current in the code  **And at the typed world**, `ℰ` names `BoCa.Fig16.LogRel.Typed.wpTS`, row 5.33's repair (`docs/adjudications.md` §12.72)
-/
/-- **`ℰ⟦T⟧δ(e) ≜ wp(e){𝒱⟦T⟧δ}`**  (`[TR]` p. 4).  `[as printed]` -/
noncomputable def eDen (δ : LSub) (T : Ty) (e : Expr) : WProp := wp e (vDen T δ)

/-!
Row 4.13, continued.
-/
/-- `⊛_{x ∈ dom(Γ)} 𝒱⟦Γ(x)⟧δ(γ(x))`.  `Γ` is positional, so `dom(Γ)` is the
LIVE slots and a consumed slot contributes no conjunct
(convention L4, `docs/adjudications.md`). -/
noncomputable def gSep (δ : LSub) : Ctx Ty → List Val → WProp
  | [],     _      => emp
  | _ :: _, []     => emp
  | s :: Γ, v :: γ => if s.live then vDen s.ty δ v ⋆ gSep δ Γ γ else gSep δ Γ γ

/-!
Row 4.13, continued.
-/
/-- **`𝒢⟦Γ⟧δ(γ) ≜ ⌜dom(Γ) ⊆ dom(γ)⌝ ⋆ ⊛_{x∈dom(Γ)} 𝒱⟦Γ(x)⟧δ(γ(x))`**
(`[TR]` p. 4; `dom(γ)` for the printed `dom(δ)`).  Both halves read
`dom(Γ)` the same way, the LIVE slots of convention L4: the pure conjunct is
`Ctx.LiveWithin`, not `Γ.length ≤ γ.length`, so a consumed slot past the end of
`γ` is out of scope for the containment exactly as it is for the `⊛`.
`[as printed]` -/
noncomputable def gDen (δ : LSub) (Γ : Ctx Ty) (γ : List Val) : WProp :=
  ⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSep δ Γ γ

/-!
### 4.14 · `Δ; Γ ⊨ e : T ≜ !∀ δ,γ. 𝒟⟦Δ⟧(δ) ─⋆ 𝒢⟦Γ⟧δ(γ) ─⋆ ℰ⟦T⟧δ(γ(e))` · [TR] p. 4 · `[repair]`

Shape glyph for glyph, and `─⋆` right-associates as the print does. Named choice: `γ(e)` is `BoCa.Expr.psub`, a PARALLEL substitution rather than a fold of single substitutions — the fold is the closing substitution only for closed γ, because `BoCa.Expr.subst` descends into `BoCa.Expr.val`. Inherits rows 4.11 and 4.13 in full  **Repair at the typed world (`docs/adjudications.md` §12.69–§12.72).**  `BoCa.Fig16.LogRel.Typed.SemX` is this judgment at `BoCa.Fig16.LogRel.Typed.vX` and `BoCa.Fig16.LogRel.Typed.wpTS`, at every record list; [TR] 6.151 holds at it with no hypothesis beyond p. 2's presuppositions (`BoCa.Fig16.LogRel.Typed.fundamentalProperty`). `BoCa.Fig16.LogRel.SemTy` stays as the literal reading
-/
/-- **`Δ; Γ ⊨ e : T ≜ !∀δ,γ. 𝒟⟦Δ⟧(δ) ─⋆ 𝒢⟦Γ⟧δ(γ) ─⋆ ℰ⟦T⟧δ(γ(e))`**
(`[TR]` p. 4).  `[as printed]` -/
noncomputable def SemTy (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty) : WProp :=
  !ₛ(all fun δ => all fun γ =>
      dDen Δ δ ─⋆ (gDen δ Γ γ ─⋆ eDen δ T (substAll γ e)))

/-!
### 4.16 · — no printed counterpart — · [TR] p. 4 · `[repair]`

Fig. 16 row 5's `P̂ : Val → SProp_β` as a predicate, because the model file encodes `SProp_β` as a SUBSET of `SProp` rather than a type. Forced by putting the real predicate in the `mut` cell; it makes visible the side condition the printed `Mut` clause carries silently. Adjudicated here: Fig. 16 row 5's `P̂ : Val → SProp_β` is a TYPE, and the carrier encodes `SProp_β` as a subset of `SProp` (`BoCa.Fig16.SPropS.toU_range`), so on this carrier the condition is not enforceable by typing and has to be re-expressed as a predicate to be stated at all. [TR] p. 4 writes the relation with the unsubscripted `SProp` while printing both `SProp` and `SProp_α`, so which stratum 𝒱 inhabits is a condition the print carries silently. Both directions are proved
-/
/-- `P̂ : Val → SProp_β`, on the printed carrier: `Fig16.SPropS.toU_range` at a
family of propositions.
`[about ours: Fig. 16 row 5's field type, as the subset of `SProp` that
`Fig16.SPropS.toU_range` says it is]` -/
def Supported (β : Life) (P : Val → WProp) : Prop := ∀ v ρ, P v ρ → ρ.InStratum β

/-!
Row 4.16, continued.
-/
/-- `Supported` is membership in the image of `SPropS.toU`, at each value —
i.e. `P` really is a `Val → SProp_β` and not merely bounded by one. -/
theorem supported_iff (β : Life) (P : Val → WProp) :
    Supported β P ↔ ∀ v, ∃ Q : SPropS BoCa.Loc BoCa.Val β, SPropS.toU Q = P v := by
  constructor
  · exact fun h v => (SPropS.toU_range β (P v)).mpr (fun ρ => h v ρ)
  · exact fun h v ρ hρ => (SPropS.toU_range β (P v)).mp (h v) ρ hρ

end BoCa.Fig16.LogRel

end
