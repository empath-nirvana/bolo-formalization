import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S3_Dynamics.Definitions
import Paper.S5_Model.Definitions
import Support.Dynamics.Machine
import Support.Lifetimes.AfterS2
import Support.LogicalRelation.AfterS5
import Support.Model.AfterS5
import Support.Syntax
import Support.TypedWorld

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

**Two readings of this display are here, and both are kept.**  The literal one
is `Fig16.LogRel.vDen`, `eDen`, `gDen`, `SemTy`: each clause as printed, over
`[TR]` p. 6's `wp`.  The repaired one is the typed world, `Fig16.LogRel.Typed.vX`,
`wpTS`, `gDenX`, `SemX` (source `docs/boca-rules.md` §12.69–§12.72): an `Imm`
payload is read at its observable view, borrow payloads are stratified by a
record list, the `Imm` clause carries the type the world recorded at the cell,
`⊸`/`∀` are Kripke over the record list, and `wp` ranges over the tagged typed
worlds `TW` that the printed proofs' operations produce.  `[TR]` 6.151 holds at
the repaired judgment with no hypothesis; at the literal one it needs
`WithloadEscrow`, which the configuration `Fig16.LogRel.ViewWitness` refuses
(source `BoCa/ViewWitness.lean`).
The typed world's `wp` (row 5.33's repair) is in this file rather than in §5's:
the worlds it ranges over are defined through value shapes, which read
lifetimes through this section's `atLife` (row 4.15).

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

Row numbers are those of the source repository's `docs/definition-inventory.md`;
citations of `docs/…` and `BoCa/…` are to that repository (`borrow_lang` at
`970a9d0`).  Declaration names are the source's, unchanged, so that
`Bridge/Names.csv` can check each one against its original.
-/

noncomputable section

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
### 4.6 · `𝒱⟦[@a] T⟧δ(v) ≜ [@aδ] 𝒱⟦T⟧δ(v)` · [TR] p. 4 · `[encoding]`

Named choice: `BoCa.Lifetime.Life.interp` is partial, so `@aδ` in an argument position is wrapped as `∃α. @aδ = α ∧ …`; `BoCa.Fig16.LogRel.atLife_eq` reduces that to the printed clause wherever `@aδ` is defined, which 𝒟⟦Δ⟧ plus `Δ ⊢ T` guarantee. An undefined `@aδ` is read as False — a case the print does not address

### 4.15 · — no printed counterpart — · [TR] p. 4 · `[repair]`

Forced by `BoCa.Lifetime.Life.interp` being partial: p. 3 prints `@aδ` as a partial function and never says what a clause means when it is undefined. `atLife` fixes the argument position to False, `LtLife` fixes the bound position to a vacuous quantifier. Adjudicated at `BoCa/LogRel.lean` convention L3 and §1, restated at `BoCa/Fig16LogRel.lean` §1 and corroborated by `docs/axiom-ledger.md` C14: `@aδ` is partial in the sources themselves ([CONF] Fig. 11 gives `aδ ≜ δ('a)`, undefined off `dom(δ)`) and neither document says what a clause means when it is undefined, so a total reading must be chosen and the grammatical position, not us, decides which. [TR]'s own proof of 6.161 (p. 42) introduces `α ⊏ @bδ` without first establishing `@bδ`, which only the `LtLife` reading allows
-/
/-- `@aδ` as a connective's ARGUMENT. -/
def atLife (δ : LSub) (a : Lifetime.Life) (F : Life → SPropU BoCa.Loc BoCa.Val) :
    WProp :=
  fun ρ => ∃ α, a.interp δ = some α ∧ F α ρ

end BoCa.Fig16.LogRel

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-!
### 4.8 · `𝒱⟦Imm @a T⟧δ(v) ≜ ∃ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦ Imm @aδ 𝒱⟦T⟧δ` · [TR] p. 4 · `[repair]`

The same `BoCa.Fig16.LogRel.atLife` choice as row 4.6, plus the `∃α` it introduces is hoisted OUTSIDE the printed `∃ℓ`; sound because `α` is a function of `δ` and `@a` alone. The payload is the predicate `𝒱⟦T⟧δ`, as printed  **Three repairs at the typed world.**  (i) The payload is held at its observable view — `⊸`/`∀` positions not under a `Mut` relaxed to `True` (`BoCa.Fig16.LogRel.Typed.vO_obs`: a weakening) — per [CONF] 415:9's *"no view at which it would be safe to access the payload"*, Fig. 8's `Imm̲` sending `⊸`/`∀` to `Unk`, 415:15's *"obfuscates any closures"* and [TR] 6.131's `⊸`/`∀` bullets (`docs/boca-rules.md` §12.69). (ii) The payload holds at the records strictly longer-lived than the cell (§12.70). (iii) The clause carries `CohE`: the program's type is the type the world recorded at the cell, up to `BoCa.Fig16.LogRel.Typed.TyEq`, 6.150's H12/H19 read through [TR] p. 18's *"witnesses and values always stay the same"* and [CONF] 415:19's *"same witness"* (§12.71). `BoCa.Fig16.LogRel.vDen_imm` stays as the literal reading
-/
/-- **`ℓ ↦ I_α 𝒱⟦S⟧(ls|⊐⊓β̄)δ`**: an `imm` cell `imm(β̄, u, σ)` with `α ⊑ ⊓β̄` whose payload
holds at `ls₀`, the members of `ls` strictly longer-lived than the cell (`@ψ = ⊓β̄`).  The
cell stores no predicate; `ls₀` is fixed by the cell's lifetime, which `Ext` keeps.
`[about ours: [TR] p. 4's Imm clause, the list stratified at the cell's lifetime]` -/
def ptoImmS (l : Loc) (α : Life) (ls : List SRec) (P : List SRec → Val → WProp) : WProp :=
  fun ρ => ∃ (s : LSet) (u : Val) (σ : WRes) (h : σ.InStratum s.join) (ls₀ : List SRec),
    ρ = ResU.single l (CellU.immOf s u σ h) ∧ P ls₀ u σ ∧ α ⊑ s.meet ∧
    ∀ x, x ∈ ls₀ ↔ (x ∈ ls ∧ x.2 ⊐ s.meet)

/-!
Row 4.8, continued.
-/
/-- **`Coh` up to `TyEq`.**  `[about ours]` -/
def CohE (rs : List FrameRec) (m : Loc) (S : Ty) (δ : LSub) : Prop :=
  ∃ S₀ δ₀, TyEq S δ S₀ δ₀ ∧ Coh rs m S₀ δ₀

/-!
### 4.9 · `𝒱⟦Mut @a T⟧δ(v) ≜ ∃ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦ Mut @aδ 𝒱⟦T⟧δ` · [TR] p. 4 · `[repair]`

On the printed carrier the cell stores the PREDICATE, which is what Fig. 16 row 5 prints, and only the `atLife` hoist of row 4.8 is an encoding step. The OLD carrier is divergent here: its `mut` clause stores a type CODE, with `BoCa.LogRel.vDen_mut_ptoMut` only a one-way bridge back. Note also that the printed clause silently carries Fig. 16 row 5's stratum typing, and row 4.17 proves it EMPTY at `Mut @a (Imm @b 1)` — `exact` here does not mean inhabited  **Repair at the typed world (`docs/boca-rules.md` §12.70).**  The cell stores `𝒱⟦T⟧` at the records strictly longer-lived than its lifetime, and the family lies in `Res_b` at every list — [TR] p. 4's `P̂ : Val → SProp_β`, 6.65's `P̂ ⊧ [β]P̂`, [CONF] 415:20 and 415:25's stratification, lifted to the list — so the stored predicate stays equal along `BoCa.Fig16.LogRel.Typed.Ext`. `BoCa.Fig16.LogRel.vDen_mut` stays as the literal reading
-/
/-- **`ℓ ↦ M_α 𝒱⟦S⟧(ls|⊐b)δ`**: a `mut` cell at `b ⊒ α` whose stored predicate is
`P ls₀`, `ls₀` having the members of `ls` strictly longer-lived than `b`; and `P̂ : Val →
SProp_b` — the family `P` lies in `Res_b` at every list.  The last conjunct is `[TR]` p. 4's
`Mut_α ≜ {(β ⊐ α, v, ρ : Res_β, P̂ : Val → SProp_β) | …}`, the type of `P̂`, read of the
family: the paper's `𝒱⟦S⟧δ` is one predicate, ours one per list.
`[about ours: [TR] p. 4's Mut clause, the list stratified at the cell's lifetime]` -/
def ptoMutS (l : Loc) (α : Life) (ls : List SRec) (P : List SRec → Val → WProp) : WProp :=
  fun ρ => ∃ (b : Life) (u : Val) (σ : WRes) (h : σ.InStratum b)
      (Q : Val → SPropS Loc Val b) (hw : Q u ⟨σ, h⟩) (ls₀ : List SRec),
    α ⊑ b ∧ ρ = ResU.single l (CellU.mutOf b u σ h Q hw) ∧ ofS Q = P ls₀ ∧
    (∀ x, x ∈ ls₀ ↔ (x ∈ ls ∧ x.2 ⊐ b)) ∧ ∀ ls' u' σ', P ls' u' σ' → σ'.InStratum b

end BoCa.Fig16.LogRel.Typed

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont)

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

Two differences, both adjudicated. (1) The print says `dom(δ)` where Lean says `dom(γ)`: `BoCa/LogRel.lean` §10 (d15), since Γ maps term variables and δ lifetime variables, so the printed containment is not type-correct. (2) The printed left-hand side carries no `δ` subscript though its right-hand side uses δ free; Lean takes δ as a parameter, which is row 4.14's reading of the same page.
-/
/-- `dom(Γ) ⊆ dom(γ)`, at the `dom(Γ)` `BoCa/LogRel.lean`'s convention L4
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
open BoCa.BoLo (Heap Steps Step1 Head Kont)

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
open BoCa.BoLo (Heap Steps Step1 Head Kont)
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

Two named choices: `ℰ⟦T₂⟧δ` is inlined as the `wp` it is defined to be (row 4.11), and the print's `v v′` — where values are a subset of expressions — becomes `.app (.val v) (.val v′)`. The cost of that injection is not here but in the machine (row 4.11)  **Repair (`docs/boca-rules.md` §12.72).**  At the typed world the clause is Kripke over the record list: `BoCa.Fig16.LogRel.Typed.vX` quantifies over every list `BoCa.Fig16.LogRel.Typed.Ext`-above the current one at the closure's resource, and `ℰ` is `BoCa.Fig16.LogRel.Typed.wpTS` (row 5.33).  §12.72 argues it from the settled reading that §6 quantifies over resources that arise, with [CONF] 415:21 and 415:19; `BoCa.Fig16.LogRel.vDen_lolli` stays as the literal reading, which §12.68's configuration refuses
-/
theorem vDen_lolli (T₁ T₂ : Ty) :
    vDen (.lolli T₁ T₂) δ v =
      all (fun v' => vDen T₁ δ v' ─⋆ wp (.app (.val v) (.val v')) (vDen T₂ δ)) := rfl

end BoCa.Fig16.LogRel

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-!
Rows 4.4, 4.8, 4.9, continued.

### 4.5 · `𝒱⟦∀ 'a ⊏ @b. T⟧δ(v) ≜ ∀ α ⊏ @bδ. ℰ⟦T⟧δ(v ())` · [TR] p. 4 · `[repair]`

The print's subscript is a bare `δ`; Lean writes `ℰ⟦T⟧` at `δ` extended by `'a ↦ α`, which is [CONF] p. 415:12. As printed, `α` is bound and never used, so the clause degenerates and `T`'s occurrences of `'a` are read by the outer `δ`. Also encoding: the printed bounded `∀ α ⊏ @bδ.` becomes an unbounded ∀ guarded by a `⌜−⌝`, sound because a pure proposition holds only of ∅, and `BoCa.Fig16.LogRel.LtLife` makes an undefined `@bδ` empty the quantifier rather than the clause. Adjudicated at `BoCa/LogRel.lean` §10 (d14), inherited by name in `BoCa/Fig16LogRel.lean`'s header: the printed form cannot be right, since `α` would be bound and never used while `T`'s occurrences of `'a` are read by the outer δ, at which `'a` need not even be defined. [CONF] p. 415:12 prints `ℰ⟦T⟧δ['a↦α]` and its prose says the substitution is extended at each quantifier — corroboration only, since (d14)'s argument is internal to [TR] p. 4  **And at the typed world (`docs/boca-rules.md` §12.72)**, Kripke over the record list as row 4.4
-/
/-- **`𝒱X full ⟦T⟧(ls)δ(v)`.**  `full = true`: the program's relation.  `full = false`: the
observable view an `imm` cell's payload is held at — `⊸`/`∀` positions relaxed to `True`.
`[about ours: [TR] p. 4's Imm clause with its payload read at the observable view, per
[CONF] 415:10 and 415:15; docs/boca-rules.md §12.69–§12.72]` -/
def vX (wpX : WpOp) : Bool → Ty → List SRec → LSub → Val → WProp
  | _, .unit, _, _, v => ⌜v = .unit⌝
  | b, .tensor T₁ T₂, ls, δ, v =>
      ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆ vX wpX b T₁ ls δ v₁ ⋆ vX wpX b T₂ ls δ v₂
  | b, .sum T₁ T₂, ls, δ, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vX wpX b T₁ ls δ v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vX wpX b T₂ ls δ v₂)
  | true, .lolli T₁ T₂, ls, δ, v => fun ρ =>
      ∀ ls', Ext ls ls' ρ → ∀ v',
        (vX wpX true T₁ ls' δ v' ─⋆
          wpX ls' (.app (.val v) (.val v')) (fun ls'' => vX wpX true T₂ ls'' δ)) ρ
  | false, .lolli _ _, _, _, _ => fun _ => True
  | true, .all x c T, ls, δ, v => fun ρ =>
      ∀ ls', Ext ls ls' ρ → ∀ α,
        (⌜LtLife δ c α⌝ ─⋆ wpX ls' (.app (.val v) (.val .unit))
          (fun ls'' => vX wpX true T ls'' (δ.extend x α))) ρ
  | false, .all _ _ _, _, _, _ => fun _ => True
  | b, .box a T, ls, δ, v => atLife δ a fun α => box α (vX wpX b T ls δ v)
  | b, .ref T, ls, δ, v =>
      ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vX wpX b T ls δ v'
  | _, .imm a T, ls, δ, v =>
      atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ ∧ CohE (rsOf ls) ℓ T δ⌝ ⋆
        ptoImmS ℓ α ls (fun ls₀ => vX wpX false T ls₀ δ)
  | _, .mut a T, ls, δ, v =>
      atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
        ptoMutS ℓ α ls (fun ls₀ => vX wpX true T ls₀ δ)
  | _, .unk, _, _, _ => emp

end BoCa.Fig16.LogRel.Typed

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont)
variable (δ : LSub) (v : Val)

/-!
Row 4.5, continued.
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
Row 4.8, continued.
-/
theorem vDen_imm (a : Lifetime.Life) (T : Ty) :
    vDen (.imm a T) δ v =
      atLife δ a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆ ptoImm ℓ α (vDen T δ)) := rfl

/-!
Row 4.9, continued.
-/
/-- **The `Mut` clause, on the nose.**  `ResI` could not state this: its `mut`
cell holds a `TyConj`, so `LogRel.vDen_mut` reads `ℓ ↦ M α ⟨T⟩` and
`LogRel.vDen_mut_ptoMut` is a one-way bridge.  Here the cell holds `P̂` itself. -/
theorem vDen_mut (a : Lifetime.Life) (T : Ty) :
    vDen (.mut a T) δ v =
      atLife δ a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆ ptoMut ℓ α (vDen T δ)) := rfl

end BoCa.Fig16.LogRel

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
### 4.11 · `ℰ⟦T⟧δ(v) ≜ wp (e) {𝒱⟦T⟧δ}` · [TR] p. 4 · `[repair]`

The row's shape is exact — the printed left-hand side binds `v` where the right-hand side uses `e`, and Lean reads `e`, correctly. What diverges is the `wp` it names: `BoCa.Fig16.BoLo.wp` runs `BoCa.BoLo.Steps`, whose `Kont` has ten frames where p. 3 prints seven (rows 3.30, 3.31), its `Head` being the p. 4 box exactly. A larger step relation makes `wp` easier to satisfy, so Lean's ℰ is strictly LARGER than [TR]'s. `BoCa/TR3.lean` re-proves over the printed machine the §6.7 rules `docs/axiom-ledger.md` D6 enumerates (6.135–6.149, all of them) and refutes the rest; `BoCa.TR3.wp_le_fig16` gives one direction only. Adjudicated at `docs/boca-rules.md` §12.42 and `docs/axiom-ledger.md` D6, instantiated clause by clause in `BoCa/Fig16LogRel.lean` §10 and §11: [TR] §3's box is elided, not exact — `inj₁ (free (alloc ()))` and `free (alloc ()); ()` are closed, typed by [TR] p. 2, and irreducible on the printed machine (`BoCa.TR3.stuck_wInj`, `BoCa.TR3.stuck_wSeq`) — and priced at the level of `wp` (`BoCa.TR3.wp_inj₁_false`, `BoCa.TR3.wp_seq_false`). The entry's narrowing of `BoCa.BoLo.Head.seq` to the printed `1↦` is current in the code  **And at the typed world**, `ℰ` names `BoCa.Fig16.LogRel.Typed.wpTS`, row 5.33's repair (`docs/boca-rules.md` §12.72)
-/
/-- **`ℰ⟦T⟧δ(e) ≜ wp(e){𝒱⟦T⟧δ}`**  (`[TR]` p. 4).  `[as printed]` -/
noncomputable def eDen (δ : LSub) (T : Ty) (e : Expr) : WProp := wp e (vDen T δ)

/-!
Row 4.13, continued.
-/
/-- `⊛_{x ∈ dom(Γ)} 𝒱⟦Γ(x)⟧δ(γ(x))`.  `Γ` is positional, so `dom(Γ)` is the
LIVE slots and a consumed slot contributes no conjunct
(`BoCa/LogRel.lean` convention L4). -/
noncomputable def gSep (δ : LSub) : Ctx Ty → List Val → WProp
  | [],     _      => emp
  | _ :: _, []     => emp
  | s :: Γ, v :: γ => if s.live then vDen s.ty δ v ⋆ gSep δ Γ γ else gSep δ Γ γ

/-!
Row 4.13, continued.
-/
/-- **`𝒢⟦Γ⟧δ(γ) ≜ ⌜dom(Γ) ⊆ dom(γ)⌝ ⋆ ⊛_{x∈dom(Γ)} 𝒱⟦Γ(x)⟧δ(γ(x))`**
(`[TR]` p. 4; `dom(γ)` is `BoCa/LogRel.lean` §10 (d15)).  Both halves read
`dom(Γ)` the same way, the LIVE slots of convention L4: the pure conjunct is
`Ctx.LiveWithin`, not `Γ.length ≤ γ.length`, so a consumed slot past the end of
`γ` is out of scope for the containment exactly as it is for the `⊛`.
`[as printed]` -/
noncomputable def gDen (δ : LSub) (Γ : Ctx Ty) (γ : List Val) : WProp :=
  ⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSep δ Γ γ

/-!
### 4.14 · `Δ; Γ ⊨ e : T ≜ !∀ δ,γ. 𝒟⟦Δ⟧(δ) ─⋆ 𝒢⟦Γ⟧δ(γ) ─⋆ ℰ⟦T⟧δ(γ(e))` · [TR] p. 4 · `[repair]`

Shape glyph for glyph, and `─⋆` right-associates as the print does. Named choice: `γ(e)` is `BoCa.Expr.psub`, a PARALLEL substitution rather than a fold of single substitutions — the fold is the closing substitution only for closed γ, because `BoCa.Expr.subst` descends into `BoCa.Expr.val`. Inherits rows 4.11 and 4.13 in full  **Repair at the typed world (`docs/boca-rules.md` §12.69–§12.72).**  `BoCa.Fig16.LogRel.Typed.SemX` is this judgment at `BoCa.Fig16.LogRel.Typed.vX` and `BoCa.Fig16.LogRel.Typed.wpTS`, at every record list; [TR] 6.151 holds at it with no hypothesis beyond p. 2's presuppositions (`BoCa.Fig16.LogRel.Typed.fundamentalProperty`). `BoCa.Fig16.LogRel.SemTy` stays as the literal reading
-/
/-- **`Δ; Γ ⊨ e : T ≜ !∀δ,γ. 𝒟⟦Δ⟧(δ) ─⋆ 𝒢⟦Γ⟧δ(γ) ─⋆ ℰ⟦T⟧δ(γ(e))`**
(`[TR]` p. 4).  `[as printed]` -/
noncomputable def SemTy (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty) : WProp :=
  !ₛ(all fun δ => all fun γ =>
      dDen Δ δ ─⋆ (gDen δ Γ γ ─⋆ eDen δ T (substAll γ e)))

/-!
### 4.16 · — no printed counterpart — · [TR] p. 4 · `[repair]`

Fig. 16 row 5's `P̂ : Val → SProp_β` as a predicate, because the model file encodes `SProp_β` as a SUBSET of `SProp` rather than a type. Forced by putting the real predicate in the `mut` cell; it makes visible the side condition the printed `Mut` clause carries silently. Adjudicated at `BoCa/Fig16LogRel.lean` §3's preamble with `BoCa/Fig16.lean` §24: Fig. 16 row 5's `P̂ : Val → SProp_β` is a TYPE, and §24 encodes `SProp_β` as a subset of `SProp` (`BoCa.Fig16.SPropS.toU_range`), so on this carrier the condition is not enforceable by typing and has to be re-expressed as a predicate to be stated at all. [TR] p. 4 writes the relation with the unsubscripted `SProp` while printing both `SProp` and `SProp_α`, so which stratum 𝒱 inhabits is a condition the print carries silently. Both directions are proved
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

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
/-- **`𝒱⟦T⟧`'s shape**: `vDen` with the `⊸` and `∀` clauses dropped (no `wp`, so no world
family), and the `Mut` clause asking the stored predicate to be *contained in* the shape
rather than equal to it.  A record or a `TW` premise at `vShape` mentions no `TW`.
`[about ours: our wp-free payload predicate]` -/
def vShape : Ty → LSub → Val → WProp
  | .unit, _, v => ⌜v = .unit⌝
  | .tensor T₁ T₂, δ, v =>
      ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆ vShape T₁ δ v₁ ⋆ vShape T₂ δ v₂
  | .sum T₁ T₂, δ, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vShape T₁ δ v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vShape T₂ δ v₂)
  | .lolli _ _, _, _ => fun _ => True
  | .all _ _ _, _, _ => fun _ => True
  | .box a T, δ, v => atLife δ a fun α => box α (vShape T δ v)
  | .ref T, δ, v => ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vShape T δ v'
  | .imm a T, δ, v => atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆ ptoImm ℓ α (vShape T δ)
  | .mut a T, δ, v => atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
      fun ρ => ∃ P, ptoMut ℓ α P ρ ∧ ∀ u σ, P u σ → vShape T δ u σ
  | .unk, _, _ => emp

/-!
### 5.33 · `wp (e) {Q̂} (ρ) ≜ ∀ρ_f # ρ. ∃ρ′ # ρ_f, ρ⁺ # (ρ_f ● ρ′), v. (⟦ρ_f ● ρ⟧,e) →* (⟦ρ_f ● ρ′ ● ρ⁺⟧,v) ∧ ρ ↭ ρ′ ● ρ⁺ ∧ ρ⁺∣own = ∅ ∧ Q̂(v)(ρ′)` · [TR] p. 6, proposition row 5 · `[repair]`

The row's own shape is transcribed exactly — every partial term bound and related by its graph, ↭ at [TR]'s guarded reading, the own-free side condition as `BoCa.Fig16.BoLo.NoOwn` — but `→*` is `BoCa.BoLo.Steps`, the completed machine of rows 3.14, 3.30 and 3.31, so this `wp` is strictly WEAKER than the printed row. Adjudicated at `docs/boca-rules.md` §12.42, `docs/axiom-ledger.md` D6 and `BoCa/Fig16Wp.lean`'s "What the machine costs": [TR] §3's `Kont` is elided rather than exact, and [CONF] Corollary 3.3's conclusion is unreachable on the machine as printed at a closed term p. 2 types at `1` (`BoCa.TR3.derives_wSeq`, `BoCa.TR3.corThree_unreachable`); every addition is a frame, and `BoCa/TR3.lean` re-proves §6.7 over the printed machine with `BoCa.TR3.wp_le_fig16` between  **And at the typed world (`docs/boca-rules.md` §12.72)**: `∀ρ_f # ρ` ranges over the frames completing `ρ` to a `BoCa.Fig16.LogRel.Typed.TW` world at the record list, tagged, and the post-configuration is one too, with the same records and list members; every other conjunct is this row's. The settled reading that §6 quantifies over resources that arise; §12.68's configuration is one no program produces, and `BoCa.Fig16.LogRel.ViewWitness.excluded` shows the typed world excludes it (§12.73)
-/
/-- **The typed world.**  `TW W ps rs`: the configuration `W` — every frame together with the
resource a `wp` runs at, `[TR]` p. 6's `ρ_f ● ρ` — is reached from `∅` by the operations the
printed proofs perform, and `ps` are the frames `[TR]` 6.64 has taken and not ended, `rs` those
frames with every sub-record of their lineages.  One constructor per operation: `alloc`
(6.141), `free` (6.142), `store` (6.145), `immFrame`/`immEnd` (6.64's entry and exit, recording
the frame and its lineage and dropping them), `mutFold`/`mutUnfold` (6.65 and 6.66), and
`reb`/`rebDeep` with `rebEnd`/`rebEndDeep` (6.150's entry and exit, at a record's cell or at a
chain view of one, at any record, a sub-record included).  `reb`'s `β` is below every lifetime
of the world, as 6.150's H11 takes it.  The typing premises are at `vShape`, `𝒱⟦T⟧`'s wp-free
shape: a premise at the program's relation would put `TW` under the negative occurrence of
`wpTS` in that relation's `⊸` clause.
`[about ours: the configurations §6 quantifies over, as a family; docs/boca-rules.md §12.72]` -/
inductive TW : WRes → List FrameRec → List FrameRec → Prop
  | empty : TW PMap.empty [] []
  | alloc {W W' : WRes} {ps rs : List FrameRec} {μ : BoCa.BoLo.Heap} {l : Loc} {v : Val} :
      TW W ps rs → ResU.Lower W μ → μ l = none →
      ResU.CompS W (ResU.single l (CellU.ownOf v)) W' → ResU.Valid W' → TW W' ps rs
  | immFrame {W X Z R W' : WRes} {ps rs ds : List FrameRec} {l : Loc} {v : Val} {α : Life}
      (T : Ty) (δ : LSub) (h : R.InStratum (LSet.singleton α).join) :
      TW W ps rs → AdmWf T δ → ResU.CompS (ResU.single l (CellU.ownOf v)) R X →
      ResU.CompS X Z W → vShape T δ v R →
      ResU.CompS (ResU.single l (CellU.immOf (LSet.singleton α) v R h)) Z W' →
      ResU.Valid W' → (∀ d, d ∈ ds ↔ Desc ⟨l, v, R, T, δ⟩ d) →
      TW W' (⟨l, v, R, T, δ⟩ :: ps) (⟨l, v, R, T, δ⟩ :: (ds ++ rs))
  | reb {W W' c : WRes} {ps rs : List FrameRec} (r : FrameRec) {le : Loc} {s : LSet}
      {β : Life} {hs : r.R.InStratum s.join} (x : LifeVar) :
      TW W ps rs → r ∈ rs → W.get le = some (CellU.immOf s r.v r.R hs) →
      ¬ LFree x r.T → ResU.Reb β r.R c →
      vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v c →
      W.InStratum β → ResU.CompS W c W' → ResU.Valid W' → TW W' ps rs
  | rebDeep {W W' c : WRes} {ps rs : List FrameRec} (r : FrameRec) {p : Option Loc} {l₀ : Loc}
      {S₀ : Ty} {u₀ : Val} {s : LSet} {w₀ : WRes} {hs : w₀.InStratum s.join} {β : Life}
      (x : LifeVar) :
      TW W ps rs → r ∈ rs → Chain r.R r.T r.v p l₀ S₀ u₀ →
      W.get l₀ = some (CellU.immOf s u₀ w₀ hs) → ¬ LFree x S₀ → ResU.Reb β w₀ c →
      vShape (S₀.immReborrow (.var x)) (r.δ.extend x β) u₀ c →
      W.InStratum β → ResU.CompS W c W' → ResU.Valid W' → TW W' ps rs
  | mutFold {W X Z ρ W' : WRes} {ps rs : List FrameRec} {l : Loc} {v : Val} {b : Life}
      {hstr : ρ.InStratum b} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρ, hstr⟩} :
      TW W ps rs → ResU.CompS (ResU.single l (CellU.ownOf v)) ρ X → ResU.CompS X Z W →
      ResU.CompS (ResU.single l (CellU.mutOf b v ρ hstr P hw)) Z W' → ResU.Valid W' →
      TW W' ps rs
  | mutUnfold {W X Z ρ W' : WRes} {ps rs : List FrameRec} {l : Loc} {v : Val} {b : Life}
      {hstr : ρ.InStratum b} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρ, hstr⟩} :
      TW W ps rs → ResU.CompS (ResU.single l (CellU.mutOf b v ρ hstr P hw)) Z W →
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρ X → ResU.CompS X Z W' → ResU.Valid W' →
      TW W' ps rs
  | free {W W' : WRes} {ps rs : List FrameRec} {l : Loc} {v : Val} :
      TW W ps rs → ResU.CompS (ResU.single l (CellU.ownOf v)) W' W → ResU.Valid W' →
      TW W' ps rs
  | store {W Z W' : WRes} {ps rs : List FrameRec} {l : Loc} {v₁ v₂ : Val} :
      TW W ps rs → ResU.CompS (ResU.single l (CellU.ownOf v₁)) Z W →
      ResU.CompS (ResU.single l (CellU.ownOf v₂)) Z W' → ResU.Valid W' → TW W' ps rs
  | immEnd {W Y X' W' : WRes} {ps rs ps' rs' : List FrameRec} (r : FrameRec) {s : LSet}
      {hs : r.R.InStratum s.join} :
      TW W ps rs → r ∈ ps → ResU.CompS (ResU.single r.le (CellU.immOf s r.v r.R hs)) Y W →
      ResU.CompS (ResU.single r.le (CellU.ownOf r.v)) r.R X' → ResU.CompS X' Y W' →
      ResU.Valid W' → (∀ r', r' ∈ ps' ↔ (r' ∈ ps ∧ r' ≠ r)) →
      (∀ d, d ∈ rs' ↔ ∃ p ∈ ps', DescR p d) → TW W' ps' rs'
  | rebEnd {W W' c : WRes} {ps rs : List FrameRec} (r : FrameRec) {le : Loc} {s : LSet}
      {β : Life} {hs : r.R.InStratum s.join} :
      TW W ps rs → r ∈ rs → W'.get le = some (CellU.immOf s r.v r.R hs) →
      ResU.Reb β r.R c → ResU.CompS W' (c.restrictDom r.R.exclPart) W →
      W'.InStratum β → TW W' ps rs
  | rebEndDeep {W W' c : WRes} {ps rs : List FrameRec} (r : FrameRec) {p : Option Loc}
      {l₀ : Loc} {S₀ : Ty} {u₀ : Val} {s : LSet} {w₀ : WRes} {hs : w₀.InStratum s.join}
      {β : Life} :
      TW W ps rs → r ∈ rs → Chain r.R r.T r.v p l₀ S₀ u₀ →
      W'.get l₀ = some (CellU.immOf s u₀ w₀ hs) → ResU.Reb β w₀ c →
      ResU.CompS W' (c.restrictDom w₀.exclPart) W → W'.InStratum β → TW W' ps rs

/-!
Row 5.33, continued.
-/
/-- **A tagged list agrees with the world**: each record's tag is the frame lifetime of a
record proper whose lineage holds it.  `[about ours: our tag discipline]` -/
def Tagged (W : WRes) (ps : List FrameRec) (ls : List SRec) : Prop :=
  ∀ x ∈ ls, ∃ p ∈ ps, DescR p x.1 ∧ FrameLife W p x.2

/-!
Rows 4.11, 5.33, continued.
-/
/-- **`[TR]` p. 6's `wp` at a tagged typed world.**  The frame quantifier ranges over the
completions `ρ_f ● ρ` that are `TW` worlds at the list's records, tagged, and the
post-configuration is one too, with the same records proper and the same list members: a
record 6.64 creates inside a run is ended before the run returns.  Every other conjunct is
`Fig16.BoLo.wp`'s, verbatim.  `[about ours: [TR] p. 6's wp relativised to tagged typed worlds;
docs/boca-rules.md §12.72]` -/
def wpTS (ls : List SRec) (e : Expr) (Q : List SRec → Val → WProp) : WProp := fun ρ =>
  ∀ (ρf fρ : WRes) (ps : List FrameRec), ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ →
    TW fρ ps (rsOf ls) → Tagged fρ ps ls →
    ∃ (ρ' ρp fρ' fρ'p π : WRes) (v : Val) (μ μ' : Heap) (ps' : List FrameRec)
      (ls' : List SRec),
      ResU.Hash ρ' ρf ∧
      ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧
      ResU.Lower fρ μ ∧
      ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧
      Steps μ e μ' (.val v) ∧
      ResU.CompS ρ' ρp π ∧ ResU.UpdV ρ π ∧
      NoOwn ρp ∧
      TW fρ'p ps' (rsOf ls') ∧ Tagged fρ'p ps' ls' ∧
      (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls) ∧ Q ls' v ρ'

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
/-- The program's relation at the tagged `wp`. -/
abbrev vP : Ty → List SRec → LSub → Val → WProp := vX wpTS true

/-!
Row 4.13, continued.
-/
/-- `⊛_{x ∈ dom(Γ)} 𝒱X⟦Γ(x)⟧(ls)δ(γ(x))`.  `[about ours]` -/
def gSepX (ls : List SRec) (δ : LSub) : Ctx Ty → List Val → WProp
  | [],     _      => emp
  | _ :: _, []     => emp
  | s :: Γ, v :: γ => if s.live then vP s.ty ls δ v ⋆ gSepX ls δ Γ γ else gSepX ls δ Γ γ

/-!
Row 4.13, continued.
-/
/-- `𝒢X⟦Γ⟧(ls)δ(γ)`.  `[about ours]` -/
def gDenX (ls : List SRec) (δ : LSub) (Γ : Ctx Ty) (γ : List Val) : WProp :=
  ⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSepX ls δ Γ γ

/-!
Row 4.14, continued.
-/
/-- **`Δ; Γ ⊨ e : T` at the typed world**: `[TR]` p. 4's judgment, `∀δ ∈ 𝒟⟦Δ⟧, γ.
𝒢⟦Γ⟧δ(γ) ⊨ ℰ⟦T⟧δ(γ(e))`, read at `𝒱X` and the tagged `wpTS`, at every record list.
`[about ours: [TR] p. 4's judgment at the definitions docs/boca-rules.md §12.69–§12.72 repair]` -/
def SemX (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty) : Prop :=
  ∀ δ γ (ls : List SRec) ρ, Δ.Models δ → gDenX ls δ Γ γ ρ →
    wpTS ls (substAll γ e) (fun ls' => vP T ls' δ) ρ

end BoCa.Fig16.LogRel.Typed

end
