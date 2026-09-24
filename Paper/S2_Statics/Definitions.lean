import Paper.S1_Syntax.Definitions
import Paper.S3_Dynamics.Definitions
import Support.Lifetimes.AfterS1
import Support.Statics.Base
import Support.Syntax

/-!
# [TR] §2 Statics  (physical pp. 2–3)

The typing judgment `Δ; Γ ⊢ e : T` (rules id, 1I, 1E, ⊗I, ⊗E, ⊕I, ⊕E, ⊸I, ⊸E, ∀I,
∀E, [l]I, [l]E, alloc, free, ⊑Imm, ⊑Mut), type well-formedness `Δ ⊢ T`
("Presumes ⊨ Δ"), the outlives judgment `Δ ⊢ T ⊐ @a` ("Presumes ⊨ Δ and
Δ ⊨ @a"), the axiom table (p. 3)

    Δ ⊢ swap     : Ref T₁ ⊸ T₂ ⊸ Ref T₂ ⊗ T₁
    Δ ⊢ copy     : Imm @a T ⊸ Imm @a T ⊗ Imm @a T
    Δ ⊢ forget   : Imm @a T ⊸ 1   ∣   Mut @a T ⊸ 1   ∣   Unk ⊸ 1
    Δ ⊢ withbor  : Ref T₁ ⊸ (∀ 'a ⊏ ⊓Δ. Imm 'a T₁ ⊸ ['a] T₂) ⊸ Ref T₁ ⊗ T₂
                   Ref T₁ ⊸ (∀ 'a ⊏ ⊓Δ. Mut 'a T₁ ⊸ ['a] T₂) ⊸ Ref T₁ ⊗ T₂      (Δ ⊢ T₁ ⊐ @b)
                   Mut @a T₁ ⊸ (∀ 'b ⊏ ⊓Δ. Mut 'b T₁ ⊸ ['b] T₂) ⊸ Mut @a T₁ ⊗ T₂
    Δ ⊢ withload : Imm @a T₁ ⊸ (∀ 'b ⊏ ⊓Δ. Imm̲ 'b T₁ ⊸ ['b] T₂) ⊸ T₂
    Δ ⊢ withswap : Mut @a T₁ ⊸ (T₁ ⊸ T₁ ⊗ T₂) ⊸ Mut @a T₁ ⊗ T₂

the metafunction `Imm̲ 'b T`, lifetime substitutions `LSub ∋ δ : LifeVar ⇀ Life`,

    ⟦Δ⟧ ≜ {δ ∣ dom(Δ) ⊆ dom(δ) ∧ ∀ 'a ∈ dom(Δ). δ('a) ⊏ Δ('a)δ}      ⊨ Δ ≜ ⟦Δ⟧ ≠ ∅
    Δ ⊨ @a ≜ ∀ δ ∈ ⟦Δ⟧. @aδ defined        Δ ⊨ @a ⊏ @b ≜ ∀ δ ∈ ⟦Δ⟧. @aδ ⊏ @bδ

and the interpretation `@aδ`.

This file imports `[TR]` §3's file: the axiom table names `swap`, `copy`,
`forget`, `withbor`, `withload` and `withswap`, which `[TR]` defines as terms on
p. 4, in §3.  Contexts `Γ` are lists of slots, each a type with a liveness bit.

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

namespace BoCa
open BoCa.Lifetime

/-!
### 2.38 · the axiom table's left column: `Δ ⊢ <term> : <type>`, with no Γ and no premise column · [TR] p. 3 · `[encoding]`

Named choice: the unwritten Γ is read as `●`. All six terms are ill-typed by the other rules (they use linear binders twice or more and call `load`/`store`, for which p. 2 prints no rule at all) — typing them axiomatically is the design, not a gap
-/
/-- `•` — every slot already consumed.  This is what `1I`, `ID`'s tail and the
    axiom table's unwritten `Γ` (§12.19) demand. -/
inductive Ctx.Dead {τ : Type} : Ctx τ → Prop where
  | nil                                   : Ctx.Dead []
  | cons {T : τ} {Γ : Ctx τ} : Ctx.Dead Γ → Ctx.Dead (⟨T, false⟩ :: Γ)

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
/-- `Γ = x : T`, with `x` at de Bruijn index `i` — `ID`'s context. -/
inductive Ctx.Solo {τ : Type} : Ctx τ → Nat → τ → Prop where
  | here  {T : τ} {Γ : Ctx τ} : Ctx.Dead Γ → Ctx.Solo (⟨T, true⟩ :: Γ) 0 T
  | there {S T : τ} {Γ : Ctx τ} {i : Nat} : Ctx.Solo Γ i T →
      Ctx.Solo (⟨S, false⟩ :: Γ) (i + 1) T

end BoCa

namespace BoCa

/-!
### 2.39 · `Δ ⊢ swap : Ref T₁ ⊸ T₂ ⊸ Ref T₂ ⊗ T₁` · [TR] p. 3 (type), p. 4 (term) · `[repair]`

The TYPE is as printed. The TERM is not: `BoCa.swap` is [CONF] Fig. 3b's `λx.λy₂. let y₁ = load x; store x y₂; (x,y₁)` where [TR] p. 4 prints `λx.λy. let z = load x; store x y; (x,y)` (row 3.24). Adjudicated at `docs/boca-rules.md` §12.20 and at `BoCa.swap`: [TR] p. 4's body binds `z`, never uses it, and returns the NEW payload, contradicting the type printed on the same axiom line, whose second component is `T₁`; [CONF] Fig. 3b's body matches that type, and [TR]'s own proof of Lemma 6.169 (p. 44) evaluates `let z = load v₁; store v₁ v₂; (v₁, z)`.

### 3.24 · `swap ≜ λx.λy.let z = load x; store x y; (x, y)` · [TR] p. 4 · `[repair]`

The Lean returns `(x, z)`, the OLD payload ([CONF] Fig. 3b, p. 415:4), where [TR] p. 4 prints `(x, y)`, the new one, with `z` bound and unused. No Lean declaration carries [TR] p. 4's printed body. Adjudicated at `docs/boca-rules.md` §12.20 and at `BoCa.swap`, three ways on the pages: [TR] p. 4's printed body binds `z` and never uses it and contradicts the type [TR] p. 3 prints for `swap`; [CONF] Fig. 3b's body matches that type; and [TR]'s own proof of Lemma 6.169 (p. 44) evaluates `let z = load v₁; store v₁ v₂; (v₁, z)`, returning the old payload
-/
/-- `swap ≜ λx.λy₂. let y₁ = load x; store x y₂; (x, y₁)` — **[CONF] Fig. 3b**
    (p. 415:4), not [TR] p. 4.  §12.20.

    **The two documents print different bodies, and we follow [CONF].
    [variant: [CONF] Fig. 3b's body, not [TR] p. 4's.]**
    [TR] p. 4 prints `swap ≜ λx.λy. let z = load x; store x y; (x, y)`: `z` is
    bound and never used, and the pair returns `y`, the **new** payload, where
    the type ascribed on [TR] p. 3 — `Ref T₁ ⊸ T₂ ⊸ Ref T₂ ⊗ T₁` — makes the
    second component the **old** one.  [CONF] Fig. 2c (p. 415:4) is the
    decisive witness: `let x = alloc v; let (x′,y) = swap x (); free x′; y` is
    stated to return `v`, and it does so only under Fig. 3b's body.
    `Examples.lean` and `PaperTests` §2 run it.

    Three things matter about the term ([CONF] p. 415:5): it returns the
    reference as well as the payload, threading it so it can be reused; it
    permits a *strong update*, sound only because linearity guarantees the
    reference is unique; and its implementation is **ill-typed** — it uses the
    linear `x` three times — yet is semantically sound at the ascribed type.
    That last point is the seed of the whole approach: borrow operations are
    typed axiomatically and validated in the logic. -/
def swap : Expr :=
  lam2 (elet (.app load' v1)
             (.seq (.app (.app store' v2) v1)
                   (.pair v2 v0)))

end BoCa

namespace BoCa
open BoCa.Lifetime

/-!
Row 2.39, continued.
-/
/-- `Ref T₁ ⊸ T₂ ⊸ Ref T₂ ⊗ T₁`.  Note `(Ref T₂) ⊗ T₁`. -/
def axSwapTy (T₁ T₂ : Ty) : Ty := .lolli (.ref T₁) (.lolli T₂ (.tensor (.ref T₂) T₁))

/-!
### 2.40 · `Δ ⊢ copy : Imm @a T ⊸ Imm @a T ⊗ Imm @a T` · [TR] p. 3 · `[encoding]`

Type symbol for symbol; `BoCa.copy` matches [TR] p. 4 verbatim, so only the unwritten Γ is an encoding step. ([CONF] calls the same axiom `dupl`)
-/
/-- `Imm @a T ⊸ Imm @a T ⊗ Imm @a T`.  ([CONF] calls it `dupl`, §12.21.) -/
def axCopyTy (a : Life) (T : Ty) : Ty := .lolli (.imm a T) (.tensor (.imm a T) (.imm a T))

/-!
### 2.41 · `Δ ⊢ forget : Imm @a T ⊸ 1` · [TR] p. 3 · `[encoding]`

First of three types stacked under one `forget` label; the term matches [TR] p. 4
-/
def axForgetImmTy (a : Life) (T : Ty) : Ty := .lolli (.imm a T) .unit

/-!
### 2.42 · `Δ ⊢ forget : Mut @a T ⊸ 1` · [TR] p. 3 · `[encoding]`

Second stacked type, as printed
-/
def axForgetMutTy (a : Life) (T : Ty) : Ty := .lolli (.mut a T) .unit

/-!
### 2.43 · `Δ ⊢ forget : Unk ⊸ 1` · [TR] p. 3 · `[encoding]`

Third stacked type, as printed — and the only rule in §2 that mentions `Unk` left of a turnstile
-/
def axForgetUnkTy : Ty := .lolli .unk .unit

end BoCa

namespace BoCa

/-!
### 2.44 · `Δ ⊢ withbor : Ref T₁ ⊸ (∀ 'a ⊏ ⊓Δ. Imm 'a T₁ ⊸ ['a] T₂) ⊸ Ref T₁ ⊗ T₂` · [TR] p. 3 (type), p. 4 (term) · `[as printed]`

Type as printed (the inner `Imm` is the bare constructor, unlike `withload`'s). The TERM is [CONF] Fig. 15's `λx.λf.(x, f () x)`, not [TR] p. 4's `λx.λf.(x, f x)` (row 3.27). The ∀ binder is schematic, as printed: the constructor takes `(x : LifeVar)` with the freshness premise `Δ.find? x = none` that §12.44 argues for ∀I, and concludes at `axWithbor1Ty x Δ.meetOfDom T₁ T₂`. It was pinned to `BoCa.Lifetime.LifeCtx.freshVar`, which made the rule one instance of the printed one — `BoCa.Ty` equality is syntactic, so no other α-variant was derivable — and §12.45 found against it. Unpinning weakens nothing: `BoCa.Lifetime.LifeCtx.freshVar_fresh` supplies the premise, so every derivation that existed survives. The other two differences are adjudicated: the term by `docs/boca-rules.md` §12.20 (row 3.27), `⊓Δ` by §12.15 with `BoCa/Life.lean` §7. The same unpinning covers `BoCa.Derives.withbor2Ax`, `BoCa.Derives.withbor3Ax` and `BoCa.Derives.withloadAx`

### 3.27 · `withbor ≜ λx.λf.(x, f x)` · [TR] p. 4 · `[repair]`

The Lean is `λx.λf.(x, f () x)` — [CONF] Fig. 15, p. 415:17 — adding the lifetime application the print omits. Adjudicated at `docs/boca-rules.md` §12.20 and at `BoCa.withbor`: [TR] p. 4's own `𝒱⟦∀ 'a ⊏ @b. T⟧δ(v) ≜ ∀ α ⊏ @bδ. ℰ⟦T⟧δ(v ())` makes the callback a thunk, so the printed body hands the borrower `x` as its lifetime argument and the borrow never arrives — the term cannot be taken as printed against the type printed beside it. [TR]'s own proof of Lemma 6.172 (p. 46) writes `wp (v_f () ℓ)`
-/
/-- `withbor ≜ λx.λf. (x, f () x)`  — [CONF] **Fig. 15** (p. 415:17).  Uses the
    linear `x` twice: it hands the borrower a borrow of `x` and *also* returns
    `x` itself.

    **The two documents print different bodies here; docs/boca-rules.md
    §12.20.  [variant: [CONF] Fig. 15's body, not [TR] p. 4's.]**
    [TR] p. 4 and [CONF] p. 415:6 both print
    `withbor ≜ λx.λf. (x, f x)`, without the lifetime application.  That is the
    *pre-lifetime* (§2.2) reading and it does not match the §2.3 type

        Ref T₁ ⊸ (∀'a ⊏ ⊓Δ. Imm 'a T₁ ⊸ ['a]T₂) ⊸ Ref T₁ ⊗ T₂

    in which `f` is a **thunk**: `𝒱⟦∀'a ⊏ @b. T⟧δ(v) ≜ ∀α ⊏ @bδ. ℰ⟦T⟧δ(v ())`
    ([TR] p. 4), so `f` must be forced with `()` before it can be applied to the
    borrow.  Only [CONF] Fig. 15's body matches that type, and [TR]'s own proof
    of Lemma 6.172 writes `wp (v () ℓ)` (l. 2523), so we take Fig. 15's.  §12.20
    records the same disagreement for `swap` ([CONF] Fig. 3b) and `withload`
    ([CONF] Fig. 14).  [CONF] p. 415:6's body is correct at §2.2's own
    un-thunked type `Ref T₁ ⊸ (Imm T₁ ⊸ T₂) ⊸ (Ref T₁) ⊗ T₂`, which is simply
    earlier than the type it is being matched against here.

    Operationally this is visible: with the [TR] body, `withbor x (Λ.λb. e)`
    reduces to `(x, λb. e)` — the borrower is handed `x` as its *lifetime*
    argument and never receives the borrow at all. -/
def withbor : Expr := lam2 (.pair v1 (.app (.app v0 unit') v1))

end BoCa

namespace BoCa
open BoCa.Lifetime

/-!
Row 2.44, continued.
-/
/-- `(1) Ref T₁ ⊸ (∀'a ⊏ ⊓Δ. Imm 'a T₁ ⊸ ['a]T₂) ⊸ Ref T₁ ⊗ T₂` -/
def axWithbor1Ty (x : LifeVar) (bnd : Life) (T₁ T₂ : Ty) : Ty :=
  .lolli (.ref T₁)
    (.lolli (.all x bnd (.lolli (.imm (.var x) T₁) (.box (.var x) T₂)))
            (.tensor (.ref T₁) T₂))

/-!
### 2.45 · `Δ ⊢ withbor : Ref T₁ ⊸ (∀ 'a ⊏ ⊓Δ. Mut 'a T₁ ⊸ ['a] T₂) ⊸ Ref T₁ ⊗ T₂`, side condition `Δ ⊢ T₁ ⊐ @b` on this line · [TR] p. 3 · `[repair]`

The side condition sits on the second `withbor` line and nowhere else, with `@b` free. Two departures: `BoCa.Lifetime.LifeCtx.Defines` is not printed at all, and the free `@b` is quantified existentially rather than left a rule-scheme parameter (`docs/boca-rules.md` §12.9). The term is again [CONF]'s. The `Δ.Defines b` conjunct is stated there and argued nowhere
-/
/-- `(2) Ref T₁ ⊸ (∀'a ⊏ ⊓Δ. Mut 'a T₁ ⊸ ['a]T₂) ⊸ Ref T₁ ⊗ T₂`, side
    condition `Δ ⊢ T₁ ⊐ @b` (§12.9, existential). -/
def axWithbor2Ty (x : LifeVar) (bnd : Life) (T₁ T₂ : Ty) : Ty :=
  .lolli (.ref T₁)
    (.lolli (.all x bnd (.lolli (.mut (.var x) T₁) (.box (.var x) T₂)))
            (.tensor (.ref T₁) T₂))

/-!
### 2.46 · `Δ ⊢ withbor : Mut @a T₁ ⊸ (∀ 'b ⊏ ⊓Δ. Mut 'b T₁ ⊸ ['b] T₂) ⊸ Mut @a T₁ ⊗ T₂` · [TR] p. 3 · `[repair]`

Type as printed, with no side condition — correct, the printed side condition is on line 2 only. The term is [CONF] Fig. 15's again, and [TR] Lemma 6.174, which is meant to discharge this constructor, proves its semantic side only under `Δ ⊢ T₁ ⊐ @a`, which row 2.28's two printed premises do not give. The term is `docs/boca-rules.md` §12.20 (row 3.27); the gap between this rule and [TR] Lemma 6.174 is §12.32, which quotes [TR] l. 2624's "Have `Δ ⊢ T₁ ⊐ @a` by well-formedness of the type `Mut @a T₁`", verifies at 1200 dpi that p. 2's well-formedness rule has two premises and no such presupposition, and decides to follow the print rather than the lemma, with the cost restated at both sites. §12.32's own pointer to `BoCa/Ty.lean`'s `Ty.wf` is dead (77e515a) and its sentence that the compatibility lemmas are not proved here has been falsified by `BoCa/Compat.lean` — though not for this constructor, so the entry's argument stands
-/
/-- `(3) Mut @a T₁ ⊸ (∀'b ⊏ ⊓Δ. Mut 'b T₁ ⊸ ['b]T₂) ⊸ Mut @a T₁ ⊗ T₂` -/
def axWithbor3Ty (a : Life) (x : LifeVar) (bnd : Life) (T₁ T₂ : Ty) : Ty :=
  .lolli (.mut a T₁)
    (.lolli (.all x bnd (.lolli (.mut (.var x) T₁) (.box (.var x) T₂)))
            (.tensor (.mut a T₁) T₂))

end BoCa

namespace BoCa

/-!
### 2.47 · `Δ ⊢ withload : Imm @a T₁ ⊸ (∀ 'b ⊏ ⊓Δ. Imm̲ 'b T₁ ⊸ ['b] T₂) ⊸ T₂` (leading `Imm` UNDERLINED) · [TR] p. 3 (type), p. 4 (term) · `[repair]`

The underline is genuinely there and the Lean reads it right — `BoCa.Ty.immReborrow`, not the constructor. But the TERM is [CONF] Fig. 14's `λx.λf. f () (load x)`, not [TR] p. 4's `λx.λf.(x, f (load x))`, which returns a pair where the ascribed type returns a bare `T₂` (row 3.28). Two adjudications. The underline is `docs/boca-rules.md` §12.28, re-verified at 600 dpi in `BoCa/Ty.lean`'s preamble, and the type calls `BoCa.Ty.immReborrow` accordingly. The term is §12.20: [TR] p. 4's body returns a pair where the type both documents print returns a bare `T₂`, and drops the lifetime application the thunked callback needs; [CONF] Fig. 14 matches, and [TR]'s own proof of Lemma 6.175 (p. 47) unfolds `withload` to `λf. f () (load v)`. The pinned binder shared with row 2.44 is that row's finding

### 3.28 · `withload ≜ λx.λf.(x, f (load x))` · [TR] p. 4 · `[repair]`

The Lean is `λx.λf. f () (load x)` — [CONF] Fig. 14, p. 415:16 — differing twice: added thunk forcing, dropped pair. Adjudicated at `docs/boca-rules.md` §12.20 and at `BoCa.withload`: the type both documents print returns a bare `T₂` where [TR] p. 4's body returns a pair, and the same p. 4 ∀ clause forces the thunk. [TR]'s own proof of Lemma 6.175 (p. 47) unfolds `withload` to `λf. f () (load v)`, which is [CONF] Fig. 14's body exactly
-/
/-- `withload ≜ λx λf. f () (load x)` — [CONF] **Fig. 14** (p. 415:16).

    **§12.20 — the two documents differ, and we follow [CONF].
    [variant: [CONF] Fig. 14's body, not [TR] p. 4's.]**  [TR] p. 4
    prints `withload ≜ λx.λf. (x, f (load x))`, which does not match the type
    both documents print: the type
    `Imm @a T₁ ⊸ (∀'b ⊏ ⊓Δ. Imm̲ 'b T₁ ⊸ ['b]T₂) ⊸ T₂` returns a bare `T₂`,
    and that body returns a pair — and it also drops the lifetime application
    that makes `f` a thunk (`𝒱⟦∀'a ⊏ @b. T⟧δ(v) ≜ ∀α ⊏ @bδ. ℰ⟦T⟧δ(v ())`,
    [TR] p. 4).  `withbor` is the same disagreement — [TR] p. 4's
    `λx.λf. (x, f x)` against [CONF] Fig. 15's `λxλf. (x, f () x)` — resolved the
    same way: [CONF] Fig. 14 is the version here.

    It is ill-typed in the base system for the usual reason and one more: it
    applies `load`, which [CONF] Fig. 3b (p. 415:4) marks `⊬` and for which
    [TR] p. 2 prints no rule at all. -/
def withload : Expr := lam2 (.app (.app v0 unit') (.app load' v1))

end BoCa

namespace BoCa
open BoCa.Lifetime

/-!
### 2.48 · `Δ ⊢ withswap : Mut @a T₁ ⊸ (T₁ ⊸ T₁ ⊗ T₂) ⊸ Mut @a T₁ ⊗ T₂` · [TR] p. 3 · `[encoding]`

The only axiom whose term matches [TR] p. 4 as well as [CONF] Fig. 15. The callback is a bare ⊸ with no ∀, so there is no thunk and no pinned binder here; only the unwritten Γ is an encoding step
-/
/-- `Mut @a T₁ ⊸ (T₁ ⊸ T₁ ⊗ T₂) ⊸ Mut @a T₁ ⊗ T₂`.  The callback is a bare
    `⊸`: no thunk, no fresh lifetime, no modality on its result. -/
def axWithswapTy (a : Life) (T₁ T₂ : Ty) : Ty :=
  .lolli (.mut a T₁) (.lolli (.lolli T₁ (.tensor T₁ T₂)) (.tensor (.mut a T₁) T₂))

/-!
### 2.49 · `Imm̲ 'b 1 ≜ 1`; `Imm̲ 'b (T₁⊕T₂)`; `Imm̲ 'b (T₁⊗T₂)`; `Imm̲ 'b (T₁⊸T₂) ≜ Unk`; `Imm̲ 'b (Ref T) ≜ Imm 'b T`; `Imm̲ 'b (Imm @a T) ≜ Imm @a T`; `Imm̲ 'b ([@a]T) ≜ Imm̲ 'b T`; `Imm̲ 'b (∀ '.a ⊏ @a. T) ≜ Unk` · [TR] p. 3 · `[as printed]`

Underlines checked on a 300 dpi render of the page: present on the right-hand side of the ⊕, ⊗ and `[@a]` clauses, absent on the `Ref` and `Imm` clauses — so `Ref` sends to the CONSTRUCTOR `Imm 'b T`, which is what the Lean has. (The eighth clause's printed binder `∀ '. a ⊏ @a. T` is a typesetter's slip; it is inert, the right-hand side is `Unk`)

### 2.50 · — no printed clause — · [TR] p. 3 · `[repair]`

p. 3 prints eight clauses; the Lean has ten. The `Mut` clause is imported from [CONF] Fig. 9; the `Unk` clause has no source at all and is forced by totality (the metafunction is otherwise undefined on `Unk`, `[@a] Unk`, `Unk ⊗ T`, `Unk ⊕ T`). Both extra clauses are separately adjudicated. `mut` is `docs/boca-rules.md` §12.10: [CONF] Fig. 9 prints `Imm̲ 'b (Mut @a T) ≜ Imm 'b T` and [CONF] p. 415:11 devotes a paragraph to it, and without it the metafunction is undefined on `Mut`, leaving `withload` unusable on any payload holding a mutable borrow. `unk` is §12.11, forced by totality, with `𝒱⟦Unk⟧δ(v) ≜ emp` as the justification and the one alternative shown unsound. `BoCa.Ty.immReborrow_idem` machine-checks the fixpoint claim. §12.10's pointer to `BoCa/MutTests.lean` is dead (77e515a); nothing in the argument rests on it
-/
/-- `Imm̲ 'b T`, the reborrow metafunction.  Structural, hence total. -/
def Ty.immReborrow (b : Life) : Ty → Ty
  | .unit          => .unit                                          -- (1)
  | .sum    T₁ T₂  => .sum    (T₁.immReborrow b) (T₂.immReborrow b)   -- (2)
  | .tensor T₁ T₂  => .tensor (T₁.immReborrow b) (T₂.immReborrow b)   -- (3)
  | .lolli  _  _   => .unk                                           -- (4)
  | .ref T         => .imm b T                                 -- (5) constructor
  | .imm a T       => .imm a T                                 -- (6) constructor
  | .box _ T       => T.immReborrow b                          -- (7) recursive
  | .all _ _ _     => .unk                                           -- (8)
  -- (9) `Imm̲ 'b (Mut @a T) ≜ Imm 'b T` — [CONF] Fig. 9 only (§12.10).  The
  -- index is the LOAD's fresh `'b`, not the mutable borrow's own `@a`: [CONF]
  -- p. 415:11 says so in as many words, and an `Imm @a T` here would be
  -- "allowed to escape the scope of the load".  The `@a` is therefore dropped.
  | .mut _ T       => .imm b T                                 -- (9) constructor
  | .unk           => .unk                                     -- §12.11, ours

/-!
Row 2.47, continued.
-/
/-- `Imm @a T₁ ⊸ (∀'b ⊏ ⊓Δ. Imm̲ 'b T₁ ⊸ ['b]T₂) ⊸ T₂`.  The underlined `Imm̲`
    is the metafunction (§12.28); at a declarative `T₁` it is a total function
    computing a real type, never a suspension. -/
def axWithloadTy (a : Life) (x : LifeVar) (bnd : Life) (T₁ T₂ : Ty) : Ty :=
  .lolli (.imm a T₁)
    (.lolli (.all x bnd (.lolli (Ty.immReborrow (.var x) T₁) (.box (.var x) T₂)))
            T₂)

end BoCa

namespace BoCa.Lifetime

/-!
### 2.51 · `LSub ∋ δ : LifeVar ⇀ Life` · [TR] p. 3 · `[encoding]`

Named choice: the print's `Life` here is p. 4's SEMANTIC `Life ≜ (ℕ, …)`, not p. 1's grammar, so the Lean codomain is `Nat`; forced, because ⟦Δ⟧ compares `δ('a)` with `Δ('a)δ`, the interpretation of a syntactic `Life`. Association list for the partial map, as at row 1.30
-/
structure LSub where
  entries : List (LifeVar × Nat)
  deriving Repr, DecidableEq, Inhabited

end BoCa.Lifetime

namespace BoCa.Lifetime.LSub

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
def find? (δ : LSub) (x : LifeVar) : Option Nat := assocFind x δ.entries

end BoCa.Lifetime.LSub

namespace BoCa.Lifetime

/-!
### 2.54 · `@aδ ≜ δ('a)`, `⊤`, `@b₁δ ⊓ @b₂δ` at `@a = @b₁ ⊔ @b₂`, `@b₁δ ⊔ @b₂δ` at `@a = @b₁ ⊔ @b₂` · [TR] p. 3 · `[repair]`

As printed the metafunction is not a function: its last two clauses carry the IDENTICAL guard `@a = @b₁ ⊔ @b₂` and different values (confirmed on a 300 dpi render of p. 3). The Lean sends syntactic ⊔ to the semantic ⊔ and syntactic ⊓ to the semantic ⊓, i.e. it reads the third clause's guard as ⊓ — [CONF] Fig. 11's homomorphic version (`docs/boca-rules.md` §12.7). The other repair, keeping the third clause and correcting the fourth guard, would make the interpretation anti-homomorphic. Partiality is `Option`: `@aδ` is undefined when a variable escapes `dom(δ)`, which is what `Δ ⊨ @a` quantifies over. Adjudicated at `docs/boca-rules.md` §12.7 and restated in `BoCa/Life.lean` §3: as printed the metafunction is not a function, so it cannot be taken as printed, and [CONF] Fig. 11 prints the homomorphic pair the Lean implements
-/
def Life.interp (δ : LSub) : Life → Option Nat
  | .var x    => δ.find? x
  | .top      => some SLife.top
  -- §12.7: `⊔ ↦ ⊔`, not `⊔ ↦ ⊓` as [TR] p. 3 prints.
  | .join a b => (a.interp δ).bind fun m => (b.interp δ).bind fun n => some (SLife.join m n)
  | .meet a b => (a.interp δ).bind fun m => (b.interp δ).bind fun n => some (SLife.meet m n)

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
@[simp] theorem Life.interp_var (δ : LSub) (x : LifeVar) :
    (Life.var x).interp δ = δ.find? x := rfl

@[simp] theorem Life.interp_top (δ : LSub) :
    (Life.top).interp δ = some SLife.top := rfl

/-!
### 2.52 · `⟦Δ⟧ ≜ {δ ∣ dom(Δ) ⊆ dom(δ) ∧ ∀'a ∈ dom(Δ). δ('a) ⊏ Δ('a)δ}` · [TR] p. 3 · `[encoding]`

Named choice: the first printed conjunct is dropped as subsumed — the second demands `δ.find? x = some m`, which already forces `'a ∈ dom(δ)`. `⊏` is the strict order of row 5.9

### 4.12 · `𝒟⟦Δ⟧(δ) ≜ ⌜δ ∈ ⟦Δ⟧⌝` · [TR] p. 4, with ⟦Δ⟧ from p. 3 · `[encoding]`

Inherits row 2.52's two named choices (association list, first conjunct subsumed) and nothing else
-/
def LifeCtx.Models (Δ : LifeCtx) (δ : LSub) : Prop :=
  ∀ x u, Δ.find? x = some u →
    ∃ m n, δ.find? x = some m ∧ u.interp δ = some n ∧ SLife.Lt m n

/-!
### 2.53 · `⊨ Δ ≜ ⟦Δ⟧ ≠ ∅` · [TR] p. 3 · `[as printed]`

Nonemptiness of the printed set is inhabitation of the predicate that defines it
-/
/-- `⊨ Δ ≜ ⟦Δ⟧ ≠ ∅`.  ([TR] p. 3.)

    Not decidable as stated — an existential over an infinite set.  §5 gives a
    decidable *sufficient* condition (`LifeCtx.Ok`) together with the witness
    that discharges it. -/
def LifeCtx.Sat (Δ : LifeCtx) : Prop := ∃ δ, Δ.Models δ

/-!
### 2.55 · `Δ ⊨ @a ≜ ∀δ ∈ ⟦Δ⟧. @aδ defined` · [TR] p. 3 · `[as printed]`

Definedness is `∃ n, a.interp δ = some n`, the print's word
-/
/-- `Δ ⊨ @a` — the real, non-computable definition. -/
def LifeCtx.Defines (Δ : LifeCtx) (a : Life) : Prop :=
  ∀ δ, Δ.Models δ → ∃ n, a.interp δ = some n

end BoCa.Lifetime

namespace BoCa
open BoCa.Lifetime

/-!
### 2.19 · `Δ ⊢ T` — "Presumes ⊨ Δ" (boxed judgment form) · [TR] p. 2 · `[encoding]`

Named choice: the presupposition `⊨ Δ` (`BoCa.Lifetime.LifeCtx.Sat`) is carried by no constructor. No `BoCa.Derives` constructor has a `BoCa.WfTy` premise, so the judgment is never consumed by the statics — which is where [TR] Lemma 6.151's binder freshness goes missing: `BoCa.Fig16.LogRel.allISide_of_wfB` and the four beside it read that freshness off this judgment, at the decidable half `BoCa.Ty.wfB` (`BoCa.wfTy_of_wfB` is the soundness), and `BoCa.Fig16.LogRel.allI_fresh_refuted` is the `∀I` node where the statics do not supply it. `BoCa.Ty.wfB` asks the `∀` rule's `Δ, ('a ⊏ @b)` to be an extension, which this rule does not (row 2.25), and asks `Δ ⊨ @a` at `BoCa.Lifetime.Life.wf`, which is the sound half of it — weaker only at the `⟦Δ⟧ = ∅` this row's own presupposition excludes

### 2.20 · `Δ ⊢ 1` · [TR] p. 2 · `[as printed]`

No premises, as printed

### 2.21 · `Δ ⊢ T₁`, `Δ ⊢ T₂` / `Δ ⊢ T₁ ⊗ T₂` · [TR] p. 2 · `[as printed]`

Two premises, as printed

### 2.22 · `Δ ⊢ T₁`, `Δ ⊢ T₂` / `Δ ⊢ T₁ ⊕ T₂` · [TR] p. 2 · `[as printed]`

Two premises, as printed

### 2.23 · `Δ ⊢ T₁`, `Δ ⊢ T₂` / `Δ ⊢ T₁ ⊸ T₂` · [TR] p. 2 · `[as printed]`

Two premises, as printed. (p. 2 sets this connective with a `–⋆` glyph and p. 1's grammar with `⊸`; one connective, two macros)

### 2.24 · `Δ ⊢ T` / `Δ ⊢ Ref T` · [TR] p. 2 · `[as printed]`

One premise, as printed

### 2.25 · `Δ, ('a ⊏ @b) ⊢ T`, `Δ ⊨ @b` / `Δ ⊢ ∀ ('a ⊏ @b).T` · [TR] p. 2 · `[as printed]`

Both premises as printed, `Δ ⊨ @b` being `BoCa.Lifetime.LifeCtx.Defines`. Note that this rule carries NO freshness hypothesis while `BoCa.Derives.allI` does — the two ∀ rules disagree with each other, and only this one matches the print

### 2.26 · `Δ ⊢ T`, `Δ ⊨ @a` / `Δ ⊢ [@a] T` · [TR] p. 2 · `[as printed]`

Both premises as printed

### 2.27 · `Δ ⊢ T`, `Δ ⊨ @a` / `Δ ⊢ Imm @a T` · [TR] p. 2 · `[as printed]`

Both premises as printed

### 2.28 · `Δ ⊢ T`, `Δ ⊨ @a` / `Δ ⊢ Mut @a T` · [TR] p. 2 · `[as printed]`

Exactly the two printed premises; [TR] Lemma 6.174 later reads a third premise (`Δ ⊢ T ⊐ @a`) off "well-formedness of `Mut @a T₁`" that this rule does not supply — the Lean follows the print, which is the right call and leaves 6.174 short

### 2.29 · no rule for `Unk` anywhere in `Δ ⊢ T` · [TR] p. 2 · `[as printed]`

The absence is faithful: `Δ ⊢ Unk` is underivable, so no type mentioning `Unk` is well formed — even though `Imm̲ 'b (T₁ ⊸ T₂) ≜ Unk` puts `Unk` inside `withload`'s result type
-/
/-- `Δ ⊢ T` — [TR] §2 p. 2, transcribed.  Nine rules for nine of the ten type
    constructors; `Unk` has none, so no type mentioning it is well formed.
    Verified at 400 dpi: `1`, `⊗`, `⊕`, `⊸`, `Ref`, `∀`, `[@a]`, `Imm`, `Mut`.

    No rule of §4 below has a premise of this judgment.  Its box on that page
    reads `Δ ⊢ T   Presumes ⊧ Δ`; the typing judgment's box carries no such
    annotation (§C.26). -/
inductive WfTy : LifeCtx → Ty → Prop where
  | unit   {Δ}                                              : WfTy Δ .unit
  | tensor {Δ T₁ T₂} : WfTy Δ T₁ → WfTy Δ T₂                → WfTy Δ (.tensor T₁ T₂)
  | sum    {Δ T₁ T₂} : WfTy Δ T₁ → WfTy Δ T₂                → WfTy Δ (.sum T₁ T₂)
  | lolli  {Δ T₁ T₂} : WfTy Δ T₁ → WfTy Δ T₂                → WfTy Δ (.lolli T₁ T₂)
  | ref    {Δ T}     : WfTy Δ T                             → WfTy Δ (.ref T)
  | all    {Δ x b T} : Δ.Defines b → WfTy (Δ.extend x b) T  → WfTy Δ (.all x b T)
  | box    {Δ a T}   : WfTy Δ T → Δ.Defines a               → WfTy Δ (.box a T)
  | imm    {Δ a T}   : WfTy Δ T → Δ.Defines a               → WfTy Δ (.imm a T)
  /-- §12.32: [TR] p. 2 prints exactly these two premises (1200 dpi), while its
      own Lemma 6.174 reads `Δ ⊢ T ⊐ @a` off "well-formedness of the type
      `Mut @a T₁`".  We follow the printed rule. -/
  | mut    {Δ a T}   : WfTy Δ T → Δ.Defines a               → WfTy Δ (.mut a T)

end BoCa

namespace BoCa.Lifetime

/-!
### 2.56 · `Δ ⊨ @a ⊏ @b ≜ ∀δ ∈ ⟦Δ⟧. @aδ ⊏ @bδ` · [TR] p. 3 · `[as printed]`

Definedness of both sides is part of the Lean statement, which is what `@aδ ⊏ @bδ` presupposes; strict, on the `Nat` carrier where `BoCa.Lifetime.SLife.Lt`, which is `β < α`
-/
/-- `Δ ⊨ @a ⊏ @b`, the real definition ([TR] p. 3).  Definedness of both sides
    is part of it, since `@aδ ⊏ @bδ` presupposes both are defined. -/
def LifeCtx.EntailsLt (Δ : LifeCtx) (a b : Life) : Prop :=
  ∀ δ, Δ.Models δ → ∃ m n, a.interp δ = some m ∧ b.interp δ = some n ∧ SLife.Lt m n

end BoCa.Lifetime

namespace BoCa
open BoCa.Lifetime

/-!
### 2.30 · `Δ ⊢ T ⊐ @a` — "Presumes ⊨ Δ and Δ ⊨ @a" (boxed judgment form) · [TR] p. 2 · `[encoding]`

Named choice: neither presupposition is a hypothesis, so the judgment is derivable at an `@a` with `¬(Δ ⊨ @a)` — including ⊤ and including an unbound `'x`. Inert for ⊤; not inert where `BoCa.Derives.boxIctx` consumes it (row 2.13)

### 2.31 · `Δ ⊢ 1 ⊐ @a` · [TR] p. 2 · `[as printed]`

No premises, as printed

### 2.32 · `Δ ⊢ T₁ ⊐ @a`, `Δ ⊢ T₂ ⊐ @a` / `Δ ⊢ T₁ ⊗ T₂ ⊐ @a` · [TR] p. 2 · `[as printed]`

Two premises, as printed. ([CONF] Fig. 7 collapses ⊗ and ⊕ into one rule; [TR] prints them separately and so does the Lean)

### 2.33 · `Δ ⊢ T₁ ⊐ @a`, `Δ ⊢ T₂ ⊐ @a` / `Δ ⊢ T₁ ⊕ T₂ ⊐ @a` · [TR] p. 2 · `[as printed]`

Two premises, as printed

### 2.34 · `Δ ⊢ T ⊐ @a` / `Δ ⊢ Ref T ⊐ @a` · [TR] p. 2 · `[as printed]`

One premise, as printed

### 2.35 · `Δ ⊨ @b ⊐ @a` / `Δ ⊢ [@b] T ⊐ @a` · [TR] p. 2 · `[as printed]`

[TR]'s single, non-disjunctive premise — [CONF] Fig. 7 prints a disjunction and the Lean rightly follows [TR]; `⊐` read as the converse of p. 3's strict `⊏`

### 2.36 · `Δ ⊨ @b ⊐ @a` / `Δ ⊢ Imm @b T ⊐ @a` · [TR] p. 2 · `[as printed]`

One premise, as printed; strict, so `Δ ⊢ Imm @a T ⊐ @a` is underivable — the print says the same, and that is what makes [CONF] Fig. 5's borrower untypeable in its printed term form

### 2.37 · `Δ ⊨ @b ⊐ @a` / `Δ ⊢ Mut @b T ⊐ @a` · [TR] p. 2 · `[as printed]`

One premise, as printed. Seven rules printed, seven in the Lean; no rule for ⊸, ∀ or `Unk` in either
-/
/-- `Δ ⊢ T ⊐ @a` — the seven rules of [TR] §2 p. 2.  Split exactly as
    `Ty.outlivesRules` is split, and for the same reason: `Ty.outlivesAll`
    reads these rules at `@a := ⊤` as a predicate rather than as a judgment.

    The three absences are the mechanism, not an oversight: no rule for `⊸`
    (an opaque closure may capture a borrow), none for `∀` (a thunk, same
    reason), and none for `Unk` (incompleteness (13), where a rule would in
    fact be sound). -/
inductive OutlivesRules (Δ : LifeCtx) (a : Life) : Ty → Prop where
  | unit                                                       : OutlivesRules Δ a .unit
  | tensor {T₁ T₂} : OutlivesRules Δ a T₁ → OutlivesRules Δ a T₂ →
      OutlivesRules Δ a (.tensor T₁ T₂)
  | sum    {T₁ T₂} : OutlivesRules Δ a T₁ → OutlivesRules Δ a T₂ →
      OutlivesRules Δ a (.sum T₁ T₂)
  | ref    {T}     : OutlivesRules Δ a T                       → OutlivesRules Δ a (.ref T)
  /-- §12.17: [TR]'s strict, non-disjunctive rule, not [CONF] Fig. 7's. -/
  | box    {b T}   : Δ.EntailsLt a b                           → OutlivesRules Δ a (.box b T)
  | imm    {b T}   : Δ.EntailsLt a b                           → OutlivesRules Δ a (.imm b T)
  | mut    {b T}   : Δ.EntailsLt a b                           → OutlivesRules Δ a (.mut b T)

/-!
Row 2.30, continued.
-/
/-- `Δ ⊢ T ⊐ @a`.  [TR] p. 2's judgment-form header presupposes `⊨ Δ` and
    `Δ ⊨ @a`, and prints nothing after `@a` (600 dpi, `CTy.lean` §4), so this
    is exactly `OutlivesRules` — the index is unrestricted, `⊤` included.
    §C.25. -/
def Outlives (Δ : LifeCtx) (T : Ty) (a : Life) : Prop :=
  OutlivesRules Δ a T

end BoCa

namespace BoCa.Lifetime

/-!
### 2.57 · `Δ ⊨ @a ⊑ @b` — premise of ⊑Imm and ⊑Mut, NEVER DEFINED · [TR] p. 2 (used); nowhere (defined) · `[encoding]`

Named choice: ⊑ read as the non-strict companion of p. 3's ⊏, at [CONF] Fig. 11's carrier order. p. 3 defines `Δ ⊨ @a` and `Δ ⊨ @a ⊏ @b` and stops. Inert because rows 2.17 and 2.18 are the only consumers and their direction is independently fixed by [TR] Lemmas 6.167 and 6.168
-/
/-- `Δ ⊨ @a ⊑ @b` — [CONF] Fig. 11's "(and similarly for `⊑̇`)", at the
    carrier's lattice order `Le`.  §2, §12.3. -/
def LifeCtx.EntailsLe (Δ : LifeCtx) (a b : Life) : Prop :=
  ∀ δ, Δ.Models δ → ∃ m n, a.interp δ = some m ∧ b.interp δ = some n ∧ SLife.Le m n

end BoCa.Lifetime

namespace BoCa
open BoCa.Lifetime

/-!
### 2.58 · `Δ ⊨ Γ ⊐ @a` — premise of [l]I, NEVER DEFINED · [TR] p. 2 (used); nowhere (defined) · `[repair]`

The print's turnstile is semantic and undefined; the Lean's is [CONF] Fig. 7's syntactic pointwise `∀x ∈ dom(Γ). Δ ⊢ Γ(x) ⊐ @a`, with `dom(Γ)` read as the live slots. Because the lift is vacuous on a dead Γ, this is the mechanism behind row 2.13. Adjudicated at `docs/boca-rules.md` §12.6 and at the declaration: the premise is undefined in [TR] (pp. 2–3), so there is nothing to take as printed, and [CONF] Fig. 7 spells it out as `∀x ∈ dom(Γ). Δ ⊢ Γ(x) ⊐ a`, Fig. 6 carrying the same shape at a coarser index. Reading `dom(Γ)` as the live slots is argued at the declaration and follows from row 2.1's positional context
-/
/-- `Δ ⊨ Γ ⊐ @a`, the premise of the context-directed `[]I`, read as [CONF]
    Figs. 6/7 spell it out: `∀x ∈ dom(Γ). Δ ⊢ Γ(x) ⊐ @a` (§12.6).  `dom(Γ)` is
    the **live** slots; a consumed slot is no longer in scope. -/
def Ctx.Outlives (Δ : LifeCtx) (Γ : Ctx Ty) (a : Life) : Prop :=
  Δ.Defines a ∧ ∀ s ∈ Γ, s.live = true → OutlivesRules Δ a s.ty

end BoCa

namespace BoCa.Lifetime

/-!
### 2.59 · `⊓Δ` — the ∀ bound in all three `withbor` forms and in `withload`, never defined as an operation · [TR] p. 3 · `[encoding]`

Named choice: for a finite Δ the n-ary meta-meet is a right fold of p. 1's binary ⊓, so the fresh variable gets a real `Life` bound and the extended context stays well-scoped. Two decisions the print does not make are baked in: the meet ranges over `dom(Δ)` rather than `cod(Δ)`, and `⊓∅ = ⊤`
-/
/-- `⊓ dom(Δ)` as a right fold of binary meets, with `⊓∅ = ⊤` (§12.15). -/
def meetOfDomL : List (LifeVar × Life) → Life
  | []          => .top
  | (x, _) :: t => .meet (.var x) (meetOfDomL t)

/-!
Row 2.59, continued.
-/
def LifeCtx.meetOfDom (Δ : LifeCtx) : Life := meetOfDomL Δ.entries

end BoCa.Lifetime

namespace BoCa
open BoCa.Lifetime

/-!
Rows 2.38, 2.39, 2.40, 2.41, 2.42, 2.43, 2.44, 2.45, 2.46, 2.47, 2.48, continued.

### 2.1 · `Δ; Γ ⊢ e : T` (boxed judgment form) · [TR] p. 2 · `[encoding]`

Named choice: a de Bruijn `Expr` and a positional `BoCa.Ctx` of ⟨type, live⟩ slots, so `●` is `BoCa.Ctx.Dead`, `x : T` is `BoCa.Ctx.Solo` and `Γ₁,Γ₂` is the `BoCa.Ctx.Split` partition. Exchange becomes free and weakening and contraction inexpressible, which is what the linear comma means

### 2.2 · ID: `Δ; x : T ⊢ x : T` · [TR] p. 2 · `[encoding]`

`BoCa.Ctx.Solo` is one live slot at a given index and every other slot dead — the singleton context, positionally

### 2.3 · 1I: `Δ; ● ⊢ () : 1` · [TR] p. 2 · `[encoding]`

`●` is `BoCa.Ctx.Dead` (all slots consumed) rather than the empty list, because Γ is positional

### 2.4 · 1E: `Δ; Γ₁ ⊢ e₁ : 1`, `Δ; Γ₂ ⊢ e₂ : T` / `Δ; Γ₁,Γ₂ ⊢ e₁; e₂ : T` · [TR] p. 2 · `[as printed]`

Both premises and the split are the printed ones; the term is `BoCa.Expr.seq`

### 2.5 · ⊗I: `Δ; Γ₁ ⊢ e₁ : T₁`, `Δ; Γ₂ ⊢ e₂ : T₂` / `Δ; Γ₁,Γ₂ ⊢ (e₁,e₂) : T₁ ⊗ T₂` · [TR] p. 2 · `[as printed]`

Symbol for symbol; the term is `BoCa.Expr.pair`

### 2.6 · ⊗E: `Δ; Γp ⊢ ep : T₁ ⊗ T₂`, `Δ; Γ, x₁:T₁, x₂:T₂ ⊢ e : T` / `Δ; Γp,Γ ⊢ let (x₁,x₂) = ep; e : T` · [TR] p. 2 · `[encoding]`

De Bruijn: the rightmost printed binder `x₂` is innermost, hence index 0, `T₁` at index 1 — which is what `BoCa.Expr.subst`'s `letpair` case does

### 2.7 · ⊕I: `Δ; Γ ⊢ e : Tᵢ`, `i ∈ {1,2}` / `Δ; Γ ⊢ i e : T₁ ⊕ T₂` · [TR] p. 2 · `[encoding]`

One rule schematic in `i` split into two constructors; `i e` is p. 1's `injᵢ e`. Neither constructor constrains the other summand, as the printed rule does not

### 2.8 · ⊕E: `Δ; Γs ⊢ es : T₁ ⊕ T₂`, `Δ; Γ, x_b : T_b ⊢ e_b : T` for `b ∈ {1,2}` / `Δ; Γs,Γ ⊢ match es {x₁ ⇒ e₁, x₂ ⇒ e₂} : T` · [TR] p. 2 · `[as printed]`

Both branches take the same Γ and the same result `T`, as printed; §2's `match` is §1's `case` — the paper uses two names for one production

### 2.9 · ⊸I: `Δ; Γ, x : T₁ ⊢ e : T₂` / `Δ; Γ ⊢ λx.e : T₁ ⊸ T₂` · [TR] p. 2 · `[as printed]`

Single premise, no well-formedness side condition on `T₁`; the binder slot is live, so the body must consume it

### 2.10 · ⊸E: `Δ; Γ₁ ⊢ e₁ : T₁`, `Δ; Γ₂ ⊢ e₂ : T₁ ⊸ T₂` / `Δ; Γ₁,Γ₂ ⊢ e₁ e₂ : T₂` · [TR] p. 2 · `[repair]`

The print applies the ARGUMENT to the FUNCTION — `e₁ : T₁` on the left of the conclusion — where the Lean concludes `.app f a`, function on the left. The flip is almost certainly right ([TR] p. 1's own production is `e₂ e₁` and p. 4's β-rule is `(µ,(λx.e) v) ↦ (µ,e[v/x])`), but it is a difference from the page. Adjudicated at `docs/boca-rules.md` §12.2, with §12.1: the printed conclusion contradicts the same document twice, since [TR] p. 1 prints the production as `e₂ e₁` and p. 4's β-rule is `(µ,(λx.e) v) ↦ (µ,e[v/x])`, function on the left, and §12.1 reads the same order off p. 3's `e K` and `K v` frames. Premise numbering is kept, so `Γ₁` is still the argument's

### 2.11 · ∀I: `Δ, ('a ⊏ @b); Γ ⊢ e : T` / `Δ; Γ ⊢ Λ.e : ∀ 'a ⊏ @b. T` · [TR] p. 2 · `[repair]`

Two things the print does not say: `Λ.e ≜ λ_.e` (row 1.8), so one `Expr` carries both a ∀ type and a ⊸ type; and an unprinted freshness premise `Δ.find? x = none`. This also falsifies `BoCa/Derives.lean`'s header claim that no constructor carries a side condition the print does not carry. The collapse is adjudicated at `docs/boca-rules.md` §12.14 (row 1.8). The freshness premise is not adjudicated anywhere: `docs/axiom-ledger.md` C14 is about `BoCa.LogRel.allI_compat`'s side conditions and not about the rule, and every other mention restates the premise as a given. [TR] p. 2's ∀I has one premise and [CONF] Fig. 7's has one

### 2.12 · ∀E: `Δ; Γ ⊢ e : ∀ 'a ⊏ @b. T`, `Δ ⊨ @a ⊏ @b` / `Δ; Γ ⊢ e[] : T[@a/'a]` · [TR] p. 2 · `[repair]`

`e[] ≜ e ()`, so the conclusion term is literally a ⊸E redex and the two elimination rules are not disjoint on terms. Adjudicated at `docs/boca-rules.md` §12.14: `e[]` is in neither [TR] p. 1's `Expr` grammar nor p. 4's ↦ box, so nothing steps it and it cannot be taken as printed; [CONF] Fig. 7 concludes `Δ; Γ ⊢ e () : T[a/'a]` and [TR] p. 4's `𝒱⟦∀⟧` writes `v ()`. Both printed premises are present in the constructor, and the overlap the reading creates is carried as an explicit open hypothesis of `BoCa.LogRel.fundamental_of_open` rather than hidden

### 2.13 · [l]I: `Δ; Γ ⊢ e : T`, `Δ ⊨ Γ ⊐ @a` / `Δ; Γ ⊢ □e : [@a] T` · [TR] p. 2 · `[repair]`

[TR] never defines the semantic `Δ ⊨ Γ ⊐ @a` (row 2.58); the Lean substitutes [CONF] Fig. 7's syntactic pointwise lift over the live slots. With Γ all-dead that premise is provably vacuous (`BoCa.Ctx.Dead.outlives`), so `[@a] T` is derivable at an `@a` that Δ does not bind — nothing in the rule requires `BoCa.Lifetime.LifeCtx.Defines`. Adjudicated at `docs/boca-rules.md` §12.6 for the undefined premise and §C.25 for the refusal to strengthen the index, which it checks at 600 dpi, and both machine-checked witnesses are live again: `BoCa.Programs.d_boxTop` is `Δ; • ⊢ λx.x : [⊤](1 ⊸ 1)`, the derivation §C.25 argues about, and `BoCa.Programs.d_outerBorrow` is §12.24's other half, `[]I` at an outer borrow's lifetime with the borrow live in the context.  §C.25's pointer to `BoCa/Ground.lean` is stale and is not load-bearing

### 2.14 · [l]E: `Δ; Γ ⊢ □e : [@a] T` / `Δ; Γ ⊢ □e : T` · [TR] p. 2 · `[encoding]`

Named choice: `□` is erased. It is a typesetting marker only — it appears in neither p. 1's `Expr` grammar nor p. 3's `Kont` grammar, so it can carry no term or evaluation content; erased, the printed premise/conclusion pair is `boxE` exactly. (The print is internally inconsistent here: [l]I boxes only in its conclusion, [l]E in both)

### 2.15 · alloc: `Δ; ● ⊢ alloc : T ⊸ Ref T` · [TR] p. 2 · `[encoding]`

Empty premise bar — `T` is schematic and unconstrained; `●` is `BoCa.Ctx.Dead` and `alloc` is row 1.10's nullary prim value

### 2.16 · free: `Δ; ● ⊢ free : Ref T ⊸ T` · [TR] p. 2 · `[encoding]`

The same two encoding choices as row 2.15; the type is symbol for symbol

### 2.17 · ⊑Imm: `Δ; Γ ⊢ e : Imm @b T`, `Δ ⊨ @a ⊑ @b` / `Δ; Γ ⊢ e : Imm @b T` · [TR] p. 2 · `[repair]`

[TR] prints `Imm @b T` in BOTH premise and conclusion, so `@a` is unused and the printed rule is the identity; the Lean concludes `Imm @a T`. The repair is what makes [TR] Lemma 6.167, whose conclusion is at `@a`, discharge the rule. Adjudicated at `docs/boca-rules.md` §12.4: as printed the rule is the identity, `@a` occurring nowhere but in the unused entailment premise, so it cannot be taken as printed. Three corroborations, each read on its page: [CONF] Fig. 7's `Imm ⊑` concludes `Δ; Γ ⊢ e : Imm @a T`, [CONF] Fig. 9's `Mut ⊑` likewise, and [TR] Lemma 6.167 concludes `Δ; Γ ⊨ e : Imm @a T`

### 2.18 · ⊑Mut: `Δ; Γ ⊢ e : Mut @b T`, `Δ ⊨ @a ⊑ @b` / `Δ; Γ ⊢ e : Mut @b T` · [TR] p. 2 · `[repair]`

The identical printed defect and the identical repair, against [TR] Lemma 6.168. Adjudicated at `docs/boca-rules.md` §12.4, the same argument at the same printed defect, corroborated by [CONF] Fig. 9's `Mut ⊑` and by [TR] Lemma 6.168, whose conclusion is `Δ; Γ ⊨ e : Mut @a T`
-/
/-- The declarative typing judgment of [TR] §2 p. 2 together with [CONF]
    Figs. 6–9, with the repairs listed in the header.

    Read `Derives Δ Γ e T` as "`Δ; Γ ⊢ e : T`, and `e` consumes exactly the
    live slots of `Γ`". -/
inductive Derives : LifeCtx → Ctx Ty → Expr → Ty → Prop where
  ---------------------------------------------------------------- core, §2
  /-- `ID`:  `Δ; x : T ⊢ x : T`. -/
  | var {Δ Γ i T} (h : Ctx.Solo Γ i T) : Derives Δ Γ (.var i) T
  /-- `1I`:  `Δ; • ⊢ () : 1`. -/
  | unitI {Δ Γ} (h : Ctx.Dead Γ) : Derives Δ Γ (.val .unit) .unit
  /-- `1E`:  `Δ; Γ₁ ⊢ e₁ : 1`, `Δ; Γ₂ ⊢ e₂ : T`  ⟹  `Δ; Γ₁,Γ₂ ⊢ e₁;e₂ : T`. -/
  | unitE {Δ Γ Γ₁ Γ₂ e₁ e₂ T} (hs : Ctx.Split Γ Γ₁ Γ₂)
      (h₁ : Derives Δ Γ₁ e₁ .unit) (h₂ : Derives Δ Γ₂ e₂ T) :
      Derives Δ Γ (.seq e₁ e₂) T
  /-- `⊗I`. -/
  | tensorI {Δ Γ Γ₁ Γ₂ e₁ e₂ T₁ T₂} (hs : Ctx.Split Γ Γ₁ Γ₂)
      (h₁ : Derives Δ Γ₁ e₁ T₁) (h₂ : Derives Δ Γ₂ e₂ T₂) :
      Derives Δ Γ (.pair e₁ e₂) (.tensor T₁ T₂)
  /-- `⊗E`.  De Bruijn: `x₂` is index 0, `x₁` is index 1. -/
  | tensorE {Δ Γ Γp Γb ep eb T₁ T₂ T} (hs : Ctx.Split Γ Γp Γb)
      (hp : Derives Δ Γp ep (.tensor T₁ T₂))
      (hb : Derives Δ (⟨T₂, true⟩ :: ⟨T₁, true⟩ :: Γb) eb T) :
      Derives Δ Γ (.letpair ep eb) T
  /-- `⊕I` at `i = 1` (§12.16).  [TR] p. 2 prints two premises, `Δ; Γ ⊢ e : Tᵢ`
      and `i ∈ {1,2}`; the other summand is entirely unconstrained (400 dpi). -/
  | sumI₁ {Δ Γ e T₁ T₂} (h : Derives Δ Γ e T₁) :
      Derives Δ Γ (.inj₁ e) (.sum T₁ T₂)
  /-- `⊕I` at `i = 2`.  As at `i = 1`, the other summand is entirely
      unconstrained. -/
  | sumI₂ {Δ Γ e T₁ T₂} (h : Derives Δ Γ e T₂) :
      Derives Δ Γ (.inj₂ e) (.sum T₁ T₂)
  /-- `⊕E`.  Both branches receive the *same* `Γ` and return the same `T`. -/
  | sumE {Δ Γ Γs Γb es e₁ e₂ T₁ T₂ T} (hs : Ctx.Split Γ Γs Γb)
      (h₀ : Derives Δ Γs es (.sum T₁ T₂))
      (h₁ : Derives Δ (⟨T₁, true⟩ :: Γb) e₁ T)
      (h₂ : Derives Δ (⟨T₂, true⟩ :: Γb) e₂ T) :
      Derives Δ Γ (.case es e₁ e₂) T
  /-- `⊸I`.  [TR] p. 2 prints the single premise `Δ; Γ, x : T₁ ⊢ e : T₂`
      (400 dpi); the domain carries no well-formedness condition.  The binder's
      slot is live in the premise, so the body must consume it: that is what
      refuses weakening. -/
  | lolliI {Δ Γ b T₁ T₂}
      (h : Derives Δ (⟨T₁, true⟩ :: Γ) b T₂) :
      Derives Δ Γ (.val (.lam b)) (.lolli T₁ T₂)
  /-- `⊸E`, with §12.2's repair.  [TR] p. 2 prints the conclusion as
      `Δ; Γ₁, Γ₂ ⊢ e₁ e₂ : T₂` with `e₁ : T₁` the argument and
      `e₂ : T₁ ⊸ T₂` the function, which contradicts the same document twice:
      p. 1's `Expr` production is `e₂ e₁`, and p. 3's β-rule is
      `(μ, (λx.e) v) ↦ (μ, e[v/x])`, function on the left.  We read it as
      `e₂ e₁` and keep the premise numbering, so the argument's context `Γ₁` is
      split off first. -/
  | lolliE {Δ Γ Γ₁ Γ₂ f a T₁ T₂} (hs : Ctx.Split Γ Γ₁ Γ₂)
      (ha : Derives Δ Γ₁ a T₁) (hf : Derives Δ Γ₂ f (.lolli T₁ T₂)) :
      Derives Δ Γ (.app f a) T₂
  ------------------------------------------------------- lifetimes, §5, §12.14
  /-- `∀I`.  [TR] p. 2 prints the single premise `Δ, ('a ⊏ @b); Γ ⊢ e : T`
      (400 dpi) — no `Δ ⊨ @b`.  `Λ.e ≜ λ_.e`, so the term is a `λ` and the
      premise's context has **no** binder: in de Bruijn that is a slot pushed
      already dead.  Its type is irrelevant and is therefore schematic. -/
  | allI {Δ Γ x b S e T} (hx : Δ.find? x = none)
      (h : Derives (Δ.extend x b) (⟨S, false⟩ :: Γ) e T) :
      Derives Δ Γ (.val (.lam e)) (.all x b T)
  /-- `∀E`.  `e[] ≜ e ()` (§12.14). -/
  | allE {Δ Γ e x b T a} (h : Derives Δ Γ e (.all x b T))
      (hlt : Δ.EntailsLt a b) :
      Derives Δ Γ (.app e (.val .unit)) (Ty.instLife x a T)
  /-- `[]I` — [CONF] Fig. 6 (p. 415:7), [CONF] Fig. 7 (p. 415:8) and [TR] p. 2
      each print exactly this rule and `[]E`, and nothing else about the
      modality (400 dpi).  `□` is a typesetting marker, so the term is
      untouched (§12.5).

      Its reach is limited in a way the sources feel: a borrower boxing at its
      **own** lifetime needs `Δ ⊢ Imm @a T ⊐ @a`, hence `Δ ⊨ @a ⊐ @a`, which no
      rule gives — so Fig. 5's and §2.3's printed borrowers are not typeable in
      their printed term form (§12.24).  At an *outer* borrow's lifetime this
      rule does apply (`BoCa.Programs.d_outerBorrow`).  What would close the gap is the
      entailment of [TR] Lemma 6.60, but that is a lemma about the model, not a
      typing rule, and no figure prints a rule expressing it. -/
  | boxIctx {Δ Γ e T a} (h : Derives Δ Γ e T) (hΓ : Ctx.Outlives Δ Γ a) :
      Derives Δ Γ e (.box a T)
  /-- `[]E`.  Unconditional erasure. -/
  | boxE {Δ Γ e T a} (h : Derives Δ Γ e (.box a T)) : Derives Δ Γ e T
  /-- `⊑Imm`, with §12.4's corrected conclusion.  [TR] p. 2 prints `Imm @b T`
      in *both* the premise and the conclusion, which makes the rule do
      nothing; three places give `@a`: [CONF] Fig. 7 (`Imm ⊑`, p. 415:8),
      [CONF] Fig. 9 (p. 415:10), and [TR]'s own Lemma 6.167 (`⊑imm-compat`,
      p. 43), whose conclusion is `Δ; Γ ⊨ e : Imm @a T`.  `⊑` is the carrier's
      lattice order, `Life.lean` §2 and §12.3. -/
  | immSub {Δ Γ e a b T} (h : Derives Δ Γ e (.imm b T))
      (hle : Δ.EntailsLe a b) :
      Derives Δ Γ e (.imm a T)
  /-- `⊑Mut`, same repair, corroborated by [CONF] Fig. 9 (p. 415:10) and
      [TR] Lemma 6.168 (`⊑mut-compat`, p. 43). -/
  | mutSub {Δ Γ e a b T} (h : Derives Δ Γ e (.mut b T))
      (hle : Δ.EntailsLe a b) :
      Derives Δ Γ e (.mut a T)
  ---------------------------------------------------------- memory, §2
  /-- `Δ; • ⊢ alloc : T ⊸ Ref T`.  [TR] p. 2 prints it with an empty premise
      bar (400 dpi): `T` is schematic and unconstrained. -/
  | allocAx {Δ Γ T} (hΓ : Ctx.Dead Γ) :
      Derives Δ Γ (.val (.prim .alloc)) (.lolli T (.ref T))
  /-- `Δ; • ⊢ free : Ref T ⊸ T`, likewise premise-free. -/
  | freeAx {Δ Γ T} (hΓ : Ctx.Dead Γ) :
      Derives Δ Γ (.val (.prim .free)) (.lolli (.ref T) T)
  ------------------------------------------------- the axiom table, §8 / [TR] p. 3
  /-  [TR] p. 3 prints these as a table of `Δ ⊢ term : Type` lines with no
      premise column at all (400 dpi); the single side condition anywhere in it
      is `Δ ⊢ T₁ ⊐ @b` beside `withbor`'s second form.  So the schematic `T₁`,
      `T₂` and `@a` are unconstrained.

      They have **no premise about their bodies** either.  Every one of the six
      terms is ill-typed by the rules above ([CONF] Fig. 3b, p. 415:4, marks
      `load`/`store` `⊬`, and [TR] p. 2 prints no rule for either; the bodies
      also use their linear binders two or three times).  That is
      not a defect: they are typed axiomatically and validated semantically, in
      a logic (BoLo) we have not built.  This is BoCa's trusted base, and it is
      the reason the separability thesis is even statable.                     -/
  | swapAx {Δ Γ T₁ T₂} (hΓ : Ctx.Dead Γ) :
      Derives Δ Γ swap (axSwapTy T₁ T₂)
  | copyAx {Δ Γ a T} (hΓ : Ctx.Dead Γ) :
      Derives Δ Γ copy (axCopyTy a T)
  | forgetImmAx {Δ Γ a T} (hΓ : Ctx.Dead Γ) :
      Derives Δ Γ forget (axForgetImmTy a T)
  | forgetMutAx {Δ Γ a T} (hΓ : Ctx.Dead Γ) :
      Derives Δ Γ forget (axForgetMutTy a T)
  | forgetUnkAx {Δ Γ} (hΓ : Ctx.Dead Γ) : Derives Δ Γ forget axForgetUnkTy
  /-- Form (1).  `⊓Δ` is `LifeCtx.meetOfDom` (§12.15).  The ∀ binder is
      schematic on the page, so it is a parameter here, fresh for `Δ` by the
      premise §12.44 argues — pinning it to `LifeCtx.freshVar` made the rule one
      instance of the printed one (§12.45), and `LifeCtx.freshVar_fresh` shows
      that instance survives. -/
  | withbor1Ax {Δ Γ T₁ T₂} (hΓ : Ctx.Dead Γ) (x : LifeVar) (hx : Δ.find? x = none) :
      Derives Δ Γ withbor (axWithbor1Ty x Δ.meetOfDom T₁ T₂)
  /-- Form (2), with the side condition `Δ ⊢ T₁ ⊐ @b` read **existentially**
      (§12.9): `@b` occurs nowhere else in the rule, [TR] Lemma 6.173 states it
      as a hypothesis and uses it only to obtain `𝒱⟦T₁⟧δ ⊨ [@bδ]𝒱⟦T₁⟧δ`. -/
  | withbor2Ax {Δ Γ T₁ T₂} (hΓ : Ctx.Dead Γ) (x : LifeVar) (hx : Δ.find? x = none)
      (hside : ∃ b, Δ.Defines b ∧ Outlives Δ T₁ b) :
      Derives Δ Γ withbor (axWithbor2Ty x Δ.meetOfDom T₁ T₂)
  /-- Form (3): reborrowing from a mutable borrow.  No side condition, as
      [CONF] Fig. 9 (p. 415:10) prints it.  §12.32: [TR] Lemma 6.174 (p. 47)
      proves the semantic side under `Δ ⊢ T₁ ⊐ @a`, read off "well-formedness of
      the type `Mut @a T₁`", which [TR] p. 2's two-premise `Δ ⊢ Mut @a T` does
      not supply.  We follow the print, so this constructor asserts more than
      the lemma meant to discharge it proves; Phase 10 has to settle it. -/
  | withbor3Ax {Δ Γ a T₁ T₂} (hΓ : Ctx.Dead Γ) (x : LifeVar) (hx : Δ.find? x = none) :
      Derives Δ Γ withbor (axWithbor3Ty a x Δ.meetOfDom T₁ T₂)
  | withloadAx {Δ Γ a T₁ T₂} (hΓ : Ctx.Dead Γ) (x : LifeVar) (hx : Δ.find? x = none) :
      Derives Δ Γ withload (axWithloadTy a x Δ.meetOfDom T₁ T₂)
  | withswapAx {Δ Γ a T₁ T₂} (hΓ : Ctx.Dead Γ) :
      Derives Δ Γ withswap (axWithswapTy a T₁ T₂)

end BoCa

namespace BoCa.Lifetime

/-!
Row 2.59, continued.
-/
def LifeCtx.freshVar (Δ : LifeCtx) : LifeVar := freshOfL Δ.entries

end BoCa.Lifetime

end
