# Adjudications

This document records where the mechanisation reads [CONF] (Wagner, Gierczak, Marshall,
Li & Ahmed, *From Linearity to Borrowing*, PACMPL 9:OOPSLA2:415, 2025) and [TR] (its
supplement, which prints the complete definitions and proofs) in a way that needs an
argument: a place where the two documents differ, where a printed item admits more than one
reading, or where the literal reading of a printed item does not support a step that a
printed proof takes.  Each entry gives the printed form (with page), the sentences of the
paper that ground the reading adopted, the reading itself and the Lean declarations that
carry it, and what the literal reading admits, with the Lean declaration that measures it
where there is one.

Comments in the Lean files cite entries by number (`docs/adjudications.md` §12.42, or just
§12.42 inside a comment that has already named this file).  The numbers are stable and are
not consecutive: only the entries the development cites are included.

* **§12.N** — readings of the printed text.  §12.67–§12.73 are the repairs behind the
  headline results (`Fig16.LogRel.Typed.fundamentalProperty`, `Fig16.LogRel.Typed.adequacy`).
* **§C.25, §C.26** — two readings of the judgment forms' boxes on [TR] p. 2.
* **G1–G8, F1, L3–L5, W2** — conventions: representation choices of the mechanisation,
  not claims about the paper.  Comments cite them by label ("convention G4", or "(G4)").
* **C14, D3, D4, D6, D8, D9, D10** — recorded differences between a Lean statement and the
  printed one, and what each costs.
* **§A.1, §A.2a** — [CONF] Theorem 3.2 and Corollary 3.3, which neither document proves.

Row numbers ("definition row 5.30") are those of `Paper/INDEX.md`, *Definitions*; lemma
numbers are [TR]'s.  Page references are to the physical pages of [TR] ("p. 5") and to
[CONF]'s journal pages ("p. 415:22").

## Part I — Readings of the printed text

### §12.1 Evaluation order

[CONF] Fig. 1 writes application as `e₂ e₁`, which raises the question of whether the paper
fixes an evaluation order. [TR] §3, p. 3 fixes one through its evaluation contexts:

```
Kont ∋ K ::= [] | (K, e) | (v, K) | let (x, y) = K in e
             | case K {inj₁ x.e₁ | inj₂ y.e₂} | e K | K v
```

Reading these off:

- **Application evaluates the argument first (right to left).** `e K` has an arbitrary
  *expression* `e` in the function position and the hole in the argument position. `K v`
  has the hole in the function position and a *value* `v` in the argument position. So the
  argument is reduced to a value first, then the function. The β-rule `(λx.e) v ↦ e[v/x]`
  puts the function on the left, so the surface syntax is ordinary `fun arg`
  juxtaposition, and the *right* operand is evaluated first.
- **Pairs evaluate left to right:** `(K, e)`, then `(v, K)`.
- `let (x,y) = K in e` and `case K {...}` reduce the scrutinee first.

This matches the context splits in the statics. `⊸E` numbers the *argument* premise `Γ₁`
and the *function* premise `Γ₂`, then concludes with `Γ₁, Γ₂`. `⊗I` numbers `e₁` (the left
component) `Γ₁`. In both rules the subscript order is the evaluation order. It also
explains the `e₂ e₁` production in the grammar: the subscripts encode evaluation order, and
`e₂` (the function) is written first.

[CONF] on its own does not settle the question. p. 415:3 says only "a standard call-by-value
variant of the untyped lambda calculus" and gives no evaluation contexts (its Fig. 1 shows
only head-step rules).

### §12.2 `⊸E`'s conclusion and the grammar

[TR] p. 2 prints the `⊸E` conclusion as `Δ; Γ₁, Γ₂ ⊢ e₁ e₂ : T₂`, where `e₁ : T₁` is the
argument and `e₂ : T₁ ⊸ T₂` is the function. Under the grammar's `e₂ e₁` production and the
`(λx.e) v` β-rule (§12.1), the function stands on the left, so we read the conclusion's
term as `e₂ e₁`. The printed form was checked at 1200 dpi; it is not a rendering artifact.

The mechanisation writes application function-left and keeps `⊸E`'s premise numbering, so
the argument's context is `Γ₁`: `BoCa.Derives.lolliE` concludes `Derives Δ Γ (.app f a) T₂`
from `Derives Δ Γ₁ a T₁` and `Derives Δ Γ₂ f (.lolli T₁ T₂)`, with `BoCa.Expr.app` taking
the function first.

### §12.3 The carrier tuple's relation: [TR] labels it `⊑`, [CONF] labels it `⊏`

Both documents use both glyphs in the rules. `⊑` appears in `⊑Imm`, `⊑Mut`, and in [CONF]
Fig. 7's `[b]T ⊐ a` rule. `⊏` appears in `∀'a ⊏ @b`, in `∀E`, and in the `Δ ⊢ T ⊐ @a`
judgment. Only one of them is defined on the carrier, and the two documents label it
differently:

- **[TR] p. 4**, checked at 2400 dpi: `Life ≜ (ℕ, ⊑ ≜ >, ⊔ ≜ min, ⊓ ≜ max, ⊤ ≜ 0)`. The
  relation glyph carries a clear under-bar, so it is `⊑`, not `⊏`, and it is equated with
  the strict `>`.
- **[CONF] Fig. 11 (p. 415:12)**, checked at 1800 dpi:
  `Life ≜ (ℕ, ⊔̇ ≜ min, ⊓̇ ≜ max, ⊤ ≜ 0, ⊏̇ ≜ >)`. The relation glyph has **no** under-bar
  and carries the figure's dot, exactly like the `⊓̇` earlier on the same line. It is `⊏`.
- [TR] p. 3 defines only `Δ ⊨ @a ⊏ @b ≜ ∀δ ∈ ⟦Δ⟧. @aδ ⊏ @bδ`. `Δ ⊨ @a ⊑ @b` is used in
  `⊑Imm`/`⊑Mut` and not given a line of its own. [CONF] Fig. 11 gives the same definition
  and adds "(and similarly for `⊑̇`)", so the entailment for `⊑` is taken from the figure.

**We follow [CONF]: the tuple defines `⊏ ≜ >`, and `⊑` is its reflexive closure `≥`.**
[CONF] p. 415:12, in the prose above Fig. 11, calls the structure "a semi-bounded lattice of
natural numbers". Read with [TR]'s labelling, the tuple is not a lattice: `⊤ = 0` is not
`⊑`-greatest, since `0 > 0` is false, and `⊔ = min` is not a join, since `α ⊑ α ⊔ α` is
false. With [CONF]'s labelling every lattice law holds. The mechanisation takes the carrier
to be `ℕᵒᵈ` (`BoCa.Fig16.Life`), so `⊤`, `⊔` and `⊓` are Mathlib's from `Lattice ℕᵒᵈ` and
are `0`, `min` and `max` on `ℕ`, as printed.

The typography supports the reading: both documents print the two glyphs distinctly within
one block. [TR] p. 2 has `⊏` in `Δ ⊨ @a ⊏ @b` and `⊑` in `⊑Imm`/`⊑Mut`, and [TR] p. 6 has
`⊒` (barred) one line above `⊐` (bare).

The reflexive instance of `⊑Imm`/`⊑Mut` is the identity coercion, and no program printed in
either document needs it. What needs `⊑` to be reflexive is the lattice structure that the
paper asserts.

### §12.4 `⊑Imm` / `⊑Mut` conclusions: the two documents differ

[TR] p. 2 prints both conclusions at `@b`, which makes the rules identities. [CONF] Figs. 7/9
print `@a`, and [TR]'s own Lemmas 6.167/6.168 are stated at `@a`. **We follow [CONF] and
use `@a`**: `BoCa.Derives.immSub` and `BoCa.Derives.mutSub` conclude at `.imm a T` and
`.mut a T` from a premise at `b` with `Δ ⊨ @a ⊑ @b`.

### §12.5 `□` in `[l]I` / `[l]E`: the two documents differ

`□e` appears in [TR]'s `[l]I` conclusion and in *both* halves of `[l]E`. It is not in the
`Expr` grammar, has no reduction rule, and does not appear in the corresponding
compatibility Lemmas 6.163/6.164. [CONF] Figs. 6/7 print the rules without it. **We follow
[CONF]:** the modality has no term-level content, `□` is read as a typesetting marker, and
the rules are not syntax-directed (`BoCa.Derives.boxIctx`, `BoCa.Derives.boxE`).

### §12.6 `Δ ⊨ Γ ⊐ @a`: the context lift, and `⊢` beside `⊨`

The context lift `Γ ⊐ @a` is not given a definition in [TR]. We read it as
`∀x ∈ dom(Γ). Δ ⊢ Γ(x) ⊐ @a`, which is how [CONF] Figs. 6/7 spell it out. Lemma 6.163's
*statement* writes this premise with `⊨` and its *proof* with `⊢`; we read both as the same
premise.

### §12.7 The `@aδ` clause guards: the two documents differ

[TR] p. 3 prints two clauses with the same guard `@a = @b₁ ⊔ @b₂`, mapping the first to `⊓`
and the second to `⊔`. [CONF] Fig. 11 has the homomorphic version (`⊔ ↦ ⊔̇`, `⊓ ↦ ⊓̇`). We
use [CONF]'s.

### §12.8 `Life`'s first alternative: the two documents differ

[TR] p. 1, at 600 dpi, prints the first alternative of the `Life` grammar as a bare
apostrophe `'`, one line under `LifeVar ∋ 'a, 'b, …`. [CONF] Fig. 7 (p. 415:8, 600 dpi)
prints `'a`. **We follow [CONF].** [TR]'s own `@aδ` definition has a case for `@a = 'a`, and
a bare `'` directly under the `LifeVar` line reads as the sort's sigil standing for the
sort, the way `x` stands for `Var`. The two readings agree.

### §12.9 The `withbor` (Ref → Mut) side condition and its lifetime `@b`

The side condition is printed as `Δ ⊢ T₁ ⊐ 'b` ([CONF] Fig. 9) and `Δ ⊢ T₁ ⊐ @b` ([TR]
p. 3). The lifetime does not occur in the conclusion. [TR] Lemma 6.173 states the condition
as a hypothesis, and its proof uses it to obtain `𝒱⟦T₁⟧δ ⊨ [@bδ] 𝒱⟦T₁⟧δ`, so that
`MutFrame` applies. **We read it existentially:** there is a lifetime `@b` with `Δ ⊨ @b` and
`Δ ⊢ T₁ ⊐ @b`. The intent, in [CONF] p. 415:10's prose, is that "the payload type for a
mutable borrow is required to have an unambiguous lifetime bound". The formal ground is the
model's stratification ([CONF] §4.2, p. 415:19–20:
`Mut_α ≜ {(β ⊐ α, v : Val, ρ : Res_β, P̂ : Val → SProp_β) | P̂(v)(ρ)}`).

**The existential is a premise.** `BoCa.Derives.withbor2Ax` carries
`hside : ∃ b, Δ.Defines b ∧ Outlives Δ T₁ b`. As with every axiom-table entry, the side
condition is discharged where the rule is used. The mechanisation does not decide it.

It can be described by an antitonicity argument. The only rules that constrain `@b` are
`imm`, `mut` and `box`, whose premise is `Δ ⊨ @b ⊏ @c` for an index `@c` occurring in `T₁`.
The rules for `1`, `⊗`, `⊕` and `Ref` do not mention `@b`. So a shorter `@b` is always at
least as good. The shortest candidate, however, cannot be a variable outside `Δ`, such as
`BoCa.Lifetime.LifeCtx.freshVar`'s: a variable that `Δ` does not bind is not `Δ`-defined,
so it is not a witness at this rule.

**The `Δ.Defines b` conjunct, and why it restricts nothing.** [TR] p. 2's judgment-form
header reads `Δ ⊢ T ⊐ @a   Presumes ⊨ Δ and Δ ⊨ @a` (600 dpi). `BoCa.Outlives` carries
neither presupposition, and §C.25 argues that it should not: a presupposition is discharged
at the use site, which leaves `⊤` free to index the modality. This rule is that use site.
It is also the one place where the presupposed index is bound by the side condition itself,
since `@b` occurs nowhere else on the printed line. So existentialising `@b` also
existentialises its presupposition, and an existential over an index that need not be
defined is not the printed condition. The conjunct restores it.

The conjunct costs nothing, by a two-case argument. If a derivation of `Outlives Δ T₁ b`
reaches an `imm`, `mut` or `box` rule, that rule's premise is `Δ.EntailsLt b c`, whose first
component is `∀ δ ∈ ⟦Δ⟧. ∃ m. @bδ = m`. That is already `Δ.Defines b`. If it does not, only
the `1`, `⊗`, `⊕` and `Ref` rules were used. Those rules are parametric in the index, so
`Outlives Δ T₁ ⊤` holds as well, and `Δ.Defines ⊤` is immediate from `⊤δ = ⊤`. Hence
`∃ b. Outlives Δ T₁ b` and `∃ b. Δ.Defines b ∧ Outlives Δ T₁ b` are the same proposition.
The conjunct does not strengthen the printed side condition. It is the printed
presupposition, written where the quantifier would otherwise hide it.

What the side condition rejects is `T₁ ⊸ T₂`, `∀'a ⊏ @b. T` and `Unk`, the type
constructors with no `⊐` rule. That is the intent: a closure environment is opaque, so no
lifetime bounds it, and such a payload has no "unambiguous lifetime bound".

### §12.10 The `Mut` clause of the `Imm` metafunction

[TR] p. 3 lists eight clauses. [CONF] Fig. 9 prints a ninth, `Imm 'b (Mut a T) ≜ Imm 'b T`,
and [CONF] p. 415:11 devotes a paragraph to it. Without it the metafunction has no value on
`Mut`, and `withload` could not be used on any payload containing a mutable borrow. The
mechanisation includes the clause, taken from [CONF] Fig. 9, with the right-hand side read
as the type *constructor* (see §12.28). It is a clause of `BoCa.Ty.immReborrow`.

The clause disturbs neither of the metafunction's two invariants. Its right-hand side is an
`Imm`, which is already in the metafunction's image, so the image is still exactly the
fixpoint set (`1`, `⊕`, `⊗`, `Imm @a T`, `Unk`, never `Ref`, `Mut`, `⊸`, `∀` or `[@a]`),
and the metafunction is still idempotent.

### §12.11 The `Imm` metafunction and `Unk`

`Unk` is a `Type`, so `Ref Unk` is expressible, and `Imm 'b (Ref Unk) = Imm 'b Unk` needs a
clause for `Unk`. Neither document gives one. The alternatives are to add a clause or to
exclude `Unk` from source syntax and treat it as an internal type.

**We add `Imm 'b Unk ≜ Unk`** (`BoCa.Ty.immReborrow`). `𝒱⟦Unk⟧δ(v) ≜ emp` ([TR] p. 4), so
an inhabitant of `Unk` owns no resource, and reborrowing an empty resource can only give an
empty one. Nothing is gained or lost either way, since `forget` is the only operation
defined on `Unk`. The one other candidate, `1`, would not be sound in the model: `𝒱⟦1⟧`
holds only of `()`, whereas the value under an `Unk` is arbitrary. With this clause `Unk` is
a fixpoint of the metafunction, which keeps the metafunction idempotent.

### §12.14 Lifetime application: `e[]` and `e ()`

[TR]'s `∀E` concludes `Δ; Γ ⊢ e[] : T[@a/'a]`. `e[]` is not in the `Expr` grammar and has
no reduction rule. [CONF] Fig. 7 concludes `Δ; Γ ⊢ e () : T[a/'a]` and states
`Λ. e ≜ λ_. e`. The logical relation agrees with [CONF]:
`𝒱⟦∀'a ⊏ @b. T⟧δ(v) ≜ ∀α ⊏ @bδ. ℰ⟦T⟧δ(v ())` ([TR] p. 4), and the compatibility proofs
write `v_f () ℓ`. **We implement `e[]` as `e ()`** and `Λ.e` as `λ_.e`:
`BoCa.Derives.allE` concludes at `.app e (.val .unit)`.

### §12.15 `⊓Δ`

`⊓Δ` occurs in the bound of every `withbor`/`withload` type in both documents, and neither
defines it as an operation. The prose makes the intended meaning clear ([CONF] p. 415:8: "a
fresh lifetime `'a`, which is shorter than all existing lifetimes in `Δ`"): the meet
(shortest) of the lifetimes that `Δ` mentions. Two choices remain open: whether `⊓Δ` ranges
over `dom(Δ)` (the variables) or `cod(Δ)` (their bounds), and what `⊓∅` is.

**`⊓Δ` is meta-notation.** It occurs only in the axiom table and in the *statements* of
Lemmas 6.172–6.175, never in a proof. In the proof of 6.172 the bound is converted directly
into the freshness quantifier:

    𝒱⟦∀'a ⊏ ⊓Δ. Imm a T ⊸ [a]T⟧(v) ⊧ ⋔α. ℓ ↦I 𝒱⟦T⟧(v) ─⋆ wp (v () ℓ) {v. [α] 𝒱⟦T⟧(v)}
    ([TR] l.2523)

`⋔` is a derived form ([CONF] §4.4): "there exists a lower bound β such that P̂ will outlive
any shorter lifetime α". Existence is the descending-chain argument at [TR] l.1285: "Such an
α always exists because for any lifetime, the set of lifetimes shorter than it is
infinite." So the proofs never compute a meet; what they need is a fresh lifetime.

On `dom` against `cod`, `dom(Δ)` is forced. `⟦Δ⟧` requires `δ('a) ⊏ Δ('a)δ`: every variable
is *strictly* shorter than its bound. Being below all the bounds therefore does not put a
lifetime below the variables, while being below all the variables puts it below everything.
`Life` has only *binary* meets over lifetime expressions, so `⊓Δ` is not itself a `Life`
term.

For the rule schemes the mechanisation still needs a `Life` term for the bound, so it
encodes `⊓Δ` as a right fold of binary meets over `dom(Δ)` with `⊓∅ = ⊤`
(`BoCa.Lifetime.meetOfDomL`, `BoCa.Lifetime.LifeCtx.meetOfDom`). Since `⊤ = 0` and `⊓` is
`max` on `ℕ`, the empty `max` is `0 = ⊤`, which is consistent.

### §12.16 `⊕I`'s conclusion `i e`

[TR] p. 2 prints `Δ; Γ ⊢ i e : T₁ ⊕ T₂`. The grammar has `inj₁ e | inj₂ e`. We read it as
`inj_i e`.

### §12.17 The `[b]T ⊐ a` rule: [CONF] and [TR] differ

- [CONF] Fig. 7: premise `(Δ ⊨ b ⊒ a) ∨ (Δ ⊢ T ⊐ a)`, a disjunction whose first disjunct is
  **non-strict**.
- [TR] p. 2: premise `Δ ⊨ @b ⊐ @a`, with no disjunction, **strict**.

[TR]'s rule is the one Lemma 6.60 is proved for, and it admits fewer derivations. **We
follow [TR]** (the `box` constructor of `BoCa.Outlives`, whose premise is
`Δ.EntailsLt a b`). Dropping `∨ (Δ ⊢ T ⊐ a)` loses derivations such as `[b](1) ⊐ a` for a
short `b`, which [CONF] admits.

The mechanisation does not test [CONF]'s reading. Its disjunction only adds derivations, so
no derivation that holds under [TR]'s rule is lost by taking it, but judgments that are
rejected under [TR]'s rule could become derivable.

The shape also differs from [CONF] Fig. 6, where `[]T ⊐ Imm` is an *axiom* with no premise.
The indexed judgment has no axiom for the modality.

### §12.19 The axiom table and `Γ`

[TR] p. 3 writes `Δ ⊢ op : T`, with no term context, while the `alloc`/`free` rules on p. 2
write `Δ; • ⊢ ...`. The compatibility lemmas are stated both ways (6.165:
`Δ; ∅ ⊨ alloc : ...`; 6.172: `Δ ⊨ withbor : ...`). We read the axiom table at the empty
context. In the mechanisation each axiom constructor (for instance
`BoCa.Derives.withbor2Ax`) takes a context whose slots are all dead (`BoCa.Ctx.Dead`).

### §12.20 The sugar bodies of [TR] p. 4 and of [CONF]: `swap`, `withload`, `withbor`

Both documents print the same ascribed types ([TR] p. 3; [CONF] Figs. 3b, 7, 9, 14, 15).
For `swap`, `withload` and `withbor` the two documents print **different bodies**, and in
each case [CONF]'s body is the one that has the ascribed type. The mechanisation follows
[CONF] (`BoCa.swap`, `BoCa.withload`, `BoCa.withbor`). `withswap` and the remaining sugar
definitions agree between the documents.

- `swap`: [TR] p. 4 prints `λx.λy. let z = load x; store x y; (x, y)`, which binds `z`
  without using it and returns the **new** payload `y`; the shared type
  `Ref T₁ ⊸ T₂ ⊸ Ref T₂ ⊗ T₁` makes the second component the old one. [CONF] Fig. 3b
  (p. 415:4) prints `swap ≜ λx λy₂. let y₁ = load x; store x y₂; (x, y₁)`, which has that
  type. [TR]'s own proof of Lemma 6.169 (`swap-compat`, p. 44) runs [CONF]'s body: it
  evaluates `let z = load v₁; store v₁ v₂; (v₁, z)`, returning the old payload `z`, and
  unfolds that `let` to `(λz. store v₁ v₂; (v₁, z)) (load v₁)`. With [CONF]'s body the
  lemma is stated as printed: `Fig16.LogRel.swap_compat`.
- `withload`: [TR] p. 4 prints `λx.λf. (x, f (load x))`, which returns a **pair**, where the
  shared type `Imm @a T₁ ⊸ (...) ⊸ T₂` returns a bare `T₂`. [CONF] Fig. 14 (p. 415:16)
  prints `withload ≜ λx λf. f () (load x)`, which has that type; [TR]'s proof of Lemma 6.175
  (p. 47) unfolds `withload` to `λf. f () (load v)`, which is [CONF]'s body.
- `withbor`: [TR] p. 4 and [CONF] p. 415:6 both print `λx.λf. (x, f x)`. The §2.3 type
  `Ref T₁ ⊸ (∀'a ⊏ ⊓Δ. Imm 'a T₁ ⊸ ['a]T₂) ⊸ Ref T₁ ⊗ T₂` makes `f` a **thunk**
  (`𝒱⟦∀'a ⊏ @b. T⟧δ(v) ≜ ∀α ⊏ @bδ. ℰ⟦T⟧δ(v ())`, [TR] p. 4), so `f` is forced with `()`
  before it receives the borrow. [CONF] Fig. 15 (p. 415:17) prints
  `withbor ≜ λxλf. (x, f () x)`, which has that type, and [TR]'s own proof of Lemma 6.172
  writes `wp (v () ℓ)` (p. 46, l. 2523). The difference is visible operationally: with the
  body read literally, `withbor x (Λ.λb. e)` reduces to `(x, λb. e)`, so the borrower
  receives `x` as its *lifetime* argument and does not receive the borrow. [CONF]
  p. 415:6's body does have its own §2.2 type `Ref T₁ ⊸ (Imm T₁ ⊸ T₂) ⊸ (Ref T₁) ⊗ T₂`,
  where there are no lifetimes; Fig. 15's is the one that has the §2.3 type that [TR] p. 4
  prints alongside the body.
- `withswap`: the two documents agree. [TR] p. 4's
  `withswap ≜ λx.λf. let (y, z) = f (load x); store x y; (x, z)` and [CONF] Fig. 15's are
  the same term, and it has its ascribed type
  `Mut a T₁ ⊸ (T₁ ⊸ T₁ ⊗ T₂) ⊸ (Mut a T₁) ⊗ T₂`. Its callback is a bare `⊸`, not a
  `∀`-thunk, so no lifetime application is involved. It is listed here so that the three
  cases above are not read as a pattern covering every sugar definition.
- Single-binder `let`. `swap` and `withswap` use `let z = e; e′`, which [TR] p. 1's `Expr`
  grammar does not produce (it has only `let (x,y) = e₁ in e₂`). We desugar it to
  `(λz. e′) e` (`BoCa.elet`), which is how [TR]'s proof of Lemma 6.169 unfolds it.

### §12.21 Two names for the same operation

[CONF] calls it `dupl`, [TR] calls it `copy`; the type is the same. The mechanisation uses
`copy` (`BoCa.copy`).

### §12.24 Fig. 5's borrower and Fig. 6's `[]I`

The borrower `λf'. avg f'` of [CONF] Fig. 5 has type `Imm File ⊸ []ℕ`, so by ⊸I its body
`avg f'` must be typed `[]ℕ` in a context containing `f' : Imm File`. Only `[]I` concludes
a `[]`, and `[]I`'s premise scans that context and finds `Imm File`, for which Fig. 6
deliberately has no rule. Read literally, then, `[]I` does not type `avg f'` in the term
form Fig. 5 writes.

**The observation is about the printed term form and no more.** `[]I` can fire at a
sub-derivation whose context does not hold the borrow, and 1E / ⊗E / ⊕E / ⊸I then carry the
`[]` out to a context that does. So a βη-variant of the same borrower in let-normal form —
the borrow-consuming work in a scrutinee position and the tail boxed — is typed by the
printed rule alone. The form `avg f'` as Fig. 5 writes it would additionally need `words`,
`lines` and `/` ascribed at codomains of the form `[]ℕ`, which Fig. 5 does not write. The
precise statement is that, read literally, the rules are not closed under the commuting
conversions Fig. 5's examples assume; it is not that a borrower can never use its borrow.

**In the lifetime-indexed system a borrower can use an *outer* borrow directly.**
`Δ ⊢ Imm @b T ⊐ @a` holds whenever `Δ ⊨ @b ⊐ @a`, so the context-directed rule boxes at any
lifetime strictly shorter than the borrows in scope. That is the shape of `login` ([CONF]
§2.3): `BoCa.Derives.boxIctx` applies at `Γ = [Imm 'a 1]` and `@a := 'b` with
`Δ ⊨ 'b ⊏ 'a`. What the context-directed rule does not do is box at the borrower's *own*
lifetime, which is what the borrower's ascribed type asks for.

A rule that would type the printed term form is

```
 T ⊒ Imm
─────────────
 Γ ⊢ e : T  ⟹  Γ ⊢ e : []T
```

which [CONF] Fig. 6 (p. 415:7) does not print, but which is the typing-level counterpart of
[TR] Lemma 6.60 (`Δ ⊢ T ⊐ @a ∧ ρ ∈ 𝒱⟦T⟧δ ⟹ @ρ ⊐ @aδ`, i.e. `𝒱⟦T⟧ ⊆ 𝒱⟦[@a]T⟧`;
`TR.lemma_6_60`), so it is sound in the model. It cannot be the *only* `[]I` rule: on its own
it is the "no `Imm`s and no functions in the return type" restriction that [CONF] p. 415:6
attributes to Wadler and does not adopt.

**In the lifetime-indexed system ([CONF] Fig. 7, [TR] p. 2) the question sits at one
point.** There the borrower's body has `f' : Imm 'a T₁` in context and must produce
`['a]T₂`, which the context-directed rule answers only with `Δ ⊢ Imm 'a T₁ ⊐ 'a`, i.e.
`Δ ⊨ 'a ⊐ 'a`. `⊐` is the strict `>` on ℕ (§12.3), so this does not hold. Making `⊐`
reflexive would admit [CONF] p. 415:6's identity-borrower use-after-free, since
`Imm 'a T₁ ⊐ 'a` would then hold and the identity borrower would have type
`Imm 'a T₁ ⊸ ['a](Imm 'a T₁)`. A third position makes both work: require only that the
*result* type outlive `'a`, which is the form the wp at [TR] p. 46, l. 2523 takes. See §12.26.

### §12.26 A result-directed `[]I`: sound in the model, and not among the printed rules

§12.24 observes that in the indexed system a borrower's body has `Imm 'a T₁` in context and
must produce `['a]T₂`, which the context-directed rule answers only with `Δ ⊨ 'a ⊐ 'a`, and
that making `⊐` reflexive would admit the identity-borrower use-after-free. Both
observations concern the **context**-directed rule only. The *result*-directed rule

```
 Δ ⊢ T ⊐ @a
────────────────────────────────────
 Δ; Γ ⊢ e : T  ⟹  Δ; Γ ⊢ e : [@a] T
```

never inspects `Γ`, so it never asks for `Imm 'a T ⊐ 'a`:

| program | borrower's result | premise | verdict |
| --- | --- | --- | --- |
| [CONF] Fig. 5 `avg` | `ℕ = 1 ⊕ 1` | the `1` and `⊕` rules | accept |
| [CONF] p. 415:6, identity borrower | `Imm 'a T₁` | `Δ ⊨ 'a ⊐ 'a` | reject, by irreflexivity |
| [CONF] p. 415:6, closure capturing the borrow | `T₁ ⊸ T₂` | no rule for `⊸` | reject |
| [CONF] §2.3 `login` | `Imm ('a ⊓ 'b) File` at `'c` | `'c ⊏ 'a` and `'c ⊏ 'b` | accept |

So this rule is compatible with §12.3's reading: one strict, irreflexive `⊐`, with `⊑` its
reflexive closure, used only by `⊑Imm`/`⊑Mut`.

**Where the rule appears.** It is not among the statics: [CONF] Fig. 6 (p. 415:7), [CONF]
Fig. 7 (p. 415:8) and [TR] p. 2 each print `[]I` with the context premise, and `[]E`, and
nothing else about the modality (400 dpi). The mechanisation's `Derives` has the
context-directed rule alone (`BoCa.Derives.boxIctx`, `BoCa.Derives.boxE`). §12.24 shows that
the printed rule types `login`'s shape and let-normal variants of Fig. 5's borrower.

**It is sound.** Lemma 6.60 and `[α]P(ρ) ≜ P(ρ) ∧ @ρ ⊐ α` give
`𝒱⟦T⟧δ ⊨ [@aδ] 𝒱⟦T⟧δ`, and [TR] takes exactly that step inside its own proofs, twice:
l. 2554 in Lemma 6.173 (`withbor-compat2`) and l. 2624 in Lemma 6.174 (`withbor-compat3`)
(line numbers of `pdftotext -layout 3764117-supplement.pdf -`). It is a lemma the paper
uses; it is not one of the typing rules. The proof of Lemma 6.176 (`withswap-compat`,
l. 2738 ff.) does not use 6.60; it goes through `wp-m-anti-frame`.

**It does not subsume the context-directed rule.** Take `Δ; • ⊢ λx.x : T ⊸ T`: the context
premise is vacuous, so `[]I` gives `[@a](T ⊸ T)` at every `@a`, while `Δ ⊢ T ⊸ T ⊐ @a` has
no rule at all. That difference is by design — it is the reason the modality exists instead
of the "no borrows and no functions in the result" restriction [CONF] p. 415:6 attributes to
Wadler, which is what the result-directed rule alone would be. The two rules are
incomparable: the context-directed one lets a borrower return a closure; the
result-directed one lets a borrower use its own borrow. An implementation that wants both
Fig. 5's borrower in its printed form and a closure-returning borrower needs both.

### §12.27 `Λ.e ≜ λ_.e` makes `λx. ()` well typed

§12.14 reads `Λ.e` as `λ_.e` and `e[]` as `e ()`. A consequence: under that identification
a `λ` whose binder is unused *is* a lifetime abstraction, and `∀I`'s premise
`Δ, ('a ⊏ @b); Γ ⊢ e : T` has no binder in `Γ` to leave unconsumed. So `λx. ()` — which is
also the body of `forget` ([TR] p. 4; `BoCa.forget`) — is well typed at `∀'a ⊏ @b. 1`, even
though the calculus has no weakening.

This is consistent with linearity: the absence of weakening is a property of `⊸`, and
`λx. ()` still has no `⊸` type. It does mean that "this term is ill-typed" is not an
accurate summary of `forget`'s body; the accurate statement is that it does not have the
type `Imm @a T ⊸ 1` that the axioms ascribe to it. It also means that telling `⊸I` from `∀I`
is exact and syntactic: the binder is used, or it is not.

### §12.28 The `Imm` metafunction and the `Imm` constructor: told apart by an underline

This reading changes the type system.

Both documents write the reborrow metafunction as `Imm` with an underline and the type
constructor as `Imm` without one, and the two occur side by side within single clauses:

```
Imm 'b (Ref T)     ≜  Imm 'b T        ← LHS underlined, RHS not              (5)
Imm 'b ([@a] T)    ≜  Imm 'b T        ← both underlined                      (7)
Imm 'b (Imm @a T)  ≜  Imm @a T        ← LHS underlined, RHS not              (6)
Imm 'b (Mut @a T)  ≜  Imm 'b T        ← LHS underlined, RHS not ([CONF] Fig. 9) (9)
```

Evidence, at 600 dpi: [TR] p. 3, the metafunction block (rows 2 and 3); [CONF] Fig. 8,
p. 415:10, rows 2 and 3; [CONF] Fig. 9, p. 415:10, top right. In every case the leading
`Imm` carries a rule under "mm" and the trailing one in (5), (6) and (9) does not. [CONF]
Fig. 9 was also read at 1200 dpi (bbox 280.4–386.8 × 225.4–235.9 pt), with clauses (5) and
(7) from Fig. 8 on the same page rendered at the same resolution as controls: (5) has a bare
`Imm` on the right, (7) an underlined one, (9) a bare one.

Two points for a reader.

1. **The distinction is invisible to `pdftotext`.** The text layer of both PDFs renders
   every occurrence as the bare word `Imm`, so a transcription made from extracted text, or
   from reading at normal size, cannot tell (5) from (7).
2. **The two readings give different type systems.** Under the recursive reading,
   `Imm 'b (Ref 1) = Imm 'b 1 = 1`: loading a borrow of a `Ref 1` yields an owned unit, and
   clause (5) forgets the borrow. Under the printed reading it is `Imm 'b 1`, a borrow of
   the payload at the load's fresh lifetime — Rust's `&Box<T> ↦ &T`. Only the second makes
   [CONF] §2.4's double-free program ill-typed while keeping its nested borrow usable, and
   those are the two programs §2.4 is written around.

The prose alone does not decide it: [CONF] p. 415:9 says of (7) that "the modality must be
removed, leaving `Imm 'b T`", which reads the same either way. Besides the glyphs, [CONF]
p. 415:11 on (9) decides it — "the lifetime on this reborrow is the fresh lifetime `'b`
introduced for the load, and not the original lifetime `a`" — which calls the right-hand
side *a reborrow*, i.e. a borrow type. The mechanisation implements the metafunction as
`BoCa.Ty.immReborrow`, distinct from the constructor.

(9) and (5) have the **same** right-hand side, `Imm 'b T`. The alternative that (9)
excludes is reusing the mutable borrow's own index and writing `Imm @a T`, which the
sentence just quoted rules out and which would let the reborrow escape the load: the `@a` is
dropped and the load's `'b` is used.

In [TR] p. 3's axiom list, at 600 dpi, the underline appears exactly once — on `withload`'s
`Imm 'b T₁` — and on none of `withbor`'s three lines. That is the expected distribution:
only `withload` hands the borrower the result of a *load*.

### §12.32 `Δ ⊢ Mut @a T`: the printed rule and the premise Lemma 6.174 reads off it

[TR] p. 2, read at 1200 dpi (crop x ∈ [354, 480] pt, y ∈ [481, 510] pt), prints

```
 Δ ⊢ T    Δ ⊨ @a
 ───────────────
  Δ ⊢ Mut @a T
```

— two premises, with no lifetime bound on the payload.

[TR] l. 2624, inside the proof of Lemma 6.174 (`withbor-compat3`, p. 47), reads:

> "Have `Δ ⊢ T₁ ⊐ @a` **by well-formedness of the type `Mut @a T₁`**, hence
> `𝒱⟦T₁⟧δ ⊧ [α] 𝒱⟦T₁⟧δ` by theorem 6.60"

The two printed premises do not give `Δ ⊢ T₁ ⊐ @a`. [CONF] p. 415:10's prose supports the
proof's reading — "the payload type for a mutable borrow is required to have an unambiguous
lifetime bound" — and it is the same condition that appears as the side condition of
`withbor`'s form (2) (§12.9). So the intended `Δ ⊢ Mut @a T` rule plausibly carries
`Δ ⊢ T ⊐ @a` as a third premise.

**The mechanisation follows p. 2 as printed**: `BoCa.WfTy.mut` has exactly the two
premises. Lemma 6.174 is proved without the third premise
(`Fig16.LogRel.withbor3_compat`): the entailment `𝒱⟦T₁⟧δ ⊨ [β] 𝒱⟦T₁⟧δ` is read off the
`mut` cell in hand, whose invariant is supported at the cell's own lifetime `β`
(`Fig16.BoLo.ptoMut`, `Fig16.LogRel.vDen_mut_supported`), rather than off a well-formedness
premise. The rest of the proof follows p. 47.

### §12.33 `fin` on `Res`: the two documents differ

This entry records the reading of `Res` adopted by the mechanisation, with both printed
forms and the checks made against it.

**What each document prints.** [TR] §5's model display, p. 4, row 7:
`ρ ∈ Res ≜ Loc ⇀ᶠⁱⁿ Cell` — a sans-serif `fin` with an fi-ligature, set above and to the
right of the barb, read at 1600 dpi on a crop with clear headroom above the barb. Row 2 of
the same display, `Res_α ≜ Loc ⇀ Cell_α`, is bare at the same resolution. [CONF] Fig. 16,
p. 415:20, prints both rows bare at 600 dpi, and the word "finite" does not occur in
[CONF]'s 27 pages (`pdftotext | grep -i finite` gives two hits, both inside "Transfinite",
one of them a bibliography title).

**The reading.** `Res` is finite, as [TR] prints it.

**Checks.** Three things that would tell against the reading, and what they show.

1. *Does [CONF] need finiteness on its own pages?* It does not face the question. [CONF]
   prints no `wp-alloc` and no equation for `@ρ`; it glosses `@ρ` in prose on p. 415:23
   ("the shortest among the lifetimes in its cells") and uses the symbol in Fig. 19. So the
   absence of the mark has no consequence on [CONF]'s own pages, and is not evidence that
   the object is meant to be unrestricted.
2. *Is `@ρ` defined without it?* `⊓ ≜ max` on ℕ ([CONF] Fig. 11, p. 415:12, 600 dpi; [TR]
   p. 4 row 9, 1600 dpi) and `@ρ ≜ ⨅_{ψ ∈ cod(ρ)} @ψ` ([TR] p. 5, 600 dpi). An unbounded
   `cod(ρ)` has no greatest element, so `@ρ` has no value, and
   `[α]P(ρ) ≜ P(ρ) ∧ @ρ ⊐ α` ([CONF] Fig. 19) is defined through it. Without finiteness,
   every lemma mentioning the outlives modality would need a side condition neither
   document prints.
3. *Does a printed proof step use it?* [TR] Lemma 6.141 (`wp-alloc`, p. 37, 600 dpi) is
   stated with no hypotheses, and its proof reads "Choose an `ℓ` such that `ℓ ∉ ρ_f • ρ`" in
   one step. That step is available when `ρ_f • ρ` misses a location, which a finite `Res`
   guarantees over an infinite `Loc` and an unrestricted `Loc ⇀ Cell` does not.

None of the three tells against the reading; (2) and (3) are what the unmarked reading would
have to supply by side conditions that neither document prints.

**Heredity.** Row 2 inherits row 7's mark, and so does every `Res_β` a `mut` cell stores.
The argument is internal to [TR]: every operation from `▶◀` on is defined on the
unstratified `Res`, `Mut_α`'s witness is a `Res_β`, and the flattening walk composes exactly
those witnesses with `◐`, so a `Res_β` must be a `Res`. Finiteness at row 2 departs from
row 2's printed bare harpoon; that departure is entry D10 and convention G1, and is
tagged `[variant: …]` at `Fig16.Res` (`Paper/S5_Model/Definitions.lean`).

That `Loc` is infinite is our assumption — neither document states it — and it enters as a
hypothesis, through `Fig16.PMap.exists_fresh`, never as a global assumption.

### §12.34 [TR] Definition 6.3, last sub-bullet: `ρ′` read as `ρ″`

**What is printed.**  [TR] p. 17:

```
Definition 6.3.  ρ ⊟ ρ′ ≜ ρ|own,mut ● ρ″  where
  • ρ′|own,mut = ∅
  • ρ″ ≤ ρ|imm
  • if ℓ ∈ dom(ρ|imm) ∖ dom(ρ′) then ℓ ∈ dom(ρ″)
  • if ℓ ∈ dom(ρ|imm) ∩ dom(ρ′) and ρ(ℓ) = imm(ᾱ, ρᵢ, v) and ρ′(ℓ) = imm(β̄, ρᵢ, v) then
      – if ᾱ ∖ β̄ = ∅, then ℓ ∉ ρ″,
      – if ᾱ ∖ β̄ ≠ ∅, then ρ′(ℓ) = imm(ᾱ ∖ β̄, ρᵢ, v)
```

The last line carries a single prime.  The glyph is unambiguous: in the PDF's word-level
bounding boxes the prime at that position is 2.364 pt wide, against 4.728 pt for the `ρ″`
two lines above on the same line height, and the two are visually distinct at 600 dpi.

**The reading adopted.**  The last line is read as constraining `ρ″`:
`ρ″(ℓ) = imm(ᾱ ∖ β̄, ρᵢ, v)`.

**What the literal reading admits.**  The bullet's own hypothesis fixes
`ρ′(ℓ) = imm(β̄, ρᵢ, v)`.  Since `β̄` and `ᾱ ∖ β̄` are disjoint and lifetime sets are drawn
from `℘⁺(Life)` (nonempty), the two cells differ, so the second sub-case cannot be met.
Read literally, `ρ ⊟ ρ′` is therefore defined only where `ᾱ ⊆ β̄` at every shared `imm`
location.  `BoCa.Fig16.ResU.SubClauseL` is the bullet as printed and `BoCa.Fig16.ResU.SubL`
is Definition 6.3 built on it.

**Grounding in the paper.**  [CONF] prints no `⊟`, so there is no second document to weigh.
[TR] itself supports the `ρ″` reading twice:

* Lemma 6.52's proof (pp. 17–18) writes
  `ρ⁺ = (ρ⁺ ⊟ ℓ ↦ imm({α}, ρ_ℓ, v_ℓ)) ● ℓ ↦ imm({α}, ρ_ℓ, v_ℓ)` at a location where it has
  just derived `⦇ρ⁺⦈(ℓ) = imm(β̄⁺, ρ_ℓ, v_ℓ)` with `α ∈ β̄⁺` and `β̄⁺` not required to be
  `{α}`; the second sub-case is used there.
* The prose immediately below the definition reads "'without' means removing the lifetimes
  of borrows from `ρ′`, but keeping the lifetimes only in `ρ`", which is
  `ρ″(ℓ) = imm(ᾱ ∖ β̄, ρᵢ, v)` in words.

**In the mechanisation.**  `BoCa.Fig16.ResU.SubClause` and `BoCa.Fig16.ResU.Sub` carry the
`ρ″` reading and are tagged `[variant: …]`; the literal reading is kept alongside as
`ResU.SubClauseL`/`ResU.SubL`.  The definition used downstream is `BoCa.Fig16.ResU.SubKeep`
(§12.58).

**Two notational points on the same page.**  [TR] §6 writes the `imm` cell as
`(lifetimes, witness, value)` where Fig. 16 and [TR] p. 5 write
`(lifetimes, value, witness)`; the positions are named by their metavariables (`ρᵢ`, `v`),
so the reading is not in doubt, and the Fig. 16 order is used throughout.  And `≤` on
resources, used in the second bullet, is printed by [CONF] p. 415:24 footnote 1 as the
`●`-extension order (§12.37).  A sub-map reading of `≤` would conflict with this
definition's own fourth bullet.

---

### §12.35 `⋈` is the domain of `○`

**What is printed.**  [TR] p. 5; [CONF] prints no `⋈`:

```
ψ₁ ⋈ ψ₂ ≜ ψ₁ ▶◀ ψ₂ ∨ ∃ i, ᾱ, β, v, ρ, P̂. {ψ₁, ψ₂} ∈ {imm(ᾱ,v,ρ), own(v), mut(β,v,ρ,P̂)}
```

Read literally, the second disjunct asserts that a two-element set is an element of a
three-element set of cells, and the existential binds an `i` that does not occur in the
body, where the structurally parallel clauses of `○` use `ψᵢ` and `ψ₃₋ᵢ`.

**The reading adopted.**  `ψ₁ ⋈ ψ₂ ⟺ ψ₁ ○ ψ₂ is defined`: `⋈` is the domain of `○`, exactly
as `▶◀` is the domain of `●` (Lemma 6.9).

**The readings available.**

* (a) `{ψ₁,ψ₂} ⊆ {…}` with the displayed binders shared by both cells.  Then two `mut`
  cells at different lifetimes, or with different invariants, are never `⋈`.  Since the
  resource-level `◐` is guarded by `▶◁` ([TR] p. 5's schema), clause (3) of `○`,
  `mut(α ⊓ β, v, ρ, P̂ ∧ Q̂)`, would then apply only at `α = β` and `P̂ = Q̂`, returning
  `mut(α ⊓ α, v, ρ, P̂ ∧ P̂)`.
* (b) The binders that differ between the two cells, `β` and `P̂`, instantiated per cell.
* (c) `⋈ ≜ dom(○)`.

(b) and (c) are the same relation.  The printed set carries one `ᾱ`, one `v` and one `ρ`;
two `imm` cells with different lifetime sets are already covered by the first disjunct
`▶◀`; and letting `β` and `P̂` vary per cell gives exactly the pairs `○` composes:
`ψ₁ = ψ₂` (clause 1, since a cell is a member of the set), two `imm` over a common `(v, ρ)`
(clause 2 via `▶◀`), two `mut` over a common `(v, ρ)` (clause 3), and the mixed
`own`/`mut`/`imm` pairs (clauses 4 and 5).

**Grounding in the paper.**  [TR] Lemma 6.3's proof reads naturally only under (b)/(c).  Its
`○` case says "In the third case, if `ρ₁(ℓ)` is owned, then the mut is the result, if it is
mut then we use associativity of `⊓` and `∧`, and if it is imm then the result is imm either
way" (p. 7).  Associativity of `⊓` and of `∧` is clause (3) applied to three cells at three
lifetimes with three invariants.  (Under (a) associativity still holds, degenerately; the
proof's wording is what points to (b)/(c).)

The two other uses of `⋈` agree.  Lemma 6.1's proof of the `⋈` case is "immediate since sets
are unordered", which confirms that `{ψ₁,ψ₂}` is meant as a set.  Lemma 6.37 (`ρ ▶◀ ρ₁` and
`ρ ▶◀ ρ₂` and `ρ₁ ⋈ ρ₂` imply `ρ ▶◀ ρ₁ ○ ρ₂`) uses `ρ₁ ⋈ ρ₂` exactly in the position
"`ρ₁ ○ ρ₂` is defined".

**In the mechanisation.**  `BoCa.Fig16.CellU.CompatR` is `dom(○)`, tagged `[variant: …]`;
`BoCa.Fig16.ResU.CompatR` and `BoCa.Fig16.ResU.CompR` are [TR] p. 5's two schemas
instantiated at it, exactly as `ResU.CompatS`/`ResU.CompS` instantiate them at `▶◀`/`●`.
Both instances of the schemas are supplied, and Lemma 6.1
(`BoCa.Fig16.ResU.compat_comm_iff`) is stated over the schema and discharged at both.

---

### §12.36 The walks' iterated comprehension is a family indexed by locations

**What is printed.**  [TR] p. 5:

```
ex(ρ)_◐ ≜ ρ|own ◐ ρ|mut ◐ ⨀_◐ {ex(ρ′)_◐ | ∃ℓ. ρ(ℓ) = mut(_,_,ρ′,_)}
ag(ρ)_◐ ≜ ρ|imm ○ ◯{ag(ρ′) | ∃ℓ. ρ(ℓ) = mut(_,_,ρ′,_)}
                 ○ ◯{ex(ρ′)_○ ○ ag(ρ′) | ∃ℓ. ρ(ℓ) = imm(_,_,ρ′)}
```

(The `ag` row's left-hand `◐` subscript does not affect the reading; [CONF] Fig. 18a writes
`A⦇ρ⦈` unsubscripted.)  [CONF] p. 415:22, Fig. 18a, writes the same rows with an explicit
codomain:

```
E⦇ρ⦈_◐ ≜ … ◐ ⨀_{ρ′ ∈ cod(ρ|mut)} E⦇ρ′⦈_•
A⦇ρ⦈   ≜ … ○ ◯_{ρ′ ∈ cod(ρ|mut)} A⦇ρ′⦈ ○ ◯_{ρ′ ∈ cod(ρ|imm)} E⦇ρ′⦈_○ ○ A⦇ρ′⦈
```

Both are set-builder notation.  `cod` is a set of values, in which two locations carrying
the same cell contribute one element.

**The two documents differ.**  [TR]'s comprehension binds an existential over locations,
which reads naturally as a family indexed by locations; [CONF]'s `cod(ρ|mut)` reads as a
set of values.  As elsewhere, [TR] is followed.

**The reading adopted.**  The iterated operators range over the family indexed by
locations: one component per `ℓ ∈ dom(ρ|mut)` (resp. `dom(ρ|imm)`), even when two
locations carry equal cells.

**Why: [TR] Lemma 6.18 requires it.**  Lemma 6.18 (p. 8): if `ρ₁ ▸◂ ρ₂` then
`ex(ρ₁ ● ρ₂)_●` and `ex(ρ₁)_● ● ex(ρ₂)_●` are Kleene-equal.  At pairwise-distinct `ℓ₁`,
`ℓ₂`, `ℓ₃`, take

```
σ  ≜ ℓ₃ ↦ own(w)          ρ₁ ≜ ℓ₁ ↦ mut(α, v, σ, P̂)          ρ₂ ≜ ℓ₂ ↦ mut(α, v, σ, P̂)
```

`ρ₁ ▸◂ ρ₂` holds because the domains are disjoint.  The two `mut` cells are equal as cells.

* On the set reading, `{ex(ρ′)_● | …}` over `ρ₁ ● ρ₂` is the singleton `{ex(σ)_●}`, and the
  left-hand side is defined.
* The right-hand side needs `ex(σ)_● ● ex(σ)_●`.  `ex(σ)_● = σ = ℓ₃ ↦ own(w)`, and `●`
  composes only `imm` cells (p. 5's `ψ₁ ● ψ₂` row), so it is undefined.

So we cannot reconcile the set reading with Lemma 6.18 at this configuration.  On the
family reading the composite's family has two entries, both `ex(σ)_●`, the left-hand side
is undefined too, and the lemma holds.  (All three locations must be distinct: if `ℓ₃ = ℓ₁`
then `ex(ρ₁)_●` already needs `mut ● own` at `ℓ₁` and both sides fail together.)  The objects
in the configuration are Fig. 16's and p. 5's; conventions G1 and G8 are in play as
everywhere, and neither bears on the reading of the comprehension.

**Corroboration from [TR]'s proof of Lemma 6.18** (p. 9).  The proof opens "Since
`ρ₁ ▸◂ ρ₂`, it must be that `ρ₁` and `ρ₂` have disjoint own-or-mut cells", and then splits
`⨀_{∈ρ₁₂}` into `⨀_{∈ρ₁} ● ⨀_{∈ρ₂}`.  `▸◂` is pointwise on `dom(ρ₁) ∩ dom(ρ₂)`, so
"disjoint own-or-mut cells" is disjointness of locations, and splitting an indexed
composite this way is valid exactly when the index is location-tagged: on the value
reading the index sets can overlap even when the locations do not, and `●` has no
idempotence to absorb a double count.

Lemma 6.20's proof (same page) is a different situation and not evidence either way: it
decomposes an overlapping union by inclusion–exclusion with Lemma 6.19's idempotence, but
its composite `ρ_ag ≜ ◯_{imm(_,_,ρ′)∈ρ₁₂} ⦇ρ′⦈_○` is the `imm`-indexed `○` composite, whose
operator is idempotent.

**In the mechanisation.**  `BoCa.Fig16.ExW.mk` and `BoCa.Fig16.AgW.mk` bind a list of
`(location, resource)` pairs constrained by `BoCa.Fig16.ResU.Sites` to enumerate
`dom(ρ|ι)` exactly once each.  `ExW`/`AgW` are tagged `[variant: the printed comprehension
is a set and this is the family it indexes]`.  The family's order is existentially bound
(`BoCa.Fig16.BigComp` folds a list); [TR] Lemma 6.3 is what makes that order immaterial.

---

### §12.37 `≤` on resources: printed by [CONF] p. 415:24 footnote 1

**What is printed.**  [CONF] p. 415:24, footnote 1 (1200 dpi):

```
¹Where ρ₁ ≤ ρ₃ ≜ ∃ρ₂ ▶◀ ρ₁. ρ₁ ● ρ₂ = ρ₃.
```

The bowtie is filled (strict compatibility) and the circle is solid (strict composition).
[TR] uses `≤` on resources in Definition 6.3's second bullet (`ρ″ ≤ ρ|imm`, p. 17) and, on
unfolding `reb`, in the proofs of Lemmas 6.54 (p. 18) and 6.57 (p. 19), and gives no
defining row.  `reb_α`'s own row ([TR] p. 5) writes the converse,
`ρ ≥ ⨀_{ℓ∈dom(π)} π(ℓ)`, as does [CONF] Fig. 19; the footnote is the gloss [CONF] p. 415:24
puts on it.

**The two documents differ**, in the ordinary way: [TR] is silent where [CONF] supplies a
defining row.  The mechanisation follows [CONF]:

```lean
def ResU.Le (ρ σ : ResU Loc Val) : Prop := ∃ τ, ResU.CompS ρ τ σ
```

`BoCa.Fig16.ResU.Le` is the footnote glyph for glyph and is tagged `[as printed]`.  The
operands of `▶◀` are transposed relative to the print, which [TR] Lemma 6.1 (`▶◀` is
symmetric, `BoCa.Fig16.ResU.compat_comm_iff`) licenses.

**Consequences.**  `≤` is not a convention of ours.  The fact that Definition 6.3's bullets
alone do not fix `ρ ⊟ ρ′` (§12.38) is a property of those bullets under the printed `≤`.
Independently, a sub-map reading of `≤` would conflict with Definition 6.3's own fourth
bullet.

---

### §12.38 [TR] Definition 6.3's bullets and the term `ρ ⊟ ρ′`

**What is printed.**  [TR] p. 17, Definition 6.3 in full (displayed at §12.34).  The prose
that follows reads "Intuitively, `ρ ⊟ ρ′` is `ρ` without the immutable borrows in `ρ′`…".
[TR] writes `ρ ⊟ ρ′` as a term wherever it occurs (pp. 17–20 and 40); Lemma 6.52 (p. 17)
states `ρ⁺ = (ρ⁺ ⊟ ρ_reb) ● ρ_reb`, an equation between values.

**The four bullets alone do not fix `ρ″`.**  At a location in `dom(ρ|imm) ∖ dom(ρ′)` the
third bullet fixes only membership in `dom(ρ″)`; the cell there is constrained only by
`ρ″ ≤ ρ|imm`, which is the `●`-extension order (§12.37), and by [TR] Lemma 6.43 `imm` cells
compose by union of lifetime sets, so a cell with a smaller lifetime set also satisfies it.
At `Loc = Val = ℕ`:

```
ρ  ≜ ℓ₀ ↦ imm({1,2}, 0, ∅)        ρ′ ≜ ∅
χ₁ ≜ ρ                            χ₂ ≜ ℓ₀ ↦ imm({1}, 0, ∅)
```

Both satisfy every bullet: bullet 1 because `∅|own,mut = ∅`; bullet 4 vacuously because
`dom(ρ′) = ∅`; bullet 3 because `ℓ₀ ∈ dom(χᵢ)`; and bullet 2 for `χ₂` via
`τ = ℓ₀ ↦ imm({2},0,∅)` and Lemma 6.43.  And `χ₁ ≠ χ₂`.  This holds on both readings of the
last sub-bullet (§12.34).

**The clause that fixes it is printed one line below the bullets:** "removing the lifetimes
of borrows from `ρ′`, **but keeping the lifetimes only in `ρ`**".  Off `dom(ρ′)` every
lifetime of `ρ(ℓ)` is one "only in `ρ`", so `ρ″(ℓ) = ρ(ℓ)`, not merely `ℓ ∈ dom(ρ″)`.
Read with that sentence, Definition 6.3 determines `ρ ⊟ ρ′`; this is §12.58.

**In the mechanisation.**  `BoCa.Fig16.ResU.Sub` (bullets only, `ρ″` reading of the last
sub-bullet) and `BoCa.Fig16.ResU.SubL` (bullets only, as printed) are graphs, and the
configuration above shows `ResU.Sub` admits two values.  `BoCa.Fig16.ResU.SubKeep` is the
third bullet read through the paragraph, with `BoCa.Fig16.ResU.SubKeep.toSub` the
implication to `ResU.Sub`; on it `⊟` is a function (`BoCa.Fig16.ResU.SubKeep.functional`),
which is what licenses writing `ρ ⊟ ρ′` as a term, and Lemma 6.52's equation holds of every
admissible value (`BoCa.Fig16.ResU.SubKeep.compS`).  Lemma 6.59 is proved at `SubKeep`.

---

### §12.39 [TR] p. 5, the second clause of `↭`: `mut` read as `imm`

**What is printed.**  [TR] p. 5, the last-but-one row of the operation display:

```
ρ₁ ↭ ρ₂ ≜  ∀ ℓ, α, β, v, ρ, P̂.
             (⦇ρ₁⦈(ℓ) = mut(α, _, _, P̂)  ⇔  ⦇ρ₂⦈(ℓ) = mut(α, _, _, P̂))
           ∧ (⦇ρ₁⦈(ℓ) = imm(β, v, ρ)     ⇔  ⦇ρ₂⦈(ℓ) = mut(β, v, ρ)),        ✓ρ₁ ∧ ✓ρ₂
```

The second clause relates an `imm` cell on the left to a `mut` cell on the right, and writes
that `mut` with three arguments.  Fig. 16 gives
`Mut_α ≜ {(β ⊐ α, v : Val, ρ : Res_β, P̂ : Val → SProp_β)}`, four components, and the row
directly above on the same page writes `mut(α, _, _, P̂)` with four.

**The reading adopted.**  `⦇ρ₁⦈(ℓ) = imm(β, v, ρ) ⇔ ⦇ρ₂⦈(ℓ) = imm(β, v, ρ)`.

**The two documents differ.**  [CONF] Fig. 18b (p. 415:22) prints the same definition with
the clauses in the other order and `imm` on both sides:

```
ρ₁ ↭ ρ₂ ≜ ∀ℓ, ᾱ, β, v, ρ, P̂.
    ⦇ρ₁⦈(ℓ) = imm(ᾱ, v, ρ)    ⇔ ⦇ρ₂⦈(ℓ) = imm(ᾱ, v, ρ)      (1)
  ∧ ⦇ρ₁⦈(ℓ) = mut(β, −, −, P̂) ⇔ ⦇ρ₂⦈(ℓ) = mut(β, −, −, P̂)   (2)
```

`imm ⇔ imm` and `mut ⇔ mut`, with `mut` four-ary and its value and witness wildcarded.  The
[CONF] form is followed, as in §12.33.

**Grounding in the paper.**  [CONF] p. 415:22, immediately below the figure: "The update
relation `↭`, defined in Fig. 18b, requires that all reachable immutable borrows are
preserved with their value `v` witness `ρ` exactly as is (Clause 1), and that all mutable
borrows are preserved up to a change in the witness (Clause 2)."  Clause 1 concerns
immutable borrows on both sides, and clause 2 wildcards the witness, which is why its
`−, −` appear.  An `imm ⇔ mut` clause would have a borrow change kind, where the prose says
"preserved".

**In the mechanisation.**  `BoCa.Fig16.ResU.Upd` transcribes [CONF] Fig. 18b: `imm ⇔ imm`
and `mut ⇔ mut` at the flattenings (`BoCa.Fig16.ResU.Flat`, with cells
`BoCa.Fig16.CellU.immOf` and `BoCa.Fig16.CellU.mutOf`).  [TR] p. 5's guard `✓ρ₁ ∧ ✓ρ₂` is
carried by `BoCa.Fig16.ResU.UpdV`; [CONF] Fig. 18b prints the relation unguarded.  Both are
defined because `wp` uses one and [TR] p. 6 the other; D3 records that inside `wp` they are
the same proposition.

---

### §12.41 `reb_α`: the escrow witness and the surviving `imm` cells

**What `reb_α` is for.**  [CONF] §3.2.3, p. 415:15:

> Recall that in well-typed programs, immutable borrows are accessed using the `withload`
> operation, whose type is parameterized by the metafunction `Imm`.  This metafunction maps
> a type to its reborrowed type, which immutably borrows any linear references or mutable
> borrows in the payload […]  To access immutable borrows in the logic, we will use a rule
> of a similar shape, but the metafunction `Imm` does not have a clear counterpart for
> separation logic propositions. […]  We instead adopt the more extensional approach of
> characterizing the full space of safe reborrows, which is captured by the reborrow
> modality, `⟲α P`.

So `⟲α P` is the extensional counterpart of a syntactic metafunction on types, and
`reb_α(ρ)` is that metafunction's action one level down, on cells.  Its three cases are the
metafunction's three cases: a linear reference becomes an immutable borrow, a mutable borrow
becomes an immutable borrow, an existing immutable borrow is kept.

**Why the `own` clause escrows and the other two do not.**  A reference owns its payload, so
rewriting `Ref T` recurses into `T`; at the resource level the payload's resource has to
*become* the new cell's witness, which is `π(ℓ)/ℓ`.  The metafunction stops at a borrow,
because a borrow's payload already sits behind it.  [CONF] p. 415:24 gives that reason in
those terms: "For a borrow cell (Cases 2–3), the partition `π(ℓ)` is additionally
constrained to contain only that cell, **since it already has a witness resource**."  So
`π(ℓ)` is the resource `ℓ`'s cell owns — what the metafunction recurses through — and `π`
decomposes `ρ` into those, which is why [CONF] p. 415:24 calls it a *partition*.

**The transcription.**  `Fig16.ResU.RebAt` and `Fig16.ResU.Reb` follow the formula ([TR]
p. 5; [CONF] Fig. 19, p. 415:23) and the prose ([CONF] pp. 415:23–24) clause by clause:
`ℓ ∈ dom(π(ℓ))` for every `ℓ ∈ dom(π)`, under none of the implications;
`own(v) ⇒ imm({α}, v, π(ℓ)/ℓ)` with no constraint on `dom(π(ℓ))`; `mut(_,v,ρ″,_) ⇒
imm({α},v,ρ″)` and the `imm` clause, each with `dom(π(ℓ)) = {ℓ}`.  The `imm` clause is read
at a subset of the source's lifetime set (definition row 5.28, §12.67(b)).  The asymmetry
between the escrowing `own` clause and the other two is the formula's.

**Two facts the printed proofs use.**  The proofs of [TR] 6.53, 6.55 and 6.61 each use a
fact about the reborrow that Fig. 19's formula, read on its own over all resources, does
not state.  [CONF] p. 415:24 prints *"The conditions placed on each partition `ℓ` in `π`
depends on the type of cell at `ℓ` in the original resource `ρ`"*; the formula carries no type, and §12.57 records how the two facts below are
that type discipline.

*For 6.61: every immutable cell of `ρ` survives in `ρ′`.*  [TR] p. 22: *"any overlapping
locations of `ρ′₁` and `ρ′₂` are in `(ρ₁ ● ρ₂)|imm`, which means `(ρ′₁ ● ρ′₂)(ℓ) =
(ρ₁ ● ρ₂)(ℓ)`."*  [CONF] p. 415:24 says the same in prose: *"its imm locations are
preserved at their original lifetimes"*.  At the literal `imm` clause `ρ′(ℓ) = ρ(ℓ)`, an
`own` location's escrow may absorb an `imm` cell of `ρ₁`, which then leaves `dom(ρ′₁)`, and
the composite carries one operand's lifetime set where `reb_α(ρ₁ ● ρ₂)` asks for the union;
6.61 then needs survival as an added hypothesis.  At the subset reading of §12.67(b), 6.61
is proved as printed: `Fig16.ResU.six61`, with the quoted overlap sentence derived
(`Fig16.ResU.reb_overlap`) and the composite cell supplied by `Fig16.ResU.six61_imm_at`.

*For 6.53 and 6.55: the escrow at an `own` location is determined by `(ρ, ℓ)`, so a frame's
`imm` cell agrees with the reborrow's in value and witness.*  [TR] p. 18, in the proof of
6.55: *"`ρ` and `ρ′` differ only by potentially changing from own or mut to imm, but
witnesses and values always stay the same."*  At the `mut` and `imm` clauses the witness is
read off the source cell; at the `own` clause it is `π(ℓ)/ℓ`, which the formula leaves to
the choice of `π`.  6.53's proof on the same page uses the same fact in the form *"the only
way for `ρ_f(ℓ)` to not be composable with `ρ(ℓ)` is for `ρ_f(ℓ)` to be own or mut"*; `▶◀`
on two `imm` cells asks in addition for equal witnesses, and that is where the p. 18
sentence enters.

**The level at which the p. 18 sentence is stated.**  The two proofs apply it at different
levels.  6.53 wants it of `ρ_f` and `ρ`.  6.55's first bullet wants it of `ag(ρ_f)` and
`ag(ρ)`: it argues from `ag(ρ_f) ▷◁ ⦇ρ′⦈_○` to `ag(ρ_f)(ℓ) ▷◁ ag(ρ)(ℓ)`, and `ag(ρ_f)` can
be defined where `ρ_f` is not (its cell arriving from inside one of `ρ_f`'s witnesses), and
can be a `mut` cell there.  `ag(ρ_f)` is the deeper of the two, so `Fig16.EscrowAgree` is
stated there, over cells that are not `own` — exactly where `Fig16.CellU.compatS_iff` and
`Fig16.CellU.compatR_iff` compare a witness at all — and 6.53's use is recovered from it
through `Fig16.AgW.get_imm`.  The other placements do not serve:

* With nothing added, at an `own` cell of `ρ′` the cell `ag(ρ)(ℓ)` is the reborrow's `imm`
  cell over the escrow while `⦇ρ′⦈_○(ℓ)` is still the `own` cell, so `ag(ρ_f) ▷◁ ⦇ρ′⦈_○`
  places no constraint on `ag(ρ_f)(ℓ)`'s witness.
* As an equation between `ρ` and `ρ′` alone, which is how it is written, it names no frame;
  read so that it applies at an `own` cell it would force `π(ℓ)/ℓ = ∅`, since `own(v)` has no
  witness (`Fig16.CellU.wit_ownOf`), and [TR] 6.121's proof (p. 32) chooses `π := ℓ ↦ ρ`,
  whose escrow is not empty.
* At `ag(ρ_f)` against `⦇ρ′⦈_○` it is a theorem, `Fig16.ResU.frame_flat_facts`, derived from
  the printed `#`, and adds nothing.
* At `ag(ρ_f)` against the reborrow `ρ` it discharges both: `Fig16.ResU.six53`, and
  `Fig16.ResU.frame_compatR_ag` (6.55's first bullet) with 6.54's closing line
  (`Fig16.ResU.ag_cell_of_reb`).  This is `Fig16.EscrowAgree`.

6.53 and 6.55 carry `Fig16.EscrowAgree` as a named hypothesis; the conclusions are as
printed.  It holds trivially off the `own` clause (`Fig16.escrowAgree_of_no_own`), and at
the typed world it is discharged at every reborrow 6.150 takes
(`Fig16.LogRel.Typed.rebChooseO_top`, `Fig16.LogRel.Typed.rebChooseO_deep_tw`, §12.71).
6.55 carries one further hypothesis: `ag(ρ)` is **defined**.  The printed phrase
`ag(ρ_f) ▷◁ ag(ρ)` presupposes it and no printed hypothesis supplies it, so it is carried as
`Fig16.AgW ρ A` (convention F1).  `ag(ρ_f)` is not carried: `Fig16.ResU.agW_of_hash_left`
produces it from the printed `#`.

**What does not supply the two facts.**

* *Validity.*  [CONF] p. 415:22: *"If `⦇ρ⦈` is defined, the resource is considered to be
  valid"*, so validity is `✓` (`Fig16.ResU.Valid`).  The configurations in which the two
  facts fail are `✓`-valid, and a strengthening of p. 415:21 strict enough to exclude them
  also excludes Fig. 17a, which the paper prints as valid.
* *The call sites.*  At [TR] p. 39 the frame is `ρ_b ● ρ_f` with `ρ_f` drawn from `wp`'s
  unrestricted `∀ρ_f # ρ` ([TR] p. 6), so the call site knows of the frame exactly the
  lemma's printed hypothesis.  At [TR] p. 33 the additions are `P(ρ′₁)` and `Q(ρ′₂)` over
  arbitrary `SProp`.
* *Restricting the escrow.*  `dom(π(ℓ)) = {ℓ}` at the `own` clause would imply both facts,
  and [TR] Lemma 6.121's proof (p. 32) chooses `π := ℓ ↦ ρ`, with a domain larger than
  `{ℓ}`.

**A question for the authors.**  Is the `own` clause's escrow intended to be determined by
the type of the cell at `ℓ` (so that two reborrows of one source agree on it), and is that
what [CONF] p. 415:24's "depends on the type of cell at `ℓ`" states, given that Fig. 16's
`Imm_α` places no refinement on a cell's witness and Lemma 6.121 needs the escrow to range
over more than `{ℓ}`?

### §12.42 [TR] §3's machine: elided congruences, and their completion

**What is printed.**  [TR] §3 prints seven `Kont` productions and eight reduction rules
(transcribed as `TR3.Head` and the `Kont` of `Paper/S3_Dynamics/Definitions.lean`).  Read as
an exact grammar, the printed machine takes no step from some terms §2 types:

- §2's `⊕I` types `injᵢ e` at any `e`, and §3's `Kont` has no `injᵢ K` frame and its box no
  `injᵢ` rule: `TR3.no_step_inj₁`, with `TR3.derives_wInj` and `TR3.stuck_wInj`.
- §2's `1E` types `e₁; e₂` at any `e₁ : 1`, and §3's `Kont` has no `K; e` frame, while `1↦`
  fires only at a literal `()`: `TR3.no_step_seq`.  [TR] p. 4's own
  `swap ≜ λx.λy. let z = load x; store x y; (x,y)` has that shape.

This reaches [CONF] Corollary 3.3: `free (alloc ()); ()` is closed, §2 types it at `1`
(`TR3.derives_wSeq`), and the literal machine takes no step from it (`TR3.stuck_wSeq`), so
`(∅, e) →* (∅, ())` is unreachable for it under the literal reading
(`TR3.corThree_unreachable`).

`store v` is not a further instance.  [TR] p. 1 prints `store v` as a `Prim`, hence a
value, and application is `e₂ e₁`, so the `Prim` `store v` and the application `(store) v`
are the same printed string and the grammar identifies them (§12.43); `(store) ℓ` is a
value and needs no rule to saturate it.  Likewise `case (inj₁ ()) {inj₁ x. x, inj₂ y. y}`
runs: its scrutinee is p. 1's value `inj₁ ()`, and `⊕↦` fires at it.

**The reading: §3 is elided.**  Read as exact, the grammar makes progress fail on terms the
type system admits, leaves §2's `⊕I` and `1E` without a reduction, and makes Corollary 3.3's
conclusion unreachable for `free (alloc ()); ()`.  Read as elided — the congruences for
`injᵢ` and `;` left to the reader, as the congruences `(K,e)` and `(v,K)` for pairs are not
— all three are restored.

**The completion.**  `BoLo.Kont` adds `injᵢ K` and `K; e` to the printed frames, and that is
the whole of it.  `BoLo.Head` is the p. 4 box, the same nine constructors as `TR3.Head`;
`BoLo.Head.seq` fires at the literal `()`, as [TR] p. 4's `1↦` prints
`(µ, (); e) ↦ (µ, e)` (definition row 3.14), and `Fig16.BoLo.wp_1` states 6.137 at `()`.
Nothing in `BoLo.Head` is beyond the printed box.

**The primitive `store v`.**  `Val.prim`'s spine is printed: [TR] p. 1 prints
`Prim ::= alloc | free | load | store | store v` ([CONF] Fig. 1 is an excerpt).  Entry
D6 records the same.

**What follows for the results.**  A rule proved against `BoLo.Steps` is a rule about the
paper's machine completed as above.  `TR3.Head` and `TR3.Steps` remain the as-printed
transcription and the evidence for this entry; what they show is which congruences §3
leaves implicit, not a different calculus.

### §12.43 `Val` is a subset of `Expr`: the subset encoding

**What is printed.**  [TR] p. 1:

    Val  ∋ v ::= () ∣ (v₁,v₂) ∣ inj₁ v ∣ inj₂ v ∣ λx.e ∣ Λ.e ∣ ℓ ∣ p
    Expr ∋ e ::= x ∣ v ∣ (e₁,e₂) ∣ inj₁ e ∣ inj₂ e ∣ e₁;e₂ ∣ let (x,y) = e₁ in e₂
                   ∣ case e {inj₁ x.e₁ ∣ inj₂ y.e₂} ∣ e₂ e₁

The production `e ::= v` makes `Val` a **subset** of `Expr`, and the grammar overlaps
itself: `(v₁,v₂)` is derivable through `v` and through `(e₁,e₂)`, `injᵢ v` through `v` and
through `injᵢ e`.  A paper grammar is read with those derivations identified — the term
`(v₁,v₂)` *is* the value, and `(e₁,e₂)` is the same syntax whose components need not be
values.  ([CONF] Fig. 1, p. 415:3, prints the same two lines without `Λ.e ∣ ℓ ∣ p`; it is an
excerpt.)

**The encoding.**  One `Expr` inductive carries the value formers, `IsVal : Expr → Prop` is
defined inductively over it, and `Val ≜ {e // IsVal e}`, with `Expr.val` the inclusion
`e ::= v` (definition row 1.17).  The expression pair and the value pair are one term, and
so are `Val.storeV v` and `.app (.prim .store) v`: [TR] p. 1's `Prim ::= … ∣ store v` and
`Expr ::= … ∣ e₂ e₁` derive the same string, so `store ℓ v` takes one step here as in the
p. 4 box.

**Why not an injective encoding.**  With `Val` and `Expr` as a mutual inductive and an
injective constructor `Expr.val`, `Expr.val (.pair v₁ v₂)` and `Expr.pair (.val v₁) (.val
v₂)` are distinct terms, and the identification the page makes has to be supplied twice:

* on the typing side, by rules typing the value forms that correspond to no printed rule;
* on the machine, by head steps turning the expression `(v₁,v₂)` into the value
  `(v₁,v₂)` (and likewise `injᵢ` and `(store) v`), which the p. 4 box does not print.

Those extra rules would add cases to the induction of [TR] 6.151 that correspond to no lemma
of [TR] §6.8.  They would also force a choice at a printed rule: [TR] p. 4's `⊗↦` writes its
redex `let (x₁,x₂) = (v₁,v₂) in e`, which the injective encoding splits into two terms.
`TR3.Head.tensor` and `BoLo.Head.letpair` take the value spelling — the one [TR] Lemma 6.138
states `wp⊗` at, since `𝒱⟦T₁ ⊗ T₂⟧` holds of a `Val` — while the printed frames `(K,e)` and
`(v,K)` reach the other.  Under the subset encoding one rule does both jobs, as on the page.

**Consequences.**  `Derives` is [TR] p. 2's rules and nothing else, and `⊗I`, `⊕I₁` and
`⊕I₂` type the value forms because those are the expression forms.  `BoLo.Head` has no
coercion steps; `Fig16.LogRel.wp_pair`, `Fig16.LogRel.wp_inj₁` and `Fig16.LogRel.wp_inj₂`
are reflexivity, the two sides of each being one term.  `Fig16.LogRel.fundamental_of_open`'s
hypotheses are each a [TR] §6.8 lemma.  A value takes no step (`BoLo.no_step_val`).
`TR3.wp_inj₁_false` is stated at a non-value argument, where it measures the absence of
an `inj₁ K` frame in the printed `Kont` (§12.42).

**`Val` is a subtype, not an `IsVal` premise at each site.**  The paper quantifies over values
as a *type*: [TR] p. 1 declares `Mem ∋ μ : Loc ⇀ Val` and p. 6 `P̂ : Val → SProp`, and
`BoLo.Heap`, `Fig16.BoLo.wp`'s postcondition and the value relation are stated at exactly
that.  An `IsVal` proof threaded through those positions would put a side condition on every
heap entry and every postcondition; the subtype puts it where the page puts it, in the
ranging metavariable.  `Val.shift` and `Val.subst` are the `Expr` operations together with
the facts that they preserve `IsVal`.

**Alternatives.**  Duplicating `⊗I`, `⊕I₁` and `⊕I₂` at the value spelling adds the same
three constructors, spelled as though they were printed rules.  Making `Expr.val`
non-injective is not available, since Lean constructors are injective.  Quotienting `Expr`
by the identification turns every recursion over `Expr` into a lift with a well-definedness
obligation, and buys nothing the subset encoding does not.

### §12.44 ∀I's `Δ, ('a ⊏ @b)` extends a partial map: `Derives.allI`'s freshness premise

**What is printed.**  [TR] p. 2, ∀I, one premise:

        Δ, ('a ⊏ @b); Γ ⊢ e : T
      ───────────────────────────
      Δ; Γ ⊢ Λ.e : ∀ 'a ⊏ @b. T

[CONF] Fig. 7 (p. 415:8) prints the same rule with the same single premise.  Neither prints
`Δ ⊨ @b`, and neither prints a freshness condition.  The well-formedness rule for the same
binder, on the same [TR] page, prints two premises — `Δ, ('a ⊏ @b) ⊢ T` and `Δ ⊨ @b` — and
no freshness.

[TR] p. 1, read at 900 dpi against a right-facing harpoon rather than an arrow:

    LifeCtx ∋ Δ : LifeVar ⇀ Life

[CONF] p. 415:8 prints the identical declaration.  Both documents declare `Δ` a **partial
map**, and [TR] p. 3 uses it as one:
`⟦Δ⟧ ≜ {δ ∣ dom(Δ) ⊆ dom(δ) ∧ ∀ 'a ∈ dom(Δ). δ('a) ⊏ Δ('a)δ}`.  The application `Δ('a)` is
meaningful only if `'a` has at most one binding.

**The reading.**  `Δ, ('a ⊏ @b)` is extension of a partial map at a point outside its
domain.  The page need not say so, because a named presentation carries the Barendregt
convention: the bound variable of `∀'a ⊏ @b. T` is chosen fresh, so `'a ∉ dom(Δ)` at every
instance of the rule.  Our `LifeCtx` is an association list and `LifeCtx.find?` is
`assocFind`, which returns the first match, so `LifeCtx.extend` shadows: at a variable `Δ`
already binds, the old entry survives in `LifeCtx.dom` while being invisible to `find?` and
to `LifeCtx.Models`.  `Derives.allI`'s premise `hx : Δ.find? x = none` is exactly the
condition under which extension and shadowing coincide.

It is also the first conjunct of the well-scopedness `LifeCtx.Ok` ("distinct binders"):
each entry's variable is not found in the tail.  So the premise imposes no condition on `Δ`
that the two documents do not impose on p. 1; it keeps the rule inside the class of
contexts they declare.

**What it costs.**  `Ty` equality is syntactic and α-equivalence is not built in, so the
premise is a genuine restriction: a conclusion `Δ; Γ ⊢ Λ.e : ∀'a ⊏ @b. T` with
`'a ∈ dom(Δ)` has no derivation here, while on the page it names the same type as its fresh
α-variant.  That loss is the loss α-identification would repair.  No printed program uses the
shadowing derivation.

**What the premise does not supply.**  It is not the freshness `Fig16.LogRel.allI_compat`
([TR] 6.161) needs.  That lemma asks three things — that `@b` does not mention `'a`, that no
bound of `Δ` mentions `'a`, and that `'a` is free in no live type of `Γ` — and [TR] takes all
three from the same convention it takes freshness from.  `Δ.find? x = none` supplies none of
them: with `Δ = ∅` and `Γ = x : Imm 'a 1`, where `'a` is the variable the rule is about to
bind, the premise holds and the third condition fails.  `Derives.allI` is not strengthened
to carry them; instead `Fig16.LogRel.fundamental_of_open` is proved for derivations in the
regime `Fig16.LogRel.DerivesIn`, whose `∀I` nodes carry the three conditions
(`Fig16.LogRel.AllISide`), and its hypothesis for 6.161 is stated with them.

**Premises beyond the printed rules.**  Three kinds of constructor of `Derives` carry a side
condition its printed rule does not: `allI`'s `hx` (this entry); `withbor1Ax`, `withbor2Ax`,
`withbor3Ax` and `withloadAx`'s `hx` (§12.45); and `withbor2Ax`'s `hside` (§12.9).  Each
restores something the documents state elsewhere rather than adding something new.
Without `hx`, `allI`'s premise would be a judgment about a `Δ` that is not the partial map
both documents declare, and the rule would silently rebind.

### §12.45 The axiom table's `∀` binder is schematic

**What is printed.**  [TR] p. 3, the axiom table:

    Δ ⊢ withbor  : Ref T₁ ⊸ (∀ 'a ⊏ ⊓Δ. Imm 'a T₁ ⊸ ['a] T₂) ⊸ Ref T₁ ⊗ T₂
                   Ref T₁ ⊸ (∀ 'a ⊏ ⊓Δ. Mut 'a T₁ ⊸ ['a] T₂) ⊸ Ref T₁ ⊗ T₂    Δ ⊢ T₁ ⊐ @b
                   Mut @a T₁ ⊸ (∀ 'b ⊏ ⊓Δ. Mut 'b T₁ ⊸ ['b] T₂) ⊸ Mut @a T₁ ⊗ T₂
    Δ ⊢ withload : Imm @a T₁ ⊸ (∀ 'b ⊏ ⊓Δ. Imm̲ 'b T₁ ⊸ ['b] T₂) ⊸ T₂

(`withload`'s inner `Imm̲` is the metafunction, told from the constructor by an underline —
§12.28.)  `'a` and `'b` are bound variables of the type.  The page identifies types up to α,
so these four lines name four types, not four families indexed by a choice of name.

**Two dependencies on `Δ`.**  The bound `⊓Δ` is a function of `Δ` on the page: §12.15 settles
that `⊓Δ` ranges over `dom(Δ)`, realised as `LifeCtx.meetOfDom` (the right fold
`meetOfDomL` of the grammar's binary meets).  The binder is not: nothing on the page makes
it a particular variable computed from `Δ`.  `LifeCtx.freshVar` (`freshOfL`, one past the
largest variable in `dom(Δ)`) is an allocator, not a canonical name for the binder of a
closed type, and §12.15 does not bear on the name of the variable the bound constrains.

**The reading.**  `Derives.withbor1Ax` takes the binder as a parameter with the freshness
premise §12.44 argues — `(x : LifeVar) (hx : Δ.find? x = none)` — and concludes at
`axWithbor1Ty x Δ.meetOfDom T₁ T₂`, as `Derives.allI` does with the same premise for the
same reason; `Derives.withbor2Ax`, `Derives.withbor3Ax` and `Derives.withloadAx` do the
same.  `Δ.freshVar` is one such `x`.

**Why the binder must be schematic.**  `Ty` equality is syntactic, so a constructor
concluding at one fixed binder would make exactly one α-variant of each printed type
derivable, and the type reaches clients by routes that do not preserve that binder:

* `Derives.var` returns the `Ty` stored in `Γ` verbatim (`Ctx.Solo`), and nothing fixes a
  stored `withbor` type's binder;
* `Derives.allE` instantiates through `Ty.instLife = Ty.applyLSub [(x,@a)]`, whose `.all`
  case renames the binder whenever the substitution would capture (`lsubCaptures`), so a
  `withbor` type carried inside a larger type through `∀E` comes back with a binder of its
  own.

Quotienting `Ty` by α would make a pinned type every α-variant; the schematic constructor
achieves the printed rule without it.

**The semantic side.**  `Fig16.LogRel.fundamental_of_open`'s hypotheses `open_withbor1`,
`open_withbor2`, `open_withbor3` and `open_withload` are stated at the schematic `x`, with
the binder's freshness for `T₁` and `T₂` read off the `Fig16.LogRel.DerivesIn` regime at the
node; `Fig16.LogRel.withbor1_compat` is 6.172 in that form.  In `withbor`'s and `withswap`'s
types the borrow's index mentions the fresh lifetime and its payload does not.

### §12.47 Four facts at [TR] 6.59's open location

These record what does and does not constrain a location of Lemma 6.59 where a reborrow put
`imm({β}, w, v)` and something else carries `mut(b, v, w, P)`.

**(a) `Res_b ⊆ Res_β`, and the `mut`'s typing is the stronger.**  The `mut` types its
payload at `Res_b`, the `imm` types the same payload at `Res_{⊔{β}} = Res_β`.  `β ⊑ b`, so
`Res_b ⊆ Res_β` (`Fig16.ResU.InStratum.mono`) and the two constraints are compatible for
every `b` strictly outliving `β`.  Strictness in `⊐` does not separate them.

**(b) `#` does not exclude a second `mut` over the same payload.**  `#` is `▸◂` together with
`✓(−●−)`.  `▸◂` constrains only the two resources' own cells, and `ρᵢ` has one; `✓` asks the
composite's flattening to exist, which at that location is `○`'s clause (3), `mutMut`, and
clause (3) asks for the same value and the same witness the configuration already supplies.
What validity does give is that the exclusive and aliasable walks have disjoint domains
(`Fig16.LogRel.Typed.ex_ag_disjoint`), which silences `ex(ρ_b)●` at every location `ag(ρᵢ)`
reaches.

**(c) `@ρ ⊐ β` reaches the deep cell, consistently.**  Fig. 16 types each cell's witness at
that cell's own stratum, so `Res_β` is hereditary (`Fig16.CellU.wit_inStratum_at`,
`Fig16.BoLo.cell_wit_inStratum`).  At an `imm` cell the chain is `β ⊏ ⊓ᾱ ⊑ ⊔ᾱ ⊏ b` and the
steps compose, by `Fig16.LSet.meet_le_join`.  So a `mut` inside an `imm` cell's witness
strictly outlives `β`, which is what the configuration has.

**(d) `γ` need not be the shorter lifetime, so `a ⊓ γ = b ⊓ γ` does not collapse.**  Stated
at the composites — `A ○ S ∼ B ○ S` with `S = ⦇ρ′ᵢ⦈_○(ℓ)` shared — the `mut`/`mut` case asks
`a ⊓ γ = b ⊓ γ`, not `a = b`.  `Life` is `ℕᵒᵈ` and `⊓` is the shorter, i.e. the larger
natural; `@A ⊐ β` gives `a < β` as naturals, and `ρ′ᵢ ∈ Res_β`, which `reb_β`'s first
conjunct supplies, gives `γ < β` — both longer than `β`, and nothing orders them against
each other.  Fig. 16's typing of `ρᵢ` adds `γ ⊐ ⊔ᾱ`, which orders `γ` against the borrow's
set and not against `a`.

**What does constrain the location.**  The aliasable walk introduces a `mut` cell only
through `ex(−)_○` inside its `imm` family — `ag(ρ) = (ρ|imm ○ ⨀ ag(ρᵥ)) ○ ⨀ (ex(ρ′)_○ ○
ag(ρ′))`, and the first two groups carry no `mut` of their own.  So every `mut` cell of
`ag(ρ)` sits beneath an `imm` cell, and that `imm` cell is carried to the top by the same
chain of `ag`s.  `↭`'s first clause pins an `imm` cell of a flattening together with its
witness; its second clause pins a `mut` cell's lifetime and invariant and leaves the value
and the witness free.  So the route to a `mut` cell runs through the clause that pins
witnesses (§12.53).

### §12.49 Definition 6.2 (`∼`) and the unfolding of `↭` in [TR] §6

[TR] p. 13 prints `∼` as Definition 6.2, and the proofs of Lemmas 6.39, 6.40, 6.44 and 6.59
unfold `↭` through it, always as *"dom(⦇ρ₁⦈∣imm,mut) = dom(⦇ρ₂⦈∣imm,mut) and for every ℓ in
that domain, ⦇ρ₁⦈(ℓ) ∼ ⦇ρ₂⦈(ℓ)"*.  Those proofs follow that decomposition step by step, so
it is transcribed as its own object: `Fig16.CellU.Sim`, definition row 5.65.

[TR] numbers its Definitions in a second sequence, so Definitions 6.1, 6.2 and 6.3 share
their numbers with Lemmas 6.1, 6.2 and 6.3.  Definition 6.1 is definition row 5.61;
Definition 6.2 is row 5.65 (`Fig16.CellU.Sim`); Definition 6.3 is row 5.66
(`Fig16.ResU.Sub`).

`Fig16.ResU.upd_iff_sim` proves that [CONF] Fig. 18b's two clauses — the form
`Fig16.ResU.Upd` takes — and [TR] §6's `dom + ∼` form are the same relation, so the
statements that use `↭` are unchanged and the proofs can follow the printed decomposition.

### §12.50 Deep immutability is the two-operator design

[CONF] p. 415:24, in Related Work: *"our model enforces deep immutability of the data an
immutable borrow points to"*.  In Fig. 17a, `⦇ρ⦈(ℓ₃)` is `imm` although `ℓ₃` is incident from
a `mut` cell.  Together these might suggest that a `mut` cell inside an `imm` cell's witness
cannot reach a flattening as a `mut`.  It can; this entry records why.

**Why Fig. 17a's `ℓ₃` is `imm`.**  In Fig. 17a `ℓ₃` carries two cells: `ρ₂`'s
`mut(α₃, v₃, ρ₃, P̂₃)`, raised through the `imm` family of `ag(ρ)` by `ex(ρ₂)_○`, and `ρ₁`'s
`imm(ᾱ₃′, v₃, ρ₃)`, raised through the `mut` family by `ag(ρ₁)`.  `○`'s clause (5) then
returns the `imm` cell, which is why its lifetime set is `ᾱ₃′` alone and not `⊓` with `α₃`.
The conversion is clause (5) firing against an `imm` view of `ℓ₃` that the resource happens
to contain; it is not structural.  A resource of the same shape with no second view — an
`imm` cell whose witness holds `mut(α₁, v₁, ρ_own, P̂₁)` at `ℓ₁` — is valid, and `ℓ₁` stays a
`mut` in the flattening.  That pair is [CONF] §4.3's own example: *"even though `ℓ₃` is
incident from a mut cell, which would normally be exclusive, it has an imm ancestor, which
makes its whole subtree shared and `ℓ₃` aliasable"* — the cell stays, and becomes composable
at `○` (§12.52).

**The two documents agree here.**  [TR] p. 5 prints `ag(ρ)`'s third group as
`⨀_○{ex(ρ′)_○ ○ ag(ρ′) | ρ(ℓ) = imm(_,_,ρ′)}` and [CONF] Fig. 18a prints
`(⨀_○ ρ′∈cod(ρ|imm) E⦇ρ′⦈_○ ○ A⦇ρ′⦈)`, both read at 1200 dpi.  Both raise the witness's
cells at their own tags.  The one difference between the documents in these rows is in the
exclusive walk and is recorded on `Fig16.ExW`: [CONF] fixes the recursive subscript at `●`
where [TR] writes the generic `◐`.

**Where deep immutability lives.**  Not in `Imm_α`'s side condition, which constrains only
`ρ : Res_{⊔ᾱ}`; not in a well-formedness predicate on resources, of which this development
has none; and not in `✓`, which admits the resource above.  It is the two-operator design:
the exclusive walk composes at `●`, where `▶◀` permits only two `imm` cells, while
everything under an `imm` is reached through `○`, whose clause (3) composes two `mut` cells
over **the same value and the same witness**.  So two borrows may both reach one location
with a `mut` provided both are under `imm` ancestors and agree on value and witness, which
is the purpose of the relaxed operator.

### §12.52 [CONF] §4.3's aliasing invariant is composition, and multiple paths are the licensed case

[CONF] p. 415:21 characterises `✓` in words (definition row 5.67):

> "Conceptually, in a valid resource, every pair of aliases map to the same object and each
> has an immutable ancestor."

> "It also portrays aliasing of exclusive locations, like `ℓ₁`, that do map to the same cell
> but, unlike the previous example, are not guarded by immutable cells, which violates the
> mutability-xor-aliasing restriction."

> "The advantage of reusing composition is that it already rules out all of the
> inconsistent aliasing cases mentioned above."

and names the mechanism:

> "flattening the resource in Fig. 17b is not defined — the conflict at `ℓ₁` causes `•` and
> therefore `E•` to be undefined, while the conflict at `ℓ₂` causes `◦` and therefore `A` to
> be undefined."

**The invariant is not a separate object.**  The paper says the enforcement *is* `▶◀` and
`▷◁` propagated through the walks, and each clause of the characterisation is a theorem of
the mechanisation:

* *every pair of aliases map to the same object* — `Fig16.CellU.compatR_iff`, an **iff**:
  `▷◁ ψ₁ ψ₂ ↔ (ψ₁.erase = ψ₂.erase ∧ (neither own → ψ₁.wit = ψ₂.wit))`.  At `●` it is
  `Fig16.CellU.CompatS.imm_imm`;
* *each has an immutable ancestor* — `Fig16.AgW.nonimm_beneath_imm`, with `Fig16.ExW.immFree`
  (6.36) for the exclusive walk;
* *no cell can be both exclusive and aliasable* — `Fig16.ResU.CompatS.disjoint_of_immFree`
  and `Fig16.ResU.flat_eq_ag_at`.

`Fig16.ResU.CompatS.disjoint_of_immFree` (the two walks never both reach a location) is an
instance of the `ℓ₁` sentence alone: it reduces to *"`•` is never defined on two exclusive
cells."*

**What the invariant does not say: path uniqueness.**  It does not say that in a valid
resource only one path reaches a location, so that an aggregate never needs decomposing.  The
paper's own **valid** example, Fig. 17a, has `ℓ₃` as one exclusive location reached by two
paths — `ρ₂`'s `mut(α₃, v₃, ρ₃, P̂₃)` raised through `ag`'s `imm` family by `ex(ρ₂)_○`, and
`ρ₁`'s `imm(ᾱ₃′, v₃, ρ₃)` raised through the `mut` family by `ag(ρ₁)` — and in its
flattening `ℓ₃` is `imm`: the `mut` under an `imm` ancestor has become aliasable.  [CONF]
p. 415:21 says so: *"even though `ℓ₃` is incident from a mut cell, which would normally be
exclusive, it has an imm ancestor, which makes its whole subtree shared and `ℓ₃`
aliasable."*  §12.50 records the same observation from the other side.

**The reading.**  Multiple paths to one location are the **licensed** case; what the
invariant excludes is paths that *disagree*, and disagreement is decided cell by cell by `▶◀`
and `▷◁`.  So the invariant constrains the **value and the witness** and says nothing about a
`mut` cell's lifetime or invariant — which are exactly the two components `↭`'s second clause
asks about.  Those come from §12.53's ancestor step.

### §12.53 [TR] 6.48's ancestor step

`Fig16.BoLo.updV_frame` is [TR] Lemma 6.48, `[as printed]`, and its proof follows p. 16 step
for step.  The step that matters here is the `mut ○ mut` case, [TR] p. 16:

> "By the update hypothesis, we have `ag(ρ₃)(ℓ) = mut(β, _, _, Q̂)`.  And furthermore, by the
> definition of `ag`, there must exist `ℓ′, ρ′` such that `ag(ρ₂)(ℓ′) = imm(_, _, ρ′)` and
> `ag(ρ₂)(ℓ) = ⦇ρ′⦈_○(ℓ)`.  By the update hypothesis, we also have
> `ag(ρ₃)(ℓ′) = ag(ρ₂)(ℓ′)`, which implies `ag(ρ₃)(ℓ) = mut(β, v, ρᵢ, Q̂)`."

This is the one place either document reasons about `↭` **without splitting by location**: a
`mut` in the aliasable walk is accounted for by the `imm` cell it sits beneath, `↭`'s clause
(1) pins that `imm` cell **together with its witness**, and the raised subtree therefore
comes across whole.  Clause (2) supplies the lifetime and the invariant; the ancestor step
supplies the value and the witness, which clause (2) wildcards.  The printed conclusion is
cell **equality**.

**The step, mechanised.**  `Fig16.ResU.upd_ag_imm_wit_factor`,
`Fig16.ResU.upd_ag_nonimm_transfer` and `Fig16.ResU.upd_ag_mut_eq` are that step, the last of
them at p. 16's own conclusion — `ag(ρ₃)(ℓ) = mut(β, v, ρᵢ, Q̂)`, cell equality, not `∼`.
The witness needs the trace run on **both** sides: a `○` composite takes its witness from an
operand that is not `own`, so the trace pins it unless the raised cell is itself an `own`, and
then `own`'s witness is `∅` and the other side's trace pins it instead.  `↭` is symmetric,
which is what lets the same step run both ways.  `Fig16.ResU.upd_ag_eq_of_ne_own` packages the
cases (clause (1) at an `imm` cell, `upd_ag_mut_eq` at a `mut` one,
`Fig16.ResU.upd_ag_own_or_none` at an `own` one).

**6.48's proof.**  `updV_frame` cuts both flattenings by 6.18 and 6.20
(`Fig16.ResU.Flat.split`); 6.36 (`Fig16.ExS.immFree`) with
`Fig16.ResU.CompatS.disjoint_of_immFree` makes the three domains disjoint, which gives the
print's three cases at a location; and the aliasable case goes through
`Fig16.ResU.upd_ag_eq_of_ne_own`.  A pointwise argument through `Fig16.BoLo.flat_compR` also
reaches 6.48's conclusion — composing one cell onto two `↭`-related cells keeps them
`↭`-related, because the other side's composite is given defined and `ρ₁ # ρ₃` forces
`mut ○ mut`'s common value and witness — but it builds none of p. 16's technique, and it is
not the proof of 6.48 here.

**Why the step and not only the lemma.**  [TR] 6.59's closing sentence needs exactly the step
6.48's proof builds (§12.55, §12.58).  A proof of 6.48 that discharges the statement pointwise
leaves nothing on the non-pointwise side of `↭` for 6.59 to use.  So a proof is recorded as
`[as printed]` only when each printed *step* has a counterpart, not merely the conclusion.

### §12.55 Stating a residual through the proved unfolding of `↭`

[TR] p. 20 unfolds `↭` to a domain equality **and** `∼` *for every
`ℓ ∈ dom(⦇−⦈∣imm,mut)`*.  `Fig16.ResU.SimForm` transcribes that unfolding and
`Fig16.ResU.upd_iff_sim` proves it **is** `↭`.  Any residual goal on the way to [TR] 6.59's
last step is stated through that unfolding — here `Fig16.ResU.SimForm`, via
`Fig16.ResU.SimFormAt` and `Fig16.ResU.simForm_iff_at` — and not re-derived beside it.

**Why the guard matters.**  `Fig16.CellU.Sim` has two disjuncts, `mut`/`mut` and `imm`/`imm`,
so `Sim` does not hold at an `own` cell; its docstring says *"an `own` cell is related to
nothing, which is why the printed uses restrict to `dom(−∣imm,mut)`."*  A pointwise
statement of the form

```
SimAtLoc   …  σL.get l = some ψ → σR.get l = some φ → CellU.Sim ψ φ
```

drops the guard `SimForm` carries (`σ₁.borrowPart.get l = some ψ₁ → …`), and so asks for
`∼` at every location a flattening carries an `own`.  At a reborrowed `ℓ` that is the
**ordinary** case — `ρ′ᵢ(ℓ)` being `own` with nothing else contributing — and the
obligation it creates there is not one the paper incurs.  Likewise a statement quantifying
over an arbitrary frame rather than a `reb_β` image, or dropping the two printed `#`s, or
treating `v`, `χ` and `⦇ρ′ᵢ⦈_○(ℓ)` as independent when they are three parts of one source
cell, is stronger than the real obligation.

**What the guarded statement leaves.**  The `mut`/`mut` corner, and the **domain** clause:
where `⦇LHS⦈(ℓ)` is `own`, `∼` asks nothing, but the domain clause asks that `⦇RHS⦈(ℓ)` be
`own` or absent.  Only clause (1) of `○` returns an `own`, so an `own` composite forces both
operands `own`, in particular `⦇ρ′ᵢ⦈_○(ℓ)`; what remains there is the same
`mut`-against-`own` discrimination the other corner needs.  Both are discharged at the
statements `Fig16.ResU.SixFiftyNineResidualKeep` and `Fig16.ResU.SixFiftyNineOffRebKeep`
(§12.58).

**The convention.**  A named goal **stronger** than the real obligation makes an achievable
thing look impossible, and the impossibility look like mathematics.  A residual is therefore
always stated through the unfolding already proved equivalent to the printed relation.

### §12.57 `reb_α`'s escrowed witness and the resources the calculus produces

**The configuration.**  `DefectB.rebA β v u` is `0 ↦ imm({β}, v, 1↦own(u))`: a shared
reborrow of location 0 whose witness claims location 1.  `DefectB.reb_rho2_rebA` shows it is a
reborrow, by `reb_β`'s `own` clause with witness `π(0)/0 = 1↦own(u)`, of
`0↦own(v) ⊎ 1↦own(u)`.  At `v = ()` the escrow corresponds to no program: compare, in Rust,

```rust
// Location 0 holds a POINTER to location 1: the escrow is legitimate.
let x = Box::new(String::from("hi"));   // 0 -> 1
let r = &x;
let _z = *x;        // error[E0505]: cannot move out of `*x` because it is borrowed
```
```rust
// Location 0 holds (), which points at nothing.
let x = ();                      // location 0
let y = String::from("hi");      // location 1, unrelated
let r = &x;
let z = y;          // compiles and runs: y is NOT in &x's footprint
```

`π(0) = {0,1}` is exactly right in the first and corresponds to no program in the second.

**What excludes it.**  `ptoImm ℓ α P̂` carries `P̂(v)(ρ′)`, so `rebA` is in
`𝒱⟦Imm @a T⟧`'s image only if `𝒱⟦T⟧δ(())` holds of the witness `1↦own(u)`; every clause of
`𝒱` that pins the value's shape or forces `∅` refuses that.  The criterion that separates
`rebA` from the resources the calculus produces is the semantic-type one (§12.59); against
`reb_α` as printed, `rebA` is a legal reborrow.  The general point: a candidate counterexample
to a printed lemma is measured against the resources the calculus produces, not against the
carrier.

**Two conditions the proofs use, and where they are printed.**

*`imm` locations survive a reborrow.*  [CONF] p. 415:24: *"`ρ′` must be just like a
subresource of the original resource `ρ` … its imm locations are preserved at their original
lifetimes"*.  In Rust:

```rust
let mut y = 5;
let r = &y;              // location 1: imm borrow of y
let b = Box::new(r);     // location 0: owns that borrow
let s = &b;              // reborrow of location 0
y = 6;   // error[E0506]: cannot assign to `y` because it is borrowed
```

If the escrow could swallow location 1 and drop it from the top level, that assignment would be
accepted and a live shared borrow would vanish.  With [TR] 6.57's printed `≤`, this sentence
grounds the subset reading of `reb_α`'s `imm` clause adopted at §12.67(b) (definition row
5.28); at that reading [TR] 6.61, 6.125 and 6.127 need no added hypothesis.

*Two reborrows agree on the escrowed witness.*  `Fig16.EscrowAgree` carries [TR] p. 18's
sentence inside 6.55's proof — *"`ρ` and `ρ′` differ only by potentially changing from own or
mut to imm, but witnesses and values always stay the same"* (§12.60).  It is a named
hypothesis on `Fig16.ResU.six53` and `Fig16.ResU.six55`, which are scored `proved*`.
`Fig16.BoLo.defectB_not_rebEscrow` shows the configuration above is exactly what it excludes.

### §12.58 Definition 6.3's third bullet and the paragraph below it

[TR] physical p. 17, immediately under Definition 6.3's four bullets (600 dpi):

> Intuitively, `ρ ⊟ ρ′` is `ρ` without the immutable borrows in `ρ′`.  But since immutable
> borrows can alias at the same location, "without" means removing the lifetimes of borrows
> from `ρ′`, **but keeping the lifetimes only in `ρ`**.

The third bullet's own glyphs ask only `ℓ ∈ dom(ρ″)` at a location outside `dom(ρ′)`; read
alone, they admit more than one `ρ″`.  The paragraph settles which: at such a location every
lifetime of `ρ(ℓ)` is one "only in `ρ`", all of them are kept, and so `ρ″(ℓ) = ρ(ℓ)`.  The
paragraph states the constraint directly rather than as a uniqueness or maximality clause.

**The mechanisation.**  `Fig16.ResU.SubKeep` is Definition 6.3 with the third bullet read
through that sentence, quoted in its docstring; `Fig16.ResU.Sub` is the bullets alone, kept
beside it for comparison, and `Fig16.ResU.SubKeep.toSub` is the implication.  On `SubKeep`:

* `Fig16.ResU.SubKeep.functional` — `⊟` is single-valued wherever `ρ` and `ρ′` carry `imm`
  cells over one value and one witness at each shared location, which is the hypothesis
  `Fig16.ResU.sub_of_le` already asks and [TR] 6.52's H1 (`Fig16.ResU.six52_H1`) establishes.
  So `ρ ⊟ ρ′` is a term, as the paper writes it.
* `Fig16.ResU.SubKeep.compS` — [TR] 6.52's `ρ = (ρ ⊟ ρ′) ● ρ′` holds of **every** admissible
  `χ`, not only of the one `Fig16.ResU.sub_of_le` builds.
* `Fig16.ResU.sub_of_le` produces `SubKeep`, so the reading is inhabited wherever the
  bullets-alone reading is.

**[TR] 6.59.**  `Fig16.ResU.SixFiftyNineResidualKeep` and
`Fig16.ResU.SixFiftyNineOffRebKeep` are the two residual statements of 6.59's last step with
their `χ` bound by `SubKeep`; both are proved, and `Fig16.ResU.six59` composes them into
[TR] Lemma 6.59.  §12.64 records why this reading is the definition.

### §12.59 "The type of cell" in [CONF] p. 415:24 is `own` / `imm` / `mut`

[CONF] p. 415:24 reads: *"The conditions placed on each partition `ℓ` in `π` depends on the
**type of cell** at `ℓ` in the original resource `ρ`."*  The same paragraph says what it means
three sentences later: *"If the cell was **owned** in `ρ` (Case 1) … If the cell was
**immutable** in `ρ` (Case 2) … if the cell was **mutable** in `ρ` (Case 3)."*  "Type of
cell" is the cell kind, `own` / `imm` / `mut`, and Fig. 19's three implications case on
exactly those three.  It does not make `reb_α`'s partition directed by the payload's semantic
type, and Fig. 19's formula carries everything the sentence asks.

**The three implications are not vacuous.**  Nothing in them alone forces `ℓ ∈ dom(ρ)`, but
the definition does: `Fig16.ResU.RebAt`'s first conjunct is `ℓ ∈ dom(π(ℓ))`,
`ρ ≥ ⨀_{ℓ∈dom(π)} π(ℓ)` is printed inside `reb_α`, and `Fig16.ResU.reb_dom_subset` derives
`dom(ρ′) ⊆ dom(ρ)` from the two.  The global condition printed inside the definition
discharges what looks like per-location prose.

**Consequence for §12.57.**  The two Rust programs there, and the observation that
`DefectB.rebA`'s escrowed witness lies in no semantic type's image, stand.  The reason `rebA`
is not a reborrow of a resource the calculus produces is the semantic-type criterion, not a
condition of `reb_α`: against `reb_α` as printed, `rebA` is a legal reborrow.

### §12.60 Two kinds of unstated condition: supplied by prose, and used by a proof

A row is scored as departing from the formula when the formula does not carry something the
development needs.  That covers two different phenomena with different remedies.

**(a) The prose supplies what the formula leaves open.**  A sentence beside the definition
states a property; the formula is its per-location unfolding and does not carry it.  Remedy:
transcribe the sentence as part of the definition (§12.64), with the sentence quoted — the
`Fig16.ResU.SubKeep` pattern (§12.58).  Instance: Definition 6.3's third bullet.

**(b) A proof uses what no sentence states.**  No sentence asserts the property; a proof step
proceeds as though it held.  Remedy: a named hypothesis with the *proof step* quoted, the
printed conclusion unchanged, and the row scored `proved*`.

**The three candidate instances, examined against both documents page by page:**

| instance | finding |
|---|---|
| `Fig16.EscrowAgree` | **(b).**  Its sentence is [TR] p. 18, *inside* 6.55's own proof — "`ρ` and `ρ′` differ only by potentially changing from own or mut to imm, but witnesses and values always stay the same".  [TR] p. 8's 6.14 sentence is a different proposition (about `○` on two cells) and is carried whole by `Fig16.CellU.compatR_iff`. |
| survival of `imm` locations under `reb_α` | [CONF] Fig. 19 prints `reb_α`'s body quantifier as `∀ℓ, v, ρ_ℓ` where [TR] p. 5 prints `∀ℓ ∈ dom(π)`.  The unguarded form is not a printed statement of survival: [CONF] p. 415:24's own specification paragraph says "The conditions placed on each partition `ℓ` **in `π`**", [TR] 6.52 unfolds `reb` with "if `ℓ ∈ dom(ρ)`" as an explicit antecedent, 6.54's bullet 2 restricts the `imm` equation on **both** sides, and 6.123/6.124/6.127's proofs each reduce the `∀` by its guard.  Reading clause (2) alone as total would also break `Fig16.BoLo.reb_emp_iff`, hence 6.124 and 6.130.  The condition is instead carried by the subset reading of the `imm` clause, grounded in [CONF] p. 415:24's "its imm locations are preserved" and [TR] 6.57's `≤` (§12.67(b)). |
| a licence on the recorded borrows in 6.60's `Imm` case | **Printed, as an assertion.**  [CONF] Fig. 13b's `⟲I` (p. 415:15) is `ℓ ↦I_β P̂ ⊨ ⟲_α ℓ ↦I_β P̂` under `β ⊐ α` alone — no `[α]` on the left, where [TR] 6.123 has one — and at `α := ↓β` with 6.63 that is `@ρ ⊒ β`, which is 6.60's `Imm` bullet.  It is a second printed assertion of the step, not a derivation of it: 6.123 (`Fig16.BoLo.reborrow_ptoImm`) spends its `box α` at exactly one place, supplying `↺`'s own `@ρ ⊐ α`, so transcribing `⟲I` reproduces the same obligation.  With the connective read at `⊓β̄` (§12.67(a)) the case needs no licence. |

**Before scoring anything (b):**

1. Search both documents page by page, prose and figures, for a printed statement — rendering
   the page where a glyph matters.  Two of the three instances above turn on differences of a
   few characters inside a figure.
2. Check whether the two documents print the object differently, and whether the prose that
   specifies the figure settles it.  [CONF] p. 415:24 settles Fig. 19's quantifier; §12.64 is
   the convention that the two together are the definition.
3. Check whether an object in the run-up is the mechanisation's own, and measure before
   attributing a condition to it.  `Fig16.CellU.wit`'s `∅` at an `own` cell does not occur in
   `Fig16.CellU.CompatR`'s definition at all; `▷◁`'s `own` guard is forced by [TR] p. 5's clause
   (5), since `own(Val)` has one field.
4. Only when 1–3 come back empty, score (b), and record where the search looked.

A hypothesis added to a statement quotes the sentence it comes from; (b) quotes a proof step
instead.  So a (b) is always an invitation to look again, and never a finding about the paper.

### §12.61 [TR] 6.150 is printed twice, and the two printings agree

[TR] Theorem 6.150 (physical p. 39) is

> `ℓ ↦ Imm α (Иβ. ↺_β P̂) ⋆ (Иβ. ∀v. P̂(v) ─⋆ wp(e){[β]Q̂}) ⊧ wp(e){Q̂}`

and [CONF] Fig. 13b (p. 415:15, *"Immutable loading and reborrowing rules"*) prints the
same entailment under the name **`I Reborrow`**, read at 900 dpi:

> `ℓ ↦ I_α (Иβ. ⟲_β P̂) ⋆ (Иβ. ∀v. P̂(v) ─⋆ wp(e){[β]Q̂}) ⊨ wp(e){Q̂}`

Glyph for glyph the same rule: `I` for `Imm` and `⟲` for `↺` are the two documents' two
spellings of one constructor and one modality, as they are everywhere else.  So 6.150 is not
an item on which the documents differ, and `Fig16.BoLo.wp_reborrow` transcribes a statement
both documents print.

**Where the two look different: a figure, not a rule.**  [CONF] Fig. 14 (p. 415:16) derives
`withload` in three steps, and its middle step is labelled `(I Reborrow)`.  The goal below
that step reads

> `ℓ ↦ I_α ( _. Иβ. ⟲_β P̂(v) ) ⋆ Иβ. ∀v. P̂(v) ─⋆ wp(v_f () v){Q̂} ⊨ wp(v_f () v){Q̂}`

— with `{Q̂}` inside the wand where Fig. 13b's rule has `{[β]Q̂}`, and with an explicit `_.`
binder in the borrowed family where Fig. 13b has none.  The `_.` is accounted for on the page:
the step below it is `wp Load I`, whose own statement (Fig. 13b) produces `ℓ ↦ I_α (_. P̂(v))`
— *"we can specialize its borrowed predicate to `v` by turning it into a constant function"*,
p. 415:16 — so the family in the cell is constant there, which is `Fig16.BoLo.wp_reborrow` at
a `P` constant in its value argument.  The `{Q̂}` without `[β]` is **not** highlighted, and
Fig. 14's caption reads *"Changes between proof states are highlighted"*; the line below it,
Fig. 14's conclusion, carries `{[β]Q̂}`, and so does Fig. 13b's rule.  We therefore read the
unhighlighted `{Q̂}` as typesetting rather than as a change; read as a change it would state
something stronger than the rule Fig. 13b prints and [TR] 6.150 proves.
`Fig16.BoLo.wp_reborrow` is the Fig. 13b / 6.150 statement.  Fig. 14's derivation is [CONF]'s
sketch of 6.175 (`withload`), a separate row.

**`P̂` stands under the `Иβ`, and [TR] 6.175 is what says so.**  6.150's own proof reads `P̂`
at one `β` (H12, H14, p. 39), which would be consistent with `P̂ : Val → SProp` independent of
`β`.  But [TR] 6.175's proof (p. 48) applies 6.150 at

> `P̂ ≔ (v′. ⌜v′ = v_ℓ⌝ ⋆ 𝒱⟦Imm̲ 'b T₁⟧_{δ['b↦β]}(v′))`

and the display *after* the step writes that `β` under the `Иβ` the same display puts in
front of it:

> `𝒱⟦∀'b ⊏ ⊓Δ. Imm̲ 'b T₁ ⊸['b]T₂⟧δ(v_f) ⊨ Иβ. ∀v′. v′ = v_ℓ ⋆ 𝒱⟦Imm̲ 'b T₁⟧_{δ['b↦β]}(v′) ─⋆ wp(v_f () v′){[β]𝒱⟦T₂⟧δ}`

`𝒱⟦Imm̲ 'b T₁⟧_{δ['b↦β]}` reads `β` at every `Ref`, `Mut` and `Imm` leaf of `T₁`, so no
`β`-free `P̂` names it.  The print writes `P̂` inside the binder's scope, which in this
notation is a family the binder scopes.

**The mechanisation.**  `Fig16.BoLo.wp_reborrow` takes `P : Life → Val → SProp`, and
`Fig16.BoLo.RebEscrow` is indexed to match, the index being the reborrow's own `β`.  H11
picks one `β` below both `И` bounds and every later step reads `P̂` at that one `β`.  The
`β`-independent statement is the instance at a `P̂` constant in its first argument, which is
what Fig. 14's `(I Reborrow)` step applies and what `Fig16.BoLo.wp_reborrow_emp_applies`
exercises.  `DefectB.wp_reborrow_unreconciled_at_split_view` is written at the same indexed
shape, so the two results line up argument for argument and
`Fig16.BoLo.defectB_not_rebEscrow` is the whole of what separates them.

### §12.62 [TR] 6.130's `P` is one of the printed `SProp_α`, and `↺_α emp` is `Res_α`

Transcribing 6.130 at an arbitrary `P : SProp` leaves exactly one obligation that its
two-line proof does not reach, and the reading that closes it is a printed object.

**What the page says.**  [TR] p. 34, at 600 dpi:

> **Lemma 6.130.**  `P ⊧ ↺_α emp`
>
> *Proof.*  Suppose `ρ ∈ P`.  Then `∅` vacuously satisfies the conditions needed to be a
> reborrowed version of `ρ`, so `ρ ∈ ↺_α emp`.

**What the conclusion unfolds to.**  `emp ≜ ⌜⊤⌝` and `⌜P_Meta⌝(ρ) ≜ ρ = ∅ ∧ P_Meta`
([TR] p. 6), so `emp` holds of `∅` and of nothing else, and `↺_α emp` holds of `ρ` exactly
when `∅ ∈ reb_α(ρ)`.  [TR] p. 5's row is

```
reb_α(ρ) ≜ {ρ′ | @ρ ⊐ α ∧ ∃π : dom(ρ′) → Res. ρ ≥ ⨀_{ℓ∈dom(π)} π(ℓ) ∧ ∀ℓ ∈ dom(π), v, ρ″. …}
```

At `ρ′ = ∅` take `π = ∅`.  Then `dom(π) = ∅ = dom(∅)`, the iterated composition over the
empty family is `∅` and `ρ ≥ ∅`, and the body's `∀ℓ ∈ dom(π)` has nothing to range over.
Those are three of the four conjuncts, and they are vacuous exactly as the proof says —
`Fig16.BoLo.reb_emp_iff` checks each.  The fourth is the leading `@ρ ⊐ α`, which the row
writes of **`ρ`** and not of the `∅` supplied for `ρ′`; §C.25 settles what it says, which is
`ρ ∈ Res_α`.  So `↺_α emp` is `Res_α` on the nose (`Fig16.BoLo.reborrow_emp_iff`), and 6.130
is the inclusion `P ⊆ Res_α`.

**`Res_α → ℙ` is printed.**  [TR] p. 4 gives `SProp_α ≜ Res_α → ℙ` on the line above
`SProp ≜ Res → ℙ`, and `Fig16.SPropS.toU_range` places the former inside the latter as
`{P | ∀ρ. P(ρ) ⇒ ρ ∈ Res_α}`.  That set is precisely what 6.130 asserts of its `P`, so the
added hypothesis names an object the model already prints.

**Both of [TR]'s own uses supply it.**  6.130 is cited twice, both inside 6.131's induction
on p. 34.  At `T = T₁ ⊸ T₂` the antecedent is `[α] 𝒱⟦T₁ ⊸ T₂⟧δ(v)`, and
`[α]P(ρ) ≜ P(ρ) ∧ @ρ ⊐ α` ([TR] p. 6) carries the conjunct itself
(`Fig16.BoLo.reborrow_emp_box`).  At `T = Ref T′` it is the owned cell `ℓ ↦ v′`, which holds
no borrow and so lies in every stratum (`Fig16.BoLo.reborrow_emp_ptoOwn`).  There is no third
use.

**The mechanisation.**  `Fig16.BoLo.reborrow_emp` states the printed entailment with that
inclusion as a named hypothesis, `reb_α` untouched, and is scored `proved*`.
`Fig16.BoLo.reborrow_emp_outside_stratum` exhibits a resource outside `Res_α` — the `mut`
witness of `Fig16.RebExample.mutRes`, whose borrow does not outlive `α = 1` — so the
hypothesis is a real restriction.

### §12.63 Where 6.125 would carry 6.61's input: at the resource, not at `P` and `Q`

[TR] 6.125's proof (p. 33) is the single citation *"By theorem 6.61"*, so 6.125 inherits
whatever 6.61 carries.  At the subset reading of `reb_α`'s `imm` clause (§12.67(b)) 6.61
carries nothing, and `Fig16.BoLo.reborrow_star` is 6.125 as printed.  At the literal clause
`ρ′(ℓ) = ρ(ℓ)`, 6.61 needs the survival of `imm` locations on each of its two sources, and
where that input would be attached decides whether the row says anything:

* **The sources are the antecedent's own factors.**  6.125 reads `↺_α P ⋆ ↺_α Q` at a
  resource `ρ`, and the `⋆` splits it as `ρ = ρ₁ ● ρ₂`; `ρ₁` and `ρ₂` are the sources 6.61
  measures.  They are bounded by `ρ`, so the input is a condition on `ρ`.
* **Lifted onto `P` and `Q` it would empty the row.**  A condition of the form
  `∀ρ₁ ρ′₁. ρ′₁ ∈ reb_α(ρ₁) ⇒ P(ρ′₁) ⇒ (imm locations of ρ₁ survive in ρ′₁)` quantifies the
  source over all of `Res`, and every `ρ₁ ∈ Res_α` has `∅` among its reborrows (§12.62) with
  `emp` holding of it — so at `P = Q = emp` the lifted condition says every member of `Res_α`
  carries no `imm` cell, which a single `imm` cell with lifetime set `{2}` in `Res_3`
  contradicts.
* On an `imm`-free resource the input holds of every image, since a `●`-factor of an
  `imm`-free resource is `imm`-free.

### §12.64 Where the prose disambiguates the formula, the prose is the definition

A definition is what the paper says a thing is.  When a displayed formula is accompanied by a
paragraph that fixes what the formula leaves open, **the two together are the definition** —
transcribing the display alone is an incomplete transcription, and completing it from the
paragraph is not a departure and not a variant.

**The instance.**  [TR] Definition 6.3's third bullet reads `ℓ ∈ dom(ρ″)` — domain membership
only, leaving the cell free — and the paragraph one line below reads *"'without' means removing
the lifetimes of borrows from `ρ′`, **but keeping the lifetimes only in `ρ`**."*  That sentence
says which cell stands there, makes `⊟` single-valued, and is what lets the print write
`ρ⁺ ⊟ ρ_reb` as a **term** wherever it occurs.  `Fig16.ResU.SubKeep` is therefore Definition
6.3; `Fig16.ResU.Sub` is the bullets without the paragraph, kept for comparison.

**Consequence for scoring.**  A row proved at the completed reading is `proved`, not
`proved*`: it is proved at the definition.  [TR] 6.59 (`Fig16.ResU.six59`) is such a row.

**Why this matters beyond the one row.**  Transcribing half a definition loses nothing visible
at the definition.  It surfaces several lemmas downstream as an obligation that will not
close, which then presents as a difficulty in the *consumer* rather than in the transcription
of the *definition* — which is how transcribing Definition 6.3 without its paragraph presents,
at [TR] 6.59.

**Scope.**  This applies only where a sentence states the property (§12.60's category (a)).
Where no sentence states it and only a *proof* proceeds as though it held —
`Fig16.EscrowAgree` — there is nothing to complete the definition *with*, and folding such a
condition into a definition would assert that the paper states something it does not.  Such
conditions stay named hypotheses on the theorems that need them, and those rows stay
`proved*`.  §12.59 shows how the two categories can be confused.

### §12.65 [TR] 6.144 and [CONF]'s `wp Load I` are two rules, and both are proved

[TR] Lemma 6.144 (physical p. 37, read at 900 dpi) is

> **Lemma 6.144 (`wp-load-I`).**
> `ℓ ↦I_α P̂ ⋆ (∀ v. ℓ ↦I_α (v′. ⌜v = v′⌝ ⋆ P̂(v)) ─⋆ Q̂(v)) ⊧ wp (load ℓ) {Q̂}`

and [CONF] Fig. 13b (p. 415:15, *"Immutable loading and reborrowing rules"*) prints a rule
of the same name, **`wp Load I`**, read at 900 dpi:

> `ℓ ↦ I_α P̂ ⋆ (∀ v. ℓ ↦ I_α (_. P̂(v)) ─⋆ wp (v) {Q̂}) ⊨ wp (load ℓ) {Q̂}`

Unlike 6.150 (§12.61), these are not the same proposition, and they differ twice.

**The borrowed family.**  [TR] writes `(v′. ⌜v = v′⌝ ⋆ P̂(v))`; [CONF] writes `(_. P̂(v))`,
the constant function, which is what its prose says it is doing — *"we can specialize its
borrowed predicate to `v` by turning it into a constant function, since all future reads
from the immutable borrow must produce the same value"* (p. 415:16).  The two families
differ off `v′ = v`: `⌜v = v′⌝ ⋆ P̂(v)` holds of nothing there, `P̂(v)` of whatever `P̂(v)`
holds of.  Inside `↦I_α` the family is only ever applied at the cell's own value, so [TR]'s
cell proposition is [CONF]'s *plus* the equation pinning that value — strictly stronger, and
`Fig16.BoLo.ptoImm` at the two families says so directly.

**Where the wand lands.**  [TR]'s wand concludes `Q̂(v)`; [CONF]'s concludes `wp (v) {Q̂}`.
6.136 (`wp-val`, `Fig16.BoLo.wp_val`) gives `Q̂(v) ⊧ wp (v) {Q̂}`.  We read 6.136's printed
`⫤⊨` as `⊨`: every citation of `wp-val` in [TR]'s compatibility proofs is forward, and no
proof turns a hypothesis `wp(v){Q̂}` into `Q̂(v)`.  So nothing converts one wand into the
other.

**The two differences push opposite ways.**  Both sit inside the premise.  A wand out of the
*weaker* antecedent is the stronger hypothesis, so [CONF]'s constant family makes its premise
stronger than [TR]'s, i.e. its rule weaker; a wand into the *weaker* conclusion is the weaker
hypothesis, so [CONF]'s `wp (v) {Q̂}` makes its premise weaker than [TR]'s, i.e. its rule
stronger.  Composing 6.136 with the family weakening therefore moves *both* premises to one
common third premise, `∀ v. ℓ ↦I_α (v′. ⌜v = v′⌝ ⋆ P̂(v)) ─⋆ wp (v) {Q̂}`, rather than
either of them to the other — which is why both rows are proved directly and neither is
derived from the other.

**The mechanisation.**  `Fig16.BoLo.wp_load_I` is [TR] 6.144, tagged `[as printed]`, and
`Fig16.BoLo.wp_load_I_conf` is [CONF] Fig. 13b's row, tagged `[variant: …]`.
`TR3.wp_load_I` is 6.144 again over [TR] §3's own machine (D6).  The proofs share their two
elided steps — `Fig16.BoLo.pure_sep_biEntails` for the print's *"since `⌜v = v′⌝ ⋆ P̂(v)` is
equivalent to `P̂(v)`"*, and `Fig16.BoLo.compS_get_erase` with `Fig16.BoLo.lower_get` for the
lookup `⟦ρ_f ● ρ⟧(ℓ) = v` the closing run performs without comment.

**Why the second printing is transcribed.**  [CONF] Fig. 14's derivation of `withload` — its
sketch of [TR] 6.175 — cites `wp Load I` at the step that produces `ℓ ↦ I_α (_. P̂(v))`, and it
is that constant family which `Fig16.BoLo.wp_reborrow` (6.150) then consumes at a `P̂` constant
in its value argument.  The [TR] form does not hand 6.175 that shape; the [CONF] form does.

### §12.66 `β̄` is the borrows outstanding at a location, not the borrows ever taken

[CONF] 415:19 (§4.1, *Immutable Cells*) is the only place either document says what the
lifetime set on an `imm` cell **is**:

> "an immutable cell will record **the set of lifetimes `β̃` that it has been borrowed at**
> (written `imm(β̃, v, ρ′)`), and the borrow connective will bound its lifetime index `α` by
> the longest among them."

"has been borrowed at" can be read as provenance — every borrow ever taken, including ones
already ended.  [TR] Definition 6.3 reads the other way: `⊟` **subtracts** lifetime sets,
`ᾱ ∖ β̄`, and its paragraph says

> "since immutable borrows can alias at the same location, 'without' means removing the
> lifetimes of borrows from `ρ′`, but keeping the lifetimes only in `ρ`."

A history is never subtracted from; a set of outstanding claims is.  **We read `β̄` as the
borrows outstanding.**  Under §12.64 the two prose passages disambiguate one formula, and the
operative one is the one that says what happens to the set.

**What the reading gives.**  If every member of `β̄` is an outstanding borrow, then every
member is held by a live slot, and `Δ ⊢ Γ ⊐ @a` says every live slot outlives `@a`.  `⊓β̄` is
a **member** of `β̄` (`Fig16.LSet.meet_mem`), so it is bounded like any other member, and the
printed premise `@bδ ⊐ @aδ` of [TR] 6.60's `Imm` case is spent where the page spends it.

`Fig16.LogRel.LifeMembers` is the reading as a predicate, with its closure:
`Fig16.LogRel.lifeMembers_empty`, `Fig16.LogRel.lifeMembers_reb` (`reb_α` mints `{α}` for the
borrow it takes and keeps a subset of each source set), `Fig16.LogRel.lifeMembers_compS` and
`Fig16.LogRel.lifeMembers_compS_left` (`●` unions the sets, [TR] 6.43).
`Fig16.LogRel.Arises` is the family of resources it holds at — `∅`, `●` with either of its
parts, and `reb_α` at a licensed lifetime — with `Fig16.LogRel.lifeMembers_of_arises` the
closure lemmas read as its recursor.

**The literal `⊔β̄`.**  Read with the connective at `⊔β̄` (definition row 5.30), 6.60's `Imm`
step asks that every recorded lifetime be outstanding, a condition of the same species as
`✓` — [CONF] 415:21's "every pair of aliases map to the same object and each has an immutable
ancestor", which is likewise absent from `Res`'s grammar and assumed by `wp`: *"The weakest
precondition assumes validity of the pre-resource."*  `Fig16.LogRel.MutImmGap.cell` and `Fig16.LogRel.MutImmGap.lset` are the
cell and lifetime set at which, under the literal `α ⊑ ⊔β̄`, `𝒱⟦Mut @a (Imm @b 1)⟧` is empty.
With the connective at `⊓β̄` (§12.67(a)), 6.60's `Imm` case needs no licence on the recorded
borrows.

### §12.67 `ℓ ↦ Imm α P̂` bounded by `⊓β̄`, and a subset in `reb_α`'s `imm` clause

This section records two readings of definitions. In each, the printed formula is read through the prose that defines its objects (§12.64). The precedent is definition row 5.66, where Definition 6.3's third bullet is read through the sentence printed under it.

**(a) `Fig16.BoLo.ptoImm`: `α ⊑ ⊓β̄`, where [TR] p. 6 prints `α ⊑ ⊔β̄`.**
Definition row 5.30. Here is what the set and the index are, in the documents' own words:

* [TR] Definition 6.3 and the sentence after it (p. 17): *"since immutable
  borrows can alias at the same location, 'without' means removing the lifetimes
  of borrows from `ρ′`, but keeping the lifetimes only in `ρ`"*. `⊟` subtracts
  lifetimes, so each lifetime in a cell's set stands for one borrow held (§12.66).
* [CONF] 415:8: *"`Δ ⊢ T ⊐ a`, which now only forbids the context from holding
  borrows at lifetime `a` or shorter"*.
* [CONF] 415:9: *"the lifetime `a` is really only a lower bound on the 'true'
  lifetime that the borrow was originally assigned"*.
* [CONF] 415:10: *"the payload type for a mutable borrow is required to have an
  unambiguous lifetime bound"*.
* [CONF] 415:14: *"the borrowed predicate must have an unambiguous lifetime
  bound … expressed at the logical level using `[β]`"*.
* [CONF] 415:20: `Mut_α`'s *"predicate `P̂` … sits in the stratification at its
  lifetime `β`"*.
* [TR] 6.60's `Imm` step (p. 21): *"`@bδ ⊑ ⊔β̄`.  And by the hypothesis,
  `@bδ ⊐ @aδ`.  Therefore `@ρ ⊐ @aδ`"*, where `@ρ = ⊓β̄` (p. 5).

An index is a lower bound on the borrow it names, and each member of `β̄` is a
borrow. So the index bounds every member, which is `α ⊑ ⊓β̄`
(`Fig16.LSet.meet_mem`, `Fig16.LSet.meet_least`). With this reading, 6.60's `Imm` step is
a single `lt_of_lt_of_le`, and `Fig16.LogRel.vDen_outlives` is 6.60 as printed. Lemmas 6.60,
6.62, 6.163 and 6.173 carry no added hypothesis for the `Imm` case.

**The literal reading.** [CONF] 415:19 says *"the borrow connective will bound its lifetime
index `α` by the longest among them"*, and [TR] p. 6 prints `⊔`. Read literally, the formula
requires the following. 6.60's `Imm` step does not follow, because `⊔β̄` and `@ρ = ⊓β̄` bound
different members. Also, `𝒱⟦Mut @a T⟧δ` is empty whenever `T` has a top-level `Imm`, because
`𝒱⟦Imm @b T′⟧δ` then leaves every stratum. The library records the cell behind that
measurement, an `imm` cell recording `{α₀, β}` (`Fig16.LogRel.MutImmGap.cell`,
`Fig16.LogRel.MutImmGap.lset_meet`). Under the `⊓β̄` reading this cell is in `𝒱⟦Imm @b 1⟧δ`
only where `@bδ ⊑ α₀ ⊓ β`, and `Fig16.LogRel.MutImmGap.inRel_same` is the case `β = α₀`.

**What the `⊓β̄` reading costs.** [TR] 6.115 (`I-ag`) concludes at `α ⊔ β`. Over the
connective at `⊓β̄`, two cells at `{1}` and `{2}` compose to `{1, 2}`, whose meet
is not `⊒ 1 ⊔ 2` (`Fig16.BoLo.not_iAgreeAtJoin`). `Fig16.BoLo.ptoImm_agree`
is 6.115 at `α ⊓ β`, and `Fig16.BoLo.ptoImm_agree_eq` is 6.115 at equal indices. [CONF]
415:13 describes `I Agree` as aliases that "all agree on the lifetime". Lemma 6.115 is
transcribed as a variant.

**(b) `Fig16.ResU.RebAt`'s `imm` clause: `ρ′(ℓ) = imm(t̄, v, χ)` for a nonempty
`t̄ ⊆ s̄`, where [TR] p. 5 prints `ρ′(ℓ) = ρ(ℓ)` at `ρ(ℓ) = imm(s̄, v, χ)`.**
Definition row 5.28.

* [CONF] 415:24: *"`ρ′` must be just like a subresource of the original
  resource `ρ` … its imm locations are preserved at their original
  lifetimes"*. A subresource of an `imm` cell is that cell over fewer
  outstanding borrows (Definition 6.3), at its own value and witness.
* [TR] 6.57's proof (p. 18) prints *"`ρ|dom(ρ′ᵢ|imm) ≤ ρ′ᵢ|imm`"*, with `≤` and not `=`.
* [TR] 6.61's proof (p. 22) opens with *"the only interesting cases are locations
  `ℓ` that are in both `ρ′₁` and `ρ′₂`"*. This holds under the subset reading
  (`Fig16.ResU.six61_imm_at`).

`t̄` is nonempty because `Fig16.LSet` is (G2). So every lifetime that the image
records is one that the source records.

**The literal reading.** Under `ρ′(ℓ) = ρ(ℓ)`, a `●`-factor of a reborrow's image is not
itself an image, because a factor of `imm(s̄, v, χ)` is `imm` over a subset. Read literally,
6.61, 6.125 and 6.127 each need an added hypothesis:

* 6.61 needs one saying that each source's `imm` cells survive into the image (§12.41, §12.57).
* 6.125 needs the same fact at its sources (§12.63).
* 6.127 needs the `ρ′` half of its closing sentence.

Under the subset reading all three are as printed and carry no added hypothesis. They are
`Fig16.ResU.six61`, `Fig16.BoLo.reborrow_star` and `Fig16.BoLo.reborrow_weak`, the last
through `Fig16.ResU.RebAt.factor`. 6.131–6.133 and 6.175 carry no such hypothesis either. The
one remaining hypothesis of `Fig16.LogRel.fundamental` is `Fig16.LogRel.WithloadEscrow`
(§12.68–§12.73). The consumers of the printed clause's equation (6.52–6.59, 6.150) read it
through `Fig16.ResU.reb_imm_cell_kw`. By that lemma, the image cell is `imm`, at the source's
value and witness, in every stratum the source cell is in.

### §12.68 A configuration of our carrier at which `WithloadEscrow` is refused

`Fig16.LogRel.ViewWitness` is built from two resources:

* An argument `ℓ₂ ↦ imm({1}, ℓ₀, ρ″)`, whose witness owns `ℓ₀`.
* A callback resource that holds the view `ℓ₀ ↦ imm({1}, (ℓ₁,()), ∅)`.

`ρ₁ ● ρ₂` is `✓` (`DefectB.Valid_composite`), and the callback is in its type
(`Fig16.LogRel.ViewWitness.f_den`). `withload` hands the callback `ℓ₀`, and the callback gets
stuck (`Fig16.LogRel.ViewWitness.run_stuck`). So three things are refused at this
configuration:

* our `Sem` at that `withload` node (`Fig16.LogRel.ViewWitness.withloadSem_refused`);
* our `FundamentalProperty` (`Fig16.LogRel.ViewWitness.fundamentalProperty_refused`);
* `Fig16.LogRel.WithloadEscrow`, from which `Fig16.LogRel.fundamental` would derive that `Sem`.

We cannot reconcile this configuration with [TR] 6.150's H19 (p. 39): *"by lemma 6.55 with
H16, `ρ_P̂(v′) # ρ_b`"*. The step runs through two transcribed objects:

* p. 5's `▶◀` between `imm` and `own`, which compares only the value;
* p. 6's `wp`, which constrains only the endpoint memories.

The configuration stays in the library. It measures the literal reading of p. 6's `wp` and
p. 4's `𝒱⟦−⟧`. §12.69–§12.72 give readings of those two definitions and leave `▶◀`
untouched. §12.73 shows that the resulting judgment excludes the configuration
(`Fig16.LogRel.ViewWitness.excluded`).

### §12.69 `𝒱⟦Imm @a T⟧`'s payload read at its observable view

Definition row 4.8. The `Imm @a T` clause of `Fig16.LogRel.Typed.vX` holds its payload at
`vX wpX false T`. That is `𝒱⟦T⟧` with every `⊸` and `∀` position not under a `Mut` relaxed
to `True`. [TR] p. 4 prints `ℓ ↦ Imm @aδ 𝒱⟦T⟧δ`, the full relation. The relaxation is a
weakening (`Fig16.LogRel.Typed.vO_obs`): `Imm @a (T₁ ⊸ T₂)` and `Imm @a (∀'a ⊏ @b. T)` admit
any resource at the `⊸`/`∀` position. Every other clause of the observable view is the same as
the full relation's, and the `Mut` clause stores the full relation in both modes.

**What the documents say a payload at a closure position is for.**

* [CONF] 415:9: *"In some cases, like for computations with capture environments that may
  hold linear references, there is no view at which it would be safe to access the payload,
  so we map these types to a new, distinguished unknown type, Unk, for which the only
  operation that is defined is forget."*
* [CONF] Fig. 8 (415:10), clauses (4) and (8) of §6.3: `Imm̲ 'b (T₁ ⊸ T₂) ≜ Unk` and
  `Imm̲ 'b (∀'a ⊏ @a. T) ≜ Unk`.
* [CONF] 415:15: the metafunction *"immutably borrows any linear references or mutable borrows
  in the payload and obfuscates any closures that may hold onto such resources"*.
* [TR] 6.131 (p. 34), the `T₁ ⊸ T₂` bullet: *"Unfold: [α] 𝒱⟦T₁ ⊸ T₂⟧δ(v) ⊧ ↺α emp.  Apply
  theorem 6.130."* The `∀` bullet reads *"analogous to case T = T₁ ⊸ T₂"*. In both, the
  payload at a closure position is discarded, not read.

So the only operation that any printed proof performs on the payload at a `⊸`/`∀` position is
to discard it, and the prose says there is no view at which that payload may be accessed.
Where the prose disambiguates the formula, we take the prose as the definition (§12.64).

Every printed consumer of an `Imm` payload reads it through 6.131 or not at all. These
consumers are 6.60, 6.64 through 6.172, 6.131–6.133, 6.167, 6.170, 6.171 and 6.175. Every
printed producer makes the full payload, which `vO_obs` weakens. The producers are 6.64
through 6.172, and 6.131's `↺↦`, `↺m` and `↺i`. The whole of §6.8 runs at this reading
(`Fig16.LogRel.Typed.fundamentalProperty`). The reading has not been checked against any rule
outside §6.

**The literal reading.** The `Imm` clause of `Fig16.LogRel.vDen` keeps the full payload and
stays in the library. Read literally, [TR] 6.150's reborrow is not determined by types.
Consider a `⊸` position of a root's pointee. The witness piece that a recorded image carries
need not be the piece that the payload's decomposition gives the closure. Because the full
`𝒱⟦⊸⟧` is resource-sensitive, the image that a later `withload` needs cannot be typed from
what the world records. We have not derived the chooser at the literal reading, and we have
not verified that any obstruction is real.

Under the observable view, the chooser is proved:

* `Fig16.LogRel.Typed.obs_transfer` moves the observable view between two pieces of one
  escrow. At `⊸`/`∀` both sides are `True`, and that is what makes the transfer go through.
* `Fig16.LogRel.Typed.rebChooseO_top_tw` and `Fig16.LogRel.Typed.rebChooseO_deep_tw` choose
  from the tagged world and the payload the program holds.

This reading is of category (a) in §12.60.

### §12.70 The `Mut` and `Imm` payloads stratified by the record list

Definition rows 4.8 and 4.9. Once `𝒱` is read relative to a record list (§12.72), a borrow
cell's payload is held at the records that are strictly longer-lived than the cell:

* `Fig16.LogRel.Typed.ptoMutS` stores `P(ls₀)`, where `ls₀` is the set of members of the
  current list strictly longer-lived than the cell's `b`, and the family `P` is in `Res_b` at
  every list.
* `Fig16.LogRel.Typed.ptoImmS` holds the payload at the members strictly longer-lived than
  `⊓β̄`.

The documents ground this as follows:

* [TR] p. 4: `Mut_α ≜ {(β ⊐ α, v : Val, ρ : Res_β, P̂ : Val → SProp_β) ∣ P̂(v)(ρ)}`. The stored
  predicate lives in the cell's own stratum.
* [TR] 6.65 (p. 24): *"If P̂ ⊧ [β] P̂, then …"*, with the cell made at *"α ⊏ γ ⊓ β"*.
* [CONF] 415:20: *"we break the circularity using stratification, but using a very different
  measure: the outlives lifetime ordering"*; *"For a mut cell, its lifetime β must be longer
  than the stratification index α, its witness ρ sits in the stratification at its lifetime β,
  and so does its predicate P̂"*.
* [CONF] 415:25: *"the lifetime stratification inherent to the type system is enough to avoid
  the use of step-indexing altogether"*.

The records longer-lived than a cell are exactly the ones that the Kripke order `Ext` never
changes. So a `mut` cell's stored predicate stays **equal** along `Ext` (`ptoMut` asks for the
equation exactly), and an `imm` cell's payload stays at the same list
(`Fig16.LogRel.Typed.vX_local`). The three cell operations behave as follows:

* Reading a cell gives its content at the current list (`Fig16.LogRel.Typed.ptoMutX_read`).
* A write needs the new content to be relevant only to records tagged above the cell
  (`Fig16.LogRel.Typed.ptoMutX_write`, discharged by
  `Fig16.LogRel.Typed.lifeBound_of_tagged`).
* A cell made at a lifetime below every record stores the whole list
  (`Fig16.LogRel.Typed.ptoMutX_create`). This is 6.65's *"α ⊏ γ ⊓ β"*, also taken below every
  tag.

This is the stratification that 6.65 prints at the cell, lifted to the list.

**The literal reading.** `Fig16.LogRel.vDen` has one predicate `𝒱⟦S⟧δ` per cell, independent
of the list. That does not combine with §12.72. A stored predicate that mentions the list is
not stable when the list grows. A stored predicate that does not mention the list cannot carry
`CohE` at the cell's `Imm` positions, or `wpTS` at its `⊸` positions. Neither half is
machine-checked in this repository.

### §12.71 The `Imm` clause carries the type the world recorded at the cell

Definition row 4.8. The `Imm @a T` clause of `Fig16.LogRel.Typed.vX` adds the conjunct
`Fig16.LogRel.Typed.CohE (rsOf ls) ℓ T δ`. It says that the record list names at `ℓ` either a
record whose type is `T`, or a chain position of a record whose pointee type is `T`, up to
`Fig16.LogRel.Typed.TyEq`. `TyEq` relates two types that become one type once each lifetime is
read at its own substitution. The conjunct reads types and substitutions only.

**This is a reading of a printed step, not a change of route.** [TR] 6.150's proof (p. 39)
takes a reborrow at H16 and spends 6.55 on it at H19: *"by lemma 6.55 with H16,
`ρ_P̂(v′) # ρ_b`"*. The documents state twice what makes that step go through:

* [TR] p. 18, inside 6.55's proof: *"ρ and ρ′ differ only by potentially changing from own or
  mut to imm, but witnesses and values always stay the same"*;
* [CONF] 415:19: *"immutable cells ψ₁, ψ₂ at the same location must all have the same
  witness"*.

The reborrow is also a choice. `↺` *"is a ⋄-style modality; it existentially quantifies over
resources ρ′ that satisfy the given proposition"* ([CONF] 415:23), over *"the full space of
safe reborrows"* ([CONF] 415:15). So H16's reborrow must be the one that the context's other
views of the same escrow already agree with. `CohE` lets that choice be made from types. The
program's type at the cell is the recorded type, so the image the world recorded is typed at
the program's `Imm̲ 'b T`.

The printed proof is kept: `Fig16.LogRel.Typed.wpTS_reborrow` is `Fig16.BoLo.wp_reborrow`'s
H1–H33. Its restriction `Fig16.BoLo.RebEscrow` becomes a chooser,
`Fig16.LogRel.Typed.RebChooseTW`, which `Fig16.LogRel.Typed.rebChooseTW_top` and
`Fig16.LogRel.Typed.rebChooseTW_deep` discharge.

`CohE` uses `TyEq` rather than syntactic equality because [TR] 6.162's `Δ-subst`,
`𝒱⟦T[@a/'a]⟧δ = 𝒱⟦T⟧δ['a↦@aδ]`, moves a value between two syntactically different types
(`Fig16.LogRel.Typed.vX_tyEq`). `⊑Imm` (6.167) changes the index, and changes nothing that
`CohE` reads.

**The literal reading.** Without the conjunct, [TR] 6.175 at `Fig16.LogRel.Sem`
needs `Fig16.LogRel.WithloadEscrow`, and the configuration of §12.68 refuses that hypothesis.

### §12.72 `⊸`/`∀` Kripke over the record list, and `wp` over tagged typed worlds

Definition rows 4.4, 4.5, 4.11, 4.13, 4.14 and 5.33.

* `Fig16.LogRel.Typed.TW W ps rs`. `W` is every frame together with the resource that a `wp`
  runs at. `W` is reached from `∅` by the operations that the printed proofs perform: 6.141,
  6.142, 6.145, 6.64's entry and exit, 6.65/6.66's fold and unfold, and 6.150's entry and exit
  at H11's `β`. `ps` holds the frames that 6.64 has taken and not ended, each a record
  `(ℓ, v, ρ′, T, δ)`, and `rs` holds their lineages. `Fig16.LogRel.Typed.TW.inv` is the
  invariant of `TW`.
* `Fig16.LogRel.Typed.wpTS ls e Q̂` is [TR] p. 6's `wp`, with `∀ρ_f # ρ` ranging over the frames
  that complete `ρ` to a tagged `TW` world at `ls`. Tagged (`Fig16.LogRel.Typed.Tagged`) means
  that each record carries its frame's lifetime. The post-configuration must be such a world
  too, with the same records proper and the same list members. Every other conjunct is
  `Fig16.BoLo.wp`'s verbatim, and `Q̂` receives the list.
* The `⊸` and `∀` clauses of `vX` quantify over every list that is `Ext`-above the current one
  at the closure's resource. `Fig16.LogRel.Typed.Ext` keeps the records relevant to that
  resource, and leaves unchanged the records longer-lived than its borrow cells.
  `Fig16.LogRel.Typed.SemX` holds at every list.

**The grounding.** §6's lemmas quantify over resources of the calculus, the ones that arise.
Two sentences say what arising buys:

* [CONF] 415:21: *"Conceptually, in a valid resource, every pair of aliases map to the same
  object and each has an immutable ancestor."* The carrier's `✓` does not carry this. The
  `ρ₁ ● ρ₂` of §12.68 is `✓`, with two aliases of `ℓ₀` at different objects. The judgment
  therefore quantifies over the configurations that `TW` produces, and §12.73 shows that the
  configuration of §12.68 is not among them.
* [CONF] 415:19: *"At the moment the borrow is created, there is a particular witness—the value
  v and a resource ρ′—for the payload predicate P̂(v)(ρ′) … ownership of this witness ρ′ is
  temporarily moved into the borrow."* A record is that witness, together with the `(T, δ)`
  at which the payload predicate `𝒱⟦T⟧δ` was taken.

Three design choices follow:

* The list is carried because a world does not determine it. The same `imm` cell arises from
  frames at different types, and the chooser and `CohE` read the recorded type.
* The `⊸`/`∀` clauses are Kripke over `Ext` rather than over every extension, because a
  closure must not be credited with records it holds no borrow of.
* The post-configuration keeps the same members because 6.64 ends its record before the run
  returns.

At `wpTS`, 6.135–6.149 are the proofs of `Fig16.BoLo.wp_bind` through `Fig16.BoLo.wp_I_forget`,
with the post-world's `TW` constructor added.

**The literal reading.** `Fig16.BoLo.wp` quantifies over every `ρ_f # ρ`, including
configurations that no program produces, and the closures of `Fig16.LogRel.vDen` run at every
such frame. The configuration of §12.68 is one of these. Our `Sem` at its `withload` node, our
`FundamentalProperty` and `WithloadEscrow` are all refused there. The literal statements stay
in the library: `Fig16.LogRel.fundamentalProperty` is 6.151 at them, from `WithloadEscrow`.

### §12.73 Why the judgment tracks history, and why the observable view rather than lifetime-indexing

**History.** The configuration of §12.68 is `✓`, and no pointwise condition excludes it:

* the view at `ℓ₀` is an `imm` cell that agrees with the owning payload in value;
* the callback holding the view is in its semantic type (`Fig16.LogRel.ViewWitness.f_den`).

It is refused only by the view's agreement with the owning payload's type, which is a fact
about how the borrow was made. Under the judgment of §12.69–§12.72 the configuration is
excluded: `Fig16.LogRel.ViewWitness.excluded` proves that no `TW` world holding `ρ₁ ● ρ₂` has
`ρ₁` in `𝒱X⟦Imm 'b T₁⟧` at its list. The argument goes as follows:

1. `CohE` names either a record of type `T₁` at `ℓ₂`, or a chain position of a record there
   (`Fig16.LogRel.ViewWitness.tyEq_T₁`).
2. In either case, `ℓ₀` is a chain position of that record at pointee `Ref 1 ⊗ 1`.
3. The invariant (`Fig16.LogRel.Typed.DeepInv`) requires the view at `ℓ₀` to have that shape.
   Its witness `∅` does not (`Fig16.LogRel.ViewWitness.not_vShape_pair_empty`,
   `Fig16.LogRel.ViewWitness.chain_refuses`).

So at its second stage, the run that `Fig16.LogRel.ViewWitness.withloadSem_refused` builds
needs a world that `wpTS` does not quantify over. `Fig16.LogRel.Typed.fundamentalProperty`
holds with no hypothesis.

**Why not lifetime-indexing alone.** [CONF] 415:25 names the lifetime stratification as what
replaces step-indexing. An alternative design records, in the world, the typing of live
reborrow images, indexed by lifetime level, with the relation at level `n` reading only facts
at longer lifetimes. Lean accepts that recursion. However, the fact that 6.150's chooser needs
is always at or above the level at which the world may record it. The consumer of a recorded
view's typing is a later reborrow, and H11 makes that reborrow strictly shorter-lived, which
puts it at a strictly higher level. This comparison of levels is not machine-checked in this
repository, and no obstruction to lifting a fact across levels has been verified.

The observable view removes the need for the fact. The chooser needs a witness's typing only
at the observable view, which the world's first-order data determine
(`Fig16.LogRel.Typed.obs_transfer`). So no relation fact is recorded in the world, and `TW`
mentions only `Fig16.LogRel.Typed.vShape`.

## Part II — The judgment boxes of [TR] p. 2

### §C.25 `@ρ ⊐ α` is universal over the borrow cells, and `[⊤]P` is the borrow-free restriction

**The relation constrains `imm` and `mut` cells and says nothing about `own` cells.**  [TR]
p. 5 abbreviates it as a comparison of `@ρ ≜ ⊓_{ψ ∈ cod(ρ)} @ψ` with `@own ≜ ⊤`, and `⊓` is
`max` on ℕ with `⊤ ≜ 0` ([TR] p. 4).  Read as a single strict comparison of that meet, it
would fail at `α = ⊤` on every borrow-free resource, `∅` included.  [TR]'s own proofs
discharge it on borrow-free resources at an unrestricted `α`, calling it immediate:

- Lemma 6.121 (`↺↦`, p. 32): "it suffices if `@(ℓ ↦ own(v)) ⊐ α`, which holds by
  definition."
- Lemma 6.124 (p. 33): "`@∅ ⊐ α` … hold by definition."
- Lemma 6.107 (`[]↦`, p. 30) is closed "by inspection", with no side condition on `α`.

None carries an index bound, and under the meet reading each would need `α ≠ ⊤`.  So
`@ρ ⊐ α` looks at the lifetimes of borrow cells only, and a borrow-free value strictly
outlives every lifetime, `⊤` included, vacuously.

**So the relation is `ρ ∈ Res_α`, which is printed.**  Clause for clause it is Fig. 16's
stratum membership (`own ↦ True`, `imm ↦ ⊓β̄ ⊐ α`, `mut ↦ β ⊐ α`) quantified over the
codomain.  `BoCa.Fig16.BoLo.Outlives ρ α` is defined as `ρ.InStratum α`
(`BoCa.Fig16.ResU.InStratum`): `[α]`'s second conjunct is membership in the stratum the
modality names.

**`[⊤]P` is `P` restricted to the resources holding no borrow.**  `Res_⊤` asks `@ψ ⊐ ⊤` of
every `imm` and `mut` cell, which none satisfies, and asks nothing of an `own` cell.  `[⊤]`
reads "P, of a resource that outlives `⊤`", and what outlives the longest lifetime is
exactly what borrows nothing.

**The two readings differ only at `⊤`, and only on borrow-free resources.**
`BoCa.Fig16.ResU.inStratum_of_atLife` (and `BoCa.Fig16.BoLo.outlives_of_atLife`) is the
direction from the meet comparison to stratum membership, and needs no side condition.

**Consequences.**  On this reading the printed statements hold as printed:

| Lemma | Status | Lean |
| --- | --- | --- |
| 6.107 (`[]↦`) | `[as printed]` | `BoCa.Fig16.BoLo.box_ptoOwn` |
| 6.121 (`↺↦`) | `[as printed]` | `BoCa.Fig16.BoLo.reborrow_ptoOwn` |
| 6.124 (`↺⌜⌝`) | `[as printed]` | `BoCa.Fig16.BoLo.reborrow_pure`, over `BoCa.Fig16.BoLo.reb_empty` |
| 6.102 (`[]∀`) | restricted to a nonempty index type, per [TR]'s "Suppose X ≠ ∅" | `BoCa.Fig16.BoLo.box_all`; the literal reading is measured at any `ρ` outside `Res_⊤` by `BoCa.Fig16.BoLo.box_all_needs_nonempty` |

**`reb_α`'s leading conjunct reads the same way.**  [TR] p. 5's last row opens with the same
`@ρ ⊐ α`; `BoCa.Fig16.ResU.Reb` writes it as `ρ.InStratum α`, so that one glyph has one
reading throughout, and this is what makes Lemma 6.124 hold as printed.

**The strictness of `⊐`.**  `⊐` is strict in both documents: [TR] p. 6 at 700 dpi shows no
under-bar, on a line adjacent to a `⊒` that has one; [CONF] Fig. 19 at 600 and 700 dpi shows
the dotted `⊐̇` with no under-bar below an `ℓ ↦ M_α P̂` whose `⊒̇` visibly has one.  [CONF]
§4.4's prose agrees that the modality restricts `P` "to the resources that strictly outlive
`α`".  The question is not the strictness of `⊐` but what it is applied to: the borrow
cells, not a meet taken over the whole codomain.

**The meet of the empty codomain.**  `@∅` is `⊤` (the meet of the empty set is `⊤ = 0`), but
`∅` lies in every stratum because it has no cells, not because of the value of its meet; the
convention is load-bearing for nothing here.

**`⊤` as a modality index.**  Neither document uses `⊤` as a modality index, and the
development does not depend on that.  `[⊤]T` is a well-formed type: `Δ ⊨ ⊤` holds ([TR] p. 3,
900 dpi: `Δ ⊨ @a ≜ ∀δ ∈ ⟦Δ⟧. @aδ defined`, with no `⊏ ⊤`), the statics restrict the index
nowhere, and [TR] Lemma 6.163 (`[]I-compat`, p. 42) has two premises and no index bound.  On
the [CONF] Fig. 7 reading of its context premise, `Δ; • ⊢ λx.x : [⊤](1 ⊸ 1)` is derivable,
and on the reading above its denotation is inhabited, by the borrow-free resources.

### §C.26 The typing judgment carries no well-formedness presupposition

On [TR] p. 2 the box for the typing judgment reads `Δ; Γ ⊢ e : T` and nothing more. The two boxes beneath it on the same page carry annotations: `Δ ⊢ T   Presumes ⊧ Δ` and `Δ ⊢ T ⊐ @a   Presumes ⊧ Δ and Δ ⊧ @a` (read at 400 dpi). So the page states a presupposition for the well-formedness and outlives judgments, and states none for the typing judgment.

The mechanisation follows the boxes. `BoCa.Derives` is the typing rules as the figures print them, and none of its constructors has a well-formedness premise. The well-formedness judgment `BoCa.WfTy` is transcribed alongside it and consumed by no constructor of `Derives` (definition row 2.19). The typed-world results are stated at a separate judgment, `BoCa.DerivesWf`. It has the same rules, with p. 2's `Δ ⊢ T` consulted at binders and eliminated types (`Ty.scopedB`), and it is used under the presuppositions `⊧ Δ` and `Δ ⊢ Γ`. That judgment puts the well-formedness judgment to use. It does not attach a presupposition to the typing box, which this entry concerns. C14 and §12.69–§12.73 cover it.

## Part III — Conventions of the mechanisation

These are choices of representation.  None of them is a reading of the paper, and none is
evidence about it.

### G1 `Res` is finite at every depth

The entries G1–G8, F1, L3–L5 and W2 record choices the mechanisation makes where the paper leaves a detail open or where Lean needs a representation. They are not readings of the paper, and nothing in them is evidence about what [TR] or [CONF] intends. When one of these choices depends on a claim about the printed text, that claim has its own adjudication entry, and the convention names it.

`Res_α` and `Res` are both realised as `Loc ⇀ᶠⁱⁿ Cell`, by `BoCa.Fig16.PMap`. A `PMap` is a function `Loc → Option _` bundled with a `Prop` field saying that some list covers its domain (`PMap.finite`). [TR] marks only strata row 7 (`Res`) with `fin`. Row 2 (`Res_α`) is bare in both documents. Finiteness at row 2, and so at every depth, is forced rather than assumed, for three reasons. Every operation from `▶◀` on is defined on the unstratified `Res`. `Mut_α`'s witness is a `Res_β`. The flattening walk composes exactly those witnesses. A `Res_β` must therefore be a `Res`. The argument, and the rows it touches, are §12.33 and D10. The `[variant: …]` tags in `Paper/S5_Model/Definitions.lean` cite this entry.

### G2 `℘⁺(Life)` as a bounded set

`℘⁺(Life)` is realised as `BoCa.Fig16.LSet`: a set of lifetimes bundled with its least and greatest member, so that `⊓ᾱ` and `⊔ᾱ` are total and choice-free (`LSet.meet`, `LSet.join`). This excludes no `ᾱ` that can inhabit any `Imm_α`. Since `⊓` is `max`, an `ᾱ` with no greatest element has no `⊓ᾱ` and satisfies no condition of the form `⊓ᾱ ⊐ α`. Conversely, every `ᾱ` that satisfies the printed side condition is an `LSet` with the same members and the same meet. So the set `Imm_α` (strata row 4) is the printed one, although its binder is not `℘⁺(Life)` glyph for glyph.

### G3 Strata as subtypes of the unstratified carrier

In the paper, the strata `Cell_α` and `Res_α` are subsets of one set, so membership is free. In Lean they are distinct types, and the inclusion becomes an obligation, which is discharged rather than declared. `BoCa.Fig16.Cell.stratumEquiv` and `BoCa.Fig16.Res.stratumEquiv` identify each stratum with the members of the unstratified type that satisfy `CellU.InStratum` / `ResU.InStratum` (`Cell.toU`, `Res.toU`, `Cell.toU_inStratum`, `Res.toU_inStratum`). `own`, `imm` and `mut` are rebuilt as constructors that take a resource of the unstratified type together with its stratum-membership proof.

Every definition from the operations on is stated through this identification. So a printed clause that shares one `ρ` across two strata — row 5.13, row 5.15, and clauses (2), (3) and (5) of row 5.16 — has a single Lean term for that `ρ`, and its comparisons are plain equality. Definition row 5.48 is the membership this presupposes.

### G4 Partial operations as graphs

A printed operation that is partial is rendered either as a graph (a relation that is single-valued where it is defined) or as a function that takes a proof of its domain. It is never rendered as a total function with a default value. Each site says which form it uses. The walks and the flattening are graphs: `BoCa.Fig16.ExW` for `ex(ρ)_◐`, `BoCa.Fig16.AgW` for `ag(ρ)`, `BoCa.Fig16.ResU.Flat` for `⦇ρ⦈` and `BoCa.Fig16.ResU.Lower` for `⟦ρ⟧`. Each is proved functional (`ExW.functional`, `AgW.functional`, `ResU.Flat.functional`, `ResU.Lower.functional`).

A printed statement that mentions a partial term is then stated with that term bound by its graph, and the definedness the print presupposes appears as inhabitation of the graph. The `[about ours: … is its graph (G4)]` tags in the lemma files mark lemmas about the graph representation itself.

### G5 The reflexive order `⊑`

`⊑` (`BoCa.Fig16.Life.Sqsubseteq`) is the reflexive closure of the printed strict order `⊏`. Neither document defines a reflexive order on lifetimes. [TR] p. 4's key assigns the underbarred glyph the strict `>`, and [CONF] Fig. 11 alludes only to `⊑̇`. §12.3 is the reading of the glyph that this convention implements. The printed definitions stated with `⊑` are `ResU.AtLife`, `BoLo.ptoImm` and `BoLo.ptoMut`. The `[as printed]` lemmas stated with it include `BoLo.box_antitone`, `BoLo.ptoImm_antitone` ([TR] 6.114) and `BoLo.ptoMut_antitone`.

### G6 The walks' comprehension as a family indexed by locations

The iterated `⨀`/`◯` in the walks ranges over a comprehension. We read that comprehension as a family indexed by the locations, not as the set of its values. [TR] p. 5 writes `{… | ∃ℓ. ρ(ℓ) = mut(…)}` and [CONF] Fig. 18a writes `ρ′ ∈ cod(ρ|mut)`. Both are set-builder notation. The index set is `BoCa.Fig16.ResU.Sites`: the locations of `ρ` carrying a cell of a given tag, each listed once. `ExW` and `AgW` compose one summand per location in it.

The choice rests on a reading of the printed text, and §12.36 carries that argument in full. In brief, the set reading and [TR] Lemma 6.18 cannot both be kept. Under the set reading, two `mut` cells with equal witnesses contribute one composand, and the reading would admit a resource holding two mutable borrows of one cell.

### G7 `ρ ≤ ρ′` (not a convention)

`ρ ≤ ρ′` is printed, not chosen. [CONF] p. 415:24, footnote 1, gives `ρ₁ ≤ ρ₃ ≜ ∃ρ₂ ▶◀ ρ₁. ρ₁ ● ρ₂ = ρ₃`, which is `BoCa.Fig16.ResU.Le` glyph for glyph. The label is kept so that existing references resolve. The two documents differ on this relation: [TR] uses `≤` on resources without defining it, and §12.37 records that.

### G8 Equality of locations is decided classically

`Loc` is abstract. Equality on it is decided classically, so `ℓ ↦ ψ` (`BoCa.Fig16.ResU.single`), domain subtraction, and everything stated at them depend on `Classical.choice`. The alternative would be a `[DecidableEq Loc]` hypothesis in the statements, and that would add a hypothesis to printed statements that carry none. Rows 5.29–5.31 and [TR] Lemmas 6.41–6.44 inherit the choice.

### F1 Partial terms and their definedness

[TR] writes `✓ρ ≜ ⦇ρ⦈ defined`, which presupposes that flattening is partial. The walks `ex(ρ)` and `ag(ρ)` are partial in the same way. On this carrier, all three are graphs (G4), and `✓ρ` is `BoCa.Fig16.ResU.Valid`, the inhabitation of the graph `ResU.Flat` (definition row 5.23: *"definedness of a graph is inhabitation of it"*). `⟦ρ⟧` is guarded by `✓ρ` in [TR]'s case brace. `ResU.Lower` carries the same guard through its existential, so a lowering exists exactly when a flattening does.

What the lemma files cite this convention for is the following. A printed display or proof step that applies a partial term, such as `ag(ρ)` in `ag(ρ_f) ▷◁ ag(ρ)` or `ag(ρ|dom(ρ′ᵢ|imm))`, presupposes that the term is defined. Sometimes no printed hypothesis delivers that definedness. The Lean statement then carries it as the inhabitation of the graph (for example `AgW ρ A`), tagged `[restricted: …]`, and leaves the printed conclusion unchanged. [TR] Lemmas 6.55 and 6.57 are the two sites (`ResU.six55`, `ResU.six57`).

### L3 `@aδ` is eliminated, not computed

`BoCa.Lifetime.Life.interp` is `Option`-valued: `@aδ` is undefined when a variable of `@a` lies outside `dom(δ)`, as it is in the sources ([CONF] Fig. 11 gives `aδ ≜ δ('a)`). Neither document says what a clause means at an undefined `@aδ`. How such a clause falls is fixed by the position `@aδ` occupies in the printed clause:

- **As a connective's argument** (`[@aδ] P`, `ℓ ↦ Imm @aδ P̂`, `ℓ ↦ Mut @aδ Ŝ`), there is nothing to apply the connective to, so the clause holds of nothing (`BoCa.Fig16.LogRel.atLife`).
- **As a quantifier's bound** (`∀α ⊏ @bδ.`, and [CONF] p. 415:12's `∀α. ⌜α ⊏ @bδ⌝ ─⋆`), the bound is a proposition about `α` that is false everywhere. The quantifier is then vacuous, and the clause holds of everything (`BoCa.Fig16.LogRel.LtLife`).

[TR]'s proof of 6.161 (p. 42) introduces `α ⊏ @bδ` without first establishing that `@bδ` is defined, and only the `LtLife` reading allows that step. On the inputs the paper quantifies over, the side condition is invisible. `Δ ⊢ T` and `δ ∈ ⟦Δ⟧` make every lifetime in `T` defined at `δ` (`Lifetime.Life.interp_defined_of_wf`), and `atLife_eq` reduces `atLife` to the printed clause wherever `@aδ` is defined.

### L4 `dom(Γ)` is the live slots

`Γ` is positional (de Bruijn). The context `Ctx` of `Derives` keeps every position and marks a consumed slot by turning off a liveness bit. We read `dom(Γ)` as the live slots. A consumed slot is not in `dom(Γ)` and contributes no conjunct to `⊛_{x∈dom(Γ)}` (`gSep`). The containment `dom(Γ) ⊆ dom(γ)` is `Ctx.LiveWithin`, not `Γ.length ≤ γ.length`, so a consumed slot past the end of `γ` is outside the containment exactly as it is outside the `⊛`.

In row 4.13, [TR] p. 4 prints `⌜dom(Γ) ⊆ dom(δ)⌝`. `Γ` maps term variables and `δ` maps lifetime variables, so we read that containment as `dom(γ)` (definition row 4.13).

### L5 `γ(e)` is a parallel substitution

The closing substitution `γ(e)` is `BoCa.Expr.psub`, a parallel substitution, and `Fig16.LogRel.substAll` names it. A fold of single substitutions `Expr.subst 0` equals the closing substitution only when `γ` is closed, because `Expr.subst` descends into `Expr.val` and would rewrite values that an earlier step has already placed.

[TR]'s `γ` ranges over runtime values, which are closed. `𝒱⟦T⟧δ` alone does not force closedness: at `1 ⊸ Unk`, where `𝒱⟦Unk⟧` is `emp` and constrains nothing, an open `λ` satisfies the relation. The parallel form sidesteps the question. `Expr.psub_cons` is the peeling lemma that the compatibility proofs of [TR] §6.8 use to take one value off the front.

### W2 Three machines, and what each is for

[TR] §3's reduction relation is a relation on memories `μ : Loc ⇀ Val`, and its `alloc` rule `(μ, alloc v) ↦ (μ ⊎ ℓ ↦ v, ℓ)` is nondeterministic in `ℓ`. The mechanisation keeps that relation on `BoCa.BoLo.Heap` (`Loc → Option Val`) and has three machines:

- **The printed machine.** `BoCa.TR3.Kont` has the seven productions p. 3 prints. `BoCa.TR3.Head` has the eight rules of the p. 4 box, with `⊕↦` as its two instances. `BoCa.TR3.Step1` is the one context rule, and `TR3.Steps` is its closure.
- **The completed machine.** `BoCa.BoLo.Kont` has the same seven frames plus two more, `K; e` (`Kont.seq`) and `injᵢ K` (`Kont.inj₁`, `Kont.inj₂`). `BoCa.BoLo.Head` has the same nine rules as `TR3.Head`, and `BoLo.Steps` is its closure. §12.42 and D6 give the reason for the two frames. The library's `wp` (`Fig16.BoLo.wp`) runs this machine. `TR3.wp` is the same row over the printed machine.
- **The executable interpreter.** `BoCa.Mem`, `BoCa.step`, `BoCa.run` and `BoCa.eval` form a deterministic total function on association-list memories. It allocates at `μ.next`, which a function has to do because it cannot choose nondeterministically. It adds the same two congruences.

The convention is that the `wp` development and the adequacy results are stated only over the two relations on `Heap`. `Fig16.BoLo.wp_alloc` may choose any fresh location (`PMap.exists_fresh`, with `BoLo.loc_infinite`), which is what makes it provable at all. `Adequacy.Theorem32` and `Adequacy.Theorem32Printed` run `BoLo.Steps` and `TR3.Steps` from `Adequacy.emptyMem`. The interpreter is a runnable companion. No result of the paper is stated over it, and no lemma relates it to either relation (D8).

## Part IV — Recorded differences

### C14 The three freshness conditions of `∀I-compat`

`BoCa.Fig16.LogRel.allI_compat` ([TR] 6.161, tagged `[variant: …]`) adds three hypotheses, all about the freshness of the binder `'a`:

- `@b` does not mention `'a`.
- No bound of `Δ` mentions `'a`.
- `'a` is free in no live type of `Γ`.

They come from the printed proof on p. 42. *"By Δ-extend, `δ['a↦α] ∈ ⟦Δ, ('a ⊏ @b)⟧`"* holds only if the extension changes neither the bound `@bδ` nor any bound of `Δ`. *"Extend `𝒢⟦Γ⟧δ` with `δ['a↦α]`"* holds only if no live type of `Γ` mentions `'a`. [TR]'s named presentation gives all three by the Barendregt convention. `BoCa.Derives.allI` carries `Δ.find? x = none` (the binder lies outside `dom(Δ)`) and none of the three. `BoCa.Fig16.LogRel.AllISide` bundles them.

All three follow from [TR] p. 2's own `Δ ⊢ T`, which stands on the page where a Barendregt convention would. At a binder outside `dom(Δ)`, a well-scoped `Δ`, a `Δ`-admissible `@b` and a `Δ`-admissible `Γ` give `AllISide` (`BoCa.Fig16.LogRel.allISide_of_scopedB`, through `Lifetime.Life.mentions_false_of_wf`, `Lifetime.LifeCtx.Ok.bound_mentions_false` and `Fig16.LogRel.not_lfree_of_scopedB`, over `BoCa.Ty.scopedB` and `BoCa.Ctx.ScopedB`). The same reading gives the `¬ LFree` conjuncts of `Withbor1Side`, `Withbor2Side`, `Withbor3Side` and `WithloadSide` (`withbor1Side_of_scopedB` … `withloadSide_of_scopedB`).

`BoCa.DerivesWf.allI` carries p. 2's `Δ ⊧ @b` beside `'a ∉ dom(Δ)`. So in `Fig16.LogRel.Typed.fundamental`, the `∀I` node obtains `AllISide` from `allISide_of_scopedB` and passes it to `Fig16.LogRel.Typed.allI_compatX`, and 6.151 needs no freshness hypothesis. Over `Derives` alone, which consumes `Δ ⊢ T` at no constructor (definition row 2.19), the conditions are not supplied. `Fig16.LogRel.witness` is `∅; • ⊢ λ().() : ∀('a ⊏ 'a). 1`, whose bound mentions its own binder, and `Fig16.LogRel.not_everyDerivationInRegime` is refuted at it.

This entry concerns the side conditions of the compatibility lemma, not the rule: the premise `Δ.find? x = none` of `Derives.allI` is discussed with definition row 2.19. A possible fourth condition, `Δ ⊨ @b`, is not needed. By L3, the `∀` clause's bound is a proposition about `@bδ` rather than a connective applied to it, so an undefined `@bδ` empties the quantifier ([TR] p. 4; [CONF] p. 415:12).

### D3 The two printed readings of `↭` inside `wp`

[TR] p. 5 prints `↭` with the guard `✓ρ₁ ∧ ✓ρ₂` (read at 760 dpi): `BoCa.Fig16.ResU.UpdV`. [CONF] Fig. 18b (p. 415:22) prints it unguarded: `BoCa.Fig16.ResU.Upd`. Both are carried. The `wp` row is transcribed from [TR] p. 6 at the guarded relation (`BoCa.Fig16.BoLo.wp`), and `BoCa.Fig16.BoLo.wpU` is the same display at the unguarded one.

Inside `wp` the two readings are the same proposition: `BoCa.Fig16.BoLo.wp_eq_wpU`. Both guards follow from the two `#`s that `wp`'s own body quantifies over. `✓ρ` comes from the frame hypothesis `ρ_f # ρ` (`Fig16.BoLo.hash_valid`). `✓(ρ′ • ρ⁺)` comes from `ρ⁺ # (ρ_f ● ρ′)` through [TR] Lemma 6.11 (`Fig16.ResU.Hash.split`). So every §6.7 rule is a statement about [TR]'s `wp` and [CONF]'s at once.

The two relations still differ away from `wp`. `ResU.Upd.refl` ([TR] 6.47) holds with no hypothesis, while `ResU.UpdV.refl` needs `✓ρ`, because at the guarded reading `✓ρ` is part of the relation. A consumer of `↭` outside `wp` has to choose. The adequacy residue `BoCa.Adequacy.Reclaim` is stated at the guarded `UpdV`, and its discharge `Adequacy.reclaim` spends the guard to obtain `⦇ρ⦈`.

### D4 [TR] 6.66 is stated as printed

[TR] Theorem 6.66 (`Anti Frame`, p. 25) is `BoCa.Fig16.LogRel.wp_M_antiFrame` (alias `TR.lemma_6_66`), at the printed display:

    ℓ ↦ Mut α P̂ ⋆ (∀v. ℓ ↦ v ─⋆ P̂(v) ─⋆ wp(e){∃v. ℓ ↦ v ⋆ P̂(v) ⋆ (ℓ ↦ Mut α P̂ ─⋆ Q̂)})  ⊨  wp(e){Q̂}

The assertion `ℓ ↦ Mut α P̂` occurs twice, once positively (the left conjunct) and once negatively (under the inner `─⋆`). So a variant that replaces it by a narrower cell assertion at both occurrences is not comparable with 6.66 in either direction. An example of such an assertion is one that pins the cell's lifetime to `α` exactly and adds `P̂(v)`'s resource. The narrower assertion strengthens the first occurrence and weakens the second. Only the printed statement is proved here, and it is the statement that 6.174 and 6.176 cite.

### D6 The printed machine and the completed machine

[TR] p. 3 (read at 800 dpi) prints seven `Kont` productions. The reduction box on p. 4 (read at 680 dpi) has eight rules, and its `1↦` fires at the literal `()`. Both are transcribed exactly: `BoCa.TR3.Kont`, `BoCa.TR3.Head` (the schematic `⊕↦` as its two instances), `BoCa.TR3.Step1` and `TR3.Steps`. `BoCa.TR3.wp` is [TR] p. 6's `wp` row over that relation.

The library's machine `BoCa.BoLo.Steps` has the same nine head constructors (`BoLo.Head`, with `BoLo.Head.seq` at `()`) and two further frames, `K; e` and `injᵢ K` (§12.42). The two machines differ in those two frames and nothing else. [TR] p. 1's `Expr` grammar derives `(v₁,v₂)`, `injᵢ v` and `store v` both as values and structurally, and `BoCa.Expr` identifies the two derivations as a paper grammar does, so each is one term and no coercion rule is needed.

**Why the two frames.** Without `injᵢ K`, `inj₁ e` takes no step for any `e` (`TR3.no_step_inj₁`). Without `K; e`, `e₁; e₂` steps only at `e₁ = ()` (`TR3.step_seq_inv`, `TR3.no_step_seq`, `TR3.steps_seq_ne_val`). [TR] p. 4's own `swap ≜ λx.λy. let z = load x; store x y; (x,y)` has that shape. Identifying `v` with the structural production supplies no frame, so the conclusion holds under either reading of the grammar. Each case has a closed witness that [TR] p. 2's judgment types:

- `TR3.stuck_wInj` at `inj₁ (free (alloc ()))`, typed at `1 ⊕ T` by `TR3.derives_wInj`.
- `TR3.stuck_wSeq` at `(free (alloc ())); ()`, typed at `1` by `TR3.derives_wSeq`.

The second witness also shows that, over the printed machine, [CONF] Corollary 3.3's conclusion is not reached (`TR3.corThree_unreachable`). At the level of `wp`, the cost is `TR3.wp_inj₁_false` and `TR3.wp_seq_false`, each refuted at a resource with an admissible frame (`TR3.wp_stuck_false_nonvacuous`).

One reading would supply the sequencing frame without adding one: `e₁; e₂` as sugar for `(λ_.e₂) e₁`, under which the printed `e K` would reach the left operand. We do not adopt it, because [CONF] Fig. 1 prints `e₁; e₂` as its own `Expr` production and [TR] p. 4 prints `1↦` as its own head rule. `λ_.()` is typeable in the system only as `forget`, and only by axiom at `Imm @a T ⊸ 1`, `Mut @a T ⊸ 1` and `Unk ⊸ 1` (`Derives.forgetImmAx`, `forgetMutAx`, `forgetUnkAx`). None of these is the `1 ⊸ T` that a desugared `;` would need.

The primitives need no extra frame. `p` is a value and application is `e₂ e₁`, so `alloc v` and `store ℓ v` are applications, and the box rules fire on them (`TR3.steps_alloc`, `TR3.steps_store`). `store ℓ v` takes one step, which is how 6.145's proof takes it. `store ℓ` alone is [TR] p. 1's `Prim` value `store v` and takes no step.

**What the difference costs.** A larger `Steps` makes `wp` easier to satisfy. `TR3.Steps.toWp` shows that the printed relation is contained in `BoLo.Steps`. `TR3.wp_le_fig16` carries that containment to the two `wp`s, and `TR3.wp_lt_fig16` shows that the entailment is strict. Every §6.7 rule is proved over both machines: 6.135–6.149, both summands of 6.139 included (`TR3.wp_bind` … `TR3.wp_I_forget`). What `wp_le_fig16` buys depends on where `wp` sits in the rule:

- 6.136, 6.137, 6.138, 6.139, 6.140, 6.141, 6.142, 6.143, 6.144 and 6.145 have no `wp` in the antecedent. Each composes with the entailment and so implies its `Fig16.BoLo` counterpart, strictly.
- 6.135, 6.146, 6.147, 6.148 and 6.149 have `wp` in the antecedent, so they strengthen antecedent and consequent together. The two versions are not comparable. Each is the printed statement about a different `↦*`, and both are proved.

[CONF] Theorem 3.2 follows the same pattern (`Adequacy.Theorem32` and `Adequacy.Theorem32Printed`).

### D8 No bridge between the executable interpreter and the heap relations

The executable interpreter (`BoCa.Mem`, `BoCa.step`) is a separate transcription from the relations on `BoCa.BoLo.Heap` (`BoLo.Head`/`BoLo.Steps`, `TR3.Head`/`TR3.Steps`). No lemma relates `Mem` to `Heap`, or `step` to either `Steps`. Nothing in the `wp` development or the adequacy results depends on the interpreter, so the absence of a bridge limits only what the interpreter's runs can be said to witness (W2).

### D9 Frame-rule non-vacuity

This entry records a non-vacuity observation about a frame-rule interface of an earlier carrier. That interface has no counterpart in this repository. Here, [TR] 6.64–6.66 are stated at the printed cell assertions `ℓ ↦ Imm α P̂` and `ℓ ↦ Mut α P̂` (`Fig16.LogRel.wp_I_frame`, `Fig16.LogRel.wp_M_frame`, `Fig16.LogRel.wp_M_antiFrame`), with no intermediate structure whose inhabitation would need to be checked.

### D10 `fin` on `Res_α`: the two strata rows

`BoCa.Fig16.Res` (Fig. 16, strata row 2) carries a finiteness mark that neither document prints at that row. Both documents print row 2's harpoon bare (read at 1600 dpi). The mark comes from row 7, which [TR] marks `Loc ⇀ᶠⁱⁿ Cell`.

Carrying the mark at row 2 is forced rather than assumed:

- Every operation from `▶◀` on is defined on the unstratified `Res`.
- `Mut_α`'s witness is a `Res_β`.
- The flattening walk composes exactly those witnesses with `◐`.

So a `Res_β` must be a `Res`. Without the mark, `@ρ ≜ ⨅_{ψ∈cod(ρ)} @ψ` with `⊓ = max` has no value on an unbounded codomain, and [TR] 6.141's proof chooses `ℓ ∉ ρ_f ● ρ` in one step. The declarations are tagged `[variant: …]` in `Paper/S5_Model/Definitions.lean`. The representation is G1, and the reading of the text is §12.33.

## Part V — Adequacy

### §A.1 Neither document prints a proof of Theorem 3.2 or Corollary 3.3

[CONF] states Theorem 3.2 (Adequacy) and Corollary 3.3 in §3, and neither document prints an argument for either. We checked this as follows:

- [TR]'s §6 has eight subsections: 6.1 Standard Lemmas, 6.2 Non-standard Lemmas, 6.3 Frame and Anti-Frame, 6.4 Standard Entailments, 6.5 Non-standard Entailments, 6.6 Reborrowing Entailments, 6.7 Weakest Precondition Rules, 6.8 Fundamental Property. There is no ninth subsection and no appendix. The last numbered result is Lemma 6.176 (`withswap`-compat), and its proof ends on p. 49, the last page.
- [TR] has four Theorems: 6.64 (`Imm Frame`), 6.65 (`Mut Frame`), 6.66 (`Anti Frame`) and 6.150 (the `↺` rule). None is an adequacy statement, and nothing in [TR] is numbered 3.2 or 3.3. Its §3 is Dynamics.
- A text search of [TR] finds no occurrence of `deq`, `ermin`, `clam`, `clai`, `leak`, `liveness`, `progress` or `safet`. The search was run on both layout and raw text extractions and tolerates ligatures, because [CONF]'s own theorem header extracts as "Adeqacy". Every page of both documents has a full text layer, so no page is an image that the search could miss.
- [CONF] numbers exactly three results: Lemma 3.1, Theorem 3.2 and Corollary 3.3, all in §3. At 600 dpi the two statements are followed immediately by the heading **4 A Semantic Model of Borrowing**. §4 states no numbered result, and §5 is Related Work and Discussion.
- [CONF]'s Data-Availability Statement reads *"Complete definitions and proofs may be found in our supplementary material [37]"*, and reference [37] is `3764117-supplement.pdf` — [TR].

What [CONF] does print about the two results is on p. 415:18: *"Additionally, we must show adequacy of the weakest precondition — that it really does characterize executions that are safe, terminating, and reclaim memory. The next section develops proofs for these properties"*. §4 then develops the model: Figs. 17–19, the flattening, the lowering, `↭` and the `wp` row. One sentence, on p. 415:23, names the conjunct that does the reclamation work:

> Inspired by Charguéraud and Pottier [5], in order to support `forget` on borrows, the post-condition is only required to hold of a fragment `ρ′` of the post-resource, but the discarded fragment `ρ⁺` must not contain any owned cells. This is essential for the memory reclamation component of adequacy (Theorem 3.2), which insists that owned cells are freed rather than forgotten.

So the statements of 3.2 and 3.3 are transcribed, and their proofs are ours, guided by the printed definitions and by that sentence. The route is short because the printed `wp` is a total-correctness row: it already asserts the run, so no termination argument has to be built. At `ρ = ρ_f = ∅`, what remains is a proposition about resources, `BoCa.Adequacy.Reclaim`, and that is where the p. 415:23 conjunct is spent (`Adequacy.reclaim`).

Each result is stated once per machine (W2, D6): `Adequacy.Theorem32`/`Adequacy.theorem32` over `BoLo.Steps`, and `Adequacy.Theorem32Printed`/`Adequacy.theorem32Printed` over `TR3.Steps`. Corollary 3.3 is stated the same way (`Adequacy.Corollary33`, `Adequacy.Corollary33Printed`). Each is stated again at the typed world (`Fig16.LogRel.Typed.theorem32`, `Fig16.LogRel.Typed.corollary33`). `Fig16.LogRel.Typed.adequacy` composes Corollary 3.3 with 6.151. The records in `Paper/CONF/Results.lean` score these rows on their statements alone.

### §A.2a The bare turnstile

Neither document gives `⊨ H`, with nothing to its left, a defining row. Three printed things fix it together, and they agree:

- [CONF] p. 415:23's *"an unrestricted modality `! P` for propositions that hold with the empty resource"*.
- Fig. 19's `{P} e {Q̂} ≜ !(P ─⋆ wp(e){Q̂})`.
- p. 415:13's `P ⊨ wp(e){Q̂} ⇔ ⊨ {P} e {Q̂}`.

With [TR] p. 6's `emp ≜ ⌜⊤⌝` and `⌜P_Meta⌝(ρ) ≜ ρ = ∅ ∧ P_Meta`, that equivalence holds on one reading of the bare `⊨`: *holds of `∅`*. `BoCa.Fig16.LogRel.Sem` reads `Δ; Γ ⊨ e : T` the same way, and `BoCa.Fig16.LogRel.sem_iff` is the unfolding. So Theorem 3.2's antecedent `⊨ wp(e){⌜P̂⌝}` is `wp(e){⌜P̂⌝}(∅)`, which is how `Adequacy.Theorem32` states it. This is the reading the development already uses, not a further convention.

