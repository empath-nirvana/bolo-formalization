READING = """
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
"""

banners["Paper/S1_Syntax/Definitions"] = """/-!
# [TR] §1 Syntax  (physical p. 1)

    Var     ∋ x, y, …
    Loc     ∋ ℓ
    Val     ∋ v  ::= () ∣ (v₁, v₂) ∣ inj₁ v ∣ inj₂ v ∣ λx.e ∣ Λ.e ∣ ℓ ∣ p
    Prim    ∋ p  ::= alloc ∣ free ∣ load ∣ store ∣ store v
    Expr    ∋ e  ::= x ∣ v ∣ (e₁, e₂) ∣ inj₁ e ∣ inj₂ e ∣ e₁ ; e₂ ∣ let (x, y) = e₁ in e₂
                   ∣ case e {inj₁ x.e₁ ∣ inj₂ y.e₂} ∣ e₂ e₁
    LifeVar ∋ 'a, 'b, …
    Life    ∋ @a, @b, … ::= ' ∣ ⊤ ∣ @a ⊔ @b ∣ @a ⊓ @b
    LifeCtx ∋ Δ  : LifeVar ⇀ Life
    Type    ∋ T  ::= 1 ∣ T₁ ⊕ T₂ ∣ T₁ ⊗ T₂ ∣ T₁ ⊸ T₂ ∣ Ref T ∣ [@a] T
                   ∣ Imm @a T ∣ Mut @a T ∣ ∀ 'a ⊏ @b. T ∣ Unk

`e ::= v` makes values a subset of expressions, and they are one here: a single
`Expr`, the predicate `IsVal` picking out the value forms, and `Val` the subtype.
`Λ.e` is `λ_.e` (row 1.8) and `store v` is `store` applied to `v` (row 1.15).
""" + READING + "-/\n"

banners["Paper/S2_Statics/Definitions"] = """/-!
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
""" + READING + "-/\n"

banners["Paper/S3_Dynamics/Definitions"] = """/-!
# [TR] §3 Dynamics  (physical pp. 3–4)

    Kont ∋ K ::= [ ] ∣ (K, e) ∣ (v, K) ∣ let (x, y) = K in e ∣ case K {inj₁ x.e₁ ∣ inj₂ y.e₂}
               ∣ e K ∣ K v
    Mem  ∋ µ : Loc ⇀ Val

the step `(µ, e) → (µ′, e′)` closed under `K[−]` from the head reduction
`(µ, e) ↦ (µ′, e′)` (rules 1↦, ⊗↦, ⊕↦, ⊸↦, alloc↦, free↦, load↦, store↦), and the
derived forms (p. 4)

    swap     ≜ λx.λy.let z = load x; store x y; (x, y)
    copy     ≜ λx.(x, x)
    forget   ≜ λx.()
    withbor  ≜ λx.λf.(x, f x)
    withload ≜ λx.λf.(x, f (load x))
    withswap ≜ λx.λf.let (y, z) = f (load x); store x y; (x, z)

Two machines are here.  `TR3.Kont`/`TR3.Head`/`TR3.Step1` is the printed one,
seven frames and eight head rules.  `BoLo.Kont`/`BoLo.Head`/`BoLo.Step1` adds the
frames `K; e`, `inj₁ K` and `inj₂ K` (rows 3.30, 3.31, `[repair]`): without them
`inj₁ (free (alloc ()))` and `free (alloc ()); ()`, closed terms `[TR]` p. 2
types, are stuck.  `[TR]` p. 6's `wp` (row 5.33) runs the second.
""" + READING + "-/\n"

banners["Paper/S4_LogicalRelation/Definitions"] = """/-!
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
`wpTS`, `gDenX`, `SemX` (source `docs/boca-rules.md` §12.69–§12.72): an `Imm`
payload is read at its observable view, borrow payloads are stratified by a
record list, the `Imm` clause carries the type the world recorded at the cell,
`⊸`/`∀` are Kripke over the record list, and `wp` ranges over the tagged typed
worlds `TW` that the printed proofs' operations produce.  `[TR]` 6.151 holds at
the repaired judgment with no hypothesis; at the literal one it needs
`WithloadEscrow`, which the configuration `Fig16.LogRel.ViewWitness` refuses
(source `BoCa/ViewWitness.lean`).
Each row below records both readings: its comment gives the printed clause,
the adjudication, and what the repair changes.  The repaired declarations are
not in this file.  They are in `Support/TypedWorld/`, which imports it:
`Records.lean` (frame records, positions, coherence, the Kripke order `Ext`),
`World.lean` (value shapes `vShape`, the typed worlds `TW`, tagging, and
`wpTS`, row 5.33's repair) and `Relation.lean` (`vX`, the repaired `Imm`/`Mut`
points-to `ptoImmS`/`ptoMutS`, and `gDenX`, `SemX`).  They come after this file
because the worlds are defined through value shapes, which read lifetimes
through this section's `atLife` (row 4.15).
""" + READING + "-/\n"

banners["Paper/S5_Model/Definitions"] = """/-!
# [TR] §5 Model  (physical pp. 4–6)

The stratified carrier (Fig. 16 rows 1–5)

    SProp_α ≜ Res_α → ℙ          Res_α ≜ Loc ⇀ Cell_α
    Cell_α  ≜ own(Val) + imm(Imm_α) + mut(Mut_α)
    Imm_α   ≜ {(ᾱ : ℘⁺(Life), v : Val, ρ : Res_⊔ᾱ) ∣ ⊓ᾱ ⊐ α}
    Mut_α   ≜ {(β ⊐ α, v : Val, ρ : Res_β, P̂ : Val → SProp_β) ∣ P̂(v)(ρ)}

the unstratified one (rows 6–9)

    P ∈ SProp ≜ Res → ℙ     ρ ∈ Res ≜ Loc ⇀ᶠⁱⁿ Cell     ψ ∈ Cell ≜ ⋃_α Cell_α
    α, β ∈ Life ≜ (ℕ, ⊑ ≜ >, ⊔ ≜ min, ⊓ ≜ max, ⊤ ≜ 0)

the operations of p. 5 — `@ψ`, `@ρ`, `↓α`, `▸◂`, `▷◁`, `●`, `○`, `ρ₁ ▸◁ ρ₂`,
`ρ₁ ◐ ρ₂`, `ρ∣ι`, `ex(ρ)_◐`, `ag(ρ)_◐`, `⦇ρ⦈ ≜ ex(ρ)_● ● ag(ρ)`, `✓ρ ≜ ⦇ρ⦈ defined`,
`⟦ψ⟧`, `⟦ρ⟧`, `ρ₁ # ρ₂ ≜ ρ₁ ▸◂ ρ₂ ∧ ✓(ρ₁ ● ρ₂)`, `ρ₁ ↭ ρ₂`, `reb_α(ρ)` — and the
propositions of p. 6:

    ℓ ↦ v          (ρ) ≜ ρ = ℓ ↦ own(v)
    ℓ ↦ Imm α P̂    (ρ) ≜ ∃ β̄, v, ρ′. ρ = ℓ ↦ imm(β̄, v, ρ′) ∧ P̂(v)(ρ′) ∧ α ⊑ ⊔β̄
    ℓ ↦ Mut α P̂    (ρ) ≜ ∃ β ⊒ α, v, ρ′. ρ = ℓ ↦ mut(β, v, ρ′, P̂)
    [α] P          (ρ) ≜ P(ρ) ∧ @ρ ⊐ α
    wp (e) {Q̂}     (ρ) ≜ ∀ ρ_f # ρ. ∃ ρ′ # ρ_f, ρ⁺ # (ρ_f ● ρ′), v.
                           (⟦ρ_f ● ρ⟧, e) →* (⟦ρ_f ● ρ′ ● ρ⁺⟧, v) ∧ ρ ↭ ρ′ ● ρ⁺ ∧ ρ⁺∣own = ∅ ∧ Q̂(v)(ρ′)
    ⌜P_Meta⌝ (ρ) ≜ ρ = ∅ ∧ P_Meta     P₁ ⋆ P₂ (ρ) ≜ ∃ ρ₁, ρ₂. ρ = ρ₁ ● ρ₂ ∧ P₁(ρ₁) ∧ P₂(ρ₂)
    P₁ ─⋆ P₂ (ρ) ≜ ∀ ρ₁, ρ₂. P₁(ρ₁) ⇒ ρ ● ρ₁ = ρ₂ ⇒ P₂(ρ₂)     emp ≜ ⌜⊤⌝     !P ≜ emp ∧ P
    ⊤, ⊥, ∧, ∨, ⇒, ∀ P̂, ∃ P̂ pointwise      И P̂ ≜ ∃ β. ∀ α ⊏ β. [α] P̂(α)
    ↺_α P (ρ) ≜ ∃ ρ′ ∈ reb_α(ρ). P(ρ′)

Partial operations (`●`, `○`, the walks `ex`/`ag`, `⦇−⦈`, `⟦−⟧`) are graphs —
relations `R a b c` read "`a ◐ b` is defined and equals `c`" — rather than total
functions with a default.  `Res` is finite at every depth (`PMap`), and the
stratification is recovered from the unstratified carrier as membership in a
stratum (`InStratum`, row 5.48).  Two rows here are `[repair]`s adjudicated in
source `docs/boca-rules.md` §12.67: `ℓ ↦ Imm α P̂` bounds `α` by `⊓β̄` (row 5.30)
and `reb_α`'s `imm` clause keeps a nonempty subset of the lifetimes (row 5.28).
""" + READING + "-/\n"

banners["Paper/S6_2_NonStandardLemmas/Definitions"] = """/-!
# [TR] §6.2 Non-standard Lemmas — the three printed Definitions  (pp. 9, 13, 17)

`[TR]` numbers its Definitions in a sequence of their own; all three fall in §6.2.

* **Definition 6.1** (p. 9).  Let `⦇ρ⦈_○ ≔ ag(ρ) ○ ex(ρ)_○`.
* **Definition 6.2** (p. 13).  Let `ψ ∼ ψ′ ≔ (ψ = mut(α, _, _, P̂) ∧ ψ′ = mut(α, _, _, P̂))
  ∨ (ψ = ψ′ = imm(α, v, ρ))`.
* **Definition 6.3** (p. 17).  `ρ ⊟ ρ′ ≜ ρ∣own,mut ● ρ″` where
  - `ρ′∣own,mut = ∅`;
  - `ρ″ ≤ ρ∣imm`;
  - if `ℓ ∈ dom(ρ∣imm) ∖ dom(ρ′)` then `ℓ ∈ dom(ρ″)`;
  - if `ℓ ∈ dom(ρ∣imm) ∩ dom(ρ′)` and `ρ(ℓ) = imm(α, ρᵢ, v)` and `ρ′(ℓ) = imm(β, ρᵢ, v)` then
    if `α ∖ β = ∅`, then `ℓ ∉ ρ″`; if `α ∖ β ≠ ∅`, then `ρ′(ℓ) = imm(α ∖ β, ρᵢ, v)`.

  *"Intuitively, `ρ ⊟ ρ′` is `ρ` without the immutable borrows in `ρ′`.  But since
  immutable borrows can alias at the same location, 'without' means removing the
  lifetimes of borrows from `ρ′`, but keeping the lifetimes only in `ρ`."*

`ResU.SubKeep` is Definition 6.3 read with that sentence, which fixes the cell
the third bullet leaves free and makes `⊟` a term (source `docs/boca-rules.md`
§12.64); `ResU.Sub` is the bullets alone, kept for comparison.
""" + READING + "-/\n"

banners["Paper/LiteralReadings/S4_LogicalRelation"] = """/-!
# Literal readings — [TR] §4

Declarations that measure a printed definition read literally, where the
library uses a repaired one.  They are kept so the adjudication can be checked,
and nothing in the paper tree depends on them.

* `MutImmGap` (row 4.17): the cell and lifetime set at which, under the literal
  `α ⊑ ⊔β̄` of `ℓ ↦ Imm α P̂`, `𝒱⟦Mut @a (Imm @b 1)⟧` is empty.
""" + READING + "-/\n"

SUPPORT_BANNER = """/-!
# Support — {topic}

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
{what}.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/
"""
SUPPORT_WHAT = {
 "Support/Syntax/Terms": "value inversion lemmas, shifting and substitution on de Bruijn terms (single and parallel), and the names of `[TR]` p. 3's derived forms and of the first de Bruijn variables",
 "Support/Lifetimes/Terms": "lifetime terms and contexts: the order and lattice operations on `Life`, lookup and extension of contexts, well-formedness, fresh variables and printing",
 "Support/Lifetimes/Substitution": "substitution of lifetimes into lifetime terms and types, with the capture and range bounds it needs",
 "Support/Lifetimes/Interpretation": "extension of a lifetime interpretation `δ` by one variable",
 "Support/Statics/Contexts": "typing contexts as lists of slots with a liveness bit, and their splitting",
 "Support/Dynamics/Machine": "the machines' plumbing: frame composition and the reflexive-transitive closure `→*`",
 "Support/Dynamics/Interpreter": "an executable interpreter — memories as association lists, a step function, a fuelled run — which `[TR]` does not print (it gives a relation) and which no result of the paper uses",
 "Support/Model/Prelude": "the carrier's prelude: `min`/`max` arithmetic, the finite-domain predicate, casts, bundled bijections, and the index `ι ∈ {own, imm, mut}` of `ρ∣ι`",
 "Support/Model/Notation": "the notation of the propositions of `[TR]` p. 6 (`⌜−⌝`, `⋆`, `─⋆`, `!`) and of `↓α`",
 "Support/Model/Cells": "facts about cells: the lifetime set of an `imm` cell, extensionality of `mut` cells, the constructor set of `Cell`, and the difference of lifetime sets",
 "Support/LogicalRelation/ClosingSubstitutions": "closing substitutions `γ(e)`, free lifetime variables of a type, and the empty resource in every stratum",
 "Support/LogicalRelation/ClosedJudgment": "the judgment `Δ; Γ ⊨ e : T` at the empty resource",
 "Support/TypedWorld/Records": "the records the typed world keeps: frame records and their lineages, root, chain and `Mut` positions, coherence of a record with the world, tags, and the Kripke order `Ext`",
 "Support/TypedWorld/World": "the typed worlds: value shapes `vShape`, the family `TW` of configurations the printed proofs' operations produce, tagging, and `[TR]` p. 6's `wp` over them (`wpTS`, row 5.33's repair)",
 "Support/TypedWorld/Relation": "the repaired logical relation of `[TR]` §4: `vX`, the `Imm`/`Mut` points-to at a record list, the context relation `gDenX` and the judgment `SemX`",
}

RESULTS_READING = """
**How this file reads.**  The numbered results of the subsection, in printed order as
far as Lean's definition-before-use allows.  Each opens with a record:

* the result's number, page and the source inventory's status (`proved`, `proved*`,
  `variant`; source `docs/paper-inventory.md`);
* the printed statement, quoted, with the extraction's garbled symbols restored;
* the printed proof, transcribed compactly and in its own order, citing the lemmas it
  cites;
* the Lean declaration, moved from the source with its name, statement and proof
  unchanged (its docstring carries the source's tag and its account of the proof),
  and the numbered alias `TR.lemma_6_N` declared after it;
* the inventory row's note.

A result whose declaration an earlier subsection's printed proof needs is declared
in that subsection's file, under a heading saying so; its record and alias stay
here.  A run of declarations the paper does not print, placed in this file only
because a result below needs it and it needs a result above, is marked
`[about ours]` and names the result it serves.  Citations of `docs/…` and `BoCa/…`
are to the source repository (`borrow_lang` at `970a9d0`).
"""

banners["Paper/S6_1_StandardLemmas/Lemmas"] = """/-!
# [TR] §6.1 Standard Lemmas  (physical pp. 6–8), Lemmas 6.1–6.15

*"There's no strict definition, but lemmas feel 'standard' when their statement
doesn't unfold resources or definitions, and don't include any particularly
unusual/custom operations."*

The algebra of the two compositions (6.1–6.4, 6.9, 6.12–6.14), compatibility
`#` (6.5, 6.6, 6.11, 6.15), and lowering `⟦−⟧` (6.7, 6.8) and validity `✓` (6.10).
`[TR]` writes `▸◁` and `◐` for "either of `▸◂`/`▷◁`" and "either of `●`/`○`"; Lean
states such a lemma once over a schema and discharges it at both.

The printed proofs of 6.7, 6.10 and 6.15 cite §6.2's walk-splitting lemmas 6.18 and
6.20, and with them 6.30, 6.31 and 6.36; those five are declared in this file,
ahead of 6.7, and so are the definition-row theorems `BigComp.perm` (row 5.56) and
two of row 5.67's, which the same proofs use.
""" + RESULTS_READING + "-/\n"

banners["Paper/S6_2_NonStandardLemmas/Lemmas"] = """/-!
# [TR] §6.2 Non-standard Lemmas  (physical pp. 8–22), Lemmas 6.16–6.63

The flattening `⦇ρ⦈` and its walks `ex`, `ag` (6.16–6.20, 6.30–6.37), the surgery
lemmas that trade a `mut` or `imm` cell for `ρ_v ● ℓ ↦ own(v)` (6.21–6.29, 6.34,
6.38, 6.39), cell-level facts (6.40–6.45), the update relation `↭` (6.46–6.51),
reborrowing (6.52–6.59, 6.61), and the logical relation's outlives lemmas (6.60,
6.62, 6.63).  Definitions 6.1–6.3, printed on pp. 9, 13 and 17, are in this
directory's `Definitions.lean`; the theorems about Definition 6.2's `∼` are in its
`Remarks.lean`.
""" + RESULTS_READING + "-/\n"

REMARKS_READING = """
These are theorems about printed definitions — rows of the source's
`docs/definition-inventory.md` whose Lean is a theorem — whose proofs use results
of `[TR]` §6, so they cannot sit with the definitions.  Each carries the row's
number, printed form, page, tag and note.  A row's theorem that a §6 result's Lean
needs is declared in that result's file, and the row here says where.
"""

banners["Paper/S4_LogicalRelation/Remarks"] = """/-!
# [TR] §4 Logical Relation — remarks on the definitions

Row 4.16's two directions between the `Mut` clause and `Supported`, and row
4.18's `sem_iff` (the judgment at `∅` is the judgment).
""" + REMARKS_READING + "-/\n"

banners["Paper/S5_Model/Remarks"] = """/-!
# [TR] §5 Model — remarks on the definitions

Row 5.62's `wp_eq_wpU` (the two printed readings of `↭` give the same `wp`),
row 5.56's `BigComp.perm` (`⨀` is order-independent), and row 5.67's theorems
(`[CONF]`'s prose characterisation of `✓`).
""" + REMARKS_READING + "-/\n"

banners["Paper/S6_2_NonStandardLemmas/Remarks"] = """/-!
# [TR] §6.2 — remarks on Definition 6.2

`ψ ∼ ψ′` (row 5.65): transitivity, and `upd_iff_sim`, the theorem that `[CONF]`
Fig. 18b's two clauses of `↭` and `[TR]` §6's "same domain, `∼` pointwise" form are
the same relation.  Lemmas 6.39 and 6.59 read `↭` through it.
""" + REMARKS_READING + "-/\n"

SUPPORT_WHAT.update({
 "Support/Model/Lifetimes": "facts about lifetimes and nonempty lifetime sets: commutativity, idempotence and associativity of `⊓` and `∪`, extensionality, extremal members and monotonicity of the meet",
 "Support/Model/CellFacts": "facts about the cell constructors: injectivity and distinctness of `own`/`imm`/`mut`, the lifetime of a `mut` cell, and the stored predicate",
 "Support/Model/Composition": "the cell- and resource-level compositions `●` and `○` and compatibilities `▶◀` and `⋈` as graphs: functionality, symmetry, the specification of each clause, erasure and witnesses",
 "Support/Model/Singletons": "restriction `ρ∣ι`, singleton resources `ℓ ↦ ψ`, the order `ρ ≤ ρ′`, and the walks and restrictions of singletons",
 "Support/Model/Walks": "the exclusive walk `ex(ρ)_◐` and `imm`-free resources, and the functionality of the walks `ex`, `ag` and of `⦇−⦈`, `⟦−⟧` (the witness families they range over)",
 "Support/Model/RelaxedWalks": "`ex(ρ)_○` has no `imm` cell, `⦇ρ⦈_○` is functional, and `○` never makes an `imm` cell from two non-`imm` ones",
 "Support/Model/Subtraction": "Definition 6.3's `⊟`: lifetime-set difference, and `⊟` inhabited, total and a term at `SubKeep`",
 "Support/Model/Algebra": "the associativity and commutativity machinery behind Lemmas 6.1–6.4: cell-level associativity of `○` clause by clause, the laws of the schema `◐`, and the iterated composition `⨀` up to permutation",
 "Support/Model/AlgebraInstances": "Lemmas 6.2 and 6.3 at `○`, Lemmas 6.41 and 6.42 as one statement, and the lifetime of a `●` composite",
 "Support/Model/WalkSplitting": "the pieces of Lemmas 6.18 and 6.20: the sites of a composite, the witness families of each walk and how they split across `●`, and inclusion–exclusion over shared `imm` cells",
 "Support/Model/Flattening": "validity and lowering: the pointwise facts behind Lemmas 6.7, 6.10 and 6.30, and the union of two memories",
 "Support/Model/Compatibility": "cell-level compatibility read off tags, values and witnesses, and `○` at an `imm` cell",
 "Support/Model/FlatteningCells": "the cells of a flattening: a cell of `ρ` reappears in `⦇ρ⦈`, the walks' witnesses lie beneath their cells, and the order `≤` on resources",
 "Support/Model/Update": "the update relation `↭` at both printed readings, `reb_α` read at one location, and the form `[TR]` §6 unfolds `↭` to",
 "Support/Model/UpdateFrame": "the pointwise route through Lemma 6.48: `⦇−⦈` of a `○`-composite and the cell-level update",
 "Support/Model/Propositions": "the propositions of `[TR]` p. 6 as used by §6.2: entailment, `emp`, the outlives relation `@ρ ⊐ α` and the `wp` row at the unguarded `↭`",
 "Support/Model/Outlives": "`@ρ ⊐ α` across `⦇−⦈`, the walks and `↭` (the steps Lemma 6.50's one sentence elides), and *“there are no borrows at any lifetime shorter than `α`”*",
 "Support/Model/Ancestors": "the immutable ancestor of a cell of the aliasable walk: every cell of `ag(ρ)` sits beneath an `imm` cell, carried across `↭` — the step of Lemma 6.48's printed proof that 6.59 reaches for",
 "Support/Model/Reborrow": "`reb_α` at one location, the frame read from `✓` alone, and the cells of a reborrow",
 "Support/Model/ReborrowFrame": "the steps of Lemmas 6.53–6.55 and 6.61 that the printed proofs name",
 "Support/Model/Restriction": "`ρ∣dom(σ)` and `ρ/dom(σ)`, the restriction `[TR]` §6 uses and neither document defines",
 "Support/Model/ReborrowLowering": "the steps of Lemmas 6.56–6.58: absorption at `○` and the domains of reborrows",
 "Support/Model/Surgery": "the steps of the surgery lemmas 6.21–6.29, 6.34, 6.38 and 6.39: the normal forms of `⦇ρ ● ℓ ↦ own(v) ● ρ_v⦈` and `⦇ρ ● ℓ ↦ imm(α, v, ρ_v)⦈`, and the `mut` cell against `ρ_v ● ℓ ↦ own(v)`",
 "Support/Model/ClosingSentence": "Lemma 6.59's closing sentence, clause by clause: the reborrowed location, the attribution of cells to `ρᵢ`, and the case off `dom(ρ_reb)`",
 "Support/LogicalRelation/Facts": "`⌜p⌝ ⋆ P` and the context relation read pointwise",
})

TYPED_NOTE = """
**The typed world.**  A result whose statement the source also proves at the typed
world — `wpTS` (row 5.33's repair) or the repaired relation `𝒱X`/`vShape` (rows
4.4–4.14's) — names that declaration in its record under *Typed-world version*; the
declaration itself is in `Support/TypedWorld/`, where a heading points back here.
"""

banners["Paper/S6_3_FrameAndAntiFrame/Lemmas"] = """/-!
# [TR] §6.3 Frame and Anti-Frame  (physical pp. 22–27), Theorems 6.64–6.66

The three frame rules at the printed `wp` (`[TR]` p. 6): Imm Frame (6.64), Mut Frame
(6.65) and Anti Frame (6.66).  Each proof builds a *"fictional"* borrow cell —
`ℓ ↦ imm({α}, v, ρ_P̂(v))` or `ℓ ↦ mut(α, v, ρ_P̂(v), P̂)` — in place of
`ℓ ↦ own(v) ● ρ_P̂(v)`, runs `e` against it, and trades it back with the surgery
lemmas of §6.2 (6.24–6.29, 6.34, 6.38, 6.39).  The printed proofs of 6.64 and 6.65
open with Lemma 6.112 (`Иf`, §6.5), which is therefore declared in this file, ahead of
its subsection.
""" + RESULTS_READING + TYPED_NOTE + "-/\n"

banners["Paper/S6_4_StandardEntailments/Lemmas"] = """/-!
# [TR] §6.4 Standard Entailments  (physical pp. 27–29), Lemmas 6.67–6.95

The sequent rules of the propositions of `[TR]` p. 6 that do not unfold the
carrier: `⊨` reflexive and transitive (6.67, 6.68), the connectives `⊤ ⊥ ∧ ∨ ⇒ ∀ ∃`
(6.69–6.80), `⌜−⌝` (6.81, 6.82), `!` (6.83–6.89), `⋆` and `–⋆` (6.90–6.94), and
exclusivity of `ℓ ↦ v` (6.95).  Each is printed with its name, which is the second
alias `TR.«name»`; a rule the print states schematically in `i ∈ {1, 2}` (6.72, 6.73)
is two declarations with aliases `TR.lemma_6_N_i`.
""" + RESULTS_READING + "-/\n"

banners["Paper/S6_5_NonStandardEntailments/Lemmas"] = """/-!
# [TR] §6.5 Non-standard Entailments  (physical pp. 29–32), Lemmas 6.96–6.119

The rules of the lifetime modality `[α]` (6.96–6.107), of the freshness quantifier
`Иα` (6.108–6.112), of immutable points-to `ℓ ↦I_α P̂` (6.113–6.116) and of mutable
points-to `ℓ ↦M_α P̂` (6.117–6.119).  Lemma 6.112 is declared in §6.3's file, whose
printed proofs open with it; its record and aliases are here.
""" + RESULTS_READING + TYPED_NOTE + "-/\n"

banners["Paper/S6_6_ReborrowingEntailments/Lemmas"] = """/-!
# [TR] §6.6 Reborrowing Entailments  (physical pp. 32–35), Lemmas 6.120–6.134

The rules of the reborrowing modality `↺_α` (6.120–6.130), and the three lemmas that
carry the logical relation through it: `↺V₁` (6.131, by induction on the type),
`↺V₂` (6.132) and `↺V₃` (6.133), and 6.134, which 6.175 applies.
""" + RESULTS_READING + TYPED_NOTE + "-/\n"

LITERAL_READING = """
**How this file reads.**  Each run opens with the result it measures and says where
that result's record is.  The declarations are the source's, with their tags; a
`[about ours: …]` tag names what is measured.  Nothing in the paper tree depends on
this file.
"""

banners["Paper/LiteralReadings/S6_4_StandardEntailments"] = """/-!
# Literal readings — [TR] §6.4

Measurements of §6.4's rules where the Lean adds a premise the printed statement
omits and the printed proof uses:

* 6.84 (`!l`): `bang_L_needs_premise`, the premise `P ⊨ Q` checked at the values
  where dropping it leaves `!P ⊨ Q` standing alone;
* 6.88 (`!∀`): `bang_all_needs_nonempty`, the index type the printed proof's
  *"Suppose `X ≠ ∅`"* excludes.
""" + LITERAL_READING + "-/\n"

banners["Paper/LiteralReadings/S6_5_NonStandardEntailments"] = """/-!
# Literal readings — [TR] §6.5

* 6.102 (`[]∀`): `box_all_needs_nonempty`, the empty index type at a resource that
  holds a borrow, which the printed proof's *"Suppose `X ≠ ∅`"* excludes;
* 6.115 (`I-ag`): `not_iAgreeAtJoin`, the printed index `α ⊔ β` of the conclusion
  measured against the cells `{1}` and `{2}` under row 5.30's `α ⊑ ⊔β̄`.
""" + LITERAL_READING + "-/\n"

banners["Paper/LiteralReadings/S6_6_ReborrowingEntailments"] = """/-!
# Literal readings — [TR] §6.6

* 6.130: `reborrow_emp_outside_stratum`, a resource outside `Res_α` against
  `↺_α emp` — the hypothesis the Lean adds is not free;
* 6.131 (`↺V₁`): `RefPrintedChainResidual`, what the `Ref` bullet's printed chain
  leaves at our objects, recorded as a `def … : Prop` and not derived; no
  obstruction to it is verified.
""" + LITERAL_READING + "-/\n"

SUPPORT_WHAT.update({
 "Support/Model/Entailments": "what §6.5–§6.6's entailments need beyond the propositions: `⫤⊨` reflexive and extensional, a `●`-factor of a reborrowed `imm` cell and the clauses that admit it, `reb_α` at `∅` and its outlives bound, and the join-indexed conclusion 6.115's literal reading measures",
 "Support/Model/FrameSurgery": "the swaps §6.3's frame rules spend at both ends of the run: `ℓ ↦ own(v) ● ρ_P̂(v)` against the `mut` or `imm` cell that borrows it, under a frame, lowered and validated",
 "Support/Model/Strata": "every resource lies in some stratum: `Res = ⋃_α Res_α`",
 "Support/Model/Empty": "the walks and restrictions of the empty resource",
 "Support/TypedWorld/Images": "the typed world's first layer (source `BoCa/TypedImage.lean`): composition read cell by cell, walks through an escrow, the `immFrame` and `alloc` steps, roots and `Ref` chains, and typed reborrow images",
 "Support/TypedWorld/Invariant": "the family `TW` and its invariant (source `BoCa/TypedWorld.lean`): `mut` cells at any depth, `Mut` positions, coherence, sub-records and lineages, and preservation of the invariant by every step",
 "Support/TypedWorld/Wp": "stratified record lists and `wp` at a tagged typed world (source `BoCa/TypedWp.lean`): relevance, the Kripke order, the stratified `Mut` clause, tags, and the frame steps that only regroup",
 "Support/TypedWorld/RelationFacts": "the repaired relation `𝒱X` read at substitutions (source `BoCa/TypedRel.lean`): monotonicity, the `imm` cell at the observable view, reading, writing and making a `mut` cell, 6.60 at `𝒱X`, congruence in `δ`, and the choosers' inputs",
 "Support/TypedWorld/FrameRules": "`[TR]` Theorems 6.64, 6.65 and 6.66 at `wpTS`, with the record list carried",
 "Support/TypedWorld/ReborrowShapes": "`[TR]` Lemmas 6.131 and 6.132 at the shape relation `vShape`",
})

banners["Paper/S6_7_WeakestPreconditionRules/Lemmas"] = """/-!
# [TR] §6.7 Weakest Precondition Rules  (physical pp. 35–40), Lemmas 6.135–6.150

The rules of `wp` (`[TR]` p. 6, row 5.33): `wp-bind` (6.135), `wp-val` (6.136), the
head steps `wp1`, `wp⊗`, `wp⊕`, `wp⊸` (6.137–6.140), the memory rules `wp-alloc`,
`wp-free`, `wp-load`, `wp-load-I`, `wp-store` (6.141–6.145), `wp-ramify` (6.146),
`wp[]` (6.147), the two forget rules (6.148, 6.149) and the reborrowing rule
`↺ rule` (6.150).

**Two machines.**  The library's `wp` runs the machine of `[TR]` §3 with the two
frames rows 3.30 and 3.31 add (`Paper/S3_Dynamics/Definitions.lean` records the
repair); `TR3.wp` (`Support/Dynamics/PrintedWp.lean`) runs `[TR]` §3's printed
machine, at its seven printed frames.  Each rule's re-proof over the printed
machine, `TR3.wp_…`, sits beside the rule (6.150 has none), and what the printed
machine costs at its stuck forms — `inj₁ e` and `e₁; e₂` with no frame to reduce
under — is measured in `Paper/LiteralReadings/S6_7_WeakestPreconditionRules.lean`.
""" + RESULTS_READING + TYPED_NOTE + "-/\n"

banners["Paper/LiteralReadings/S6_7_WeakestPreconditionRules"] = """/-!
# Literal readings — [TR] §6.7

* 6.135 (`wp-bind`), over `[TR]` §3's printed machine: the closed, well-typed terms
  `inj₁ (free (alloc ()))` and `free (alloc ()); ()` are stuck there
  (`stuck_wInj`, `stuck_wSeq`), `TR3.wp` is false at such a term
  (`wp_inj₁_false`, `wp_seq_false`, with `wp_stuck_false_nonvacuous`), and
  `TR3.wp` is strictly below the library's `wp` (`wp_lt_fig16`);
* 6.150 (`↺ rule`): `DefectB.wp_reborrow_unreconciled_at_split_view`, the
  entailment written without the hypothesis `RebEscrow`, measured at a configuration
  built in `BoCa/DefectB.lean` (moved here with it), and `defectB_not_rebEscrow`,
  that configuration outside `RebEscrow` — the two stand together.
""" + LITERAL_READING + "-/\n"

banners["Paper/LiteralReadings/S6_6_ReborrowingEntailments"] = banners["Paper/LiteralReadings/S6_6_ReborrowingEntailments"].replace(
"""* 6.130: `reborrow_emp_outside_stratum`, a resource outside `Res_α` against
  `↺_α emp` — the hypothesis the Lean adds is not free;""",
"""* 6.130: `reborrow_emp_outside_stratum`, a resource outside `Res_α` against
  `↺_α emp` — the hypothesis the Lean adds is not free — at the resource
  `RebExample` builds;""")

SUPPORT_WHAT.update({
 "Support/Dynamics/Machine": "the machines' plumbing: frame composition and the reflexive-transitive closure `→*` for both machines, and for `[TR]` §3's printed machine the inversion of its steps at `inj₁ e` and `e₁; e₂`, the saturated primitives, and the closed terms `alloc ()`, `free (alloc ())`, `inj₁ (free (alloc ()))` and `free (alloc ()); ()`",
 "Support/Dynamics/PrintedWp": "`[TR]` p. 6's `wp` over `[TR]` §3's printed machine (`TR3.wp`), and the `∀`-wand `wp-ramify` reads",
 "Support/Model/ReborrowRule": "what `[TR]` 6.150 names and does not prove: the hypothesis `RebEscrow` (6.55's two inputs at the reborrows `↺_β P̂` names), a lifetime below two given ones, and `ρ⁺|own = ∅` through the pieces of `ρᵢ ● ρ⁺′`",
 "Support/Model/SubtractionKeep": "Lemma 6.52 at `SubKeep`, the form 6.150 spends",
 "Support/Model/UpdateSymmetry": "`↭` is symmetric, and `ρ ↭ ρ` read off validity",
 "Support/TypedWorld/Reborrow": "`[TR]` Theorem 6.150 at `wpTS` (source `BoCa/TypedReborrow.lean`): the chooser `RebChooseTW` that replaces `RebEscrow`, and the rule",
})
