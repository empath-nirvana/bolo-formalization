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
 "Support/Syntax": "substitution and shifting on de Bruijn terms, value inversion lemmas, and the pretty names of `[TR]` p. 3's derived forms",
 "Support/Lifetimes/AfterS1": "lifetime-syntax plumbing: lookup, extension, printing, occurrence and well-formedness of `Life` terms",
 "Support/Lifetimes/AfterS2": "lifetime-substitution plumbing used after the statics",
 "Support/Statics/Base": "context plumbing for the typing judgment",
 "Support/Statics/AfterS4": "facts about the statics stated through the logical relation",
 "Support/Dynamics/Machine": "the machines' plumbing: frame composition, the reflexive-transitive closure `→*`, and heap deletion",
 "Support/Dynamics/Interpreter": "an executable interpreter — memories as association lists, a step function, a fuelled run — which `[TR]` does not print (it gives a relation) and which no result of the paper uses",
 "Support/Model/Base": "the carrier's prelude: finite partial maps, bijections, and the notation for the lifetime order",
 "Support/Model/AfterS5": "facts about the model's definitions: extensionality, the stratum embeddings, and the equations of the cell constructors",
 "Support/LogicalRelation/AfterS5": "the pieces of the logical relation that are not printed clauses: closing substitutions and free lifetime variables",
 "Support/LogicalRelation/AfterS4": "facts about the logical relation used by later sections",
 "Support/TypedWorld": "the typed-world machinery the repaired judgment ranges over: frame records, value shapes, root and chain positions, coherence and relevance of records, and the Kripke order `Ext`",
}
