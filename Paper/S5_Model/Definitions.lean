import Paper.S1_Syntax.Definitions
import Paper.S3_Dynamics.Definitions
import Support.Dynamics.Machine
import Support.Model.Prelude

/-!
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

namespace BoCa.Fig16

/-!
### 5.2 · `Res_α ≜ Loc ⇀ Cell_α` · [TR] p. 4, strata row 2 · `[repair]`

The harpoon is bare at this row in BOTH documents; `BoCa.Fig16.PMap` bundles a finite-domain field, so `Res_α` has strictly fewer inhabitants than printed and finiteness becomes hereditary. A declared variant (`docs/axiom-ledger.md` D10, `docs/boca-rules.md` §12.33) forced by row 5.7's `fin` plus flattening's nested witnesses — but row-2 heredity is a separate question from the settled row-7 one. Adjudicated at `docs/boca-rules.md` §12.33, `docs/axiom-ledger.md` D10 and `BoCa/Fig16.lean` §3 with convention G1: the unmarked reading is untenable rather than merely inconvenient, since `@ρ ≜ ⨅_{ψ∈cod(ρ)} @ψ` with ⊓ = max has no value on an unbounded codomain and [TR] 6.141's proof chooses `ℓ ∉ ρ_f ● ρ` in one step; heredity is then forced, because `Mut_α`'s witness is a `Res_β` that every operation consumes as a `Res`

### 5.7 · `ρ ∈ Res ≜ Loc ⇀ᶠⁱⁿ Cell` · [TR] p. 4, strata row 7 · `[as printed]`

The `fin` mark is [TR]'s; [CONF] Fig. 16 prints the harpoon bare, and that question is settled toward [TR]
-/
/-- `Loc ⇀ᶠⁱⁿ A` — a partial map with finite domain.  The function is the data;
finiteness is a `Prop`, so two finite maps agreeing everywhere are equal
(`PMap.ext`). -/
structure PMap (Loc A : Type) where
  /-- `ρ(ℓ)`. -/
  get : Loc → Option A
  /-- The `fin` mark of `[TR]` p. 4 row 7. -/
  finite : FinDom get

end BoCa.Fig16

namespace BoCa.Fig16.PMap
variable {Loc A B : Type}

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
/-- The empty resource. -/
def empty : PMap Loc A where
  get := fun _ => none
  finite := ⟨[], fun _ h => absurd rfl h⟩

@[simp] theorem empty_get (l : Loc) : (empty (A := A)).get l = none := rfl

/-- Postcompose a total function; the domain, hence the covering list, is
unchanged. -/
def map (f : A → B) (p : PMap Loc A) : PMap Loc B where
  get := fun l => (p.get l).map f
  finite := by
    obtain ⟨d, hd⟩ := p.finite
    refine ⟨d, fun l hl => hd l (fun e => ?_)⟩
    simp only [e, Option.map_none] at hl
    exact hl rfl

@[simp] theorem map_get (f : A → B) (p : PMap Loc A) (l : Loc) :
    (p.map f).get l = (p.get l).map f := rfl

theorem ext {p q : PMap Loc A} (h : ∀ l, p.get l = q.get l) : p = q := by
  cases p with
  | mk g hg =>
    cases q with
    | mk g' hg' =>
      have hgg : g = g' := funext h
      subst hgg
      rfl

end BoCa.Fig16.PMap

namespace BoCa.Fig16

/-!
### 5.9 · `α, β ∈ Life ≜ (ℕ, ⊑ ≜ >, ⊔ ≜ min, ⊓ ≜ max, ⊤ ≜ 0)` · [TR] p. 4, strata row 9 · `[repair]`

The glyph the row assigns `>` is the UNDERBARRED ⊑. Lean gives the strict `>` to ⊏ (following [CONF] Fig. 11) and adds a reflexive ⊑ of its own (row 5.59). [TR]'s own key cannot be right as printed: p. 6 uses the underbarred ⊒ in `ℓ ↦ Mut` and the bare ⊐ in `[α]P` two lines apart, which the key would collapse into one relation. Adjudicated at `docs/boca-rules.md` §12.3 and `BoCa/Fig16.lean` §1 with convention G5: under the printed key the structure is not a lattice — `⊤ = 0` is not ⊑-greatest, since `0 > 0` is false, and ⊔ = min is not a join — while [CONF] p. 415:12's prose above Fig. 11 calls it "a semi-bounded lattice of natural numbers". §12.3 attributes that word to the tuple's own line, which is where the entry is wrong; the reading is not
-/
abbrev Life : Type := ℕᵒᵈ

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
/-- `℘⁺(Life)` at the sets where `⊓ᾱ` and `⊔ᾱ` are defined: a set of lifetimes
together with its least member `join` (`⊔ᾱ`) and its greatest `meet` (`⊓ᾱ`). -/
structure LSet where
  /-- `x ∈ ᾱ`. -/
  mem : Life → Prop
  /-- `⊔ᾱ ≜ min ᾱ` — the longest lifetime in `ᾱ`. -/
  join : Life
  /-- `⊓ᾱ ≜ max ᾱ` — the shortest lifetime in `ᾱ`. -/
  meet : Life
  /-- `⊔ᾱ ∈ ᾱ`; in particular `ᾱ ≠ ∅`, which is the `+` of `℘⁺`. -/
  join_mem : mem join
  /-- `⊓ᾱ ∈ ᾱ`. -/
  meet_mem : mem meet
  /-- `⊔ᾱ` is the longest, i.e. the `⊑`-greatest. -/
  join_greatest : ∀ x, mem x → x ≤ join
  /-- `⊓ᾱ` is the shortest, i.e. the `⊑`-least. -/
  meet_least : ∀ x, mem x → meet ≤ x

end BoCa.Fig16

namespace BoCa.Fig16.LSet

theorem meet_le_join (s : LSet) : s.meet ≤ s.join := s.join_greatest _ s.meet_mem

end BoCa.Fig16.LSet

namespace BoCa.Fig16
variable (Loc Val : Type)

/-!
### 5.4 · `Imm_α ≜ {(ᾱ : ℘⁺(Life), v : Val, ρ : Res_⊔ᾱ) ∣ ⊓ᾱ ⊐ α}` · [TR] p. 4, strata row 4 · `[encoding]`

`℘⁺(Life)` is `BoCa.Fig16.LSet` — a set bundled with its min and max so `⊔ᾱ` and `⊓ᾱ` stay total and choice-free; `BoCa.Fig16.LSet.exists_of_bounded` shows the printed side condition admits exactly the `LSet`s, so the SET `Imm_α` is unchanged
-/
/-- `Imm_α ≜ {(ᾱ : ℘⁺(Life), v : Val, ρ : Res_{⊔ᾱ}) | ⊓ᾱ ⊐ α}`, one layer.
The printed side condition is the field `hls`; it is part of the *type*, as
printed, not a hypothesis carried alongside.

The binder is `LSet`, which is `℘⁺(Life)` at the sets where `⊓ᾱ` is defined
(G2).  That is the same set of inhabitants: `⊓` is `max`, so an `ᾱ` without a
greatest element has no `⊓ᾱ` and satisfies no condition of the form `⊓ᾱ ⊐ α`,
and `LSet.exists_of_bounded` is the converse — every `ᾱ` that does satisfy it
is an `LSet` with the same members and the same meet — so the *set* `Imm_α` is
the printed one, though the binder is not `℘⁺(Life)` glyph for glyph.
`[variant: `Res` is finite at every depth (G1, §3, ledger D10, `docs/boca-rules.md` §12.33); of the two printed `Res` rows only row 7, and only in `[TR]`, carries the mark]` -/
structure ImmF (α : Life) (below : ∀ β, α < β → Type) : Type where
  /-- `ᾱ : ℘⁺(Life)`. -/
  ls : LSet
  /-- `⊓ᾱ ⊐ α` — the shortest of `ᾱ` still outlives the stratification index. -/
  hls : α < ls.meet
  /-- `v : Val`. -/
  v : Val
  /-- `ρ : Res_{⊔ᾱ}` — the witness sits at the *longest* of `ᾱ`. -/
  ρ : PMap Loc (below ls.join (lt_of_lt_of_le hls ls.meet_le_join))

/-!
### 5.5 · `Mut_α ≜ {(β ⊐ α, v : Val, ρ : Res_β, P̂ : Val → SProp_β) ∣ P̂(v)(ρ)}` · [TR] p. 4, strata row 5 · `[as printed]`

The invariant is a genuine predicate, not a type code; both printed conditions are fields
-/
/-- `Mut_α ≜ {(β ⊐ α, v : Val, ρ : Res_β, P̂ : Val → SProp_β) | P̂(v)(ρ)}`, one
layer.  Both printed conditions are fields: `β ⊐ α` is the first tuple slot,
and the refinement `| P̂(v)(ρ)` is `hw`.  `P̂` is a genuine predicate.
`[variant: `Res` is finite at every depth (G1, §3, ledger D10, `docs/boca-rules.md` §12.33); of the two printed `Res` rows only row 7, and only in `[TR]`, carries the mark]` -/
structure MutF (α : Life) (below : ∀ β, α < β → Type) : Type where
  /-- The cell's own lifetime. -/
  β : Life
  /-- `β ⊐ α` — the witness strictly outlives the holder.  This is what makes
  the whole definition well-founded. -/
  hβ : α < β
  /-- `v : Val`. -/
  v : Val
  /-- `ρ : Res_β`. -/
  ρ : PMap Loc (below β hβ)
  /-- `P̂ : Val → SProp_β` — a PREDICATE, not a code and not a syntactic type. -/
  P : Val → PMap Loc (below β hβ) → Prop
  /-- `| P̂(v)(ρ)` — the printed refinement. -/
  hw : P v ρ

/-!
### 5.3 · `Cell_α ≜ own(Val) + imm(Imm_α) + mut(Mut_α)` · [TR] p. 4, strata row 3 · `[as printed]`

Three-way disjoint sum, one layer; `BoCa.Fig16.Cell_eq` is the printed row as an equation. The well-founded construction behind it is ours (row 5.58)
-/
/-- `Cell_α ≜ own(Val) + imm(Imm_α) + mut(Mut_α)`, one layer.
`[variant: `Res` is finite at every depth (G1, §3, ledger D10, `docs/boca-rules.md` §12.33); of the two printed `Res` rows only row 7, and only in `[TR]`, carries the mark]` -/
inductive CellF (α : Life) (below : ∀ β, α < β → Type) : Type where
  /-- `own(Val)`. -/
  | own (v : Val)
  /-- `imm(Imm_α)`. -/
  | imm (i : ImmF Loc Val α below)
  /-- `mut(Mut_α)`. -/
  | mut (m : MutF Loc Val α below)

/-!
Row 5.3, continued.

### 5.58 · — neither document prints the recursion, only the measure — · [TR] p. 4, row 3 · `[repair]`

The construction that makes the printed fixpoint equation well-founded; the equation is propositional here, not definitional, so every constructor goes through a cast. Adjudicated at `BoCa/Fig16.lean`'s header, "Why this is definable at all": every recursive occurrence is at a strictly smaller lifetime index, so ordinary well-founded recursion suffices with no step-indexing, fuel or defunctionalised invariant, and the printed row is recovered as `BoCa.Fig16.Cell_eq`. [CONF] p. 415:20 says the circularity is broken "using stratification, but using a very different measure"
-/
/-- `Cell_α` — well-founded recursion on the lifetime index; every recursive
occurrence is at a strictly smaller natural.  `[TR]` §5 says nothing about the
construction; `[CONF]` 415:20 names the **measure** — "we break the circularity
using stratification, but using a very different measure: the outlives lifetime
ordering" — which is what this recursion descends.  Neither prints the
recursion itself; the printed row is the fixpoint equation, which is `Cell_eq`.
`[about ours: the construction, not the row]` -/
def Cell : Life → Type :=
  WellFounded.fix (invImage OrderDual.ofDual Nat.lt_wfRel).wf (CellF Loc Val)

/-!
Row 5.2, continued.
-/
/-- `Res_α ≜ Loc ⇀ᶠⁱⁿ Cell_α`.  **Neither** document marks the harpoon at this
row — `[CONF]` Fig. 16 and `[TR]` p. 4 row 2 both print it bare, verified at
1600 dpi — and the mark is inherited here from row 7, which `[TR]` does mark;
§3 is the argument that the inheritance is forced rather than assumed.
`[variant: the harpoon is bare at this row in both documents; finiteness is
taken from row 7 and made hereditary]` -/
abbrev Res (α : Life) : Type := PMap Loc (Cell Loc Val α)

/-!
### 5.1 · `SProp_α ≜ Res_α → ℙ` · [TR] p. 4, strata row 1 · `[as printed]`

Total arrow into `Prop`; its domain is row 5.2, so it inherits row 5.2's variant
-/
/-- `SProp_α ≜ Res_α → ℙ`.  The arrow is total.
`[variant: `Res` is finite at every depth (G1, §3, ledger D10, `docs/boca-rules.md` §12.33); of the two printed `Res` rows only row 7, and only in `[TR]`, carries the mark]` -/
abbrev SProp (α : Life) : Type := Res Loc Val α → Prop

/-!
Rows 5.3, 5.58, continued.
-/
/-- The fixpoint equation — Fig. 16 row 3 as an equation, which is the form the
row is printed in.  Propositional here, not definitional, so the constructors
below go through `cast`.
`[variant: `Res` is finite at every depth (G1, §3, ledger D10, `docs/boca-rules.md` §12.33); of the two printed `Res` rows only row 7, and only in `[TR]`, carries the mark]` -/
theorem Cell_eq (α : Life) :
    Cell Loc Val α = CellF Loc Val α (fun β _ => Cell Loc Val β) :=
  WellFounded.fix_eq (invImage OrderDual.ofDual Nat.lt_wfRel).wf (CellF Loc Val) α

/-!
Row 5.4, continued.
-/
/-- `Imm_α` — Fig. 16 row 4, at the strata it is a row of.
`[variant: `Res` is finite at every depth (G1, §3, ledger D10, `docs/boca-rules.md` §12.33); of the two printed `Res` rows only row 7, and only in `[TR]`, carries the mark]` -/
abbrev Imm (α : Life) : Type := ImmF Loc Val α (fun β _ => Cell Loc Val β)

/-!
Row 5.5, continued.
-/
/-- `Mut_α` — Fig. 16 row 5, at the strata it is a row of.
`[variant: `Res` is finite at every depth (G1, §3, ledger D10, `docs/boca-rules.md` §12.33); of the two printed `Res` rows only row 7, and only in `[TR]`, carries the mark]` -/
abbrev Mut (α : Life) : Type := MutF Loc Val α (fun β _ => Cell Loc Val β)

/-!
### 5.8 · `ψ ∈ Cell ≜ ⋃_α Cell_α` · [TR] p. 4, strata row 8 · `[encoding]`

The union is an inductive whose payloads are the already-built strata; `BoCa.Fig16.CellU.inStratum_iff` and `BoCa.Fig16.CellU.exists_stratum` prove it is exactly `⋃_α Cell_α`. Splitting the payloads into `ImmU`/`MutU` is ours — no row of either document is an unstratified `Imm` or `Mut`
-/
/-- `imm(ᾱ, v, ρ)` as an element of the union.  `[CONF]` **does** print an
unstratified `Imm` — p. 415:19 (300 dpi) has `Imm ≈ ℘(Life) × Val × Res`,
component for component this structure, with a bare `℘` where Fig. 16 binds
`℘⁺` — but only inside the *ill-founded sketch it then rejects* (415:20: "the
prevailing technique for breaking this kind of circularity is to stratify").
No **final** row of either carrier is an unstratified `Imm`: Fig. 16 row 8 is
`⋃_α Cell_α` and `Imm_α` is the stratified row, so this decomposition is ours.
The `LSet` binder is `℘⁺(Life)` at the sets that have a meet, as at `ImmF`, and
no `ᾱ` without one occurs in any `Cell_α`, hence in none of the union.
`[about ours: the union's `imm` payload, decomposed]` -/
structure ImmU : Type where
  /-- `ᾱ : ℘⁺(Life)`. -/
  ls : LSet
  /-- `v : Val`. -/
  v : Val
  /-- `ρ : Res_{⊔ᾱ}`. -/
  ρ : Res Loc Val ls.join

/-!
Row 5.8, continued.
-/
/-- `mut(β, v, ρ, P̂)` as an element of the union, with its printed refinement.
As `ImmU`: `[CONF]` prints `Mut ≈ Life × Val × Res` (415:19) and
`Mut ≈ Life × Val × Res × (Val → Res → ℙ)` (415:20) — the latter component for
component this structure minus `hw` — but both belong to the rejected sketch,
and no final row of either carrier is an unstratified `Mut`.
`[about ours: the union's `mut` payload, decomposed]` -/
structure MutU : Type where
  /-- The cell's own lifetime. -/
  β : Life
  /-- `v : Val`. -/
  v : Val
  /-- `ρ : Res_β`. -/
  ρ : Res Loc Val β
  /-- `P̂ : Val → SProp_β`. -/
  P : Val → SProp Loc Val β
  /-- `| P̂(v)(ρ)`. -/
  hw : P v ρ

/-!
Row 5.8, continued.
-/
/-- `ψ ∈ Cell ≜ ⋃_α Cell_α`.  The union is realised directly, its payloads
being the already-constructed strata; §6's `CellU.inStratum_iff` and
`CellU.exists_stratum` are the proof that this is `⋃_α Cell_α` and not
something larger or smaller.
`[variant: `Res` is finite at every depth (G1, §3, ledger D10, `docs/boca-rules.md` §12.33); of the two printed `Res` rows only row 7, and only in `[TR]`, carries the mark]` -/
inductive CellU : Type where
  /-- `own(Val)`. -/
  | own (v : Val)
  /-- `imm(Imm)`. -/
  | imm (i : ImmU Loc Val)
  /-- `mut(Mut)`. -/
  | mut (m : MutU Loc Val)

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
/-- One layer of a stratum, forgetting the side condition. -/
def CellF.toU {α : Life} :
    CellF Loc Val α (fun β _ => Cell Loc Val β) → CellU Loc Val
  | .own v => .own v
  | .imm i => .imm ⟨i.ls, i.v, i.ρ⟩
  | .mut m => .mut ⟨m.β, m.v, m.ρ, m.P, m.hw⟩

/-- `own(v)`.  `[as printed]` -/
def CellU.ownOf (v : Val) : CellU Loc Val := .own v

end BoCa.Fig16

namespace BoCa.Fig16
variable (Loc Val : Type)

/-!
Row 5.7, continued.
-/
/-- `ρ ∈ Res ≜ Loc ⇀ᶠⁱⁿ Cell`.  The `fin` mark is `[TR]` p. 4 row 7, read at
1600 dpi; `[CONF]` Fig. 16 prints the harpoon bare and never mentions
finiteness, and that omission is the typesetting error (§3).
The mark on *this* row is `[TR]`'s print; the variance is in `Cell`, whose
payloads are finite at every depth.
`[variant: `Res` is finite at every depth (G1, §3, ledger D10, `docs/boca-rules.md` §12.33); of the two printed `Res` rows only row 7, and only in `[TR]`, carries the mark]` -/
abbrev ResU : Type := PMap Loc (CellU Loc Val)

/-!
### 5.6 · `P ∈ SProp ≜ Res → ℙ` · [TR] p. 4, strata row 6 · `[as printed]`

This, not row 5.1, is the carrier of the whole p. 6 proposition display
-/
/-- `P ∈ SProp ≜ Res → ℙ`.
`[variant: `Res` is finite at every depth (G1, §3, ledger D10, `docs/boca-rules.md` §12.33); of the two printed `Res` rows only row 7, and only in `[TR]`, carries the mark]` -/
abbrev SPropU : Type := ResU Loc Val → Prop

end BoCa.Fig16

namespace BoCa.Fig16.Life

/-!
Row 5.9, continued.
-/
/-- `⊤ ≜ 0` — the longest lifetime.  `[as printed]`

`ℕ` is an `OrderBot` with `⊥ = 0`, so `ℕᵒᵈ` is an `OrderTop` with `⊤ = toDual 0`
— the printed row on the nose.  `⊔` and `⊓` are Mathlib's, from `Lattice ℕᵒᵈ`,
where they are `min` and `max` on `ℕ`, again as printed. -/
abbrev top : Life := ⊤

/-!
Row 5.9, continued.
-/
/-- `α ⊔ β ≜ min α β` — the join, the longer-lived of the two.  `[as printed]` -/
abbrev join (a b : Life) : Life := a ⊔ b

/-!
Row 5.9, continued.
-/
/-- `α ⊓ β ≜ max α β` — the meet, the shorter-lived of the two.  `[as printed]` -/
abbrev meet (a b : Life) : Life := a ⊓ b

/-!
Row 5.9, continued.
-/
/-- `α ⊏ β ≜ α > β` — "`α` is outlived by `β`", strict.  `[as printed]`
(following `[CONF]` Fig. 11's labelling; see §1) -/
abbrev Sqsubset (a b : Life) : Prop := a < b

/-!
Row 5.9, continued.
-/
/-- `α ⊐ β ≜ β ⊏ α` — "`α` outlives `β`", strict.  Fig. 16 uses this form and
no other.  `[as printed]` -/
abbrev Sqsupset (a b : Life) : Prop := b < a

end BoCa.Fig16.Life

namespace BoCa.Fig16

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
@[inherit_doc] scoped infix:50 " ⊐ " => Life.Sqsupset

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### 5.10 · `@ψ ≜ ⊤` if own; `α` if `mut(α,_,_,_)`; `⊓ᾱ` if `imm(ᾱ,_,_,_)` · [TR] p. 5, operation row 1 · `[as printed]`

The print writes `own` argumentless and `imm` 4-ary; `Imm_α` is a 3-tuple and ▸◂, ⋈, ●, ○, ⟦ψ⟧, ↭ and `reb_α` all write `imm` 3-ary on the same page, so the arities are forced and the slip is tagged in-file
-/
/-- `@ψ` — the lifetime of a cell (`[TR]` p. 5).
`[variant: [TR] writes the own case argumentless and the imm case 4-ary; the
arities of Imm_α and of every other clause on the page are used]` -/
def CellU.at : CellU Loc Val → Life
  | .own _ => ⊤
  | .imm i => i.ls.meet
  | .mut m => m.β

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
@[simp] theorem CellU.at_ownOf (v : Val) : (ownOf (Loc := Loc) v).at = ⊤ := rfl

/-- The tag of a cell. -/
def CellU.kind : CellU Loc Val → Kind
  | .own _ => .own
  | .imm _ => .imm
  | .mut _ => .mut

@[simp] theorem CellU.kind_ownOf (v : Val) :
    (CellU.ownOf (Loc := Loc) v).kind = Kind.own := rfl

/-- The meet over an explicitly given list.  Proof apparatus. -/
def ResU.atOn (ρ : ResU Loc Val) : List Loc → Life
  | [] => ⊤
  | l :: d => ((ρ.get l).elim ⊤ CellU.at) ⊓ ResU.atOn ρ d

theorem ResU.atOn_ub (ρ : ResU Loc Val) (d : List Loc) :
    ∀ l ψ, l ∈ d → ρ.get l = some ψ → ρ.atOn d ≤ ψ.at := by
  induction d with
  | nil => intro l ψ h; exact absurd h (by simp)
  | cons k d ih =>
      intro l ψ hmem hget
      show ((ρ.get k).elim ⊤ CellU.at) ⊓ ResU.atOn ρ d ≤ ψ.at
      rcases List.mem_cons.mp hmem with rfl | hmem
      · rw [hget]; exact inf_le_left
      · exact le_trans inf_le_right (ih l ψ hmem hget)

theorem ResU.atOn_lub (ρ : ResU Loc Val) (d : List Loc) (b : Life)
    (hb : ∀ l ψ, ρ.get l = some ψ → b ≤ ψ.at) : b ≤ ρ.atOn d := by
  induction d with
  | nil => exact le_top
  | cons k d ih =>
      show b ≤ ((ρ.get k).elim ⊤ CellU.at) ⊓ ResU.atOn ρ d
      cases hk : ρ.get k with
      | none => exact le_inf le_top ih
      | some ψ => exact le_inf (hb k ψ hk) ih

end BoCa.Fig16

namespace BoCa.Fig16.Life

/-!
### 5.12 · `↓α ≜ α + 1` · [TR] p. 5, operation row 3 · `[as printed]`

[CONF] prints no defining equation for ↓, only prose at p. 415:23
-/
/-- `↓α ≜ α + 1`, the next-shorter lifetime (`[TR]` p. 5; `[CONF]` prints no
defining **equation** — it uses `↓@ρ` and glosses it in prose at 415:23, "the
next shortest lifetime `↓@ρ` for any `ρ`", read at 1200 dpi).  `[as printed]` -/
def down (a : Life) : Life := OrderDual.toDual (OrderDual.ofDual a + 1)

end BoCa.Fig16.Life

namespace BoCa.Fig16.LSet

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
/-- `ᾱ₁ ∪ ᾱ₂` — the union used by `imm`-composition (`[TR]` p. 5; `[CONF]`
Fig. 16 below the internal rule).  Round set union, not `⊎`.  The `join` and
`meet` are recomputed rather than carried, and `LSet.ext` says they are
determined by the members, so this is set union and nothing more.
`[as printed]` -/
def union (s t : LSet) : LSet where
  mem x := s.mem x ∨ t.mem x
  join := s.join ⊔ t.join
  meet := s.meet ⊓ t.meet
  join_mem := by
    rcases Nat.le_total s.join t.join with h | h
    · rw [sup_eq_left.mpr (show t.join ≤ s.join from h)]; exact Or.inl s.join_mem
    · rw [sup_eq_right.mpr (show s.join ≤ t.join from h)]; exact Or.inr t.join_mem
  meet_mem := by
    rcases Nat.le_total s.meet t.meet with h | h
    · rw [inf_eq_right.mpr (show t.meet ≤ s.meet from h)]; exact Or.inr t.meet_mem
    · rw [inf_eq_left.mpr (show s.meet ≤ t.meet from h)]; exact Or.inl s.meet_mem
  join_greatest := by
    intro x hx
    rcases hx with h | h
    · exact Nat.le_trans (minLeL _ _) (s.join_greatest x h)
    · exact Nat.le_trans (minLeR _ _) (t.join_greatest x h)
  meet_least := by
    intro x hx
    rcases hx with h | h
    · exact Nat.le_trans (s.meet_least x h) (leMaxL _ _)
    · exact Nat.le_trans (t.meet_least x h) (leMaxR _ _)

end BoCa.Fig16.LSet

namespace BoCa.Fig16

@[inherit_doc LSet.union] scoped infixl:65 " ∪ " => LSet.union

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

theorem ImmU.ext {i j : ImmU Loc Val} (hs : i.ls = j.ls) (hv : i.v = j.v)
    (hρ : i.ρ ≍ j.ρ) : i = j := by
  obtain ⟨s₁, v₁, ρ₁⟩ := i
  obtain ⟨s₂, v₂, ρ₂⟩ := j
  simp only at hs hv hρ
  subst hs; subst hv
  simp only [heq_eq_eq] at hρ
  subst hρ; rfl

/-!
### 5.17 · `ρ₁ ▸◁ ρ₂ ≜ ∀ℓ ∈ dom(ρ₁) ∩ dom(ρ₂). ρ₁(ℓ) ▸◁ ρ₂(ℓ)` · [TR] p. 5, operation row 8 · `[as printed]`

The half-filled glyph is a metavariable over the two cell compatibilities — read off Lemma 6.1's two proof cases, not off the shape — and the Lean writes the row once as a schema and supplies both instances; it constrains only the overlap, as printed
-/
/-- `ρ₁ ▶◁ ρ₂` — the pointwise lift, one schema in the cell-level relation `C`.
Note it constrains only the overlap: disjoint resources are compatible in
either mode.  The print's `▶◁` ranges over the two cell-level relations `▶◀`
and `⋈`; `C` here ranges over all of them, and the instance below pins it.
`[variant: written as a schema in an arbitrary cell-level relation, where the
print's metavariable ranges over two]` -/
def ResU.Compat (C : CellU Loc Val → CellU Loc Val → Prop) (ρ₁ ρ₂ : ResU Loc Val) : Prop :=
  ∀ l ψ₁ ψ₂, ρ₁.get l = some ψ₁ → ρ₂.get l = some ψ₂ → C ψ₁ ψ₂

/-!
### 5.18 · `ρ₁ ◖ ρ₂ ≜ ρ₁/dom(ρ₂) ⊎ ρ₂/dom(ρ₁) ⊎ [ℓ ↦ ψ₁ ◖ ψ₂ ∣ …]`, guarded by `ρ₁ ▸◁ ρ₂` · [TR] p. 5, operation row 9 · `[as printed]`

[TR]'s guarded reading is taken; [CONF] Fig. 16 prints it unguarded and ends with a clause that does not type. `BoCa.Fig16.OptComp` is the three printed pieces pointwise, and the composite's domain is the union
-/
/-- The three pieces of `ρ₁ ◐ ρ₂` at one location: `ρ₁` off `dom(ρ₂)`, `ρ₂` off
`dom(ρ₁)`, and the cellwise `◐` on the overlap. -/
def OptComp (C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop) :
    Option (CellU Loc Val) → Option (CellU Loc Val) → Option (CellU Loc Val) → Prop
  | none, none, o => o = none
  | some ψ, none, o => o = some ψ
  | none, some ψ, o => o = some ψ
  | some ψ₁, some ψ₂, o => ∃ ψ, o = some ψ ∧ C ψ₁ ψ₂ ψ

/-!
Row 5.18, continued.
-/
/-- `ρ₁ ◐ ρ₂ = ρ` — one schema, in the cell-level guard `R` and the cell-level
composition `C`.  As `ResU.Compat`, the two parameters range over more than the
print's two correlated pairs, and they are independent here where the print
correlates them; the instance below pins both.
`[variant: written as a schema in an arbitrary guard and composition, where the
print's two metavariables range over two correlated pairs; guard and `ρ₂(ℓ)`
from `[TR]`]` -/
def ResU.Comp (R : CellU Loc Val → CellU Loc Val → Prop)
    (C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop)
    (ρ₁ ρ₂ ρ : ResU Loc Val) : Prop :=
  ResU.Compat R ρ₁ ρ₂ ∧ ∀ l, OptComp C (ρ₁.get l) (ρ₂.get l) (ρ.get l)

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
theorem optRestrict_eq_none {o : Option (CellU Loc Val)} (k : Kind) (e : o = none) :
    (o.bind fun ψ => if ψ.kind = k then some ψ else none) = none := by subst e; rfl

/-!
### 5.19 · `ρ∣ι ≜ [ℓ ↦ ψ ∣ ρ(ℓ) = ψ = ι(…)]`, `ι ∈ {own, mut, imm}` · [TR] p. 5, operation row 10 · `[as printed]`

Single-tag only, as printed; the multi-tag restriction [TR] §6 uses from Definition 6.3 on has no printed defining row and is row 5.51, and the domain restriction [TR] §6 uses from Lemma 6.56 on is row 5.64
-/
/-- `ρ|ι ≜ [ℓ ↦ ψ | ρ(ℓ) = ψ = ι(…)]`.  The defining equation is `[TR]` p. 5's;
`[CONF]` uses `ρ|own`, `ρ|mut` and `ρ|imm` in Fig. 18a (1600 dpi) and the
equation does not appear there.

Coverage gap, recorded: `[TR]` §6 also uses a multi-tag restriction `ρ|own,mut`
and a domain restriction `ρ|dom(ρ′)`, and this line defines neither.
`[as printed]` -/
def ResU.restrict (ρ : ResU Loc Val) (k : Kind) : ResU Loc Val where
  get := fun l => (ρ.get l).bind fun ψ => if ψ.kind = k then some ψ else none
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    exact ⟨d, fun l hl => hd l (fun e => hl (optRestrict_eq_none k e))⟩

/-!
### 5.24 · `⟦ψ⟧ ≜ v` when `ψ` is `own(v)`, `mut(_,v,_,_)` or `imm(_,v,_)` · [TR] p. 5, operation row 15 · `[as printed]`

Total on cells, as printed; the 3-ary `imm` here corroborates that row 5.10's 4-ary `imm` is an isolated slip. [CONF] never prints this row
-/
/-- `⟦ψ⟧`.  `[as printed]` -/
def CellU.erase : CellU Loc Val → Val
  | .own v => v
  | .imm i => i.v
  | .mut m => m.v

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
@[simp] theorem CellU.erase_ownOf (v : Val) : (CellU.ownOf (Loc := Loc) v).erase = v := rfl

end BoCa.Fig16

namespace BoCa.Fig16.LSet

/-- A singleton lifetime set. -/
def singleton (a : Life) : LSet where
  mem x := x = a
  join := a
  meet := a
  join_mem := rfl
  meet_mem := rfl
  join_greatest := fun _ h => Nat.le_of_eq h.symm
  meet_least := fun _ h => Nat.le_of_eq h

end BoCa.Fig16.LSet

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-- `Res` at the `Loc` and `Val` of `[TR]` §3. -/
abbrev WRes : Type := ResU BoCa.Loc BoCa.Val

/-- `SProp ≜ Res → ℙ` at those. -/
abbrev WProp : Type := SPropU BoCa.Loc BoCa.Val

end BoCa.Fig16.BoLo

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
### 5.34 · `⌜P_Meta⌝ (ρ) ≜ ρ = ∅ ∧ P_Meta` · [TR] p. 6, proposition row 6 · `[as printed]`

∅ is `BoCa.Fig16.PMap.empty`
-/
/-- `⌜P_meta⌝ (ρ) ≜ ρ = ∅ ∧ P_meta`. -/
def pure (p : Prop) : SPropU Loc Val := fun ρ => ρ = PMap.empty ∧ p

/-!
### 5.37 · `emp ≜ ⌜⊤⌝` · [TR] p. 6, proposition row 9 · `[as printed]`

One of three rows the display gives no `(ρ)` column; derived, as there
-/
/-- `emp ≜ ⌜⊤⌝`. -/
def emp : SPropU Loc Val := pure True

/-!
### 5.39 · `⊤ (ρ) ≜ ⊤` · [TR] p. 6, proposition row 11 · `[as printed]`

The logical top, not `Life`'s `⊤ ≜ 0`
-/
/-- `⊤ (ρ) ≜ ⊤`. -/
def top : SPropU Loc Val := fun _ => True

/-!
### 5.40 · `⊥ (ρ) ≜ ⊥` · [TR] p. 6, proposition row 12 · `[as printed]`

The text layer loses both glyphs on this row; read off a render
-/
/-- `⊥ (ρ) ≜ ⊥`. -/
def bot : SPropU Loc Val := fun _ => False

/-!
### 5.41 · `P₁ ∧ P₂ (ρ) ≜ P₁(ρ) ∧ P₂(ρ)` · [TR] p. 6, proposition row 13 · `[as printed]`

Pointwise, as printed
-/
/-- `P₁ ∧ P₂ (ρ) ≜ P₁(ρ) ∧ P₂(ρ)`. -/
def and (P Q : SPropU Loc Val) : SPropU Loc Val := fun ρ => P ρ ∧ Q ρ

/-!
### 5.38 · `!P ≜ emp ∧ P` · [TR] p. 6, proposition row 10 · `[as printed]`

Derived from the two rows above it; `BoCa.Fig16.BoLo.bang_L_needs_premise` records that [TR] Lemma 6.84 is refutable under this very definition
-/
/-- `!P ≜ emp ∧ P`. -/
def bang (P : SPropU Loc Val) : SPropU Loc Val := and emp P

/-!
### 5.42 · `P₁ ∨ P₂ (ρ) ≜ P₁(ρ) ∨ P₂(ρ)` · [TR] p. 6, proposition row 14 · `[as printed]`

Pointwise, as printed
-/
/-- `P₁ ∨ P₂ (ρ) ≜ P₁(ρ) ∨ P₂(ρ)`. -/
def or (P Q : SPropU Loc Val) : SPropU Loc Val := fun ρ => P ρ ∨ Q ρ

/-!
### 5.43 · `P₁ ⇒ P₂ (ρ) ≜ P₁(ρ) ⇒ P₂(ρ)` · [TR] p. 6, proposition row 15 · `[as printed]`

Pointwise, as printed — the non-affine implication, not a Kripke one
-/
/-- `P₁ ⇒ P₂ (ρ) ≜ P₁(ρ) ⇒ P₂(ρ)`. -/
def imp (P Q : SPropU Loc Val) : SPropU Loc Val := fun ρ => P ρ → Q ρ

/-!
### 5.44 · `∀ P̂ (ρ) ≜ ∀x. P̂(x)(ρ)` · [TR] p. 6, proposition row 16 · `[encoding]`

`x` ranges over an arbitrary Lean type where the print leaves the binder's domain implicit; nothing else differs
-/
/-- `∀P̂ (ρ) ≜ ∀x. P̂(x)(ρ)`. -/
def all {A : Type} (Φ : A → SPropU Loc Val) : SPropU Loc Val := fun ρ => ∀ x, Φ x ρ

/-!
### 5.45 · `∃ P̂ (ρ) ≜ ∃x. P̂(x)(ρ)` · [TR] p. 6, proposition row 17 · `[encoding]`

The same implicit-domain choice as row 5.44
-/
/-- `∃P̂ (ρ) ≜ ∃x. P̂(x)(ρ)`. -/
def ex {A : Type} (Φ : A → SPropU Loc Val) : SPropU Loc Val := fun ρ => ∃ x, Φ x ρ

end BoCa.Fig16.BoLo

namespace BoCa.Fig16

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
@[inherit_doc] scoped infix:50 " ⊏ " => Life.Sqsubset

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### 5.48 · — presupposed, never written — · [TR] pp. 4–5 · `[repair]`

In the paper the strata are subsets of one set, so membership is free; here they are distinct types and the inclusion becomes an obligation. Every printed clause that shares ONE ρ across two strata — row 5.13, row 5.15, and clauses (2), (3), (5) of row 5.16 — is stated through it. Adjudicated at `BoCa/Fig16.lean` convention G3 with §6's preamble and §22: in the paper the strata are subsets of one set, so membership is free; here they are distinct types and the inclusion becomes an obligation, which is discharged rather than declared, and that is what lets §10 onward state the printed operations with one shared ρ and plain equality
-/
/-- `ψ ∈ Cell_α` — the `α`-th piece of `⋃_α Cell_α`.  An `own` cell carries no
side condition and so lies in every stratum; an `imm` or `mut` cell lies in
`Cell_α` exactly when its printed side condition holds.
`[about ours: the membership that ⋃_α Cell_α presupposes, written out]` -/
def CellU.InStratum (α : Life) : CellU Loc Val → Prop
  | .own _ => True
  | .imm i => i.ls.meet ⊐ α
  | .mut m => m.β ⊐ α

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
/-- …and back, given the side condition. -/
def CellU.toLayer (α : Life) :
    (ψ : CellU Loc Val) → ψ.InStratum α → CellF Loc Val α (fun β _ => Cell Loc Val β)
  | .own v, _ => .own v
  | .imm i, h => .imm ⟨i.ls, h, i.v, i.ρ⟩
  | .mut m, h => .mut ⟨m.β, h, m.v, m.ρ, m.P, m.hw⟩

theorem CellF.toU_inStratum {α : Life}
    (x : CellF Loc Val α (fun β _ => Cell Loc Val β)) : (CellF.toU x).InStratum α := by
  cases x with
  | own v => exact trivial
  | imm i => exact i.hls
  | «mut» m => exact m.hβ

theorem CellU.toU_toLayer {α : Life} (ψ : CellU Loc Val) (h : ψ.InStratum α) :
    CellF.toU (ψ.toLayer α h) = ψ := by cases ψ <;> rfl

@[simp] theorem CellU.inStratum_ownOf (α : Life) (v : Val) :
    (ownOf (Loc := Loc) v).InStratum α := trivial

theorem CellU.InStratum.sup {a b : Life} {ψ : CellU Loc Val}
    (h₁ : ψ.InStratum a) (h₂ : ψ.InStratum b) : ψ.InStratum (a ⊔ b) := by
  cases ψ
  · exact trivial
  · exact sup_lt_iff.mpr ⟨h₁, h₂⟩
  · exact sup_lt_iff.mpr ⟨h₁, h₂⟩

/-- The union is directed: the strata grow as `α` shortens, because the two
printed side conditions only weaken. -/
theorem CellU.InStratum.mono {α α' : Life} (h : α' ≤ α) {ψ : CellU Loc Val}
    (hψ : ψ.InStratum α) : ψ.InStratum α' := by
  cases ψ
  · exact trivial
  · exact lt_of_le_of_lt h hψ
  · exact lt_of_le_of_lt h hψ

/-!
Row 5.48, continued.
-/
/-- `ρ ∈ Res_α` — every cell of `ρ` lies in stratum `α`. -/
def ResU.InStratum (α : Life) (ρ : ResU Loc Val) : Prop :=
  ∀ l ψ, ρ.get l = some ψ → ψ.InStratum α

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable (Loc Val)

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
/-- `Res_α` as a subset of `Res`. -/
abbrev ResS (α : Life) : Type := { ρ : ResU Loc Val // ρ.InStratum α }

/-- `SProp_α ≜ Res_α → ℙ`, read on the union. -/
abbrev SPropS (α : Life) : Type := ResS Loc Val α → Prop

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

theorem ResU.InStratum.sup {a b : Life} {ρ : ResU Loc Val}
    (h₁ : ρ.InStratum a) (h₂ : ρ.InStratum b) : ρ.InStratum (a ⊔ b) :=
  fun l ψ e => (h₁ l ψ e).sup (h₂ l ψ e)

theorem ResU.InStratum.mono {α α' : Life} (h : α' ≤ α) {ρ : ResU Loc Val}
    (hρ : ρ.InStratum α) : ρ.InStratum α' := fun l ψ e => (hρ l ψ e).mono h

theorem ResU.InStratum.inf_left {a b : Life} {ρ : ResU Loc Val}
    (h : ρ.InStratum a) : ρ.InStratum (a ⊓ b) := by
  intro l ψ e
  cases ψ with
  | own v => exact trivial
  | imm i => exact lt_of_le_of_lt inf_le_left (h l _ e)
  | «mut» m => exact lt_of_le_of_lt inf_le_left (h l _ e)

end BoCa.Fig16

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
### 5.32 · `[α] P  (ρ) ≜ P(ρ) ∧ @ρ ⊐ α` · [TR] p. 6, proposition row 4 · `[as printed]`

The glyph after `@ρ` carries no underbar — strict ⊐ — where row 5.31 two lines above carries the underbarred ⊒; [CONF] Fig. 19 orders the two conjuncts the other way, which is the same proposition
-/
/-- `@ρ ⊐ α` — universal over the BORROW cells of `ρ`.

`[TR]` p. 5 abbreviates the relation as a compare of `@ρ ≜ ⨅_{ψ ∈ cod(ρ)} @ψ`,
and `@own ≜ ⊤`; read as a single strict compare of that meet, a borrow-free
resource would fail the relation at `α = ⊤`.  `[TR]`'s own proofs read it the
other way, on borrow-free resources and at an unrestricted `α`: Lemma 6.121
(`↺↦`, p. 32) closes with "it suffices if `@(ℓ ↦ own(v)) ⊐ α`, **which holds by
definition**", and Lemma 6.124 (p. 33) with "`@∅ ⊐ α` … hold by definition".
Neither carries a side condition on `α`.

So the relation constrains the `imm` and `mut` cells and says nothing about the
`own` ones — which is `CellU.InStratum` clause for clause (`own ↦ True`,
`imm ↦ ⊓β̄ ⊐ α`, `mut ↦ β ⊐ α`), and `ResU.InStratum` over the codomain.  That
is Fig. 16's `Res_α`, so `[α]`'s conjunct is membership in the stratum the
modality names.  `[as printed]` (`[TR]` p. 5, as pp. 32–33 use it) -/
def Outlives (ρ : ResU Loc Val) (α : Life) : Prop := ρ.InStratum α

/-!
Row 5.32, continued.
-/
/-- `[α]P (ρ) ≜ P(ρ) ∧ @ρ ⊐ α`.  The glyph after `@ρ` carries no underbar at
1600 dpi: it is the strict `⊐`, where the `mut` row two lines above carries the
reflexive `⊒`.  `[CONF]` Fig. 19 (p. 415:23) prints the two conjuncts the other
way round.  `[as printed]` (`[TR]` p. 6's row) -/
def box (α : Life) (P : SPropU Loc Val) : SPropU Loc Val :=
  fun ρ => P ρ ∧ Outlives ρ α

/-!
### 5.46 · `И P̂ ≜ ∃β. ∀α ⊏ β. [α] P̂(α)` · [TR] p. 6, proposition row 18 · `[as printed]`

[TR]'s row with the `[α]` modality is taken; [CONF] Fig. 19 prints it without, and [TR]'s own 6.108 and 6.109 proofs unfold to the form with `[α]`
-/
/-- `⋔P̂ ≜ ∃β. ∀α ⊏ β. [α]P̂(α)` — one of the three rows the display gives no
`(ρ)` column, so it is derived: `∃`, the metalanguage's bounded `∀`, and `[α]`.

The documents differ here, and `[TR]` is what this follows: `[CONF]` Fig. 19
(p. 415:23) prints `⋔P̂ ≜ ∃β, ∀α ⊏ β. P̂(α)`, with no modality.  `[TR]`'s own
proofs of 6.108 and 6.109 (p. 30) unfold `⋔` to the form with `[α]`, and
`[CONF]` §4.4's prose backs it — `P` will *outlive* any shorter lifetime `α`,
and "outlives" is `[α]`.  `[as printed]` (`[TR]` p. 6's row) -/
def fresh (P : Life → SPropU Loc Val) : SPropU Loc Val :=
  fun ρ => ∃ β, ∀ α, α ⊏ β → box α (P α) ρ

end BoCa.Fig16.BoLo

namespace BoCa.Fig16
variable {Loc Val : Type}

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
theorem CellF.toLayer_toU {α : Life} (x : CellF Loc Val α (fun β _ => Cell Loc Val β))
    (h : (CellF.toU x).InStratum α) : (CellF.toU x).toLayer α h = x := by
  cases x <;> rfl

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable (Loc Val)

/-- `Cell_α` as a subset of `Cell`. -/
abbrev CellS (α : Life) : Type := { ψ : CellU Loc Val // ψ.InStratum α }

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### 5.51 · — `ρ∣own,mut` is used from [TR] Def. 6.3 on with no defining row — · [TR] p. 5 gives only single-tag `ρ∣ι` · `[repair]`

Closes a printed coverage gap; [TR] Definition 6.3 and Lemma 6.52 are stated at it. Adjudicated at `BoCa/Fig16.lean` §16, which names the printed coverage gap precisely: [TR] p. 5's defining row gives only the single-tag `ρ∣ι`, while [TR] Definition 6.3 (p. 17) and Lemma 6.52 are stated at `ρ∣own,mut`, which no row defines. `restrict` is recovered as the one-tag instance, so nothing above it is restated
-/
/-- `ρ|ῑ` for a set of tags — `[TR]` §6's `ρ|own,mut`.  The p. 5 row defines
only the single-tag `ρ|ι`, which is the instance `ResU.restrict`.
`[variant: `[TR]` p. 5 prints `ρ|ι` at a single tag and uses `ρ|own,mut` from
§6 on without a defining row; this is the multi-tag form those uses need]` -/
def ResU.restrictOn (ρ : ResU Loc Val) (p : Kind → Bool) : ResU Loc Val where
  get := fun l => (ρ.get l).bind fun ψ => if p ψ.kind then some ψ else none
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨d, fun l hl => hd l (fun e => hl ?_)⟩
    show (ρ.get l).bind _ = none
    rw [e]; rfl

/-!
Row 5.51, continued.
-/
/-- `ρ|own,mut` — `[TR]` Definition 6.3 (p. 17) and Lemma 6.52.
`[variant: as `ResU.restrictOn`; no defining row is printed for the multi-tag
restriction]` -/
def ResU.exclPart (ρ : ResU Loc Val) : ResU Loc Val :=
  ρ.restrictOn (fun k => !(k == Kind.imm))

/-!
### 5.52 · `ℓ ↦ ψ` — used from [TR] Lemma 6.17 on, defined nowhere · [TR] pp. 5–6 · `[repair]`

The evident notation, given no defining row by either document; deciding `ℓ′ = ℓ` on an abstract `Loc` is where classical choice enters, so rows 5.29–5.31 and [TR] Lemmas 6.41–6.44 all carry it. Adjudicated at `BoCa/Fig16.lean` §16 with convention G8: neither document gives `ℓ ↦ ψ` a defining row, though [TR] states Lemmas 6.17, 6.22–6.29 and 6.40–6.44 at it, and deciding `ℓ′ = ℓ` on an abstract `Loc` is where classical choice enters. The alternative is rejected with a reason — a `[DecidableEq Loc]` instance argument would put a hypothesis into the printed statements of 6.41–6.44 — and `docs/axiom-ledger.md` names the cluster rather than burying it
-/
open Classical in
/-- `ℓ ↦ ψ` — the singleton resource.  Neither document gives it a defining
row; it is the evident notation, used from `[TR]` Lemma 6.17 on.
Convention **G8**: deciding `ℓ′ = ℓ` on an abstract `Loc` is `Classical`, which
is where every statement about `ℓ ↦ ψ` picks up `Classical.choice`.  The
alternative — a `[DecidableEq Loc]` instance argument — would put a hypothesis
into the printed statements of 6.41–6.44, and statements are stone.
`[about ours: the notation both documents use without a defining row]` -/
noncomputable def ResU.single (l : Loc) (ψ : CellU Loc Val) : ResU Loc Val where
  get := fun l' => if l' = l then some ψ else none
  finite := by
    refine ⟨[l], fun l' h => ?_⟩
    by_cases e : l' = l
    · exact e ▸ List.mem_singleton.mpr rfl
    · exact absurd (if_neg e) h

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
open Classical in
@[simp] theorem ResU.single_get_self (l : Loc) (ψ : CellU Loc Val) :
    (ResU.single l ψ).get l = some ψ := if_pos rfl

end BoCa.Fig16

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
### 5.29 · `ℓ ↦ v  (ρ) ≜ ρ = ℓ ↦ own(v)` · [TR] p. 6, proposition row 1 · `[as printed]`

The singleton is `BoCa.Fig16.ResU.single` (row 5.52), which neither document gives a defining row
-/
/-- `ℓ ↦ v (ρ) ≜ ρ = ℓ ↦ own(v)`. -/
noncomputable def ptoOwn (l : Loc) (v : Val) : SPropU Loc Val :=
  fun ρ => ρ = ResU.single l (CellU.ownOf v)

end BoCa.Fig16.BoLo

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### 5.53 · `ρ/ℓ` — the `/` of `ρ₁/dom(ρ₂)` and of `π(ℓ)/ℓ` · [TR] p. 5, rows 9 and 19 · `[repair]`

Domain subtraction is used twice on p. 5 and defined nowhere; [CONF] Fig. 19 writes the same operation with a set-minus. Adjudicated at `BoCa/Fig16.lean` §16 and §20e and at the declaration: both uses are on [TR] p. 5 and neither document defines the operation, [CONF] Fig. 19 writing it as a set-minus; the classical equality test is convention G8, already opened by `BoCa.Fig16.ResU.single`
-/
open Classical in
/-- `ρ/ℓ` — `ρ` with the cell at `ℓ` removed.  `[TR]` p. 5 writes `/` for domain
subtraction in `◐`'s own defining row (`ρ₁/dom(ρ₂) ⊎ …`) and in `reb_α`'s
`π(ℓ)/ℓ`, and gives it no defining row anywhere; `[CONF]` Fig. 19 writes the same
operation `π(ℓ) ∖ ℓ`.  Deciding `ℓ′ = ℓ` on an abstract `Loc` is convention
**G8**, the door `ResU.single` already opens.
`[about ours: the notation both documents use without a defining row]` -/
noncomputable def ResU.del (ρ : ResU Loc Val) (l : Loc) : ResU Loc Val where
  get := fun l' => if l' = l then none else ρ.get l'
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨d, fun l' h => hd l' (fun e => h ?_)⟩
    show (if l' = l then none else ρ.get l') = none
    by_cases f : l' = l
    · exact if_pos f
    · rw [if_neg f]; exact e

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
open Classical in
@[simp] theorem ResU.del_get_self (ρ : ResU Loc Val) (l : Loc) :
    (ρ.del l).get l = none := if_pos rfl

/-!
### 5.55 · — the index set of the `ex`/`ag` comprehensions and of `dom(ρ′)` — · [TR] p. 5, rows 11, 12, 19 · `[repair]`

The location index set the family reading of rows 5.20 and 5.21 needs; the `Nodup` field is what makes a list of pairs a function. Adjudicated at `BoCa/Fig16.lean` §16 and §20e and at each declaration: `Sites` is convention G6's index set, the thing `∃ℓ. ρ(ℓ) = mut(…)` ranges over and `cod(ρ∣mut)` does not, so it inherits `docs/boca-rules.md` §12.36's argument; `Dom` is `Sites` with the tag dropped, which is what `reb_α`'s `π : dom(ρ′) → Res` needs
-/
/-- `d` lists the locations of `ρ` carrying a cell of tag `k`, each exactly
once.  This is convention G6's index set: it is what `∃ ℓ. ρ(ℓ) = mut(…)`
ranges over in `[TR]` p. 5's comprehension and what `cod(ρ|mut)` ranges over in
`[CONF]` Fig. 18a.
`[about ours: the index set of the printed comprehension, named]` -/
def ResU.Sites (ρ : ResU Loc Val) (k : Kind) (d : List Loc) : Prop :=
  d.Nodup ∧ ∀ l, l ∈ d ↔ ∃ ψ, ρ.get l = some ψ ∧ ψ.kind = k

/-!
Row 5.55, continued.
-/
/-- `d` lists the locations of `ρ`, each exactly once — `dom(ρ)` as a list.  This
is `ResU.Sites` (§16) with the tag restriction dropped: the walks' families are
indexed by the locations carrying one tag, where `reb_α`'s `π` is indexed by all
of `dom(ρ′)`.  `dom(π(ℓ)) = {ℓ}` is this at the one-element list.  The `Nodup` is
what makes a list of pairs a *function* on `dom(ρ′)`.
`[about ours: the index set of a printed family, named, as `ResU.Sites` names the
walks']` -/
def ResU.Dom (ρ : ResU Loc Val) (d : List Loc) : Prop :=
  d.Nodup ∧ ∀ l, l ∈ d ↔ ∃ ψ, ρ.get l = some ψ

/-!
### 5.56 · `⨀` — the iterated composition, with no printed empty case · [TR] p. 5, rows 11, 12, 19 · `[repair]`

The fold behind the printed large operator. The empty case is printed nowhere, and without it `ex(ρ)_◖` would have no value on any mut-free ρ — so `✓ρ` on the simplest resources depends on it; `BoCa.Fig16.BigComp.perm` makes the fold order irrelevant. Adjudicated at `BoCa/Fig16.lean` §16: the empty case is necessary and not convenient — neither document prints it, and without it `ex(ρ)_◖` has no value on any mut-free ρ — and `BoCa.Fig16.BigComp.perm` discharges the order-independence out of [TR] Lemmas 6.1–6.3 instead of assuming it
-/
/-- `⨀_◐` — the iterated composition, folded right with `∅` at the end.  By
Lemma 6.4 (`ρ ◐ ∅ = ρ`, §20) that is the fold of the list.  Which fold is taken
is irrelevant exactly when `[TR]` Lemmas 6.1–6.3 hold, and they are proved in
§20; `BigComp.perm` (§20a) is that independence, so the graph may be stated at
one fold without loss.  `BigComp.nil : ⨀∅ = ∅` is ours: neither document prints
the empty case, and without it `ex(ρ)_◐` would be undefined for every mut-free
`ρ`.
`[about ours: the fold shape of a printed iterated operator, and the
existential over its order]` -/
inductive BigComp (R : CellU Loc Val → CellU Loc Val → Prop)
    (C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop) :
    List (ResU Loc Val) → ResU Loc Val → Prop where
  | nil : BigComp R C [] PMap.empty
  | cons {σ τ ρ : ResU Loc Val} {σs : List (ResU Loc Val)} :
      BigComp R C σs τ → ResU.Comp R C σ τ ρ → BigComp R C (σ :: σs) ρ

/-!
### 5.57 · — the paper's `SProp_α ⊆ SProp_{α′} ⊆ SProp` is a set inclusion — · [TR] p. 4, rows 1 and 6 · `[repair]`

Extension by falsity outside the smaller stratum, which is how the inclusion is encoded; clause (3) of row 5.16 and the invariant match of row 5.31 both go through it. `BoCa.Fig16.SPropS.toU_range` names the cost: `SProp_α` becomes the subset of `SProp` whose members hold only in `Res_α`. Adjudicated at `BoCa/Fig16.lean` §8 with §24: `P̂ : Val → SProp_α` is already a family of subsets of `Res_{α′}`, so writing the paper's inclusion out is extension by falsity and changes no statement; §24 names the price rather than hiding it, and `BoCa.Fig16.SPropS.toU_range` proves it
-/
/-- `SProp_α ⊆ SProp_{α'}`, as the image of the inclusion of subsets. -/
def SPropS.embed {a a' : Life} (P : Val → SPropS Loc Val a) : Val → SPropS Loc Val a' :=
  fun v r => ∃ h : r.val.InStratum a, P v ⟨r.val, h⟩

/-!
Row 5.57, continued.
-/
/-- `P̂ ∧ Q̂`, the invariant `○` clause 3 builds, at the stratum `α ⊓ β`. -/
def SPropS.conj {a b : Life} (P : Val → SPropS Loc Val a) (Q : Val → SPropS Loc Val b) :
    Val → SPropS Loc Val (a ⊓ b) :=
  fun v r => SPropS.embed P v r ∧ SPropS.embed Q v r

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
theorem SPropS.conj_holds {a b : Life} {P : Val → SPropS Loc Val a}
    {Q : Val → SPropS Loc Val b} {v : Val} {ρ : ResU Loc Val}
    (ha : ρ.InStratum a) (hb : ρ.InStratum b)
    (hP : P v ⟨ρ, ha⟩) (hQ : Q v ⟨ρ, hb⟩) :
    SPropS.conj P Q v ⟨ρ, ha.mono inf_le_left⟩ := ⟨⟨ha, hP⟩, ⟨hb, hQ⟩⟩

/-!
Row 5.57, continued.
-/
/-- `SProp_α ⊆ SProp` — §8's inclusion, at the union.  `[about ours: the
encoding of a set-theoretic inclusion, not a change of statement]` -/
def SPropS.toU {a : Life} (P : SPropS Loc Val a) : SPropU Loc Val :=
  fun ρ => ∃ h : ρ.InStratum a, P ⟨ρ, h⟩

/-!
Row 5.57, continued.
-/
/-- The other way: restriction along `Res_α ⊆ Res`. -/
def SPropU.toS (a : Life) (P : SPropU Loc Val) : SPropS Loc Val a := fun r => P r.val

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
theorem SPropU.toU_toS_iff (a : Life) (P : SPropU Loc Val) (ρ : ResU Loc Val) :
    SPropS.toU (SPropU.toS a P) ρ ↔ (P ρ ∧ ρ.InStratum a) :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-!
Row 5.57, continued.
-/
/-- **`SProp_α` is the set of propositions that hold only in `Res_α`.**  The
image of `SPropS.toU` is `{P | ∀ρ. P(ρ) ⇒ ρ ∈ Res_α}`, which is what
`SProp_α ⊆ SProp` says once a proposition is a set of resources.
`[about ours: the image of the encoding above, which is where the paper's
`SProp_α` goes]` -/
theorem SPropS.toU_range (a : Life) (P : SPropU Loc Val) :
    (∃ Q : SPropS Loc Val a, SPropS.toU Q = P) ↔ ∀ ρ, P ρ → ρ.InStratum a := by
  constructor
  · rintro ⟨Q, rfl⟩ ρ h
    exact h.1
  · intro h
    refine ⟨SPropU.toS a P, funext fun ρ => propext ?_⟩
    rw [SPropU.toU_toS_iff]
    exact ⟨fun k => k.1, fun k => ⟨k, h ρ k⟩⟩

end BoCa.Fig16

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
Row 5.57, continued.
-/
/-- `SProp_β ⊆ SProp` at a family, which is the shape a `mut` cell's invariant
has: `SPropS.toU` at each value. -/
def ofS {b : Life} (Q : Val → SPropS Loc Val b) : Val → SPropU Loc Val :=
  fun v => SPropS.toU (Q v)

end BoCa.Fig16.BoLo

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
Row 5.58, continued.
-/
/-- Unfold one layer of `Cell_α`. -/
def Cell.toF {α : Life} (ψ : Cell Loc Val α) : CellF Loc Val α (fun β _ => Cell Loc Val β) :=
  cast (Cell_eq Loc Val α) ψ

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
/-- The injection `Cell_α ↪ Cell`. -/
def Cell.toU {α : Life} (ψ : Cell Loc Val α) : CellU Loc Val := CellF.toU ψ.toF

theorem Cell.toU_inStratum {α : Life} (ψ : Cell Loc Val α) : ψ.toU.InStratum α :=
  CellF.toU_inStratum ψ.toF

/-- The injection `Res_α ↪ Res`.  The covering list is unchanged, so the `fin`
mark transports. -/
def Res.toU {α : Life} (ρ : Res Loc Val α) : ResU Loc Val := ρ.map Cell.toU

theorem Res.toU_inStratum {α : Life} (ρ : Res Loc Val α) : ρ.toU.InStratum α := by
  intro l ψ e
  have he : Option.map Cell.toU (ρ.get l) = some ψ := e
  cases f : ρ.get l with
  | none => rw [f] at he; exact absurd he (by simp)
  | some ψ' =>
      rw [f] at he
      simp only [Option.map_some, Option.some.injEq] at he
      exact he ▸ ψ'.toU_inStratum

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable (Loc Val)
variable {Loc Val}

/-- The forward half of `Res.stratumEquiv`, named. -/
def Res.toS {α : Life} (ρ : Res Loc Val α) : ResS Loc Val α := ⟨ρ.toU, ρ.toU_inStratum⟩

@[simp] theorem Res.val_toS {α : Life} (ρ : Res Loc Val α) : (ρ.toS).val = ρ.toU := rfl

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- The witness of an `imm` cell, as a member of `Res`. -/
def ImmU.res (i : ImmU Loc Val) : ResU Loc Val := i.ρ.toU

/-- The witness of a `mut` cell, as a member of `Res`. -/
def MutU.res (m : MutU Loc Val) : ResU Loc Val := m.ρ.toU

/-- The witness of a cell, as a member of `Res`.  An `own` cell has none and `∅`
stands in for it.  **Ours** — the print never names this projection; it is here
so that "the same `ρ`" can be read off a composition without inverting it. -/
def CellU.wit : CellU Loc Val → ResU Loc Val
  | .own _ => PMap.empty
  | .imm i => i.res
  | .mut m => m.res

@[simp] theorem CellU.wit_ownOf (v : Val) :
    (CellU.ownOf (Loc := Loc) v).wit = PMap.empty := rfl

/-!
### 5.20 · `ex(ρ)_◖ ≜ ρ∣own ◖ ρ∣mut ◖ ⨀{ex(ρ′)_◖ ∣ ∃ℓ. ρ(ℓ) = mut(_,_,ρ′,_)}` · [TR] p. 5, operation row 11 · `[repair]`

The printed comprehension is a SET and the Lean composes a FAMILY indexed by locations. On the set reading two `mut` cells with equal witnesses compose once, [TR] Lemma 6.18 is false, and a resource with two mutable borrows of one cell would be admitted (`BoCa.Fig16.WalkNeg.set_reading_would_admit`); declared at `docs/boca-rules.md` §12.36. Adjudicated at `docs/boca-rules.md` §12.36 and `BoCa/Fig16.lean` §17 with convention G6: one reading of the printed set-builder makes a printed lemma false, since on the set reading [TR] Lemma 6.18 fails at two `mut` cells with equal witnesses, and the crux is compiled rather than asserted. [CONF] Fig. 18a writes the same row as `cod(ρ∣mut)`
-/
mutual

/-- `ex(ρ)_◐ = σ` — the exclusive walk, as a graph.  The list `w` pairs each
`mut` location of `ρ` with the walk of the cell's witness (convention G6);
`hs` says the locations are exactly those, each once; `hb` is `⨀`; `hnm` is
`ρ|own ◐ ρ|mut`; `hσ` is the outer `◐`.  `w` is bound here and appears in no
statement.
`[variant: the printed comprehension is a set and this is the family it indexes
(convention G6, §17); the recursive subscript is `[TR]`'s generic `◐`, not
`[CONF]` Fig. 18a's `•`]` -/
inductive ExW (R : CellU Loc Val → CellU Loc Val → Prop)
    (C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop) :
    ResU Loc Val → ResU Loc Val → Prop where
  | mk {ρ σ nm b : ResU Loc Val} {w : List (Loc × ResU Loc Val)}
      (hs : ResU.Sites ρ Kind.mut (w.map Prod.fst))
      (hw : ExWits R C ρ w)
      (hb : BigComp R C (w.map Prod.snd) b)
      (hnm : ResU.Comp R C (ρ.restrict Kind.own) (ρ.restrict Kind.mut) nm)
      (hσ : ResU.Comp R C nm b σ) :
      ExW R C ρ σ

/-- The family `{ex(ρ′)_◐ | ∃ℓ. ρ(ℓ) = mut(_,_,ρ′,_)}`, tagged by location. -/
inductive ExWits (R : CellU Loc Val → CellU Loc Val → Prop)
    (C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop) :
    ResU Loc Val → List (Loc × ResU Loc Val) → Prop where
  | nil {ρ : ResU Loc Val} : ExWits R C ρ []
  | cons {ρ e : ResU Loc Val} {l : Loc} {w : List (Loc × ResU Loc Val)}
      (ψ : CellU Loc Val) (hψ : ρ.get l = some ψ) (hk : ψ.kind = Kind.mut)
      (he : ExW R C ψ.wit e) (hw : ExWits R C ρ w) :
      ExWits R C ρ ((l, e) :: w)

end

/-!
Row 5.58, continued.
-/
/-- Fold one layer of `Cell_α`. -/
def Cell.ofF {α : Life} (x : CellF Loc Val α (fun β _ => Cell Loc Val β)) : Cell Loc Val α :=
  cast (Cell_eq Loc Val α).symm x

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
@[simp] theorem Cell.toF_ofF {α : Life} (x : CellF Loc Val α (fun β _ => Cell Loc Val β)) :
    (Cell.ofF x).toF = x := cast_right _ x

@[simp] theorem Cell.ofF_toF {α : Life} (ψ : Cell Loc Val α) : Cell.ofF ψ.toF = ψ :=
  cast_left _ ψ

/-- Its inverse on the cells that lie in the stratum. -/
def CellU.toStratum (α : Life) (ψ : CellU Loc Val) (h : ψ.InStratum α) : Cell Loc Val α :=
  Cell.ofF (ψ.toLayer α h)

def optToStratum (α : Life) : (o : Option (CellU Loc Val)) →
    (∀ ψ, o = some ψ → ψ.InStratum α) → Option (Cell Loc Val α)
  | none, _ => none
  | some ψ, h => some (ψ.toStratum α (h ψ rfl))

theorem optToStratum_eq_none {α : Life} {o : Option (CellU Loc Val)}
    (k : ∀ ψ, o = some ψ → ψ.InStratum α) (e : o = none) : optToStratum α o k = none := by
  subst e; rfl

def ResU.toStratum {α : Life} (ρ : ResU Loc Val) (h : ρ.InStratum α) : Res Loc Val α where
  get := fun l => optToStratum α (ρ.get l) (fun ψ e => h l ψ e)
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨d, fun l hl => hd l (fun e => ?_)⟩
    exact hl (optToStratum_eq_none _ e)

theorem CellU.toU_toStratum {α : Life} (ψ : CellU Loc Val) (h : ψ.InStratum α) :
    (ψ.toStratum α h).toU = ψ := by
  unfold Cell.toU CellU.toStratum
  rw [Cell.toF_ofF, CellU.toU_toLayer]

theorem optToStratum_toU {α : Life} (o : Option (CellU Loc Val))
    (k : ∀ ψ, o = some ψ → ψ.InStratum α) :
    Option.map Cell.toU (optToStratum α o k) = o := by
  cases o with
  | none => rfl
  | some ψ => exact congrArg some (CellU.toU_toStratum ψ _)

theorem ResU.toU_toStratum {α : Life} (ρ : ResU Loc Val) (h : ρ.InStratum α) :
    (ρ.toStratum h).toU = ρ :=
  PMap.ext fun l => optToStratum_toU (ρ.get l) _

theorem Cell.toStratum_toU {α : Life} (ψ : Cell Loc Val α) (h : ψ.toU.InStratum α) :
    ψ.toU.toStratum α h = ψ := by
  unfold CellU.toStratum
  rw [show ψ.toU.toLayer α h = ψ.toF from CellF.toLayer_toU ψ.toF h, Cell.ofF_toF]

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable (Loc Val)
variable {Loc Val}

/-!
Row 5.48, continued.
-/
/-- **`Cell_α ≃ {ψ ∈ Cell | ψ ∈ Cell_α}`.**  The paper's `Cell_α ⊆ Cell`, as an
equivalence between the recursively defined stratum and the corresponding
subset of the union.  `[about ours: the inclusion is between sets in the paper
and has to be proved here, because the strata are distinct types]` -/
def Cell.stratumEquiv (α : Life) : Equiv (Cell Loc Val α) (CellS Loc Val α) where
  toFun ψ := ⟨ψ.toU, ψ.toU_inStratum⟩
  invFun c := c.val.toStratum α c.property
  leftInv ψ := Cell.toStratum_toU ψ _
  rightInv c := Subtype.ext (CellU.toU_toStratum c.val c.property)

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
theorem optToStratum_map {α : Life} (o : Option (Cell Loc Val α))
    (k : ∀ ψ, Option.map Cell.toU o = some ψ → ψ.InStratum α) :
    optToStratum α (Option.map Cell.toU o) k = o := by
  cases o with
  | none => rfl
  | some ψ => exact congrArg some (Cell.toStratum_toU ψ _)

theorem Res.toStratum_toU {α : Life} (ρ : Res Loc Val α) (h : ρ.toU.InStratum α) :
    ρ.toU.toStratum h = ρ :=
  PMap.ext fun l => optToStratum_map (ρ.get l) _

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable (Loc Val)
variable {Loc Val}

/-!
Row 5.48, continued.
-/
/-- **`Res_α ≃ {ρ ∈ Res | ρ ∈ Res_α}`.**  Same statement one level up.
`[about ours: as Cell.stratumEquiv]` -/
def Res.stratumEquiv (α : Life) : Equiv (Res Loc Val α) (ResS Loc Val α) where
  toFun ρ := ⟨ρ.toU, ρ.toU_inStratum⟩
  invFun r := r.val.toStratum r.property
  leftInv ρ := Res.toStratum_toU ρ _
  rightInv r := Subtype.ext (ResU.toU_toStratum r.val r.property)

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
/-- The backward half of `Res.stratumEquiv`, named. -/
def ResS.toRes {α : Life} (r : ResS Loc Val α) : Res Loc Val α := r.val.toStratum r.property

@[simp] theorem ResS.toS_toRes {α : Life} (r : ResS Loc Val α) : r.toRes.toS = r :=
  (Res.stratumEquiv α).rightInv r

@[simp] theorem Res.toRes_toS {α : Life} (ρ : Res Loc Val α) : ρ.toS.toRes = ρ :=
  (Res.stratumEquiv α).leftInv ρ

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

@[simp] theorem ResS.toU_toRes {α : Life} (r : ResS Loc Val α) : r.toRes.toU = r.val :=
  ResU.toU_toStratum r.val r.property

/-- `imm(ᾱ, v, ρ)`, with `ρ : Res` and `h` the print's own typing constraint
`ρ : Res_{⊔ᾱ}`.  `[as printed]` -/
def CellU.immOf (s : LSet) (v : Val) (ρ : ResU Loc Val)
    (h : ρ.InStratum s.join) : CellU Loc Val :=
  .imm ⟨s, v, ResS.toRes ⟨ρ, h⟩⟩

@[simp] theorem CellU.at_immOf (s : LSet) (v : Val) (ρ : ResU Loc Val)
    (h : ρ.InStratum s.join) : (immOf s v ρ h).at = s.meet := rfl

/-- `mut(β, v, ρ, P̂)`, with `ρ : Res`, `h` the print's `ρ : Res_β`, `P̂` a
predicate on `Res_β` — i.e. an element of `Val → SProp_β`, read on the union
through §6's equivalence — and `hw` the printed refinement `P̂(v)(ρ)`.
`mutOf` is injective in `P̂` (`CellU.mutOf_inj`), so the cell remembers exactly
the subset of `Res_β` the paper's cell remembers, and no more.
`[as printed]` -/
def CellU.mutOf (b : Life) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum b)
    (P : Val → SPropS Loc Val b) (hw : P v ⟨ρ, h⟩) : CellU Loc Val :=
  .mut ⟨b, v, ResS.toRes ⟨ρ, h⟩, fun v r => P v r.toS, by
    show P v (ResS.toRes ⟨ρ, h⟩).toS
    rw [ResS.toS_toRes]
    exact hw⟩

@[simp] theorem CellU.at_mutOf (b : Life) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum b)
    (P : Val → SPropS Loc Val b) (hw : P v ⟨ρ, h⟩) : (mutOf b v ρ h P hw).at = b := rfl

@[simp] theorem CellU.inStratum_immOf (α : Life) (s : LSet) (v : Val) (ρ : ResU Loc Val)
    (h : ρ.InStratum s.join) : (immOf s v ρ h).InStratum α ↔ s.meet ⊐ α := Iff.rfl

@[simp] theorem CellU.inStratum_mutOf (α : Life) (b : Life) (v : Val) (ρ : ResU Loc Val)
    (h : ρ.InStratum b) (P : Val → SPropS Loc Val b) (hw : P v ⟨ρ, h⟩) :
    (mutOf b v ρ h P hw).InStratum α ↔ b ⊐ α := Iff.rfl

@[simp] theorem CellU.kind_immOf (s : LSet) (v : Val) (ρ : ResU Loc Val)
    (h : ρ.InStratum s.join) : (CellU.immOf s v ρ h).kind = Kind.imm := rfl

@[simp] theorem CellU.kind_mutOf (b : Life) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum b)
    (P : Val → SPropS Loc Val b) (hw : P v ⟨ρ, h⟩) :
    (CellU.mutOf b v ρ h P hw).kind = Kind.mut := rfl

@[simp] theorem CellU.erase_immOf (s : LSet) (v : Val) (ρ : ResU Loc Val)
    (h : ρ.InStratum s.join) : (CellU.immOf s v ρ h).erase = v := rfl

@[simp] theorem CellU.erase_mutOf (b : Life) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum b)
    (P : Val → SPropS Loc Val b) (hw : P v ⟨ρ, h⟩) :
    (CellU.mutOf b v ρ h P hw).erase = v := rfl

@[simp] theorem CellU.wit_immOf (s : LSet) (v : Val) (ρ : ResU Loc Val)
    (h : ρ.InStratum s.join) : (CellU.immOf s v ρ h).wit = ρ :=
  ResS.toU_toRes ⟨ρ, h⟩

@[simp] theorem CellU.wit_mutOf (b : Life) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum b)
    (P : Val → SPropS Loc Val b) (hw : P v ⟨ρ, h⟩) :
    (CellU.mutOf b v ρ h P hw).wit = ρ :=
  ResS.toU_toRes ⟨ρ, h⟩

/-!
### 5.13 · `ψ₁ ▸◂ ψ₂ ≜ ∃ᾱ₁,ᾱ₂,v,ρ. ψ₁ = imm(ᾱ₁,v,ρ) ∧ ψ₂ = imm(ᾱ₂,v,ρ)` · [TR] p. 5, operation row 4 · `[as printed]`

The extra existential binders are the print's own typing constraints on ρ and are `Prop`s, hence proof-irrelevant; the single printed ρ is one Lean term compared by equality
-/
/-- `ψ₁ ▶◀ ψ₂` — strict cell compatibility.  The print binds `ᾱ₁, ᾱ₂, v, ρ`;
the two extra binders here are its own typing constraints `ρ : Res_{⊔ᾱᵢ}`,
written as propositions because `ρ` ranges over `Res`.  They are `Prop`s, so
they add nothing.  `[as printed]` -/
def CellU.CompatS (ψ₁ ψ₂ : CellU Loc Val) : Prop :=
  ∃ (s₁ s₂ : LSet) (v : Val) (ρ : ResU Loc Val)
    (h₁ : ρ.InStratum s₁.join) (h₂ : ρ.InStratum s₂.join),
    ψ₁ = CellU.immOf s₁ v ρ h₁ ∧ ψ₂ = CellU.immOf s₂ v ρ h₂

/-!
### 5.15 · `ψ₁ ● ψ₂ ≜ imm(ᾱ₁ ∪ ᾱ₂, v, ρ)` when both are `imm` at the same `v`, ρ · [TR] p. 5, operation row 6 · `[as printed]`

Given both ways, as a function of the ▸◂ proof and as a graph; `BoCa.Fig16.CellU.compS_defined_iff` says the domain is exactly ▸◂, and `BoCa.Fig16.LSet.union` is round set union with the bounds recomputed (`BoCa.Fig16.LSet.ext`: no extra data)
-/
/-- `ψ₁ ● ψ₂ = ψ` — the printed equation as a graph, so that the resource-level
schema of §12 can be instantiated at it.  `[as printed]` (as a graph — G4) -/
def CellU.CompS (ψ₁ ψ₂ ψ : CellU Loc Val) : Prop :=
  ∃ (s₁ s₂ : LSet) (v : Val) (ρ : ResU Loc Val)
    (h₁ : ρ.InStratum s₁.join) (h₂ : ρ.InStratum s₂.join)
    (h₃ : ρ.InStratum (s₁ ∪ s₂).join),
    ψ₁ = CellU.immOf s₁ v ρ h₁ ∧ ψ₂ = CellU.immOf s₂ v ρ h₂ ∧
    ψ = CellU.immOf (s₁ ∪ s₂) v ρ h₃

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
theorem CellU.immOf_inj {s₁ s₂ : LSet} {v₁ v₂ : Val} {ρ₁ ρ₂ : ResU Loc Val}
    {h₁ : ρ₁.InStratum s₁.join} {h₂ : ρ₂.InStratum s₂.join}
    (e : immOf s₁ v₁ ρ₁ h₁ = immOf s₂ v₂ ρ₂ h₂) : s₁ = s₂ ∧ v₁ = v₂ ∧ ρ₁ = ρ₂ := by
  simp only [immOf] at e
  injection e with e'
  refine ⟨congrArg ImmU.ls e', congrArg ImmU.v e', ?_⟩
  have := congrArg ImmU.res e'
  simpa [ImmU.res] using this

/-- `imm(ᾱ, v, ρ)` really is the general `imm` cell. -/
theorem ImmU.immOf_eta (i : ImmU Loc Val) :
    CellU.immOf i.ls i.v i.res i.ρ.toU_inStratum = .imm i := by
  show CellU.imm _ = CellU.imm i
  refine congrArg CellU.imm (ImmU.ext rfl rfl ?_)
  simp only [heq_eq_eq]
  exact Res.toRes_toS i.ρ

theorem CellU.immOf_congr {s s' : LSet} {v v' : Val} {ρ ρ' : ResU Loc Val}
    (hs : s = s') (hv : v = v') (hρ : ρ = ρ')
    (h : ρ.InStratum s.join) (h' : ρ'.InStratum s'.join) :
    CellU.immOf s v ρ h = CellU.immOf s' v' ρ' h' := by
  subst hs; subst hv; subst hρ; rfl

/-- `●` is single-valued. -/
theorem CellU.CompS.functional {ψ₁ ψ₂ ψ ψ' : CellU Loc Val}
    (h : CellU.CompS ψ₁ ψ₂ ψ) (h' : CellU.CompS ψ₁ ψ₂ ψ') : ψ = ψ' := by
  obtain ⟨s₁, s₂, v, ρ, k₁, k₂, k₃, e₁, e₂, e₃⟩ := h
  obtain ⟨t₁, t₂, w, σ, m₁, m₂, m₃, f₁, f₂, f₃⟩ := h'
  obtain ⟨hs₁, hv₁, hρ₁⟩ := CellU.immOf_inj (e₁.symm.trans f₁)
  obtain ⟨hs₂, -, -⟩ := CellU.immOf_inj (e₂.symm.trans f₂)
  subst hs₁; subst hs₂; subst hv₁; subst hρ₁
  rw [e₃, f₃]

/-!
Row 5.17, continued.
-/
/-- `ρ₁ ▶◀ ρ₂` — the schema at the strict mode.  `[CONF]` uses this in
Fig. 18a and Fig. 19 and never defines it, and `[TR]` uses it in Lemmas 6.9 and
6.37 without a defining row; both obtain it by instantiating the schema.
Instantiating the printed schema's parameters is not a difference in
statement (inventory convention 5), so this is the print's own relation.
`[as printed]` -/
abbrev ResU.CompatS (ρ₁ ρ₂ : ResU Loc Val) : Prop := ResU.Compat CellU.CompatS ρ₁ ρ₂

/-!
Row 5.18, continued.
-/
/-- `ρ₁ ● ρ₂ = ρ` — the schema at the strict mode.
Instantiating the printed schema's parameters is not a difference in
statement (inventory convention 5).  Documents-differ, resolved toward
`[TR]` and declared: `[CONF]` Fig. 16's own `ρ₁ • ρ₂` row is unguarded and
its comprehension ends `ρ₂ = ψ₂`, which does not type.  `[as printed]` -/
abbrev ResU.CompS (ρ₁ ρ₂ ρ : ResU Loc Val) : Prop :=
  ResU.Comp CellU.CompatS CellU.CompS ρ₁ ρ₂ ρ

/-!
Row 5.20, continued.
-/
/-- `ex(ρ)_●` — the exclusive walk at the strict operator. -/
abbrev ExS (ρ σ : ResU Loc Val) : Prop := ExW CellU.CompatS CellU.CompS ρ σ

/-!
### 5.28 · `reb_α(ρ) ≜ {ρ′ ∣ @ρ ⊐ α ∧ ∃π : dom(ρ′) → Res. ρ ≥ ⨀_● π(ℓ) ∧ …}` · [TR] p. 5, operation row 19 · `[repair]`

Membership in the printed set; `π` is an association list with `Nodup` keys pinned to `dom(ρ′)`, which IS the printed function, and `ρ ≥ x` is `BoCa.Fig16.ResU.Le` from [CONF] p. 415:24 fn. 1 since [TR] uses ≥ with no defining row (row 5.54). **The `imm` clause is read at a subset**: where the print has `ρ(ℓ) = imm(_,_,_) ⇒ ρ′(ℓ) = ρ(ℓ)`, `BoCa.Fig16.ResU.RebAt` has `ρ′(ℓ) = imm(t̄, v, χ)` for a nonempty `t̄ ⊆ s̄` at `ρ(ℓ) = imm(s̄, v, χ)`, same value and witness. Adjudicated at `docs/boca-rules.md` §12.67(b): [CONF] 415:24 — *"`ρ′` must be just like a subresource of the original resource `ρ` … its imm locations are preserved at their original lifetimes"* — and [TR] 6.57's proof, which prints `ρ∣dom(ρ′ᵢ∣imm) ≤ ρ′ᵢ∣imm` (`≤`, not `=`); at this reading [TR] 6.61's *"the only interesting cases are locations `ℓ` that are in both `ρ′₁` and `ρ′₂`"* holds (`BoCa.Fig16.ResU.six61_imm_at`). The literal `ρ′(ℓ) = ρ(ℓ)` is recorded there with its cost: 6.61, 6.125 and 6.127 needed the added hypotheses `ImmSurvives`, `RebSurv` and `SplitAgree`, since a `●`-factor of an `imm` cell is `imm` over a subset
-/
/-- The body of `reb_α`'s `∀ ℓ ∈ dom(π), v, ρ″`, at one location `ℓ` and the
piece `p = π(ℓ)` the family gives it.

The first conjunct is `ℓ ∈ dom(π(ℓ))`, which the print asserts of every `ℓ` in
`dom(π)` and under none of the implications.  Then the three cases of `ρ(ℓ)`, in
the printed order: an owned cell becomes an `imm` at `{α}` over the **rest** of
its piece, `π(ℓ)/ℓ`, and carries **no** `dom(π(ℓ)) = {ℓ}`; a mutable borrow
becomes an `imm` at `{α}` over the witness it already holds, and its piece is the
cell alone; an immutable borrow passes through as an `imm` cell over a nonempty
subset of its lifetime set, at the same value and witness, and its piece is the
cell alone.

The `imm` clause is the printed `ρ′(ℓ) = ρ(ℓ)` read as `[CONF]` 415:24 describes
`reb_α`: "`ρ′` must be just like a subresource of the original resource `ρ` … its
imm locations are preserved at their original lifetimes".  A subresource of an
`imm` cell is that cell over fewer outstanding borrows (`[TR]` Definition 6.3 and
the sentence after it, p. 17), and `[TR]` 6.57's proof prints
`ρ|dom(ρ′ᵢ|imm) ≤ ρ′ᵢ|imm` — `≤`, not `=`.  `t̄ ⊆ s̄` with `t̄` nonempty keeps
every lifetime `t̄` records one `s̄` records.  `docs/boca-rules.md` §12.67.

`imm({α}, v, −)` is `CellU.immOf` at `LSet.singleton α`, whose join is `α`, and
the existential over the typing constraint is that constructor's `h` — the cell
does not depend on which proof of it is supplied.  The print binds `v` and `ρ″`
in the outer `∀`; `∀` distributes over the conjunction, so binding them at each
clause's own pattern is the same proposition.
`[variant: the `imm` clause at a nonempty subset of `ρ(ℓ)`'s lifetime set,
`docs/boca-rules.md` §12.67]`
(`[TR]` p. 5's `reb_α`) -/
def ResU.RebAt (α : Life) (ρ ρ' : ResU Loc Val) (l : Loc) (p : ResU Loc Val) : Prop :=
  (∃ ψ, p.get l = some ψ) ∧
  (∀ v : Val, ρ.get l = some (CellU.ownOf v) →
      ∃ h : (p.del l).InStratum (LSet.singleton α).join,
        ρ'.get l = some (CellU.immOf (LSet.singleton α) v (p.del l) h)) ∧
  (∀ (b : Life) (v : Val) (χ : ResU Loc Val) (hb : χ.InStratum b)
      (P : Val → SPropS Loc Val b) (hw : P v ⟨χ, hb⟩),
      ρ.get l = some (CellU.mutOf b v χ hb P hw) →
        (∃ h : χ.InStratum (LSet.singleton α).join,
            ρ'.get l = some (CellU.immOf (LSet.singleton α) v χ h)) ∧
        ResU.Dom p [l]) ∧
  (∀ (s : LSet) (v : Val) (χ : ResU Loc Val) (h : χ.InStratum s.join),
      ρ.get l = some (CellU.immOf s v χ h) →
        (∃ (t : LSet) (ht : χ.InStratum t.join), (∀ x, t.mem x → s.mem x) ∧
            ρ'.get l = some (CellU.immOf t v χ ht)) ∧ ResU.Dom p [l])

end BoCa.Fig16

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
### 5.35 · `P₁ ⋆ P₂ (ρ) ≜ ∃ρ₁,ρ₂. ρ = ρ₁ ● ρ₂ ∧ P₁(ρ₁) ∧ P₂(ρ₂)` · [TR] p. 6, proposition row 7 · `[as printed]`

The strict composition's graph, so definedness is asserted rather than presupposed — which is what [CONF] Fig. 19 writes out
-/
/-- `P₁ ⋆ P₂ (ρ) ≜ ∃ρ₁,ρ₂. ρ = ρ₁ ● ρ₂ ∧ P₁(ρ₁) ∧ P₂(ρ₂)`.  `ResU.CompS` is
the composition's graph, so definedness is asserted rather than presupposed
(G4); `[CONF]` Fig. 19 (p. 415:23) writes that out, binding `∃ρ₁, ρ₂ ▶◀ ρ₁`
before the equation.  `[as printed]` (`[TR]` p. 6's row) -/
def sep (P Q : SPropU Loc Val) : SPropU Loc Val :=
  fun ρ => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ P ρ₁ ∧ Q ρ₂

/-!
### 5.36 · `P₁ –⋆ P₂ (ρ) ≜ ∀ρ₁,ρ₂. P₁(ρ₁) ⇒ ρ ● ρ₁ = ρ₂ ⇒ P₂(ρ₂)` · [TR] p. 6, proposition row 8 · `[as printed]`

[TR]'s composition order is taken ([CONF] Fig. 19 composes the other way); [TR] Lemma 6.2 makes them the same proposition
-/
/-- `P₁ ─⋆ P₂ (ρ) ≜ ∀ρ₁,ρ₂. P₁(ρ₁) ⇒ ρ ● ρ₁ = ρ₂ ⇒ P₂(ρ₂)` — an equation on
the composite, not a compatibility premise.  `[CONF]` Fig. 19 states the row at
`ρ₂` and composes `ρ₁ ● ρ₂` where `[TR]` composes `ρ ● ρ₁`; `[TR]` Lemma 6.2 is
that they are the same proposition.  `[as printed]` (`[TR]` p. 6's row) -/
def wand (P Q : SPropU Loc Val) : SPropU Loc Val :=
  fun ρ => ∀ ρ₁ ρ₂, P ρ₁ → ResU.CompS ρ ρ₁ ρ₂ → Q ρ₂

end BoCa.Fig16.BoLo

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### 5.54 · `ρ₁ ≤ ρ₃ ≜ ∃ρ₂ ▶◀ ρ₁. ρ₁ ● ρ₂ = ρ₃` — `≥` used in `reb_α`, `≤` in [TR] Def. 6.3 · [CONF] p. 415:24 fn. 1 (printed); [TR] p. 5, row 19 (used) · `[as printed]`

A documents-differ row, scored against the document that prints a defining row: [TR] uses the order and defines it nowhere, and [CONF] p. 415:24's footnote 1 prints `ρ₁ ≤ ρ₃ ≜ ∃ρ₂ ▶◀ ρ₁. ρ₁ ● ρ₂ = ρ₃`, read at 1200 dpi. `BoCa.Fig16.ResU.Le` is that glyph for glyph, with the operands of ▶◀ transposed, which [TR] Lemma 6.1 licenses. The declaration and `BoCa/Fig16.lean` §16 both carry `[as printed]`, and `docs/boca-rules.md` §12.37 is the retraction of the earlier `ours` reading, of which this row was the last site
-/
/-- `ρ ≤ ρ′` — `[CONF]` p. 415:24 footnote 1 (1200 dpi):
`ρ₁ ≤ ρ₃ ≜ ∃ρ₂ ▶◀ ρ₁. ρ₁ ● ρ₂ = ρ₃`.  This is that, glyph for glyph; the
operands of `▶◀` are transposed, which `[TR]` Lemma 6.1 licenses.  `[TR]` uses
`≤` in Definition 6.3 and `reb_α` and never defines it — documents-differ,
resolved toward the document that prints a defining row (§16;
`docs/boca-rules.md` §12.37).  `[as printed]` -/
def ResU.Le (ρ σ : ResU Loc Val) : Prop := ∃ τ, ResU.CompS ρ τ σ

/-!
Row 5.28, continued.
-/
/-- `ρ′ ∈ reb_α(ρ)` — `[TR]` p. 5's last row, as membership in the set it prints.

The four printed conjuncts, in order: `@ρ ⊐ α`, written at `ResU.AtLife`'s graph
so that nothing is chosen (`ResU.reb_at_iff` is the same condition at `ResU.at`);
`π : dom(ρ′) → Res` as a list of `(location, resource)` pairs whose first
projection is `dom(ρ′)` without repetition, the idiom §17 and §18 use for the
printed comprehensions; `ρ ≥ ⨀_{ℓ∈dom(π)} π(ℓ)`, the iterated **strict**
composition — the operator is a filled disc at 900 dpi — with `ρ ≥ x` read as
`ResU.Le x ρ` per `[CONF]` p. 415:24 footnote 1; and the body, `ResU.RebAt`, at
every member of the family.  `[as printed]` -/
def ResU.Reb (α : Life) (ρ ρ' : ResU Loc Val) : Prop :=
  ρ.InStratum α ∧
  ∃ (π : List (Loc × ResU Loc Val)) (b : ResU Loc Val),
    ρ'.Dom (π.map Prod.fst) ∧
    BigComp CellU.CompatS CellU.CompS (π.map Prod.snd) b ∧
    ResU.Le b ρ ∧
    ∀ l p, (l, p) ∈ π → ResU.RebAt α ρ ρ' l p

end BoCa.Fig16

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
### 5.47 · `↺_α P (ρ) ≜ ∃ρ′ ∈ reb_α(ρ). P(ρ′)` · [TR] p. 6, proposition row 19 · `[as printed]`

[CONF] Fig. 19 fuses this row with `reb_α` and binds `@ρ = α` where [TR] p. 5's `reb_α` binds `@ρ ⊐ α`; [TR]'s split is followed
-/
/-- `↻_α P (ρ) ≜ ∃ρ′ ∈ reb_α(ρ). P(ρ′)`.

`[CONF]` Fig. 19 (p. 415:23) fuses `↻_α` and `reb_α` into one row and orders
`reb`'s three clauses `own`, `imm`, `mut` where `[TR]` p. 5 orders them `own`,
`mut`, `imm`; the conjunction is the same.  `[as printed]` (`[TR]` p. 6's row) -/
def reborrow (α : Life) (P : SPropU Loc Val) : SPropU Loc Val :=
  fun ρ => ∃ ρ', ResU.Reb α ρ ρ' ∧ P ρ'

end BoCa.Fig16.BoLo

namespace BoCa.Fig16.Life

/-!
### 5.59 · — ⊑ appears in [TR] p. 4 row 9 as the STRICT `>` — · [TR] p. 4, row 9 · `[repair]`

The reflexive closure of ⊏, where the printed glyph carries the strict `>`. Adjudicated at `docs/boca-rules.md` §12.3 with convention G5, corroborated by [CONF] Fig. 19's dotted underbarred glyphs at the two rows that use it: Fig. 16's underbarred glyphs are the reflexive order. `BoCa/Fig16.lean` §1 now enumerates every printed definition stated with it — `BoCa.Fig16.ResU.AtLife`, `BoCa.Fig16.BoLo.ptoImm`, `BoCa.Fig16.BoLo.ptoMut` — and every `[as printed]` lemma — `BoCa.Fig16.BoLo.box_antitone`, `BoCa.Fig16.BoLo.ptoImm_antitone` ([TR] 6.114) and `BoCa.Fig16.BoLo.ptoMut_antitone` — and separates the statements that are our own facts about it
-/
/-- `α ⊑ β` — the reflexive closure of `⊏`.  **Ours** (G5): neither document
defines a reflexive order — `[TR]` p. 4 assigns this glyph the strict `>`
(§1). -/
abbrev Sqsubseteq (a b : Life) : Prop := a ≤ b

end BoCa.Fig16.Life

namespace BoCa.Fig16

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
@[inherit_doc] scoped infix:50 " ⊑ " => Life.Sqsubseteq

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### 5.11 · `@ρ ≜ ⊓_{ψ ∈ cod(ρ)} @ψ` · [TR] p. 5, operation row 2 · `[encoding]`

Named choice: a graph plus a noncomputable function, phrased as the greatest lower bound and proved equal to the fold over any covering list. Totality (`BoCa.Fig16.ResU.exists_atLife`) is exactly what row 5.7's `fin` buys
-/
/-- `@ρ ≜ ⨅_{ψ ∈ cod(ρ)} @ψ`, as its graph: `a` is the greatest `⊑`-lower bound
of `{@ψ | ψ ∈ cod(ρ)}`.  The print writes an iterated `⊓ ≜ max` and no order
symbol; a greatest lower bound for `⊑` is the same thing, and `atLife_atOn`
gives the fold form on any covering list.  `[as printed]` (as a graph — G4;
`⊑` is ours, G5) -/
def ResU.AtLife (ρ : ResU Loc Val) (a : Life) : Prop :=
  (∀ l ψ, ρ.get l = some ψ → a ⊑ ψ.at) ∧
  (∀ b, (∀ l ψ, ρ.get l = some ψ → b ⊑ ψ.at) → b ⊑ a)

/-!
Row 5.11, continued.
-/
theorem ResU.atLife_atOn (ρ : ResU Loc Val) (d : List Loc)
    (hd : ∀ l ψ, ρ.get l = some ψ → l ∈ d) : ρ.AtLife (ρ.atOn d) :=
  ⟨fun l ψ h => ρ.atOn_ub d l ψ (hd l ψ h) h, fun b hb => ρ.atOn_lub d b hb⟩

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
/-- **`@ρ` is total** — the meet exists for every resource, because `Res` is
finite.  `[about ours: the totality of the printed `@ρ`, which is what the
`fin` mark of [TR] p. 4 row 7 is needed for]` -/
theorem ResU.exists_atLife (ρ : ResU Loc Val) : ∃ a, ρ.AtLife a := by
  obtain ⟨d, hd⟩ := ρ.finite
  exact ⟨ρ.atOn d, ρ.atLife_atOn d (fun l ψ e => hd l (by rw [e]; simp))⟩

/-!
Row 5.11, continued.
-/
/-- `@ρ` as a function.  The choice is of the covering list, not of the value:
the value is unique by `AtLife.unique`.  `[as printed]` (the function form of
def. 14; `Classical.choose` picks the covering list) -/
noncomputable def ResU.at (ρ : ResU Loc Val) : Life := Classical.choose ρ.exists_atLife

end BoCa.Fig16

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
### 5.30 · `ℓ ↦ Imm α P̂  (ρ) ≜ ∃β̄,v,ρ′. ρ = ℓ ↦ imm(β̄,v,ρ′) ∧ P̂(v)(ρ′) ∧ α ⊑ ⊔β̄` · [TR] p. 6, proposition row 2 · `[repair]`

**Two repairs.**  (i) The last conjunct is `α ⊑ ⊓β̄`, not the printed `α ⊑ ⊔β̄`. Adjudicated at `docs/boca-rules.md` §12.67(a): each lifetime in `β̄` is one outstanding borrow ([TR] Definition 6.3 and the sentence after it, p. 17: *"'without' means removing the lifetimes of borrows from `ρ′`, but keeping the lifetimes only in `ρ`"*), and the index is a lower bound on each ([CONF] 415:8 *"forbids the context from holding borrows at lifetime `a` or shorter"*, 415:9 *"the lifetime `a` is really only a lower bound on the 'true' lifetime"*, 415:10 and 415:14 *"an unambiguous lifetime bound"*, 415:20 `Mut_α`'s predicate *"sits in the stratification at its lifetime `β`"*), which is what [TR] 6.60's `Imm` step (p. 21) spends to reach `@ρ = ⊓β̄`. The literal reading — [CONF] 415:19 *"the borrow connective will bound its lifetime index `α` by the longest among them"* and [TR] p. 6's `⊔` — is recorded there with its cost: 6.60's `Imm` step does not follow, and `𝒱⟦Mut @a T⟧` is empty whenever `T` has a top-level `Imm`. [TR] 6.115 is `variant` in consequence (`BoCa.Fig16.BoLo.not_iAgreeAtJoin`). (ii) `⊑` is implemented with `BoCa.Fig16.Life.Sqsubseteq`, the REFLEXIVE order the model file declares ours, where [TR] p. 4 row 9's key makes the printed ⊑ the strict `>`; load-bearing because `reb_α` produces `imm({α},v,−)`, whose `⊓β̄` is exactly `α`. Adjudicated at `docs/boca-rules.md` §12.3 with `BoCa/Fig16.lean` convention G5; [CONF] Fig. 19 (p. 415:23) prints this row's relation with the dotted UNDERBARRED ⊑
-/
/-- `ℓ ↦ I_α P̂ (ρ) ≜ ∃β̄,v,ρ′. ρ = ℓ ↦ imm(β̄,v,ρ′) ∧ P̂(v)(ρ′) ∧ α ⊑ ⊓β̄`.

The printed row bounds `α` by `⊔β̄`; the last conjunct here bounds it by `⊓β̄`.
Each lifetime in `β̄` is one outstanding borrow (`[TR]` Definition 6.3 and the
sentence after it, p. 17), and `α` is a lower bound on each of them: `[CONF]`
415:9 calls the index "really only a lower bound on the 'true' lifetime that the
borrow was originally assigned", 415:8 has `Δ ⊢ T ⊐ a` forbid "the context from
holding borrows at lifetime `a` or shorter", and 415:14 asks the borrowed
predicate for "an unambiguous lifetime bound".  At `⊔β̄`, `[TR]` 6.60's `Imm`
step does not follow and `𝒱⟦Mut @a T⟧` is empty wherever `T` has a top-level
`Imm`.  `docs/boca-rules.md` §12.67.
`[variant: `⊓β̄` for the printed `⊔β̄`, `docs/boca-rules.md` §12.67]` -/
noncomputable def ptoImm (l : Loc) (α : Life) (P : Val → SPropU Loc Val) :
    SPropU Loc Val :=
  fun ρ => ∃ (s : LSet) (v : Val) (σ : ResU Loc Val) (h : σ.InStratum s.join),
    ρ = ResU.single l (CellU.immOf s v σ h) ∧ P v σ ∧ α ⊑ s.meet

/-!
### 5.31 · `ℓ ↦ Mut α P̂  (ρ) ≜ ∃β ⊒ α, v, ρ′. ρ = ℓ ↦ mut(β,v,ρ′,P̂)` · [TR] p. 6, proposition row 3 · `[repair]`

The same undeclared reflexive-⊑ substitution as row 5.30, admitting `β = α` where [TR]'s key makes ⊒ strict. The other half — matching the stored invariant through `BoCa.Fig16.BoLo.ofS` — costs nothing, since a paper `P̂ : Val → SProp_β` is already false off `Res_β` (`BoCa.Fig16.SPropS.toU_range`). Adjudicated at `docs/boca-rules.md` §12.3 with convention G5 for the glyph — [CONF] Fig. 19 prints `∃β ⊒ α` with the dotted underbar — and at `BoCa/Fig16.lean` §24 for the invariant match, which names the cost outright rather than hiding it (`BoCa.Fig16.SPropS.toU_range`)
-/
/-- `ℓ ↦ M_α P̂ (ρ) ≜ ∃β ⊒ α,v,ρ′. ρ = ℓ ↦ mut(β,v,ρ′,P̂)`. -/
noncomputable def ptoMut (l : Loc) (α : Life) (P : Val → SPropU Loc Val) :
    SPropU Loc Val :=
  fun ρ => ∃ (b : Life) (v : Val) (σ : ResU Loc Val) (h : σ.InStratum b)
      (Q : Val → SPropS Loc Val b) (hw : Q v ⟨σ, h⟩),
    α ⊑ b ∧ ρ = ResU.single l (CellU.mutOf b v σ h Q hw) ∧ ofS Q = P

/-!
### 5.63 · `ρ⁺∣own = ∅` is named; `ℓ ↦ _` has no printed counterpart · [TR] p. 6, row 5 · `[repair]`

`NoOwn` is the printed side condition given a name, and `noOwn_compS` is the closure under composition that `wp`-bind and `wp`-M-forget use in one step; `ptoAny` has no printed counterpart at all and is used only to state non-vacuity witnesses. Adjudicated at `BoCa/Fig16Wp.lean` §1: `NoOwn` is [TR] p. 6's own `ρ⁺∣own = ∅` given a name, and `noOwn_compS` the closure the printed proofs of 6.135 and 6.148 take in one step. `ptoAny` is justified at its consumers rather than at itself — `BoCa.Fig16.BoLo.ptoOwn_excl` and `BoCa.Fig16.BoLo.ptoMut_excl` each carry the tag saying [TR] Lemma 6.95's and 6.119's elided `_` is read as a cell of any kind, so both are strictly stronger than the printed instances. It is that widened wildcard, not only a non-vacuity witness
-/
/-- `ℓ ↦ _` — a single cell at `ℓ`, of any kind. -/
noncomputable def ptoAny (l : Loc) : SPropU Loc Val :=
  fun ρ => ∃ ψ, ρ = ResU.single l ψ

end BoCa.Fig16.BoLo

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
Row 5.63, continued.
-/
/-- `ρ|own = ∅` — the printed side condition on the discarded fragment. -/
def NoOwn (ρ : WRes) : Prop := ρ.restrict Kind.own = PMap.empty

end BoCa.Fig16.BoLo

namespace BoCa.Fig16
variable {Loc Val : Type}

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
theorem ResU.restrict_eq_some {ρ : ResU Loc Val} {k : Kind} {l : Loc} {ψ : CellU Loc Val} :
    (ρ.restrict k).get l = some ψ ↔ (ρ.get l = some ψ ∧ ψ.kind = k) := by
  have hdef : (ρ.restrict k).get l
      = (ρ.get l).bind (fun ψ => if ψ.kind = k then some ψ else none) := rfl
  rw [hdef]
  cases hf : ρ.get l with
  | none => simp
  | some ψ' =>
      simp only [Option.bind_some]
      by_cases hk : ψ'.kind = k
      · rw [if_pos hk]
        exact ⟨fun he => by cases Option.some.inj he; exact ⟨rfl, hk⟩, fun he => he.1⟩
      · rw [if_neg hk]
        refine ⟨fun he => absurd he (by simp), fun he => ?_⟩
        cases Option.some.inj he.1
        exact absurd he.2 hk

end BoCa.Fig16

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

theorem noOwn_iff {ρ : WRes} :
    NoOwn ρ ↔ ∀ l ψ, ρ.get l = some ψ → ψ.kind ≠ Kind.own := by
  constructor
  · intro h l ψ hl hk
    have hs : (ρ.restrict Kind.own).get l = some ψ := ResU.restrict_eq_some.mpr ⟨hl, hk⟩
    rw [h] at hs
    exact absurd hs (by simp)
  · intro h
    refine PMap.ext fun l => ?_
    cases e : (ρ.restrict Kind.own).get l with
    | none => rfl
    | some ψ =>
        obtain ⟨hg, hk⟩ := ResU.restrict_eq_some.mp e
        exact absurd hk (h l ψ hg)

/-!
Row 5.63, continued.
-/
/-- `ρ⁺|own = ∅` is closed under `●`, which is what `wp-bind` and
`wp-M-forget` need of it: a `●`-composite cell is an `imm` cell
(`Fig16.CellU.CompS`), and off the overlap the cell is one of the operands'.
`[about ours: the closure the printed proofs of 6.135 and 6.148 use in one
step]` -/
theorem noOwn_compS {ρ₁ ρ₂ ρ : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ)
    (h₁ : NoOwn ρ₁) (h₂ : NoOwn ρ₂) : NoOwn ρ := by
  refine noOwn_iff.mpr fun l ψ hl => ?_
  have hc := h.2 l
  cases e₁ : ρ₁.get l <;> cases e₂ : ρ₂.get l <;> rw [e₁, e₂] at hc
  · rw [hc] at hl; exact absurd hl (by simp)
  · rw [hc] at hl; cases Option.some.inj hl; exact noOwn_iff.mp h₂ l _ e₂
  · rw [hc] at hl; cases Option.some.inj hl; exact noOwn_iff.mp h₁ l _ e₁
  · obtain ⟨χ, hχ, hC⟩ := hc
    rw [hχ] at hl
    cases Option.some.inj hl
    obtain ⟨s₁, s₂, w, χw, k₁, k₂, k₃, -, -, e⟩ := hC
    rw [e]
    simp

end BoCa.Fig16.BoLo

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### 5.64 · `ρ∣dom(ρ′)` — a domain restriction, used from [TR] Lemma 6.56 on with no defining row · [TR] p. 18, Lemmas 6.56 and 6.57 · `[repair]`

The second half of the coverage gap row 5.19 records: [TR] p. 5's row gives only `ρ∣ι`, and [TR] Lemmas 6.56 and 6.57 are stated at `ρ∣dom(ρ′∣mut,own)` and `ρ∣dom(ρ′∣imm)`, which no row defines. `ρ/dom(ρ′)` comes with it — [TR] p. 5 writes it inside `◐`'s own defining row and row 5.53 covers only the one-location `ρ/ℓ` — and the two are what `BoCa.Fig16.ResU.restrictDom_compS` splits `ρ` by, which is how [TR] 6.56's appeal to 6.11 is discharged. Adjudicated at `BoCa/Fig16.lean` §12, which names the gap, and at `BoCa/Reborrow.lean` §9, where the definitions sit beside their first consumers; the membership test is on `dom(ρ′)` and needs no decidable equality on `Loc`
-/
/-- `ρ|dom(σ)` — `ρ` at the locations `σ` is defined at.
`[about ours: the notation `[TR]` §6 uses without a defining row]` -/
def ResU.restrictDom (ρ σ : ResU Loc Val) : ResU Loc Val where
  get := fun l => if (σ.get l).isSome then ρ.get l else none
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨d, fun l hl => hd l (fun e => hl ?_)⟩
    show (if (σ.get l).isSome then ρ.get l else none) = none
    rw [e]; exact ite_self none

/-!
Row 5.64, continued.
-/
/-- `ρ/dom(σ)` — `ρ` off the locations `σ` is defined at.  `[TR]` p. 5 writes
`ρ₁/dom(ρ₂)` in `◐`'s own defining row and gives it no row of its own.
`[about ours: the notation both documents use without a defining row]` -/
def ResU.delDom (ρ σ : ResU Loc Val) : ResU Loc Val where
  get := fun l => if (σ.get l).isSome then none else ρ.get l
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨d, fun l hl => hd l (fun e => hl ?_)⟩
    show (if (σ.get l).isSome then none else ρ.get l) = none
    rw [e]; exact ite_self none

/-!
### 5.67 · — [CONF] §4.3's characterisation of `✓`: *"in a valid resource, every pair of aliases map to the same object and each has an immutable ancestor"*, and *"aliasing of exclusive locations … not guarded by immutable cells … violates the mutability-xor-aliasing restriction"* — · [CONF] p. 415:21, not in [TR] §5 · `[as printed]`

Prose, not a defining row, and it characterises an object that already has one — `✓ρ ≜ ⦇ρ⦈ defined` (row 5.59). [CONF] p. 415:21 says the enforcement is composition itself and nothing more: *"the advantage of reusing composition is that it already rules out all of the inconsistent aliasing cases"*, and names the mechanism — *"the conflict at `ℓ₁` causes `•` and therefore `E•` to be undefined, while the conflict at `ℓ₂` causes `◦` and therefore `A` to be undefined"*. So there is nothing extra to transcribe, and the three clauses are already theorems: *same object* is `CellU.compatR_iff`, proved as an **iff** (`▷◁ ⟺ a common value, and a common witness wherever there is one to share`), with `CellU.CompatS.imm_imm` at `●`; *an immutable ancestor* is `AgW.nonimm_beneath_imm` with `ExW.immFree` (6.36); *no cell both exclusive and aliasable* is `ResU.CompatS.disjoint_of_immFree` and `ResU.flat_eq_ag_at`. The row exists because the prose was uncited for the whole of `[TR]` §6's development; `docs/boca-rules.md` §12.52 assembles it and records what it does **not** say
-/
/-- Two compatible `imm` cells agree on the value and on the witness — with the
witness compared by *plain equality* in `Res`, which is what the print's single
`ρ` says. -/
theorem CellU.CompatS.imm_imm {i₁ i₂ : ImmU Loc Val}
    (h : CellU.CompatS (.imm i₁) (.imm i₂)) : i₁.v = i₂.v ∧ i₁.res = i₂.res := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, e₁, e₂⟩ := h
  rw [← ImmU.immOf_eta i₁] at e₁
  rw [← ImmU.immOf_eta i₂] at e₂
  obtain ⟨-, hv₁, hρ₁⟩ := CellU.immOf_inj e₁
  obtain ⟨-, hv₂, hρ₂⟩ := CellU.immOf_inj e₂
  exact ⟨hv₁.trans hv₂.symm, hρ₁.trans hρ₂.symm⟩

/-!
Row 5.15, continued.
-/
/-- `ψ₁ ● ψ₂` — strict cell composition, as a function of the `▶◀` proof that is
its domain.  `[as printed]` (the printed equation is `compS_immOf`) -/
def CellU.compS : (ψ₁ ψ₂ : CellU Loc Val) → ψ₁.CompatS ψ₂ → CellU Loc Val
  | .imm i₁, .imm i₂, h =>
      CellU.immOf (i₁.ls ∪ i₂.ls) i₁.v i₁.res
        (by
          have e : i₁.ρ.toU = i₂.ρ.toU := (CellU.CompatS.imm_imm h).2
          have k₂ : ResU.InStratum i₂.ls.join i₁.ρ.toU := by
            rw [e]; exact i₂.ρ.toU_inStratum
          exact ResU.InStratum.sup i₁.ρ.toU_inStratum k₂)
  | .own _, _, h => absurd h (by rintro ⟨_, _, _, _, _, _, e, -⟩; simp [CellU.immOf] at e)
  | .mut _, _, h => absurd h (by rintro ⟨_, _, _, _, _, _, e, -⟩; simp [CellU.immOf] at e)
  | .imm _, .own _, h => absurd h (by rintro ⟨_, _, _, _, _, _, -, e⟩; simp [CellU.immOf] at e)
  | .imm _, .mut _, h => absurd h (by rintro ⟨_, _, _, _, _, _, -, e⟩; simp [CellU.immOf] at e)

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
theorem CellU.compS_spec : ∀ (ψ₁ ψ₂ : CellU Loc Val) (h : ψ₁.CompatS ψ₂),
    CellU.CompS ψ₁ ψ₂ (CellU.compS ψ₁ ψ₂ h)
  | .imm i₁, .imm i₂, h => by
      have hv : i₁.v = i₂.v := (CellU.CompatS.imm_imm h).1
      have hρ : i₁.res = i₂.res := (CellU.CompatS.imm_imm h).2
      have k₁ : ResU.InStratum i₁.ls.join i₁.res := i₁.ρ.toU_inStratum
      have k₂ : ResU.InStratum i₂.ls.join i₁.res := by rw [hρ]; exact i₂.ρ.toU_inStratum
      refine ⟨i₁.ls, i₂.ls, i₁.v, i₁.res, k₁, k₂, ResU.InStratum.sup k₁ k₂,
        (ImmU.immOf_eta i₁).symm, ?_, rfl⟩
      exact ((CellU.immOf_congr rfl hv hρ k₂ i₂.ρ.toU_inStratum).trans (ImmU.immOf_eta i₂)).symm
  | .own _, _, h => absurd h (by rintro ⟨_, _, _, _, _, _, e, -⟩; simp [CellU.immOf] at e)
  | .mut _, _, h => absurd h (by rintro ⟨_, _, _, _, _, _, e, -⟩; simp [CellU.immOf] at e)
  | .imm _, .own _, h => absurd h (by rintro ⟨_, _, _, _, _, _, -, e⟩; simp [CellU.immOf] at e)
  | .imm _, .mut _, h => absurd h (by rintro ⟨_, _, _, _, _, _, -, e⟩; simp [CellU.immOf] at e)

/-!
Row 5.15, continued.
-/
/-- **The printed equation for `●`.**  `[as printed]` -/
theorem CellU.compS_immOf {s₁ s₂ : LSet} {v : Val} {ρ : ResU Loc Val}
    {h₁ : ρ.InStratum s₁.join} {h₂ : ρ.InStratum s₂.join}
    (h : CellU.CompatS (CellU.immOf s₁ v ρ h₁) (CellU.immOf s₂ v ρ h₂))
    (h₃ : ρ.InStratum (s₁ ∪ s₂).join) :
    CellU.compS _ _ h = CellU.immOf (s₁ ∪ s₂) v ρ h₃ :=
  CellU.CompS.functional (CellU.compS_spec _ _ h)
    ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, rfl, rfl, rfl⟩

/-!
### 5.16 · `ψ₁ ○ ψ₂ ≜` five clauses (`ψ₁`; `ψ₁ ● ψ₂`; `mut(α⊓β,v,ρ,P̂∧Q̂)`; `ψᵢ`; `ψᵢ`) · [TR] p. 5, operation row 7 · `[as printed]`

Clause (4) at `i ∈ {1,2}` becomes two constructors and clause (5) over a two-element set becomes four; clause (1) is unconditional, so ○ is total on the diagonal exactly as printed, and the (1)/(2) and (1)/(3) overlaps are reconciled by `BoCa.Fig16.CellU.compS_self` and `BoCa.Fig16.CellU.compR_same_mutMut`
-/
/-- `ψ₁ ○ ψ₂ = ψ` — the graph of relaxed cell composition, five clauses, as
printed.  As in `▶◀`, the stratum-membership arguments are the print's own
typing constraints on `ρ` and `P̂`, and they are `Prop`s.  `[as printed]` -/
inductive CellU.CompR : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop where
  /-- (1) `ψ₁` if `ψ₁ = ψ₂`. -/
  | same (ψ : CellU Loc Val) : CellU.CompR ψ ψ ψ
  /-- (2) `ψ₁ ● ψ₂` if `ψ₁ ▶◀ ψ₂`. -/
  | strict {ψ₁ ψ₂ : CellU Loc Val} (h : ψ₁.CompatS ψ₂) :
      CellU.CompR ψ₁ ψ₂ (CellU.compS ψ₁ ψ₂ h)
  /-- (3) `mut(α ⊓ β, v, ρ, P̂ ∧ Q̂)`. -/
  | mutMut (a b : Life) (v : Val) (ρ : ResU Loc Val)
      (ha : ρ.InStratum a) (hb : ρ.InStratum b)
      (P : Val → SPropS Loc Val a) (Q : Val → SPropS Loc Val b)
      (hP : P v ⟨ρ, ha⟩) (hQ : Q v ⟨ρ, hb⟩) :
      CellU.CompR (CellU.mutOf a v ρ ha P hP) (CellU.mutOf b v ρ hb Q hQ)
        (CellU.mutOf (a ⊓ b) v ρ ha.inf_left (SPropS.conj P Q)
          (SPropS.conj_holds ha hb hP hQ))
  /-- (4), `i = 1`. -/
  | mutOwn (a : Life) (v : Val) (ρ : ResU Loc Val) (ha : ρ.InStratum a)
      (P : Val → SPropS Loc Val a) (hP : P v ⟨ρ, ha⟩) :
      CellU.CompR (CellU.mutOf a v ρ ha P hP) (CellU.ownOf v)
        (CellU.mutOf a v ρ ha P hP)
  /-- (4), `i = 2`. -/
  | ownMut (a : Life) (v : Val) (ρ : ResU Loc Val) (ha : ρ.InStratum a)
      (P : Val → SPropS Loc Val a) (hP : P v ⟨ρ, ha⟩) :
      CellU.CompR (CellU.ownOf v) (CellU.mutOf a v ρ ha P hP)
        (CellU.mutOf a v ρ ha P hP)
  /-- (5), `i = 1`, against `own(v)`. -/
  | immOwn (s : LSet) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum s.join) :
      CellU.CompR (CellU.immOf s v ρ h) (CellU.ownOf v) (CellU.immOf s v ρ h)
  /-- (5), `i = 2`, against `own(v)`. -/
  | ownImm (s : LSet) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum s.join) :
      CellU.CompR (CellU.ownOf v) (CellU.immOf s v ρ h) (CellU.immOf s v ρ h)
  /-- (5), `i = 1`, against `mut(β, v, ρ, P̂)`. -/
  | immMut (s : LSet) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum s.join)
      (b : Life) (hb : ρ.InStratum b) (P : Val → SPropS Loc Val b) (hP : P v ⟨ρ, hb⟩) :
      CellU.CompR (CellU.immOf s v ρ h) (CellU.mutOf b v ρ hb P hP)
        (CellU.immOf s v ρ h)
  /-- (5), `i = 2`, against `mut(β, v, ρ, P̂)`. -/
  | mutImm (s : LSet) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum s.join)
      (b : Life) (hb : ρ.InStratum b) (P : Val → SPropS Loc Val b) (hP : P v ⟨ρ, hb⟩) :
      CellU.CompR (CellU.mutOf b v ρ hb P hP) (CellU.immOf s v ρ h)
        (CellU.immOf s v ρ h)

/-!
### 5.14 · `ψ₁ ▷◁ ψ₂ ≜ ψ₁ ▸◂ ψ₂ ∨ ∃i,ᾱ,β,v,ρ,P̂. {ψ₁,ψ₂} ∈ {imm(ᾱ,v,ρ), own(v), mut(β,v,ρ,P̂)}` · [TR] p. 5, operation row 5 · `[repair]`

The printed second disjunct does not type — a two-element SET asserted to be an ELEMENT of a three-element set of cells — and binds an unused `∃i`. Lean reads ⋈ as the domain of ○, settled against [TR]'s own Lemma 6.3 proof (`docs/boca-rules.md` §12.35). Adjudicated at `docs/boca-rules.md` §12.35 and `BoCa/Fig16.lean` §15: the printed disjunct cannot be taken as printed at all, a two-element SET asserted to be an ELEMENT of a three-element set of cells, with an `∃i` that is never used. Corroborated by [TR] p. 7's own proof of 6.3 and by Lemma 6.37's use of `ρ₁ ⋈ ρ₂` in the position "ρ₁ ○ ρ₂ is defined"
-/
/-- `ψ₁ ⋈ ψ₂` — relaxed cell compatibility, as the domain of `○`.
`[variant: `[TR]` p. 5's printed second disjunct does not type (a two-element
set asserted to be an element of a three-element set of cells, and an unused
`∃ i`); this is the reading forced by `[TR]` Lemma 6.3's own `○`-case proof,
with Lemma 6.9 as the precedent and 6.1 and 6.37 consistent with it — §15]` -/
def CellU.CompatR (ψ₁ ψ₂ : CellU Loc Val) : Prop := ∃ ψ, CellU.CompR ψ₁ ψ₂ ψ

/-!
Row 5.17, continued.
-/
/-- `ρ₁ ⋈ ρ₂` — §12's `▶◁` schema at the relaxed mode.
`[variant: obtained by instantiating the printed schema at `⋈`, whose cell-level
reading is §15's]` -/
abbrev ResU.CompatR (ρ₁ ρ₂ : ResU Loc Val) : Prop := ResU.Compat CellU.CompatR ρ₁ ρ₂

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
/-- The three-way union at one location, as a function of the guard. -/
def optCompS : (o₁ o₂ : Option (CellU Loc Val)) →
    (∀ ψ₁ ψ₂, o₁ = some ψ₁ → o₂ = some ψ₂ → CellU.CompatS ψ₁ ψ₂) → Option (CellU Loc Val)
  | none, none, _ => none
  | some ψ, none, _ => some ψ
  | none, some ψ, _ => some ψ
  | some ψ₁, some ψ₂, h => some (CellU.compS ψ₁ ψ₂ (h ψ₁ ψ₂ rfl rfl))

theorem optCompS_eq_none {o₁ o₂ : Option (CellU Loc Val)}
    (k : ∀ ψ₁ ψ₂, o₁ = some ψ₁ → o₂ = some ψ₂ → CellU.CompatS ψ₁ ψ₂)
    (e₁ : o₁ = none) (e₂ : o₂ = none) : optCompS o₁ o₂ k = none := by
  subst e₁; subst e₂; rfl

/-!
Row 5.18, continued.
-/
/-- `ρ₁ ● ρ₂`, as a function of the `▶◀` guard.  The composite is finite
because both operands are: `d₁ ++ d₂` covers it. -/
def ResU.compS (ρ₁ ρ₂ : ResU Loc Val) (h : ResU.CompatS ρ₁ ρ₂) : ResU Loc Val where
  get := fun l => optCompS (ρ₁.get l) (ρ₂.get l) (fun ψ₁ ψ₂ e₁ e₂ => h l ψ₁ ψ₂ e₁ e₂)
  finite := by
    obtain ⟨d₁, k₁⟩ := ρ₁.finite
    obtain ⟨d₂, k₂⟩ := ρ₂.finite
    refine ⟨d₁ ++ d₂, fun l hl => ?_⟩
    cases e₁ : ρ₁.get l with
    | none =>
        cases e₂ : ρ₂.get l with
        | none => exact absurd (optCompS_eq_none _ e₁ e₂) hl
        | some ψ => exact List.mem_append.mpr (Or.inr (k₂ l (by rw [e₂]; simp)))
    | some ψ => exact List.mem_append.mpr (Or.inl (k₁ l (by rw [e₁]; simp)))

/-!
Row 5.18, continued.
-/
/-- `ρ₁ ○ ρ₂ = ρ` — §12's `◐` schema at the relaxed mode.
`[variant: obtained by instantiating the printed schema at `⋈`/`○`; the guard
and the `ρ₂(ℓ)` are `[TR]`'s, as in §12]` -/
abbrev ResU.CompR (ρ₁ ρ₂ ρ : ResU Loc Val) : Prop :=
  ResU.Comp CellU.CompatR CellU.CompR ρ₁ ρ₂ ρ

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
/-- The cell-level `○` as a function of its guard.  `○` is single-valued
(`CellU.CompR.functional`, §11), so the choice is of a representative of a
singleton; `Classical.choose` is what extracts it from the `∃` that `⋈` is.
`[about ours: the function form of a graph the print gives by cases]` -/
noncomputable def CellU.compR (ψ₁ ψ₂ : CellU Loc Val) (h : ψ₁.CompatR ψ₂) : CellU Loc Val :=
  h.choose

noncomputable def optCompR : (o₁ o₂ : Option (CellU Loc Val)) →
    (∀ ψ₁ ψ₂, o₁ = some ψ₁ → o₂ = some ψ₂ → CellU.CompatR ψ₁ ψ₂) → Option (CellU Loc Val)
  | none, none, _ => none
  | some ψ, none, _ => some ψ
  | none, some ψ, _ => some ψ
  | some ψ₁, some ψ₂, h => some (CellU.compR ψ₁ ψ₂ (h ψ₁ ψ₂ rfl rfl))

theorem optCompR_eq_none {o₁ o₂ : Option (CellU Loc Val)}
    (k : ∀ ψ₁ ψ₂, o₁ = some ψ₁ → o₂ = some ψ₂ → CellU.CompatR ψ₁ ψ₂)
    (e₁ : o₁ = none) (e₂ : o₂ = none) : optCompR o₁ o₂ k = none := by
  subst e₁; subst e₂; rfl

/-!
Row 5.18, continued.
-/
/-- `ρ₁ ○ ρ₂`, as a function of the `⋈` guard — the relaxed twin of
`ResU.compS` (§12).  Finite because both operands are.
`[about ours: the function form of a graph the print gives by cases]` -/
noncomputable def ResU.compR (ρ₁ ρ₂ : ResU Loc Val) (h : ResU.CompatR ρ₁ ρ₂) : ResU Loc Val where
  get := fun l => optCompR (ρ₁.get l) (ρ₂.get l) (fun ψ₁ ψ₂ e₁ e₂ => h l ψ₁ ψ₂ e₁ e₂)
  finite := by
    obtain ⟨d₁, k₁⟩ := ρ₁.finite
    obtain ⟨d₂, k₂⟩ := ρ₂.finite
    refine ⟨d₁ ++ d₂, fun l hl => ?_⟩
    cases e₁ : ρ₁.get l with
    | none =>
        cases e₂ : ρ₂.get l with
        | none => exact absurd (optCompR_eq_none _ e₁ e₂) hl
        | some ψ => exact List.mem_append.mpr (Or.inr (k₂ l (by rw [e₂]; simp)))
    | some ψ => exact List.mem_append.mpr (Or.inl (k₁ l (by rw [e₁]; simp)))

/-!
Row 5.20, continued.
-/
/-- `ex(ρ)_○` — the exclusive walk at the relaxed operator, which is what
`ag`'s third piece calls. -/
abbrev ExR (ρ σ : ResU Loc Val) : Prop := ExW CellU.CompatR CellU.CompR ρ σ

/-!
### 5.21 · `ag(ρ)_◖ ≜ ρ∣imm ○ ◯{ag(ρ′) ∣ …mut…} ○ ◯{ex(ρ′)_○ ○ ag(ρ′) ∣ …imm…}` · [TR] p. 5, operation row 12 · `[repair]`

The same set-versus-family reading as row 5.20; additionally the ◖ subscript printed on the LEFT-hand side occurs nowhere on the right (the body is at ○ throughout, with `ex(ρ′)_○` explicitly hollow) and is dropped as vestigial, following [CONF] Fig. 18a's unsubscripted flattening — so no `ag(ρ)_●` exists here. Adjudicated at `BoCa/Fig16.lean` §18, the family half by `docs/boca-rules.md` §12.36 and convention G6: the printed left-hand subscript parametrizes nothing, occurring nowhere on the right-hand side, whose body is at ○ throughout with `ex(ρ′)_○` explicitly hollow, and [CONF] p. 415:22 writes the same row unsubscripted
-/
mutual

/-- `ag(ρ) = σ` — the aliasable walk, as a graph, always at `○`.
`[variant: the printed comprehensions are sets and these are the families they
index (convention G6, §17); the vestigial `◐` on the printed left-hand side is
dropped, following `[CONF]` Fig. 18a's unsubscripted `A⦇ρ⦈`]` -/
inductive AgW : ResU Loc Val → ResU Loc Val → Prop where
  | mk {ρ σ a bm bi : ResU Loc Val} {wm wi : List (Loc × ResU Loc Val)}
      (hsm : ResU.Sites ρ Kind.mut (wm.map Prod.fst))
      (hsi : ResU.Sites ρ Kind.imm (wi.map Prod.fst))
      (hwm : AgWitsM ρ wm)
      (hwi : AgWitsI ρ wi)
      (hbm : BigComp CellU.CompatR CellU.CompR (wm.map Prod.snd) bm)
      (hbi : BigComp CellU.CompatR CellU.CompR (wi.map Prod.snd) bi)
      (ha : ResU.CompR (ρ.restrict Kind.imm) bm a)
      (hσ : ResU.CompR a bi σ) :
      AgW ρ σ

/-- The family `{ag(ρ′) | ∃ℓ. ρ(ℓ) = mut(_,_,ρ′,_)}`, tagged by location. -/
inductive AgWitsM : ResU Loc Val → List (Loc × ResU Loc Val) → Prop where
  | nil {ρ : ResU Loc Val} : AgWitsM ρ []
  | cons {ρ e : ResU Loc Val} {l : Loc} {w : List (Loc × ResU Loc Val)}
      (ψ : CellU Loc Val) (hψ : ρ.get l = some ψ) (hk : ψ.kind = Kind.mut)
      (he : AgW ψ.wit e) (hw : AgWitsM ρ w) :
      AgWitsM ρ ((l, e) :: w)

/-- The family `{ex(ρ′)_○ ○ ag(ρ′) | ∃ℓ. ρ(ℓ) = imm(_,_,ρ′)}`, tagged by
location. -/
inductive AgWitsI : ResU Loc Val → List (Loc × ResU Loc Val) → Prop where
  | nil {ρ : ResU Loc Val} : AgWitsI ρ []
  | cons {ρ p : ResU Loc Val} {l : Loc} {w : List (Loc × ResU Loc Val)}
      (ψ : CellU Loc Val) (hψ : ρ.get l = some ψ) (hk : ψ.kind = Kind.imm)
      (e a : ResU Loc Val) (hex : ExR ψ.wit e) (hag : AgW ψ.wit a)
      (hp : ResU.CompR e a p) (hw : AgWitsI ρ w) :
      AgWitsI ρ ((l, p) :: w)

end

/-!
### 5.22 · `⦇ρ⦈ ≜ ex(ρ)_● ● ag(ρ)` · [TR] p. 5, operation row 13 · `[as printed]`

Both the subscript on `ex` and the composition bullet are solid, and `ag` carries no subscript. A graph, single-valued by `BoCa.Fig16.ResU.Flat.functional`
-/
/-- `⦇ρ⦈ = σ` — `⦇ρ⦈ ≜ ex(ρ)_● ● ag(ρ)`.  `[as printed]` (as a graph — G4) -/
def ResU.Flat (ρ σ : ResU Loc Val) : Prop :=
  ∃ e a, ExS ρ e ∧ AgW ρ a ∧ ResU.CompS e a σ

/-!
### 5.23 · `✓ρ ≜ ⦇ρ⦈ defined` · [TR] p. 5, operation row 14 · `[as printed]`

Definedness of a graph is inhabitation of it, which is what the print's word says
-/
/-- `✓ρ ≜ ⦇ρ⦈ defined`.  `[as printed]` -/
def ResU.Valid (ρ : ResU Loc Val) : Prop := ∃ σ, ResU.Flat ρ σ

/-!
### 5.25 · `⟦ρ⟧ ≜ [ℓ ↦ v ∣ ⟦⦇ρ⦈(ℓ)⟧ = v]`, `✓ρ` · [TR] p. 5, operation row 16 · `[as printed]`

[TR]'s row with the inner erasure and the `✓ρ` guard; [CONF] Fig. 18a prints neither and so equates a `Cell` with a `Val`
-/
/-- `⟦ρ⟧ = m` — `⟦ρ⟧ ≜ [ℓ ↦ v | ⟦⦇ρ⦈(ℓ)⟧ = v]` when `✓ρ`, with `⟦ψ⟧` §13's
`CellU.erase`.  The guard is carried by the existential: a lowering exists
exactly when the flattening does.
`[as printed]` (as a graph — G4; `[TR]`'s row, not `[CONF]` Fig. 18a's, which
prints neither the inner `⟦−⟧` nor the guard) -/
def ResU.Lower (ρ : ResU Loc Val) (m : Loc → Option Val) : Prop :=
  ∃ σ, ResU.Flat ρ σ ∧ ∀ l, m l = (σ.get l).map CellU.erase

/-!
### 5.26 · `ρ₁ # ρ₂ ≜ ρ₁ ▸◂ ρ₂ ∧ ✓(ρ₁ ● ρ₂)` · [TR] p. 5, operation row 17 · `[as printed]`

The bowtie is filled and the bullet solid, so the strict pair; the first conjunct is redundant (it is the composition's own first field) and is kept because the print carries it
-/
/-- `ρ₁ # ρ₂ ≜ ρ₁ ▶◀ ρ₂ ∧ ✓(ρ₁ ● ρ₂)`.  The first conjunct is redundant — it is
`ResU.Comp`'s own first field — and is kept because the print carries it.
`[as printed]` -/
def ResU.Hash (ρ₁ ρ₂ : ResU Loc Val) : Prop :=
  ResU.CompatS ρ₁ ρ₂ ∧ ∃ ρ, ResU.CompS ρ₁ ρ₂ ρ ∧ ResU.Valid ρ

/-!
### 5.60 · `⦇ρ⦈(ℓ)` — an application of a partial term · [TR] p. 5, row 18 · `[repair]`

"Some flattening of ρ carries ψ at ℓ" — false when `⦇ρ⦈` is undefined, single-valued by `BoCa.Fig16.ResU.Flat.functional`. This is exactly where [TR]'s guarded ↭ and [CONF]'s unguarded one come apart (`BoCa.Fig16.ResU.upd_of_not_valid`). Adjudicated at `BoCa/Fig16.lean` §20e with convention G4 and at the declaration: the print applies a partial term and says nothing about the undefined case, so a reading must be chosen; the one taken is stated, proved single-valued by `BoCa.Fig16.ResU.Flat.functional`, and identified as exactly where the two printed readings of ↭ part company
-/
/-- `⦇ρ⦈(ℓ) = ψ` — the printed partial-value equation, as `↭` uses it.  `⦇−⦈` is
a graph here (G4), so this says some flattening of `ρ` carries `ψ` at `ℓ`; it is
false when `⦇ρ⦈` is undefined, and single-valued in `ψ` by
`ResU.Flat.functional` (§20a).
`[about ours: the application `⦇ρ⦈(ℓ)` of a printed term, at the graph]` -/
def ResU.FlatAt (ρ : ResU Loc Val) (l : Loc) (ψ : CellU Loc Val) : Prop :=
  ∃ σ, ResU.Flat ρ σ ∧ σ.get l = some ψ

/-!
### 5.27 · `ρ₁ ↭ ρ₂ ≜ {∀ℓ,… (⦇ρ₁⦈(ℓ)=mut(α,_,_,P̂) ⇔ ⦇ρ₂⦈(ℓ)=mut(α,_,_,P̂)) ∧ (⦇ρ₁⦈(ℓ)=imm(β̄,v,ρ) ⇔ ⦇ρ₂⦈(ℓ)=mut(β̄,v,ρ))}`, `✓ρ₁ ∧ ✓ρ₂` · [TR] p. 5, operation row 18 · `[repair]`

The second clause's right-hand side prints a THREE-ary `mut` with a barred first argument; the Lean writes `imm`, following [CONF] Fig. 18b. The repair is forced — `mut` is 4-ary everywhere and its first slot is a single lifetime — but it changes a constructor, not a subscript. Adjudicated at `docs/boca-rules.md` §12.39, `BoCa/Fig16.lean` §20e and `docs/axiom-ledger.md` D3: the arity is the tell — `mut` is four-ary in Fig. 16 and in the clause two lines above, and its first argument here is printed overbarred, a lifetime SET in a single-lifetime slot — so the clause is well formed on no reading. [CONF] Fig. 18b prints `imm ⇔ imm` and `mut(β,−,−,P̂) ⇔ mut(β,−,−,P̂)`
-/
/-- Clause (1) of `↭`: `⦇ρ₁⦈(ℓ) = imm(ᾱ, v, ρ) ⇔ ⦇ρ₂⦈(ℓ) = imm(ᾱ, v, ρ)`, with
the lifetime set, the value and the witness all fixed across the `⇔` — nothing
wildcarded.  `h` is the print's own typing constraint on `imm`'s third
component.  This is `[CONF]` Fig. 18b's clause (1); `[TR]` p. 5 prints it
second, and prints `mut` for the second `imm` (§20e).  `[as printed]` -/
def ResU.UpdImm (ρ₁ ρ₂ : ResU Loc Val) : Prop :=
  ∀ (l : Loc) (s : LSet) (v : Val) (χ : ResU Loc Val) (h : χ.InStratum s.join),
    ρ₁.FlatAt l (CellU.immOf s v χ h) ↔ ρ₂.FlatAt l (CellU.immOf s v χ h)

/-!
Row 5.27, continued.
-/
/-- Clause (2) of `↭`: `⦇ρ₁⦈(ℓ) = mut(β, −, −, P̂) ⇔ ⦇ρ₂⦈(ℓ) = mut(β, −, −, P̂)`.
The lifetime `β` and the invariant `P̂` are bound outside the `⇔`, so they are
fixed; the two `−`s are the value and the witness, bound **inside** each side
and so free to differ between `ρ₁` and `ρ₂`.  `P̂`'s sort depends on `β` in the
print (`P̂ : Val → SProp_β`) and does so here.  This is `[CONF]` Fig. 18b's
clause (2), which `[TR]` p. 5 prints first.  `[as printed]` -/
def ResU.UpdMut (ρ₁ ρ₂ : ResU Loc Val) : Prop :=
  ∀ (l : Loc) (b : Life) (P : Val → SPropS Loc Val b),
    (∃ (v : Val) (χ : ResU Loc Val) (h : χ.InStratum b) (hw : P v ⟨χ, h⟩),
        ρ₁.FlatAt l (CellU.mutOf b v χ h P hw)) ↔
    (∃ (v : Val) (χ : ResU Loc Val) (h : χ.InStratum b) (hw : P v ⟨χ, h⟩),
        ρ₂.FlatAt l (CellU.mutOf b v χ h P hw))

/-!
Row 5.27, continued.

### 5.62 · — [CONF] Fig. 18b's unguarded ↭, and the `wp` row read at it — · not in [TR] §5 · `[repair]`

The second printed reading of ↭ (`docs/axiom-ledger.md` D3), kept alongside [TR]'s; `BoCa.Fig16.BoLo.wp_eq_wpU` proves the two readings give the same `SProp` inside the `wp` row, so nothing downstream has to choose. Adjudicated at `docs/axiom-ledger.md` D3 with `BoCa/Fig16.lean` §20e and `BoCa/Fig16Wp.lean` §2: both readings of ↭ are printed rows in the same documents, so both are carried and the choice is closed by proof rather than fiat — `BoCa.Fig16.BoLo.wp_eq_wpU` shows [TR]'s two guards follow from the `#`s that `wp` already quantifies over — and what survives away from `wp` is named. `BoCa.Fig16.ResU.Upd` is itself `[as printed]` against [CONF] Fig. 18b, so this row bundles a printed item with two declarations of ours
-/
/-- `ρ₁ ↭ ρ₂` as `[CONF]` Fig. 18b (p. 415:22) prints it: the two clauses, and
**no** validity guard.  `[as printed]` -/
def ResU.Upd (ρ₁ ρ₂ : ResU Loc Val) : Prop := ρ₁.UpdImm ρ₂ ∧ ρ₁.UpdMut ρ₂

/-!
Row 5.27, continued.
-/
/-- `ρ₁ ↭ ρ₂` as `[TR]` p. 5 prints it: the same two clauses, guarded by the
`✓ρ₁ ∧ ✓ρ₂` set to the right of the row's case-brace.  `[as printed]` -/
def ResU.UpdV (ρ₁ ρ₂ : ResU Loc Val) : Prop := ρ₁.Upd ρ₂ ∧ ρ₁.Valid ∧ ρ₂.Valid

end BoCa.Fig16

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
### 5.33 · `wp (e) {Q̂} (ρ) ≜ ∀ρ_f # ρ. ∃ρ′ # ρ_f, ρ⁺ # (ρ_f ● ρ′), v. (⟦ρ_f ● ρ⟧,e) →* (⟦ρ_f ● ρ′ ● ρ⁺⟧,v) ∧ ρ ↭ ρ′ ● ρ⁺ ∧ ρ⁺∣own = ∅ ∧ Q̂(v)(ρ′)` · [TR] p. 6, proposition row 5 · `[repair]`

The row's own shape is transcribed exactly — every partial term bound and related by its graph, ↭ at [TR]'s guarded reading, the own-free side condition as `BoCa.Fig16.BoLo.NoOwn` — but `→*` is `BoCa.BoLo.Steps`, the completed machine of rows 3.14, 3.30 and 3.31, so this `wp` is strictly WEAKER than the printed row. Adjudicated at `docs/boca-rules.md` §12.42, `docs/axiom-ledger.md` D6 and `BoCa/Fig16Wp.lean`'s "What the machine costs": [TR] §3's `Kont` is elided rather than exact, and [CONF] Corollary 3.3's conclusion is unreachable on the machine as printed at a closed term p. 2 types at `1` (`BoCa.TR3.derives_wSeq`, `BoCa.TR3.corThree_unreachable`); every addition is a frame, and `BoCa/TR3.lean` re-proves §6.7 over the printed machine with `BoCa.TR3.wp_le_fig16` between  **And at the typed world (`docs/boca-rules.md` §12.72)**: `∀ρ_f # ρ` ranges over the frames completing `ρ` to a `BoCa.Fig16.LogRel.Typed.TW` world at the record list, tagged, and the post-configuration is one too, with the same records and list members; every other conjunct is this row's. The settled reading that §6 quantifies over resources that arise; §12.68's configuration is one no program produces, and `BoCa.Fig16.LogRel.ViewWitness.excluded` shows the typed world excludes it (§12.73)
-/
/-- **`wp(e){Q̂}`** — `[TR]` p. 6's last-but-one row, on the printed carrier.

    wp(e){Q̂}(ρ) ≜ ∀ρ_f # ρ. ∃ρ′ # ρ_f, ρ⁺ # (ρ_f ● ρ′), v.
                     (⟦ρ_f ● ρ⟧, e) ↦* (⟦ρ_f ● ρ′ ● ρ⁺⟧, v)
                   ∧ ρ ↭ ρ′ ● ρ⁺ ∧ ρ⁺|own = ∅ ∧ Q̂(v)(ρ′)

`●` is the strict composition and `↭` is `[TR]` p. 5's guarded row.  The four
composites and the two lowerings the row applies are partial, so each is bound
and related by its graph: `fρ` is `ρ_f ● ρ`, `fρ'` is `ρ_f ● ρ′`, `fρ'p` is
`ρ_f ● ρ′ ● ρ⁺` and `π` is `ρ′ ● ρ⁺`.  `[as printed]` (`[TR]` p. 6's row; the
printed compositions and lowerings appear as their graphs — G4) -/
def wp (e : Expr) (Q : Val → WProp) : WProp := fun ρ =>
  ∀ ρf : WRes, ResU.Hash ρf ρ →
    ∃ (ρ' ρp fρ fρ' fρ'p π : WRes) (v : Val) (μ μ' : Heap),
      ResU.Hash ρ' ρf ∧
      ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧
      ResU.CompS ρf ρ fρ ∧ ResU.Lower fρ μ ∧
      ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧
      Steps μ e μ' (.val v) ∧
      ResU.CompS ρ' ρp π ∧ ResU.UpdV ρ π ∧
      NoOwn ρp ∧
      Q v ρ'

/-!
Row 5.62, continued.
-/
/-- **`wp` with `[CONF]` Fig. 18b's `↭`** — the same row of `[TR]` p. 6 with the
unguarded `ResU.Upd` where `wp` above takes `[TR]` p. 5's guarded `ResU.UpdV`.
`BoCa/Wp.lean` offers the pair the same way, and `wp_updV_iff_upd` below is what
closes ledger D3 for this file: on the printed carrier the two readings are the
same proposition.

`[variant: `wp` above with the `↭` of `[CONF]` Fig. 18b (p. 415:22) in place of
`[TR]` p. 5's, and otherwise identical — so it inherits `wp`'s own departures,
the larger machine of ledger D6 among them.]` -/
def wpU (e : Expr) (Q : Val → WProp) : WProp := fun ρ =>
  ∀ ρf : WRes, ResU.Hash ρf ρ →
    ∃ (ρ' ρp fρ fρ' fρ'p π : WRes) (v : Val) (μ μ' : Heap),
      ResU.Hash ρ' ρf ∧
      ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧
      ResU.CompS ρf ρ fρ ∧ ResU.Lower fρ μ ∧
      ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧
      Steps μ e μ' (.val v) ∧
      ResU.CompS ρ' ρp π ∧ ResU.Upd ρ π ∧
      NoOwn ρp ∧
      Q v ρ'

end BoCa.Fig16.BoLo

end
