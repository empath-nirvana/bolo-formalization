import Mathlib
import Paper.S1_Syntax.Definitions
import Support.Syntax.Terms

/-!
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

namespace BoCa.TR3

/-!
### 3.1 · `Kont ∋ K ::= [ ]` · [TR] p. 3 · `[as printed]`

Nullary constructor; plugging into the hole is the identity by `rfl`

### 3.2 · `Kont ::= … ∣ (K, e)` · [TR] p. 3 · `[as printed]`

Plugs to `.pair (plug K e) e₂`; no binder and no `Val`/`Expr` coercion in this frame

### 3.3 · `Kont ::= … ∣ (v, K)` · [TR] p. 3 · `[encoding]`

Named choice: the printed `v ⊆ e` is `BoCa.Expr.val`, the inclusion of row 1.17, so plugging writes `.pair (.val v) …`

### 3.4 · `Kont ::= … ∣ let (x, y) = K in e` · [TR] p. 3 · `[encoding]`

De Bruijn: the two binder names are erased and the body is the frame's second field (`x` = index 1, `y` = index 0)

### 3.5 · `Kont ::= … ∣ case K {inj₁ x.e₁ ∣ inj₂ y.e₂}` · [TR] p. 3 · `[encoding]`

De Bruijn: each branch binds index 0; the `injᵢ` patterns become the branch positions

### 3.6 · `Kont ::= … ∣ e K` · [TR] p. 3 · `[as printed]`

Hole in the argument, function an arbitrary expression — the argument-first order the print fixes

### 3.7 · `Kont ::= … ∣ K v` · [TR] p. 3 · `[encoding]`

The `BoCa.Expr.val` inclusion again; plugs to `.app (plug K e) (.val v)`
-/
/-- `[TR]` p. 3's evaluation contexts, all seven productions and no others:

    K ::= [ ] | (K,e) | (v,K) | let (x,y) = K in e
        | case K {inj₁ x.e₁ | inj₂ y.e₂} | e K | K v

`BoCa.BoLo.Kont` has these and three more (`K; e`, `inj₁ K`, `inj₂ K`).
`[as printed]` -/
inductive Kont where
  /-- `[ ]` -/
  | hole
  /-- `(K, e)` -/
  | pairL   (K : Kont) (e : Expr)
  /-- `(v, K)` -/
  | pairR   (v : Val)  (K : Kont)
  /-- `let (x,y) = K in e` -/
  | letpair (K : Kont) (e : Expr)
  /-- `case K {inj₁ x.e₁ | inj₂ y.e₂}` -/
  | case    (K : Kont) (e₁ e₂ : Expr)
  /-- `e K` — the argument is under the hole, the function is not yet a value. -/
  | appR    (e : Expr) (K : Kont)
  /-- `K v` — the argument is already a value. -/
  | appL    (K : Kont) (v : Val)
  deriving Repr

end BoCa.TR3

namespace BoCa.BoLo
open BoCa.Lifetime

/-!
Rows 3.1, 3.2, 3.3, 3.4, 3.5, 3.6, 3.7, continued.

### 3.30 · — no printed counterpart in §3 — · [TR] p. 3 · `[repair]`

Forced because [TR] p. 2's 1E types `e₁; e₂` at any `e₁ : 1` while p. 3 prints no such frame. Adjudicated at `docs/adjudications.md` §12.42 and D6, and argued rather than asserted: [TR] p. 2's 1E types `e₁; e₂` at any `e₁ : 1` while p. 3 prints no `K; e` frame, so a closed term the printed judgment types is stuck beside its own redex (`BoCa.TR3.stuck_wSeq`); `docs/adjudications.md` D6 refutes the one reading that would close it, `;` as sugar for `(λ_.e₂) e₁`; and `BoCa.TR3.corThree_unreachable` shows [CONF] Corollary 3.3's conclusion unreachable on the machine as printed

### 3.31 · — no printed counterpart in §3 — · [TR] p. 3 · `[repair]`

Forced because [TR] p. 2's ⊕I types `injᵢ e` at any `e` while p. 3 prints no `injᵢ K` frame. Adjudicated at `docs/adjudications.md` §12.42 and D6: [TR] p. 2's ⊕I types `injᵢ e` at any `e`, p. 3 prints no `injᵢ K`, `BoCa.TR3.no_step_inj₁` proves `inj₁ e` irreducible for every `e`, and `BoCa.TR3.stuck_wInj` is a closed typed witness. The argument survives both readings of the self-overlapping `Expr` grammar, since what is missing is a FRAME and identifying `v` with the structural production supplies none
-/
/-- [TR] §3's evaluation contexts. -/
inductive Kont where
  | hole
  | pairL   (K : Kont) (e : Expr)        -- `(K, e)`
  | pairR   (v : Val)  (K : Kont)        -- `(v, K)`
  | letpair (K : Kont) (e : Expr)        -- `let (x,y) = K in e`
  | case    (K : Kont) (e₁ e₂ : Expr)    -- `case K {…}`
  | appR    (e : Expr) (K : Kont)        -- `e K`  — argument-first
  | appL    (K : Kont) (v : Val)         -- `K v`
  | seq     (K : Kont) (e : Expr)        -- `K; e`      (added, see above)
  | inj₁    (K : Kont)                   -- `inj₁ K`    (added)
  | inj₂    (K : Kont)                   -- `inj₂ K`    (added)
  deriving Repr

end BoCa.BoLo

namespace BoCa.TR3.Kont

/-!
### 3.8 · `K[e]` (used in the context rule; the grammar fixes it implicitly) · [TR] p. 4 · `[encoding]`

The clause list is not printed, but each production has exactly one hole so the recursion is forced; carries the `BoCa.Expr.val` coercion at rows 3.3 and 3.7
-/
/-- `K[e]`. -/
def plug : Kont → Expr → Expr
  | .hole,         e => e
  | .pairL K e₂,   e => .pair (plug K e) e₂
  | .pairR v K,    e => .pair (.val v) (plug K e)
  | .letpair K e₂, e => .letpair (plug K e) e₂
  | .case K e₁ e₂, e => .case (plug K e) e₁ e₂
  | .appR f K,     e => .app f (plug K e)
  | .appL K v,     e => .app (plug K e) (.val v)

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
@[simp] theorem plug_hole (e : Expr) : plug .hole e = e := rfl

end BoCa.TR3.Kont

namespace BoCa.BoLo.Kont
open BoCa.Lifetime

/-!
Row 3.8, continued.
-/
/-- `K[e]`. -/
def plug : Kont → Expr → Expr
  | .hole,          e => e
  | .pairL K e₂,    e => .pair (plug K e) e₂
  | .pairR v K,     e => .pair (.val v) (plug K e)
  | .letpair K e₂,  e => .letpair (plug K e) e₂
  | .case K e₁ e₂,  e => .case (plug K e) e₁ e₂
  | .appR f K,      e => .app f (plug K e)
  | .appL K v,      e => .app (plug K e) (.val v)
  | .seq K e₂,      e => .seq (plug K e) e₂
  | .inj₁ K,        e => .inj₁ (plug K e)
  | .inj₂ K,        e => .inj₂ (plug K e)

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
@[simp] theorem plug_hole (e : Expr) : plug .hole e = e := rfl

end BoCa.BoLo.Kont

namespace BoCa.BoLo
open BoCa.Lifetime

/-!
### 3.9 · `Mem ∋ µ : Loc ⇀ Val` · [TR] p. 3 · `[encoding]`

Named choice: a total function into `Option` for the partial map. The print asks no finiteness here, unlike p. 4's `Res ≜ Loc ⇀ᶠⁱⁿ Cell`
-/
/-- A flat physical memory, `μ : Loc ⇀ Val` ([TR] §3). -/
abbrev Heap := Loc → Option Val

end BoCa.BoLo

namespace BoCa.BoLo.Heap
open BoCa.Lifetime

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
/-- `μ / ℓ` — [TR]'s `free` REMOVES the entry (`μ ⊎ [ℓ↦v] ↦ μ`), so a later
    `load` is genuinely stuck. -/
def del (μ : Heap) (ℓ : Loc) : Heap := fun k => if k = ℓ then none else μ k

@[simp] theorem del_same (μ : Heap) (ℓ : Loc) : del μ ℓ ℓ = none := by simp [del]

@[simp] theorem del_other {μ : Heap} {ℓ k : Loc} (h : k ≠ ℓ) : del μ ℓ k = μ k := by
  simp [del, h]

/-!
### 3.23 · `µ[ℓ ↦ v]` (in store↦) · [TR] p. 4 · `[as printed]`

Pointwise override at `ℓ`
-/
/-- `μ[ℓ ↦ v]`. -/
def upd (μ : Heap) (ℓ : Loc) (v : Val) : Heap := fun k => if k = ℓ then some v else μ k

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
@[simp] theorem upd_same (μ : Heap) (ℓ : Loc) (v : Val) : upd μ ℓ v ℓ = some v := by
  simp [upd]

@[simp] theorem upd_other {μ : Heap} {ℓ k : Loc} {v : Val} (h : k ≠ ℓ) :
    upd μ ℓ v k = μ k := by simp [upd, h]

end BoCa.BoLo.Heap

namespace BoCa.TR3
open BoCa.BoLo (Heap)

/-!
### 3.11 · the boxed judgments `(µ,e) → (µ′,e′)` and `(µ,e) ↦ (µ′,e′)` · [TR] p. 4 · `[encoding]`

Named choice: `→` is a definition with an ∃ over `K` rather than an inductive, because the index `K[e]` is not a constructor application. `Step1` is the print's `→` and `Steps` its `→*`; the head arrow `↦` is `Head`

### 3.13 · 1↦: `(µ, (); e) ↦ (µ, e)` · [TR] p. 4 · `[encoding]`

`.seq (.val .unit) e` — the left component is literally `()`, written through the `BoCa.Expr.val` inclusion

### 3.15 · ⊗↦: `(µ, let (x₁,x₂) = (v₁,v₂) in e) ↦ (µ, e[v₁/x₁, v₂/x₂])` · [TR] p. 4 · `[encoding]`

De Bruijn simultaneous substitution — `x₁` is index 1 and `x₂` index 0 — and `(v₁,v₂)` read as `BoCa.Val.pair` per the print's `v ⊆ e`

### 3.16 · ⊕↦: `(µ, case (injᵢ v) {inj₁ x.e₁ ∣ inj₂ y.e₂}) ↦ (µ, eᵢ[v/xᵢ])` · [TR] p. 4 · `[encoding]`

The schematic `i` split into its two instances; substitution de Bruijn

### 3.17 · ⊸↦: `(µ, (λx.e) v) ↦ (µ, e[v/x])` · [TR] p. 4 · `[encoding]`

De Bruijn substitution at index 0; the term is `.app (.val (.lam b)) (.val v)`

### 3.18 · alloc↦: `(µ, alloc v) ↦ (µ ⊎ ℓ ↦ v, ℓ)` · [TR] p. 4 · `[encoding]`

`⊎` as the side condition "`µ` is undefined at `ℓ`" plus an update; `ℓ` stays universally quantified, so the rule is nondeterministic exactly as printed

### 3.19 · free↦: `(µ ⊎ ℓ ↦ v, free ℓ) ↦ (µ, v)` · [TR] p. 4 · `[encoding]`

The left-hand `⊎` as "`µ` carries `v` at `ℓ`" and the result as `BoCa.BoLo.Heap.del`, which is the printed `µ`

### 3.20 · load↦: `µ(ℓ) = v` / `(µ, load ℓ) ↦ (µ, v)` · [TR] p. 4 · `[encoding]`

The term is `.app (.val (.prim .load)) (.val (.loc ℓ))` — row 1.10's nullary prim value applied to the location

### 3.22 · store↦: `ℓ ∈ dom(µ)` / `(µ, store ℓ v) ↦ (µ[ℓ ↦ v], ())` · [TR] p. 4 · `[encoding]`

One printed rule, one constructor. [TR] p. 1 derives the printed function part `store ℓ` twice — through `Prim ::= … ∣ store v` and through `e₂ e₁` — and a paper grammar identifies the two derivations; so does `Expr` (row 1.17), so the one printed left-hand side is one Lean term (`docs/adjudications.md` §12.43)
-/
/-- The eight head reductions of the `↦` box on `[TR]` p. 4, at the terms
`[TR]` p. 1's grammar gives them.  `⊕↦` is schematic in `i` and appears as its
two instances, so eight rules give nine constructors.

`alloc↦` is nondeterministic in `ℓ`, as printed: `μ ⊎ ℓ ↦ v` says only that `ℓ`
is fresh.  `free↦`'s `μ ⊎ ℓ ↦ v` on the left says the cell is there and is
removed.  `store↦`'s side condition is the printed `ℓ ∈ dom(μ)`, written as the
value `w` the location holds.

`BoCa.BoLo.Head` is these same nine rules under other names, so the two
machines differ only in `Kont`.  `[as printed]` -/
inductive Head : Heap → Expr → Heap → Expr → Prop where
  /-- `1↦`:  `(μ, (); e) ↦ (μ, e)`.  The left component is literally `()`. -/
  | one (μ : Heap) (e : Expr) : Head μ (.seq (.val .unit) e) μ e
  /-- `⊗↦`:  `(μ, let (x₁,x₂) = (v₁,v₂) in e) ↦ (μ, e[v₁/x₁, v₂/x₂])`. -/
  | tensor (μ : Heap) (v₁ v₂ : Val) (e : Expr) :
      Head μ (.letpair (.val (.pair v₁ v₂)) e) μ
        ((e.subst 0 (v₂.shift 1 0)).subst 0 v₁)
  /-- `⊕↦` at `i = 1`. -/
  | sum₁ (μ : Heap) (v : Val) (e₁ e₂ : Expr) :
      Head μ (.case (.val (.inj₁ v)) e₁ e₂) μ (e₁.subst 0 v)
  /-- `⊕↦` at `i = 2`. -/
  | sum₂ (μ : Heap) (v : Val) (e₁ e₂ : Expr) :
      Head μ (.case (.val (.inj₂ v)) e₁ e₂) μ (e₂.subst 0 v)
  /-- `⊸↦`:  `(μ, (λx.e) v) ↦ (μ, e[v/x])`. -/
  | lolli (μ : Heap) (b : Expr) (v : Val) :
      Head μ (.app (.val (.lam b)) (.val v)) μ (b.subst 0 v)
  /-- `alloc↦`:  `(μ, alloc v) ↦ (μ ⊎ ℓ ↦ v, ℓ)`. -/
  | alloc (μ : Heap) (v : Val) (ℓ : Loc) (h : μ ℓ = none) :
      Head μ (.app (.val (.prim .alloc)) (.val v)) (μ.upd ℓ v) (.val (.loc ℓ))
  /-- `free↦`:  `(μ ⊎ ℓ ↦ v, free ℓ) ↦ (μ, v)`. -/
  | free (μ : Heap) (ℓ : Loc) (v : Val) (h : μ ℓ = some v) :
      Head μ (.app (.val (.prim .free)) (.val (.loc ℓ))) (μ.del ℓ) (.val v)
  /-- `load↦`:  `μ(ℓ) = v` ⟹ `(μ, load ℓ) ↦ (μ, v)`. -/
  | load (μ : Heap) (ℓ : Loc) (v : Val) (h : μ ℓ = some v) :
      Head μ (.app (.val (.prim .load)) (.val (.loc ℓ))) μ (.val v)
  /-- `store↦`:  `ℓ ∈ dom(μ)` ⟹ `(μ, store ℓ v) ↦ (μ[ℓ ↦ v], ())`.  Its
      function part `store ℓ` is `[TR]` p. 1's VALUE `store v` and also the
      application `(store) ℓ`; the printed grammar identifies the two and so
      does `Expr`, so ONE printed rule is ONE constructor. -/
  | store (μ : Heap) (ℓ : Loc) (v w : Val) (h : μ ℓ = some w) :
      Head μ (.app (.app (.val (.prim .store)) (.val (.loc ℓ))) (.val v))
        (μ.upd ℓ v) (.val .unit)

/-!
Row 3.11, continued.

### 3.12 · →: `(µ,e) ↦ (µ′,e′)` / `(µ, K[e]) → (µ′, K[e′])` · [TR] p. 4 · `[encoding]`

`∃ K a a′, e = K.plug a ∧ e′ = K.plug a′ ∧ Head µ a µ′ a′`
-/
/-- `(μ,e) ↦ (μ',e')  ⟹  (μ, K[e]) → (μ', K[e'])` — the one context rule of the
`[TR]` p. 4 box, and the whole of `→`.  A `def` rather than an inductive for the
reason `BoCa.BoLo.Step1` gives: the index `K[e]` is not a constructor application.
`[as printed]` -/
def Step1 (μ : Heap) (e : Expr) (μ' : Heap) (e' : Expr) : Prop :=
  ∃ (K : Kont) (a a' : Expr), e = K.plug a ∧ e' = K.plug a' ∧ Head μ a μ' a'

end BoCa.TR3

namespace BoCa.BoLo
open BoCa.Lifetime

/-!
Rows 3.11, 3.15, 3.16, 3.17, 3.18, 3.19, 3.20, continued.

### 3.14 · 1↦: `(µ, (); e) ↦ (µ, e)` · [TR] p. 4 · `[as printed]`

Fires at `.seq (.val .unit) e`, the printed literal `()`. It fired at any value until the row was written; `BoCa.BoLo.wp_1` and `BoCa.Fig16.BoLo.wp_1` already stated 6.137 at `()`, so narrowing it changed no theorem statement

### 3.21 · store↦: `ℓ ∈ dom(µ)` / `(µ, store ℓ v) ↦ (µ[ℓ ↦ v], ())` · [TR] p. 4 · `[encoding]`

The left-hand side is `.app (.app (.val (.prim .store)) (.val (.loc ℓ))) (.val v)`, which is also `.app (.val (.storeV (.loc ℓ))) (.val v)`: the function part is [TR] p. 1's own `Prim` value `store v` and the application the same grammar derives, one term either way (rows 1.15, 1.17)
-/
/-- The head reductions of [TR] §3 (the `↦` box of p. 4), read on heaps.
    `alloc` is NONDETERMINISTIC in the fresh location, as printed. -/
inductive Head : Heap → Expr → Heap → Expr → Prop where
  | beta (μ : Heap) (b : Expr) (v : Val) :
      Head μ (.app (.val (.lam b)) (.val v)) μ (b.subst 0 v)
  | alloc (μ : Heap) (v : Val) (ℓ : Loc) (h : μ ℓ = none) :
      Head μ (.app (.val (.prim .alloc)) (.val v)) (μ.upd ℓ v) (.val (.loc ℓ))
  | free (μ : Heap) (ℓ : Loc) (v : Val) (h : μ ℓ = some v) :
      Head μ (.app (.val (.prim .free)) (.val (.loc ℓ))) (μ.del ℓ) (.val v)
  | load (μ : Heap) (ℓ : Loc) (v : Val) (h : μ ℓ = some v) :
      Head μ (.app (.val (.prim .load)) (.val (.loc ℓ))) μ (.val v)
  /-- `store↦` — `[TR]` p. 4's `(µ, store ℓ v) ↦ (µ[ℓ ↦ v], ())`.  Its function
      part `store ℓ` is `[TR]` p. 1's value `store v`, which is the application
      `(store) ℓ`, so the printed left-hand side is this one term and no rule
      coerces between two spellings of it. -/
  | store (μ : Heap) (ℓ : Loc) (v w : Val) (h : μ ℓ = some w) :
      Head μ (.app (.app (.val (.prim .store)) (.val (.loc ℓ))) (.val v))
        (μ.upd ℓ v) (.val .unit)
  /-- `1↦` — `[TR]` p. 4 prints `(µ, (); e) ↦ (µ, e)`, at a literal `()` and not at
      an arbitrary value.  `1E` types `e₁; e₂` at `e₁ : 1` and `𝒱⟦1⟧` holds only of
      `()`, so nothing in the paper needs the wider rule. -/
  | seq (μ : Heap) (e : Expr) : Head μ (.seq (.val .unit) e) μ e
  | letpair (μ : Heap) (v₁ v₂ : Val) (e : Expr) :
      Head μ (.letpair (.val (.pair v₁ v₂)) e) μ ((e.subst 0 (v₂.shift 1 0)).subst 0 v₁)
  | case₁ (μ : Heap) (v : Val) (e₁ e₂ : Expr) :
      Head μ (.case (.val (.inj₁ v)) e₁ e₂) μ (e₁.subst 0 v)
  | case₂ (μ : Heap) (v : Val) (e₁ e₂ : Expr) :
      Head μ (.case (.val (.inj₂ v)) e₁ e₂) μ (e₂.subst 0 v)

/-!
Rows 3.11, 3.12, continued.
-/
/-- `(μ, K[e]) ↦ (μ', K[e'])` — one step.

    Stated as a `def` rather than an inductive family: the index `K[e]` is not a
    constructor application, so an inductive would need dependent elimination at
    every inversion, and there are many. -/
def Step1 (μ : Heap) (e : Expr) (μ' : Heap) (e' : Expr) : Prop :=
  ∃ (K : Kont) (a a' : Expr), e = K.plug a ∧ e' = K.plug a' ∧ Head μ a μ' a'

end BoCa.BoLo

namespace BoCa

/-!
### 3.25 · `copy ≜ λx.(x, x)` · [TR] p. 4 · `[encoding]`

De Bruijn; [CONF] Fig. 15 calls the same term `dupl`
-/
/-- `copy ≜ λx. (x, x)`  — the conference paper calls it `dupl`
    (docs/adjudications.md §12.21).  Uses the linear `x` twice. -/
def copy : Expr := .val (.lam (.pair v0 v0))

/-!
### 3.26 · `forget ≜ λx.()` · [TR] p. 4 · `[encoding]`

De Bruijn; the binder is unused, as printed
-/
/-- `forget ≜ λx. ()`  — never uses `x`, so it needs weakening. -/
def forget : Expr := .val (.lam unit')

/-!
### 3.36 · — no printed counterpart; [TR] §1 prints only `let (x,y) = e₁ in e₂` — · [TR] p. 4 · `[repair]`

[TR] p. 4's own `swap` and `withswap` use a unary `let z = e;` that no printed grammar produces; `BoCa.elet` desugars it to `(λz. body) e`. Adjudicated at the `elet` declaration and `docs/adjudications.md` §12.20: [TR] p. 4's own `swap` and `withswap` are written with a unary `let z = e; e′` that [TR] p. 1's grammar does not produce, so a desugaring is forced rather than chosen, and which one is settled by the print — [TR]'s proof of Lemma 6.169 (p. 44) unfolds that `let` to `(λz. store v₁ v₂; (v₁, z)) (load v₁)`, which is `BoCa.elet` exactly. `BoCa.lam2` on its own would be `plumbing`
-/
/-- `let x = e; body` is sugar for `(λx. body) e` — the grammar in Fig. 1 has no
    `let`, only `e₁; e₂` and `let (x,y) = e₁; e₂`. -/
def elet (e : Expr) (body : Expr) : Expr := .app (.val (.lam body)) e

/-!
Row 3.36, continued.
-/
def lam2 (body : Expr) : Expr := .val (.lam (.val (.lam body)))

/-!
### 3.29 · `withswap ≜ λx.λf.let (y, z) = f (load x); store x y; (x, z)` · [TR] p. 4 · `[encoding]`

De Bruijn; decoded clause by clause it is the printed term, and [CONF] Fig. 15 prints the identical body
-/
/-- `withswap ≜ λx λf. let (y, z) = f (load x); store x y; (x, z)`.

    **Unlike `swap`, `withload` and `withbor`, this one is not a §12.20 case.**
    Verified at 900 dpi on both sources: [TR] p. 4 prints
    `λx.λf.let (y, z) = f (load x); store x y; (x, z)` and [CONF] **Fig. 15**
    (p. 415:17) prints the identical term, and it does match its ascribed type
    `Mut @a T₁ ⊸ (T₁ ⊸ T₁ ⊗ T₂) ⊸ (Mut @a T₁) ⊗ T₂` in both halves: the
    callback returns the pair `(y, z) : T₁ ⊗ T₂`, the *old* payload's
    replacement `y` is stored back, and the result `(x, z)` is the borrow
    together with `z : T₂`.  Note also that `f` is **not** a thunk here — the
    callback's type is a bare `⊸`, with no `∀` — so, unlike `withbor` and
    `withload`, there is no lifetime application to restore either.  Phases 4
    and 5 both had to take [CONF]'s version over [TR]'s; Phase 6 does not.

    It is ill-typed in the base system for the usual reasons: `x` is used three
    times, and `load`/`store` are marked `⊬` by [CONF] Fig. 3b (p. 415:4) and
    have no rule at all in [TR] p. 2.

    de Bruijn: under `λx λf` the binders are `x = 1`, `f = 0`; the `letpair`
    pushes `y = 1`, `z = 0` and shifts them to `x = 3`, `f = 2`. -/
def withswap : Expr :=
  lam2 (.letpair (.app v0 (.app load' v1))
         (.seq (.app (.app store' v3) v1)
               (.pair v3 v0)))

end BoCa

end
