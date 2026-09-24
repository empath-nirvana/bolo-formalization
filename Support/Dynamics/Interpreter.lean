import Paper.S1_Syntax.Definitions
import Support.Syntax.Terms

/-!
# Support — Dynamics — Interpreter

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
an executable interpreter — memories as association lists, a step function, a fuelled run — which `[TR]` does not print (it gives a relation) and which no result of the paper uses.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa

/-!
### 3.10 · `Mem ∋ µ : Loc ⇀ Val` (the executable counterpart) · [TR] p. 3 · `[repair]`

The `next` field is not in the print and makes `BoCa.step`'s allocation deterministic where `alloc↦` is nondeterministic in `ℓ`. Adjudicated at `BoCa/Wp.lean`'s convention W2 and `BoCa/TR3.lean` §1: [TR] p. 3's `alloc↦` is nondeterministic in `ℓ` and a total function cannot implement it, so the executable machine allocates at `µ.next`; `docs/axiom-ledger.md` D8 records that nothing bridges the two. The printed map is implemented separately as `BoCa.BoLo.Heap`, on which every `wp` theorem is proved, so the difference is confined to an artifact neither document prints
-/
structure Mem where
  cells : List (Loc × Val)
  next  : Loc
  deriving Repr

def Mem.empty : Mem := ⟨[], 0⟩

def Mem.get? (μ : Mem) (ℓ : Loc) : Option Val :=
  μ.cells.find? (·.1 = ℓ) |>.map (·.2)

def Mem.alloc (μ : Mem) (v : Val) : Loc × Mem :=
  (μ.next, ⟨(μ.next, v) :: μ.cells, μ.next + 1⟩)

def Mem.free (μ : Mem) (ℓ : Loc) : Mem :=
  { μ with cells := μ.cells.filter (·.1 ≠ ℓ) }

def Mem.set (μ : Mem) (ℓ : Loc) (v : Val) : Mem :=
  { μ with cells := μ.cells.map fun c => if c.1 = ℓ then (ℓ, v) else c }

/-- Non-empty memory at the end of a run is a leak — the bug in Fig. 2b. -/
def Mem.leaked (μ : Mem) : Bool := !μ.cells.isEmpty

inductive Stuck where
  | unboundVar | notAFunction | notAPair | notASum | notAUnit
  | useAfterFree | badPrimArg
  deriving DecidableEq, Repr

inductive Step where
  | next  (μ : Mem) (e : Expr)
  | value (v : Val)
  | stuck (r : Stuck)

/-!
### 3.37 · — no printed counterpart; the print gives a relation — · [TR] p. 4 · `[repair]`

A deterministic executable machine where the print gives a relation; it adds the `K; e` and `injᵢ K` congruences. Nothing in the `wp` development depends on it. Every difference is adjudicated: determinism by `BoCa/Wp.lean`'s W2 and `docs/axiom-ledger.md` D8, the two congruences by `docs/boca-rules.md` §12.42, evaluation order by §12.1. That closes the one difference §12.42 had ruled ours when it narrowed `BoCa.BoLo.Head.seq` and the executable machine did not follow
-/
/-- Apply a primitive value to one argument.

    `alloc`, `free` and `load` are saturated by it; `store` is not, and what one
    argument builds is `[TR]` p. 1's printed value `store v` — which is that
    application, so `delta` returns it as a value rather than stepping to one.
    Every value whose head is a primitive appears on the left, so `step` needs
    no arity test: the grammar already says how many arguments each production
    still wants. -/
def delta (μ : Mem) : Expr → Val → Step
  | .prim .alloc,   v => let (ℓ, μ') := μ.alloc v; .next μ' (.loc ℓ)
  | .prim .free,    ⟨.loc ℓ, _⟩ =>
      match μ.get? ℓ with
      | some v => .next (μ.free ℓ) v.val
      | none   => .stuck .useAfterFree
  | .prim .load,    ⟨.loc ℓ, _⟩ =>
      match μ.get? ℓ with
      | some v => .next μ v.val
      | none   => .stuck .useAfterFree
  | .prim .store,   v => .value (.storeV v)
  | .app (.prim .store) (.loc ℓ), v =>
      match μ.get? ℓ with
      | some _ => .next (μ.set ℓ v) .unit
      | none   => .stuck .useAfterFree
  | _, _ => .stuck .badPrimArg

/-!
Row 3.37, continued.
-/
/-- One step of call-by-value reduction.

    Evaluation order follows the evaluation contexts of the technical report
    (§3 Dynamics):

      K ::= [] | (K, e) | (v, K) | let (x,y) = K in e
          | case K {inj₁ x. e₁ | inj₂ y. e₂} | e K | K v

    Pairs are **left-to-right** (`(K,e)` before `(v,K)`), but application is
    **argument-first / right-to-left**: the frame `e K` puts the hole in the
    argument while the function is still an arbitrary expression, and only once
    the argument is a value `v` does the frame `K v` evaluate the function.
    This matches ⊸E, whose premises are argument-then-function and whose split
    is `Γ₁, Γ₂` with `Γ₁` typing the argument.

    (The order makes no difference to any Fig. 2 program — in all of them the
    function is already a value — but the `Kont` grammar settles the question,
    so `step` follows it.)

    Two places where this `step` is deliberately more permissive than the
    report's `Kont` grammar, which appears to be incomplete: the report has no
    frame for `K; e` or for `injᵢ K`, so under a literal reading `free x; y`
    would be stuck. We keep the obvious congruence rules.

    A pair of values IS the value pair, so there is no administrative step from
    one to the other and no rule that takes it: `.value` is returned directly.
    The same holds of `injᵢ v` and of `store v`, the last being why the `app`
    branch can answer `.value`.

    `seq` fires at `()` and nowhere else, as `1↦` prints it. -/
def step (μ : Mem) : Expr → Step
  | .var _  => .stuck .unboundVar
  | .unit   => .value .unit
  | .lam b  => .value (.lam b)
  | .loc ℓ  => .value (.loc ℓ)
  | .prim p => .value (.prim p)

  | .pair e₁ e₂ =>
    match step μ e₁ with
    | .value v₁    => match step μ e₂ with
                      | .value v₂    => .value (.pair v₁ v₂)
                      | .next μ' e₂' => .next μ' (.pair e₁ e₂')
                      | .stuck r     => .stuck r
    | .next μ' e₁' => .next μ' (.pair e₁' e₂)
    | .stuck r     => .stuck r

  | .inj₁ e => match step μ e with
    | .value v    => .value (.inj₁ v)
    | .next μ' e' => .next μ' (.inj₁ e')
    | .stuck r    => .stuck r

  | .inj₂ e => match step μ e with
    | .value v    => .value (.inj₂ v)
    | .next μ' e' => .next μ' (.inj₂ e')
    | .stuck r    => .stuck r

  | .seq e₁ e₂ => match step μ e₁ with
    | .value ⟨.unit, _⟩ => .next μ e₂
    | .value _          => .stuck .notAUnit
    | .next μ' e₁'      => .next μ' (.seq e₁' e₂)
    | .stuck r          => .stuck r

  | .letpair e₁ e₂ => match step μ e₁ with
    | .value ⟨.pair a b, h⟩ =>
        .next μ ((e₂.subst 0 (Val.shift 1 0 ⟨b, h.pair_right⟩)).subst 0 ⟨a, h.pair_left⟩)
    | .value _     => .stuck .notAPair
    | .next μ' e₁' => .next μ' (.letpair e₁' e₂)
    | .stuck r     => .stuck r

  | .case e e₁ e₂ => match step μ e with
    | .value ⟨.inj₁ a, h⟩ => .next μ (e₁.subst 0 ⟨a, h.inj₁_inv⟩)
    | .value ⟨.inj₂ a, h⟩ => .next μ (e₂.subst 0 ⟨a, h.inj₂_inv⟩)
    | .value _            => .stuck .notASum
    | .next μ' e'         => .next μ' (.case e' e₁ e₂)
    | .stuck r            => .stuck r

  -- frame `e K` first: the argument is evaluated while the function is still an
  -- arbitrary expression; the frame `K v` then evaluates the function.
  | .app f a => match step μ a with
    | .value v    => match step μ f with
                     | .value w    => match w.val with
                                      | .lam b      => .next μ (b.subst 0 v)
                                      | .prim p     => delta μ (.prim p) v
                                      | .app f' a'  => delta μ (.app f' a') v
                                      | _           => .stuck .notAFunction
                     | .next μ' f' => .next μ' (.app f' a)
                     | .stuck r    => .stuck r
    | .next μ' a' => .next μ' (.app f a')
    | .stuck r    => .stuck r

/-- Outcome of a bounded run. Fuel keeps everything total. -/
inductive Outcome where
  | value   (v : Val) (leaked : Bool)
  | stuck   (r : Stuck)
  | timeout
  deriving Repr

/-!
Row 3.37, continued.
-/
def run : Nat → Mem → Expr → Outcome
  | 0,     _, _ => .timeout
  | n + 1, μ, e =>
    match step μ e with
    | .value v    => .value v μ.leaked
    | .next μ' e' => run n μ' e'
    | .stuck r    => .stuck r

/-!
Row 3.37, continued.
-/
def eval (e : Expr) : Outcome := run 1000 Mem.empty e

end BoCa

end
