# The pure fragment of BoCa

This directory is an extension of the mechanisation, not part of the transcription.  It
asks which BoCa programs are *pure*, and what that means, in the sense of Matsushita and
Ishii, *Pure Borrow* (PLDI 2026), §1:

> Functional programming favors purity, or the property that the result of the computation
> is always the same regardless of the timing and context.

Pure Borrow §7 notes that the metatheory of *From Linearity to Borrowing* does not address
the functional behaviour of borrowing programs (issue
[#1](https://github.com/empath-nirvana/bolo-formalization/issues/1)).  BoCa's calculus is
impure by design (it has `alloc`, `free`, `load`, `store`).  What follows identifies a
fragment, by types, and proves what its programs guarantee.  It uses the library's
Fundamental Property (`[TR]` Lemma 6.151) and typed world unchanged.

`[CONF]` is the conference paper and `[TR]` its supplement, as elsewhere in this repository.

## Building and checking

```sh
lake build Purity            # not a default target
scripts/check-purity.sh      # builds it, then checks every declaration's axioms
scripts/check-hygiene.sh     # its keyword scan covers Extensions/ too
```

The library imports `Paper` and `Support` and nothing imports it; `Paper/`, `Support/` and
`comparator/` are unchanged.  Every declaration's axioms are within `[propext,
Classical.choice, Quot.sound]`, and the directory contains no `sorry`, `axiom`,
`native_decide`, `implemented_by`, `opaque`, `partial` or `unsafe`.

## The fragment

A program `Δ; Γ ⊢ e : T` typed by `DerivesWf` is in the pure fragment (`PureTyping`,
`Pure.lean`) when its interface holds no exclusive resource:

* every live slot of `Γ` has a type built from `1`, `⊕`, `⊗` and `Imm @a S`, `S` arbitrary
  (`PureArgTy`): plain data and immutable borrows;
* `T` is built from `1`, `⊕` and `⊗` (`PlainTy`): plain data.

Inside, the program may allocate, mutate and free as it likes.

At these types the relation's resources are simple: a plain-data value holds `∅` and mentions
no location (`vP_plain`); an argument holds only `imm` cells (`vP_pureArg`, `gDenX_pure`).

## What is proved

The results come in two levels, as purity does here.

**Level 1: pure relative to the borrowed data.**  For `γ` closing values in the relation at
`ρ`, and a tagged typed world `ρf ● ρ` with heap `μ`:

| result | statement |
|---|---|
| `pure_heap` | the run the Fundamental Property exhibits ends at exactly `μ`, with a plain-data value `v`; every fresh run returns `v` and ends at `μ` up to an injective renaming of its locations |
| `pure_result` | every fresh run of `γ(e)` from `μ` returns `v`; given one, so does every run of `γ(e)` from any heap `μ₂` that agrees with `μ` on the allocated locations reachable from `γ`, `μ₂` being otherwise arbitrary |
| `derivesWf_runIn` | every run of `γ(e)`, from any heap, touches only locations reachable from `γ` or allocated by the run itself (holds of every `DerivesWf` program, pure or not) |

So a program of the fragment, on fresh runs, is observationally a function of its argument
values and the memory they reach, and it gives the heap back: temporaries are freed, and
nothing it can reach is changed.  This is purity *relative to the borrowed contents*.  The same call made at
another time can return a different value if the borrowed data was mutated in between, by
the lender, between two borrows.  That is the sense in which Rust treats `fn(&T) -> U` without
interior mutability as a function of `T`.

Within one borrow's lifetime the borrowed contents do not change: on the run the relation
exhibits for a computation, from a world holding the borrow's `imm` cell, nothing beneath the
cell changes, whether the cell is in the computation's resource or in its frame.  This is the model's *deep
immutability* (`[CONF]` §5, p. 415:24: *"our model enforces deep immutability of the data an
immutable borrow points to, while Tree Borrows only maintains a shallow immutability of the
reference itself"*), proved here at the level of the machine:

| result | statement |
|---|---|
| `frozen_keeps`, `wpTS_frozen` | on the run a `wpTS` exhibits at `ρ`, every location beneath an `imm` cell of `⦇ρ⦈` (in `⦇χ⦈_○` for a cell `imm(ᾱ, u, χ)`) keeps its value |
| `wpTS_footprint` (first clause) | every location of `⦇ρf⦈`, the frame, keeps its value |

The step is `[TR]` Lemma 6.48's: an `imm` cell of `ag(ρ₂)` is kept by `↭` with its witness,
and the witness's flattening is a factor of both aliasable walks (the library's
`ResU.flat_imm_wit_factor`).  So a borrowed structure is frozen for code that holds the borrow
and for code that does not.

**Level 2: pure in Pure Borrow's sense.**  A closed program of plain-data type has no
borrowed input, and is pure outright:

| result | statement |
|---|---|
| `closed_pure` | for `∅; ∅ ⊢ e : T`, `T` plain: adequacy's run from the empty memory returns a plain-data `v`, freeing everything it allocates; every fresh run from every heap whatsoever returns `v`; from the heap of every tagged typed world there is a run that gives the heap back |

## The machine facts underneath

These hold of every term, typed or not.

| file | results |
|---|---|
| `Rename.lean` | `Expr.rename`, `Heap.rename`; renaming commutes with shifting, substitution and plugging; runs are invariant under permutations of locations (`steps_rename`) |
| `Steps.lean` | unique decomposition (`plug_decomp`); a step that is not an allocation is the only step (`step1_det`); a run that never allocates is the only run to a value (`stepsNA_det`) |
| `Fresh.lean` | fresh runs (each allocation picks a location the configuration does not name); fresh runs from one configuration agree up to a permutation (`freshRun_det`) |
| `Sim.lean` | every run is the image of every fresh run from the same configuration along a function injective on its heap (`fresh_run_image`) |
| `Local.lean` | **locality**: a fresh run from `(μ₁, e)` and any run from `(μ₂, e)`, where `μ₂` agrees with `μ₁` on what `e` reaches, return values related by a renaming (`fresh_run_local`) |
| `Read.lean` | every run touches only what its term reaches or what it allocates (`steps_runIn`) |

Allocation is the machine's only nondeterminism.  On fresh runs it is invisible up to a
renaming of locations, and a plain-data result mentions no location, so it is invisible
altogether.  This is the counterpart here of the fresh-identifier question Pure Borrow §7
raises for its borrow ids δ, in a different calculus: there the conjecture concerns ids
generated by its denotational semantics; here the fresh names are heap locations, and the
renaming is proved.

## What typing contributes, and the boundary

The semantic relation (the conclusion of the Fundamental Property) bounds what a run
*changes* (`wpTS_footprint`, `wpTS_frozen`).  It does not bound what a run *reads*.

`Boundary.lean` makes this exact.  `peek k = let x = alloc () in ((λ_. ()) (load k); free x)`
is in the semantic relation at `∅; ∅ ⊨ peek k : 1` (`peek_sem`).  In a world whose heap lacks
`k`, its run allocates `k` itself and loads it; in a world whose heap holds `k`, it allocates
elsewhere and loads the cell `k` of the frame.  From the world whose frame owns `k`, every run
of `peek k` to a value loads `k`, which it did not allocate.

| statement | at `DerivesWf` | at `SemX` |
|---|---|---|
| a closed plain-data program has a run touching only what it allocates (`ReadFootprintSyn`, `ReadFootprintSem`) | holds, `readFootprintSyn` | does not hold, `not_readFootprintSem` at `peek 0` |

Two features of the model meet in `peek`: a load leaves no trace in the post-world, so `↭`
constrains what a run changes and never what it reads; and `wp` exhibits one run per world,
whose `alloc↦` may pick a location that depends on the frame.

The syntactic fact that separates the two columns is that no typing rule types a location:
a `DerivesWf` term mentions none (`derivesWf_locFree`), so every location of `γ(e)` comes from
`γ` (`occ_substAll_of_locFree`).  With `Read.lean`'s machine fact, that is the read footprint
of well-typed programs.

## What remains open

Each item below is not derived; no obstruction to it has been verified.

* **Existence of fresh runs.**  `pure_result`, `closed_pure` and the fresh-run half of
  `pure_heap` speak about fresh runs, the runs of any allocator that never reuses a location
  its configuration names (a bump allocator, for instance).  The exhibited run of `wpTS` need
  not be fresh, and that a well-typed program always has a fresh run is not derived.  The
  exhibited run's own statements (`pure_heap`'s first half, the run in `closed_pure`) are
  unconditional.  `FreshExistence.lean` states the missing fact and shows the semantic
  relation alone does not give it (below).
* **Runs that are not fresh.**  An allocator that reuses a location the program still names
  is outside these statements for untyped terms.  For well-typed terms it would need a
  typing invariant along the run (no dangling name is ever used), which the semantic proof of
  the Fundamental Property does not provide.
* **Heaps outside typed worlds.**  The heap statements (`pure_heap`, `heap_restored`) hold
  at the heaps of tagged typed worlds.  `pure_result`'s second heap is arbitrary.
* **The reachable set and the borrowed resource.**  `pure_result` asks the two heaps to agree
  on every location reachable from `γ`.  That over-approximates what the borrows grant: a
  closure stored behind an `Imm` borrow is reachable, but `withload` hands it back at `Unk`
  and it cannot be called.  A statement over `⦇ρ⦈` instead of the reachable set is not
  attempted.
* **Results at the semantic judgment.**  `peek` bounds the *read* footprint only: its result
  does not depend on the frame.  Whether `SemX` alone makes a plain-data program's result a
  function of its arguments is not settled here.
* **Equations.**  Termination (`[CONF]` Theorem 3.2) and the results above suggest that calls of
  the fragment can be reordered, duplicated or dropped.  No such program equivalence is stated
  or proved here.
* **Mutable borrows in the interface.**  A program taking `Mut @a S` or `Ref S` changes that
  memory, and would be pure in the linear-state sense (like the `ST` monad): a function from
  the lent contents to the result and the new contents.  The write footprint
  (`wpTS_footprint`) bounds the change; the functional statement is not attempted.

## State-monad correspondence (stage 2): where it stands

The next question of issue #1 is whether a well-typed program *with* exclusive state in its
interface (owned `Ref`, `Mut` borrows) denotes a state-passing function
`args × State → result × State`, with the pure fragment as the case of an empty state, and
with states compared up to renaming of freshly allocated cells so that a `Ref` escaping into
the result can grow the state.  The planned steps were: (1) every well-typed program has a
fresh run; (2) the denotation `⟦e⟧`, read off the determinacy of fresh runs; (3) adequacy,
every run computes `⟦e⟧` up to renaming; (4) a `Mut` borrow as a lens, the lent cell after the
scope being the `put` of what the callback did; (5) examples.

**The work stops at step 1.**  Steps 2–5 are not attempted: a denotation read off fresh runs,
and its adequacy for *every* run, both rest on step 1, and without it they would only restate
`pure_result`'s conditional form.

| statement | at `DerivesWf` | at `SemX` |
|---|---|---|
| from every tagged typed world, the program, closed by values of the semantic relation, has a fresh run to a value (`FreshRunsExistSyn`, `FreshRunsExistSem`) | does not hold, `not_freshRunsExistSyn` | does not hold, `not_freshRunsExistSem` at `peek 0` |
| the same for a closed program (`FreshRunsExistClosed`) | proved, `freshRunsExistClosed` (below) | — |
| the same for a program of the pure fragment (`FreshRunsExistPure`) | proved at argument types where no `⊸`/`∀` is read at the program's view (`freshRunsExistPureInd`); for all argument types with the arguments in the relation at the fresh runs (`freshRunsExistPureF`); otherwise not derived | — |

From the empty world, every run of `peek 0` to a value allocates `0` so that its `load 0`
succeeds; `0` is named by the term, so no fresh run reaches a value.  `FreshRunsExistSyn` fails
for a different reason (`Closures.lean`): its closing values come from the semantic relation,
which admits at `1 ⊸ 1` the closure `λ_. staleL` of `Stale.lean`, and the well-typed `f ()`
then runs it.  The forms that remain open keep what the program can reach syntactically
typed: a closed program cannot reach the frame's closures, and in the pure fragment a closure
behind an `Imm` borrow reaches the program only at `Unk` and cannot be called.
`pure_result_every_run` records what `FreshRunsExistPure` would give: every run of a program of
the pure fragment, from the world's heap or from any heap agreeing on what the arguments
reach, returns the exhibited value.

A run can be renamed into a fresh one as long as it never reads through a name whose location
it freed and then reallocated.  That is a property of the states along a run.  The semantic
relation constrains a run only through its final world, and `DerivesWf` does not type a run's
intermediate terms: they mention locations, which no typing rule types
(`derivesWf_locFree`), and the axiom terms' reducts duplicate a lent location
(`withbor ≜ λx.λf.(x, f () x)` reduces to `(ℓ, f () ℓ)`).

### The nominal route, and where it stops

A nominal argument for fresh-run existence would go as follows.  The model compares locations
only by equality, so the relation should be invariant under permutations of locations.  A
`DerivesWf` term names no location (`derivesWf_locFree`), so it is fixed by every permutation.
At each allocation of the exhibited run, the chosen location would be renamed to one nothing
names, and invariance would keep the run valid.

`Stale.lean` shows that the program-side facts this argument uses are not enough:

| statement | at `SemX` and location-free |
|---|---|
| every location-free term of the semantic relation has a fresh run from every tagged typed world (`FreshRunsExistSemLocFree`) | does not hold, `not_freshRunsExistSemLocFree` at `staleL` |

    staleL = let x = alloc () in free x;
             let y = alloc (inj₁ ()) in (λ_. ()) (load x); case (free y) {_ ⇒ () | _ ⇒ ()}

`staleL` names no location (`staleL_locFree`) and is in the relation at `∅; ∅ ⊨ staleL : 1`
(`staleL_sem`): from every world its run reallocates `x`'s location for `y`, reads `inj₁ ()`
through `x`, and gives the heap back.  From the empty world it has no fresh run
(`staleL_no_fresh`): a fresh run may not reallocate a location the term still names, and then
`load x` is stuck.

The renaming step above is where the argument meets `staleL`: renaming only the allocation of
`y` is not a permutation of the configuration, because the term still names the old location
through `x`.  Renaming the whole run by a permutation keeps every allocation as stale as it
was.  Whatever the model's invariance under permutations, it is a fact about the model and
holds for `staleL` as well; with membership in the relation and location-freeness, it cannot
yield fresh runs.  A proof of fresh-run existence has to use more of the typing than that the
term names no location — here, that `staleL` uses `x` after `free x` consumes it.  The
equivariance of the model's definitions (step 1 of the route) is therefore not mechanised:
it would not close step 2.  No definition read for this work inspects a location other than
by equality, but that is not verified.

### An invariant along runs: design

What follows is a design for proving fresh-run existence from an invariant along runs; it was
not started.  Fresh runs came instead from the Fundamental Property at a class of fresh runs
(below).

**Invariants on names alone** (`Invariant.lean`).
* *Term liveness* (`TermLive`): every location the term mentions is allocated.  `staleL`
  breaks it: after `free x` the term still mentions `x`'s location.  It is not enough on its
  own (`not_termLiveSuffices`): `staleH` has a run from the empty heap all of whose states are
  term-live and no fresh run.  A value stored in a cell goes stale without the term
  mentioning it, and is read back once its location is reallocated.
* *Reach liveness*: every location reachable from the term through the heap is allocated.
  That excludes `staleH`, and a run satisfying it at every allocation could be renamed into a
  fresh one by `Local.lean`'s simulation (not proved here).  But well-typed programs break it
  in `withswap`'s window: during the callback, the lent cell still holds the payload the
  callback owns and may free (`withswapWindow`; its typing and run are not built, so this is
  not machine-checked).

So an invariant that suffices has to say which cells' contents are *moved out*, as
`withswap`'s is during its callback, and has to know that nothing but the pending `store`
reaches such a cell.  That is a fact about ownership, which is carried by types.

**The invariant proposed: a run-time typing of configurations.**  A store typing
`Σ : Loc ⇀ Ty × state`, `state ∈ {owned, lent-imm 'a, lent-mut 'a, moved-out}`, and a
judgment `Σ; Δ; Γ ⊢ e : T` extending `DerivesWf` with
* locations: `ℓ : Ref T` for an owned cell, used once across the term and the heap;
  `ℓ : Imm 'a T` and `ℓ : Mut 'a T` for a lent cell, the lender's own occurrence frozen;
* one rule for each intermediate state of the axiom terms' reducts: `withbor`'s
  `(ℓ, f () ℓ)`, `withload`'s `f () (load ℓ)` and its loaded value, `withswap`'s
  `let (y, z) = f v; store ℓ y; (ℓ, z)` with `ℓ` moved out, and `swap`'s two states;
* a heap typing: every cell's content typed by `Σ`, a moved-out cell's content unconstrained.

Its consequences would be reach liveness outside moved-out cells, and that a moved-out cell is
touched only by its pending `store` — enough for the renaming argument.

**Cost.**  The preservation proof ranges over the 9 head redexes and the 10 evaluation frames,
against the 27 rules of `DerivesWf` (by inversion) and about ten run-time rules.  It needs
weakening and splitting lemmas for the linear contexts, substitution of a value for a linear
variable (de Bruijn, through `Ctx.Split`), substitution of a lifetime into a derivation (for
`∀E`, which the semantic proof never needs), decomposition of a typing of `K[e]`, and, for
`FreshRunsExistPure`, a bridge from a tagged typed world and `gDenX` to a store typing.  The
hard cases are `withbor` (the lender's frozen occurrence beside the borrower's, and the
borrow's lifetime at run time), `withswap` (the moved-out state), `∀E` (lifetime
substitution) and `free` (an owned cell leaving `Σ`).  The estimate is several thousand
lines, on the scale of the typed world itself.

### Where the freedom in allocation comes from (`Policy.lean`)

* **The allocation rule is demonic.**  `Typed.wpTS_alloc` (`Support/TypedWorld/Wp.lean:573`,
  `[TR]` 6.141) chooses its location by `PMap.exists_fresh` from the flattening `⦇ρf ● ρ⦈`
  (line 579).  A location is missing from the flattening exactly when it is missing from the
  heap (`lower_eq_none_iff`, line 580), and nothing after the choice depends on it.
  `wpTS_alloc_any` proves the rule at *every* heap-fresh location: the step to it satisfies
  row 5.33's post-conditions (`PostAt`) from every tagged typed world.
* **The freedom is in `wpTS`'s definition** (`Support/TypedWorld/World.lean:137`, the
  existential run at line 146).  The run the Fundamental Property exhibits is assembled only
  by `wpTS_val` (`Wp.lean:529`), `wpTS_head` (541), `wpTS_alloc` (594), `wpTS_free` (628), the
  two load rules (649, 677), `wpTS_store` (717) and `wpTS_bind` (`Steps.plug`, `Steps.trans`,
  754); every other rule passes the run through.  Each of these constructions is a run under
  any allocation policy that picks a heap-fresh location, given `wpTS_alloc_any`.  So a
  `wpTS` whose run were a `PolRun pol` would satisfy the same rules.  In this repository that
  means re-running the typed world (`Wp`, `FrameRules`, `Reborrow`, `Relation`,
  `Compatibility`, and the Fundamental Property's induction) at a second `wpTS`, several
  thousand lines in which only the eight constructions above change; it is not done here.
  In a development where `wpTS` can be edited, the change is to its run conjunct: replace
  `Steps μ e μ' (.val v)` by `PolRun pol μ e μ' (.val v)` for a policy `pol` returning a
  heap-fresh location on finite heaps, and re-prove the eight constructions.
* **A term of the semantic relation can need the freedom** (`not_semPolicyRuns`).  `peek 1`
  is in the relation at `∅; ∅ ⊨ peek 1 : 1`; from the empty world the least-free policy
  (`leastFree`) allocates `0`, and `load 1` is stuck.  Its semantic proof allocates `1` when
  the heap misses it.  A policy-indexed `wpTS` would exclude such terms from the relation, as
  it should: `peek` is not well typed.

## Every run under an allocation policy (branch `policy-wp`)

`Support/`'s `wp` is stated at every class of runs closed under the operations its rules build
runs with (`Typed.RunRel`, `Typed.wpTSR`), with the printed `wp` the instance at every run
(`docs/adjudications.md` §12.74).  The Fundamental Property holds at every class
(`Typed.fundamentalR`), in particular at the runs of any allocation policy
(`BoLo.PolRun`, `Typed.polRel`); `Typed.adequacyPol` is adequacy under every policy.  A policy
run is the only one from its start (`polStep_det`, `polRun_det`, `PolicyRuns.lean`), so:

| result | statement |
|---|---|
| `closed_policy_adequacy` | for every policy, the run of a closed program of type `1` from the empty memory ends at `()` and the empty memory, and every run under the policy that reaches a value is this one |
| `closed_policy_pure` | for a closed program of plain-data type and every policy, from the heap of every tagged typed world the policy's run gives the heap back with a plain-data value, and it is the only policy run to a value |
| `pure_policy_heap` | the same for the pure fragment, its arguments in the relation at the policy's runs |

What remains open.  These results fix the allocator; they do not compare two allocators, or
runs from heaps that agree only on what the arguments reach — `Local.lean`'s comparison, which
needs one of the runs fresh.  A policy sees only the memory, while a fresh choice must avoid the
locations the term names, and a choice that looks at the term is not preserved by plugging at a
single class: the run of a redex cannot see the context it is plugged into.  The next section
indexes the class instead.  The least-free policy is not
fresh in general: during a `withswap` callback the lent cell still names the payload, which
the callback may free and the policy then reallocate (`withswapWindow`; not machine-checked).
For open programs the arguments must be in the relation at the policy's runs
(`gDenXR (polRel pol)`); a closure the relation at every run admits need not be
(`staleClosure`, `not_semPolicyRuns`).

## Fresh runs of well-typed programs (branch `fresh-avoid`)

The class of runs is indexed (`Typed.RunRel.I`); plugging a run into a context `K` may change the
index (`RunRel.shift`), and `wp` holds at every index.  `Typed.freshRel` is indexed by a finite list
`N`: its runs allocate only locations that neither `N` nor the configuration names
(`BoLo.FreshRunN`, `Support/Dynamics/Fresh.lean`); a run plugged into `K` must avoid the locations
of `K` too (`FreshRunN.plug`).  The Fundamental Property holds at it (`Typed.fundamentalR`), and
`Typed.adequacyFresh` is adequacy with fresh allocation.

| result | statement |
|---|---|
| `freshRunsExistClosed` | a closed well-typed program has a fresh run from the heap of every tagged typed world: `FreshRunsExistClosed` |
| `closed_pure_every_run` | a closed program of plain-data type returns one plain-data value on **every** run from **every** heap |
| `freshRunsExistPureF` | a program of the pure fragment has a fresh run, its arguments in the relation at the fresh runs |
| `pure_result_every_run_fresh` | with the arguments in that relation, from every tagged typed world's heap `μ`: a fresh run gives `μ` back and returns `v`; every run from `μ`, and every run from any heap agreeing with `μ` on what the arguments reach, returns `v` |

`staleL` and `λ_. staleL` are not in the relation at the fresh runs: from the empty world
`staleL` has no fresh run.  What remains open: `FreshRunsExistPure` with the arguments in the
relation at every run.  At plain data the relation mentions no `wp`; but a `Mut` cell inside a
borrowed payload stores a predicate that mentions `wp` (`vX`'s `Mut` clause), where the two
relations need not agree.  The transfer is not derived, and no obstruction is verified.

### The pure fragment with arguments in the relation at every run (branch `fresh-pure`)

The relation mentions `wp` only at `⊸` and `∀` read at the program's view.  An `Imm` payload is
read at the observable view, where `⊸` and `∀` are `True`, but a `Mut` cell's stored predicate
is read at the program's view wherever the cell sits.  `Ind b T` (`Independence.lean`) says no
`⊸`/`∀` of `T` is read at the program's view; there the relation does not depend on `wp`
(`vX_indep`), so neither does the context relation (`gDenXR_indep`).

| result | statement |
|---|---|
| `freshRunsExistPureInd` | `FreshRunsExistPure` at argument types satisfying `Ind` (`PureTypingInd`): plain data, `Imm` borrows of data, of references, of borrows, of functions, of `Mut` borrows of data |
| `pure_result_every_run_ind` | at those types, with the arguments in the relation at every run: a fresh run gives the heap back and returns `v`, every run from the world's heap returns `v`, and every run from any heap agreeing on what the arguments reach returns `v` |
| `vX_lolli_depends` | at the program's view the relation at `1 ⊸ 1` differs between every run and the fresh runs: `λ_. staleL` is in the first and not in the second (`staleClosure_outside_fresh`) |

Open: `FreshRunsExistPure` at argument types outside `Ind`, such as `Imm @a (Mut @b (1 ⊸ 1))`,
with the arguments in the relation at every run.  The step that does not go through is
`gDenXR_indep`'s at the `Mut` cell's stored predicate (`ptoMutS`'s `ofS Q = P ls₀`), where the
two predicates differ (`vX_lolli_depends`).  Not derived, and no obstruction is verified: the
program cannot call such a function (it reaches the program at `Unk`), but no argument here
uses that.  Arguments that arise from a well-typed program run at the fresh runs are in the
relation at the fresh runs, where `pure_result_every_run_fresh` applies to every argument type.

## Files

| file | contents |
|---|---|
| `Rename.lean`, `Steps.lean`, `Fresh.lean`, `Sim.lean` | the machine: renaming, determinism, fresh runs |
| `Footprint.lean` | the write footprint of a `wpTS` run (`wpTS_footprint`, `_every`, `_fresh`); the exhibited run with its resources (`wpTS_exhibited`) |
| `Frozen.lean` | deep immutability (`frozen_keeps`, `wpTS_frozen`); a resource of `imm` cells is given back whole (`heap_restored`) |
| `Local.lean` | reachability, locality (`fresh_run_local`) |
| `Syntax.lean` | a `DerivesWf` term mentions no location |
| `Read.lean` | the read footprint of every run, and of well-typed programs |
| `Pure.lean` | the fragment; `pure_heap`, `pure_result`, `closed_pure` |
| `Boundary.lean` | `peek`; `readFootprintSyn`, `not_readFootprintSem` |
| `FreshExistence.lean` | `FreshRunsExistSyn`, `FreshRunsExistSem`; `not_freshRunsExistSem` at `peek 0` |
| `Closures.lean` | `not_freshRunsExistSyn` at `(λ_. staleL) ()`; `FreshRunsExistClosed`, `FreshRunsExistPure`; `pure_result_every_run` |
| `FreshRuns.lean` | `freshRunsExistClosed`, `closed_pure_every_run`, `freshRunsExistPureF`, `pure_result_every_run_fresh` |
| `Invariant.lean` | `TermLive`, `LiveSteps`; `staleH`; `not_termLiveSuffices`; `withswapWindow` (recorded) |
| `Stale.lean` | `staleL`: location-free, in the relation, no fresh run; `not_freshRunsExistSemLocFree` |
| `PolicyRuns.lean` | `polStep_det`, `polRun_det`; `closed_policy_adequacy`, `closed_policy_pure`, `pure_policy_heap` |
| `Policy.lean` | `wpTS_alloc_any` (6.141 at every heap-fresh location), `PostAt`; `PolRun`, `leastFree`; `not_semPolicyRuns` at `peek 1` |
| `Independence.lean` | `Ind`, `vX_indep`, `gDenXR_indep`; `freshRunsExistPureInd`, `pure_result_every_run_ind`; `vX_lolli_depends` |
| `Examples.lean` | `negB` (open, `b : Imm 'a (1 ⊕ 1)`) and `negClosed` (closed): negation through a temporary cell, with their instances |
