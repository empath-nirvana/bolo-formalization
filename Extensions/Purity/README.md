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
  unconditional.
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
| `Examples.lean` | `negB` (open, `b : Imm 'a (1 ⊕ 1)`) and `negClosed` (closed): negation through a temporary cell, with their instances |
