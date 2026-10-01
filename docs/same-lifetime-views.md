# Same-lifetime views through a pointer

**Question.** Given a borrow `x : Imm @a (Ref T)`, can a program obtain a view of the pointee at
the same lifetime `@a`? This is Rust's `&'a Box<T> → &'a T`. If it can, a stored iterator over a
borrowed linked structure keeps one type, `Imm @a Node`, as it advances.

**Answer.** The printed rules make no such view, and a conservative extension does. `[TR]`'s
proof rules create an `imm` cell in two places only: 6.64 (Imm Frame) makes the one cell
`ℓ ↦ imm({α}, v, ρ_P̂(v))`, and 6.150 (`↺` rule) makes views of a borrow's payload at a *fresh*
`β`, shorter than everything around it. No run creates an `imm` cell (`↭`'s clause (1)). So the
only read through an `Imm`, `withload`, gives the pointee at a fresh `'b`, and each step down a
borrowed list is a new, shorter lifetime. The extension changes *when* views are made, not what
a run may do. At the frame where the program owns `ℓ ↦ v ⋆ 𝒱⟦T⟧δ(v)`, it makes 6.64's cell and,
at the same `α`, a view of every location `v` reaches through owned pointers. This is RustBelt's
sharing predicate for `Box`. `[TR]` p. 6's `wp` and p. 5's `↭` are unchanged, and every printed
rule still holds as it is. With the views in place, `deref ≜ λx. load x` has type
`Shr α (Ref T) ⊸ Shr α T`, and iterating it keeps `α`.

Lean: `Extensions/Views/` (`lake build Views`; `scripts/check-views.sh`). Every declaration
depends only on `propext`, `Classical.choice` and `Quot.sound` (138 declarations). The library
under `Paper/` and `Support/` is unchanged.

## 1. The printed rules (first pass, still in force)

`Extensions/Views/Pointee.lean` and `Extensions/Views/Typed.lean` are statements about the
printed rules, and they stand.

- `upd_imm_of_top`, `wp_view_preexists`: a run returns no top-level `imm` cell that `⦇ρ⦈` lacked
  (`↭`'s clause (1), right to left; `[CONF]` Fig. 18b; `[TR]` p. 5 read under §12.39). These
  quantify over every valid `ρ`. They are positive facts about `[TR]` p. 6's `wp`, so they hold
  at arising resources too.
- `no_view_of_pointee`, `no_closed_projection`: from `ptrBorrow α ℓ ℓ₁ =
  ℓ ↦ imm({α}, ℓ₁, ℓ₁ ↦ own(()))`, no expression returns `𝒱⟦Imm @b 1⟧`. That resource is the one
  6.64 makes from `ℓ ↦ own(ℓ₁) ● ℓ₁ ↦ own(())`. `Typed.no_projection` builds it as a typed world
  (`TW.empty`, three allocations, `TW.immFrame`), so it arises.
- `frame_view_excluded` (6.38 at a frame) and `mut_view_excluded` (`↭`'s `mut` clause) quantify
  over every valid resource. `mut_view_excluded`'s cell `ℓ ↦ mut(b, v, ρ_w, P̂)` is the one 6.65
  makes, so it arises.

What these establish is narrower than the first pass stated. A view the start of a run lacks
cannot appear during the run. They say nothing about a view made at the frame, before the run
starts. The first pass's §3 ("Why a frame-exit change cannot lift it") is right about the exit.
The extension changes the frame's entry instead.

## 2. The extension

**The shared borrow** (`Extensions/Views/Shared.lean`).

```
shrV α (Ref T) δ v ≜ ∃ℓ u. ⌜v = ℓ⌝ ⋆ ℓ ↦ Imm α (u′. ⌜u′ = u⌝ ∧ 𝒱⟦T⟧δ(u′)) ⋆ shrV α T δ u
shrV α (T₁ ⊗ T₂) δ v, shrV α (T₁ ⊕ T₂) δ v, shrV α ([@a] T) δ v   componentwise
shrV α 1 δ v ≜ ⌜v = ()⌝,   shrV α T δ v ≜ emp   at ⊸, ∀, Imm, Mut, Unk
shrDen α T δ ≜ shrV α (Ref T) δ
```

`shrDen α T δ (ℓ)` is `[TR]` p. 4's `ℓ ↦ Imm α 𝒱⟦T⟧δ` (pinned to the stored value) together with a
view at `α` of each pointee, and each view's witness is the pointee's own payload. `shrV α T δ`
is the shared reading of `Imm̲ 'a T` (`[TR]` p. 3): `Ref T ↦ Imm 'a T`, componentwise through
`⊗`, `⊕`, `[@a]`, and nothing at `⊸`/`∀`.

**Minting** (`Extensions/Views/Mint.lean`). `Mint α O Y` says three things. Every cell of `Y` is
`imm({α}, u, w)` and sits on an `own(u)` cell of `ex(O)`. `ag(Y) = Y ○ ex(O)_○ ○ ag(O)`. And `ag(Y)`
is defined. 6.64's cell is a mint over `ρ_v ● ℓ ↦ own(v)` (`mint_single`). Adding the view of an
`own` cell of `ex(O)`, whose witness is a sub-resource of `O`, keeps a mint (`Mint.add`).
`mint_views` and `mint_shr_of` build `shrDen`'s resource that way, by induction on the type.

**The frame rule** (`Extensions/Views/Frame.lean`). `wp_mint_frame` is 6.64 with a mint in place
of the one cell. Its proof follows `Fig16.LogRel.wp_I_frame` step for step. The four facts that
proof spends about its cell are proved at a mint:

| 6.64's step | at one cell (library) | at a mint |
|---|---|---|
| H13, H15 (6.34) | `ResU.six34` | `Mint.hash` |
| H34 (6.26 with 6.8) | `ResU.lower_swap_imm_own` | `Mint.lower_iff` |
| H26 (6.29) | `ResU.six29` | `Mint.top` |
| H28 (6.38) | `ResU.six38` | `Mint.post_hash` |
| H35 (6.39) | `ResU.six39` | `Mint.upd` |

`Mint.flat` is the normal form behind 6.34, 6.26 and 6.39: `⦇Z ● Y⦈` is `⦇Z ● O⦈` with `Y`'s cells
in place of the `own` cells beneath them. `Mint.post_hash` keeps 6.38's ancestor step. A
location of `ex(O)` in the aliasable walk of the post-resource sits beneath an `imm` cell
(`AgW.nonimm_beneath_imm`). `↭` carries that cell back to `⦇Z ● O⦈`, where its walk avoids
`ex(O)` (`AgW.flat_imm_wit_le`). `wp_I_frame_of_mint` recovers `[TR]` 6.64 as printed, as the
one-cell instance.

**The rules** (`Shared.lean`, `Uses.lean`):

- `wp_S_frame`: `ℓ ↦ v ⋆ 𝒱⟦T⟧δ(v) ⋆ (Иα. Shr α T(ℓ) ─⋆ wp(e){[α](ℓ ↦ v ⋆ 𝒱⟦T⟧δ(v) ─⋆ Q̂)}) ⊨ wp(e){Q̂}`.
- `wp_load_S`: `load ℓ` from `Shr α T(ℓ)` returns the stored value with `shrV α T δ`, at `α`.
- `deref_sem`, `deref_closed`: `deref ≜ λx. load x` takes `Shr α (Ref T)` to `Shr α T`. At `∅` it
  satisfies `∀w. Shr α (Ref T)(w) ─⋆ ℰ⟦Shr α T⟧(deref w)`, `𝒱⟦−⊸−⟧`'s clause with `shrDen` at both ends.
- `derefN_sem`: `n` successive `deref`s take `Shr α (Refⁿ S)` to `Shr α S`, at one `α`.
- `shrV_copy` (copy), `wp_S_forget` (forget), `shrV_mono` (`⊑Imm`), and `shrDen_head`: the head is
  `𝒱⟦Imm @a T⟧δ` and the rest is own-free.
- `minted_projection`: at `ℓ ↦ own(ℓ₁) ● ℓ₁ ↦ own(())`, the shared borrow is the first pass's
  `ptrBorrow α ℓ ℓ₁` plus one own-free cell at `ℓ₁`. From it, `deref ℓ` returns
  `𝒱⟦Imm @a 1⟧δ`. `no_view_of_pointee` says no expression does that from `ptrBorrow α ℓ ℓ₁` alone.

## 3. Why it is sound

`wp` and `↭` are `[TR]` p. 6's and p. 5's, so every rule proved about them holds unchanged. That
includes bind (6.135), the update lemmas (6.47–6.50), the frame rules (6.64–6.66), the reborrow
rule and its surgery (6.150, 6.52–6.59), and adequacy. The extension adds no relation. Its new
obligations are the five facts in the table above, and they are proved. No hypothesis restricts
the frames: the frame rule holds at every `ρ_f # ρ`. The views are made from resources the frame
owns, so no frame can hold a cell at their locations (`Mint.hash`).

**The frozen fact.** What a shared borrow needs to stay valid is that the pointees are frozen
while `α` lives. That follows from the printed `↭` at every valid resource, arising or not.
`frozen_under_imm` shows that if `ρ ↭ π` and `⦇ρ⦈` has an `imm` cell over `w`, every cell of
`⦇w⦈_○` is in `⦇π⦈` with its value. The proof is `↭`'s clause (1) with 6.48's ancestor
accounting (`ResU.flat_imm_wit_factor`). This is RustBelt's persistence of a sharing predicate.
No new invariant is introduced.

**Coherence with printed views.** Each minted view's witness is the owning payload's sub-resource,
the witness 6.150's `own` clause gives that location (`ResU.RebAt`). So minted views agree with
the views a later 6.150 makes there ([CONF] 415:19: *"immutable cells ψ₁, ψ₂ at the same location
must all have the same witness"*). The alternative, a view with an empty witness (a finer
partition), would disagree with them, as §12.68's configuration does. Not machine-checked here:
`withload` (`wp_reborrow`, `RebEscrow`) applied to a shared borrow's head inside the frame.

## 4. The typed world

`Fig16.LogRel.fundamentalProperty` is proved at the typed world (`Fig16.LogRel.Typed.TW`,
§12.72), the family of resources the printed operations produce. The share frame is not one of
those operations. `minted_not_nestLife` (`Extensions/Views/Nest.lean`) builds the share frame's
resource for `2 ↦ own(1) ● 1 ↦ own(0) ● 0 ↦ own(())` and shows it fails
`Fig16.LogRel.Typed.NestLife` at the frame's record. The view at `0` is not shorter than the view
at `1`, because both are at `α`. So `minted_not_TW`: no `TW` world holding that record is this
resource.

`NestLife` records that every view below an existing view comes from 6.150 at a fresh, shorter
`β`. `FrameLife`'s second clause records the same of a frame's lineage, and `TW.reb`/`TW.rebDeep`
take `β` below the whole world. Bringing the share frame into the typed world means three
changes in place, with no new predicate:

1. relax `NestLife` and `FrameLife`'s second clause from `⊏` to `⊑`;
2. add the share frame's entry and exit to `TW`, with `TW.inv`, `TW.valid` and `TW.linLife` cases;
3. prove the frame at `wpTS`.

The minted views appear to have the shape `DeepInv`, `JointAt` and `JointDeep` ask of views at
chain positions: each view's witness is the pointee's payload, and the views at one level form
one reborrow image of the level above, at `β₀ = α`. This is not machine-checked.

This was not done here. It changes `Support/TypedWorld/`, the world family 6.151 rests on
(§12.72). A `Support/` change was refused by this session's permissions, so the decision is the
user's. It would also not, by itself, extend the syntactic Fundamental Property. A program that
uses a shared borrow needs a type for it, either a new type former or a deep reading of `Imm`.
That changes `[TR]` p. 1's `Ty` or p. 4's `𝒱⟦Imm⟧`, which is a design decision.

Read informally, the relaxation looks cheap. The strict `NestLife` is consumed once, in
`ti_endReb`, to show that no child view outlives the end of its parent's reborrow. That argument
still closes with `⊑`, because the remaining world is in `Res_β`. The other places that mention
it (`ti_frame`, `nm_reb_like`, `ti_end`) establish it, and a strict bound implies the weak one.
`FrameLife`'s second clause is consumed in `not_rel_lineage` and `witLB_of`, and each needs only
`⊑`. `frameLife_reb_like` establishes it. This is not machine-checked.

## 5. The `Mut` analogue

With `[TR]` p. 4's `Mut`, a closed `Mut @a (Ref T) ⊸ Mut @a T` would have to put a `mut` cell at a
location the witness of the borrow's `mut` cell owns. `↭`'s `mut` clause excludes that
(`mut_view_excluded`, at 6.65's cell, which arises). The route that works for `Imm` is to make
the pointee's borrow at the frame, while the pointer cell stays frozen for `α`. That needs more
than the `Imm` case:

- the frozen pointer cell is an `imm` cell whose witness is not the full payload, so it is not a
  mint;
- the pointee's `mut` cell must be folded back at the exit, which is 6.65's half, not 6.64's;
- a cell holding a pair with a pointer field (a list node) cannot be split into a frozen part and
  a `mut` part. The `mut` predicate would have to pin the pointer component.

None of this is built here. With `[TR]`'s rules as they are, `Mut` through `Ref` stays at a
fresh lifetime per step: `withbor` on the pointee, with `withswap` to reach it.

## 6. Practical consequence

- **A stored iterator over an owned, `Ref`-linked list.** Share the list once
  (`wp_S_frame`). The iterator's state is `Shr α Node`, and each step is `deref` (or `wp_load_S`
  and a field projection), which returns `Shr α Next` at the same `α` (`derefN_sem`). The state
  can be copied (`shrV_copy`), stored and returned within `α`'s frame. The calculus has no
  recursive types, so `derefN_sem` is stated for `Refⁿ S`. Every lemma is generic in the type,
  so it applies to each unrolling.
- **`fold_imm` returning views of nodes.** Within one share frame, a fold can return
  `Shr α Node` values at the frame's `α`. Under `[TR]`'s `withload`, each level is a callback at
  a fresh `'b`, and nothing at `'b` leaves it.
- **Mixing with printed code.** The head of a shared borrow is a `[TR]` `Imm`
  (`shrDen_head`), and the views can be forgotten (`wp_S_forget`). So printed rules about `Imm`
  apply to it. The FP-level account of programs that type shared borrows is the open step of §4.
- **Mutable iteration** (`IterMut`) is §5's open design.

## 7. Lean index

| File | Contents |
|---|---|
| `Pointee.lean` | first pass: the printed `↭` and `wp` make no same-lifetime view |
| `Typed.lean` | first pass: the same at the typed world |
| `Mint.lean` | `Mint`; `Mint.flat`, `.hash`, `.lower_iff`, `.upd`, `.post_flat`, `.top`, `.post_hash`; `mint_single`, `Mint.add`; `frozen_under_imm` |
| `Frame.lean` | `wp_mint_frame` |
| `Shared.lean` | `shrV`, `shrDen`, `mint_views`, `mint_shr_of`, `mint_shr`, `wp_S_frame`, `wp_load_S`, `derefV`, `deref_sem`, `deref_closed`, `shrV_noOwn`, `wp_S_forget`, `shrV_mono`, `shrDen_head` |
| `Uses.lean` | `wp_I_frame_of_mint`, `shrV_copy`, `refN`, `derefN`, `derefN_sem`, `minted_projection` |
| `Nest.lean` | `minted_not_nestLife`, `minted_not_TW` |
