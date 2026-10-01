# Same-lifetime views through a pointer

**Question.** Given a borrow `x : Imm @a (Ref T)`, can a program obtain a view of the pointee at
the same lifetime `@a`? This is Rust's `&'a Box<T> → &'a T`. If it can, a stored iterator over a
borrowed linked structure keeps one type, `Imm @a Node`, as it advances.

**Answer.** No. The printed model excludes it, and so does the transcription. The exclusion
comes from the conjunct `ρ ↭ ρ′ ● ρ⁺` of `[TR]` p. 6's `wp`, read through the `imm` clause of
`↭` (`[TR]` p. 5; `[CONF]` Fig. 18b, clause (1)). It holds at every run, at every lifetime, and
for every expression. No frame rule and no typed-world invariant is involved. The printed
statics agree: `withload` gives the pointee only at a fresh `'b ⊏ ⊓Δ`, inside a callback whose
result is `['b] T₂`.

Lean: `Extensions/Views/` (`lake build Views`; `scripts/check-views.sh`). Every declaration
depends only on `propext`, `Classical.choice` and `Quot.sound`. The library under `Paper/` and
`Support/` is unchanged.

## 1. What is printed

**The statics** (`[TR]` p. 3; `[CONF]` Fig. 8, p. 415:10).

```
Δ ⊢ withload : Imm @a T₁ ⊸ (∀'b ⊏ ⊓Δ. Imm̲ 'b T₁ ⊸ ['b] T₂) ⊸ T₂
Imm̲ 'b (Ref T)     ≜ Imm 'b T
Imm̲ 'b (Imm @a T)  ≜ Imm @a T
```

`withload` is the only axiom that reads through an `Imm`. At `T₁ = Ref T` its callback receives
`Imm 'b T`, with `'b` shorter than every lifetime in `Δ`, `@a` included. The callback's result
is `['b] T₂` with `'b` not free in `T₂`. `Δ ⊢ Imm 'b T ⊐ 'b` would need `'b ⊐ 'b`. So the view
cannot leave the callback, and `⊑Imm` (p. 2) only shortens a lifetime, so it cannot be raised
back to `@a`. The prose gives the reason ([CONF] p. 415:9): a standard `load` "could be exploited
to free a nested linear reference twice", so `withload` "provides a new borrow of the nested
linear reference", "reborrowing internal references at the fresh lifetime `'b`". A nested borrow
is the contrast: "in the case of a nested borrow, aliases to the inner borrow `Imm a T` are
allowed to exist anyway", so `Imm̲ 'b (Imm @a T) ≜ Imm @a T` keeps `@a`. The same page derives
`load : Imm a T ⊸ T` for every `T` with `Imm̲ 'b T = T`. That covers `T = Imm @c U`, but no `T`
that contains a `Ref`.

**The model.**

- `𝒱⟦Imm @a T⟧δ(v) ≜ ∃ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦ Imm @aδ 𝒱⟦T⟧δ` and `𝒱⟦Ref T⟧δ(v) ≜ ∃ℓ,v′. ⌜v = ℓ⌝ ⋆
  ℓ ↦ v′ ⋆ 𝒱⟦T⟧δ(v′)` (`[TR]` p. 4). The witness of an `Imm @a (Ref T)` cell therefore holds
  `ℓ₁ ↦ own(v′)` for the pointee `ℓ₁`.
- `⦇ρ⦈ ≜ ex(ρ)_● ● ag(ρ)` (`[TR]` p. 5). `ag` walks an `imm` witness through `ex(ρ′)_○ ○ ag(ρ′)`,
  so `⦇ℓ ↦ imm(ᾱ, ℓ₁, ℓ₁ ↦ own(v′))⦈(ℓ₁) = own(v′)`.
- `ρ₁ ↭ ρ₂`, clause (1) ([CONF] Fig. 18b): `⦇ρ₁⦈(ℓ) = imm(ᾱ, v, ρ) ⇔ ⦇ρ₂⦈(ℓ) = imm(ᾱ, v, ρ)`.
  Below the figure: "requires that all reachable immutable borrows are preserved with their value
  `v` witness `ρ` exactly as is".
- `wp(e){Q̂}(ρ) ≜ ∀ρ_f # ρ. ∃ρ′ # ρ_f, ρ⁺ # (ρ_f ● ρ′), v. … ∧ ρ ↭ ρ′ ● ρ⁺ ∧ ρ⁺|own = ∅ ∧
  Q̂(v)(ρ′)` (`[TR]` p. 6).

**The frame rules.** 6.64 (Imm Frame, p. 22) runs its body from `ρ_b ● ρᵢ`, where
`ρᵢ = ℓ ↦ imm({α}, v, ρ_P̂(v))`, and carries H21, `ρ_b ● ρᵢ ↭ ρ′ ● ρ⁺`. Its H28 is 6.38
(p. 12): under H1–H6, `ρ′ ● ρ⁺/ℓ # ρ_v ● ℓ ↦ own(v)`, so at a frame's end no cell of `ρ′ ● ρ⁺`
lies where the escrow `ρ_v` holds an `own` cell. 6.65 (Mut Frame, p. 24) has the same shape:
its body runs from `ρ_b ● ρ_m`, and it carries H21 `↭` and H27 via 6.24. 6.66 (Anti Frame,
p. 25) re-establishes `ℓ ↦ Mut α P̂` around a run.

**What the printed rules say.** A view is an `imm` cell in the post-resource `ρ′`. By clause
(1) of `↭`, read right to left, that cell is already an `imm` cell of `⦇ρ⦈`, with the same
value and witness, where `ρ` is the resource the run started at. A run can therefore return a
view only if the view existed before the run. At `Imm @a (Ref T)`, the pointee is `own` in
`⦇ρ⦈`, so no run returns a view of it. At `Imm @a (Imm @c U)`, the inner borrow is already
`imm` in `⦇ρ⦈`, so returning it is not excluded. The two clauses of `Imm̲` match this. Views are
made only inside a scope that ends before the enclosing run's `↭` is checked: 6.64's `ρᵢ` and
6.150's `↺_α` image, which 6.52 removes before 6.59's final `↭`.

## 2. What the transcription does

| Printed object | Lean | Tag | Bearing on the argument |
|---|---|---|---|
| `wp`, row 5.33 | `Fig16.BoLo.wp` | `[repair]`, which concerns only `→*` (§12.42, D6) | The argument does not use the run |
| `↭`, row 5.27 | `Fig16.ResU.UpdV`, `UpdImm` | `[repair]` §12.39 | [TR] p. 5 prints the right-hand side of clause (1) as a three-argument `mut(β̄, v, ρ)`. It is read as `imm`, which [CONF] Fig. 18b prints. The `⇔` is printed in both documents |
| `↭`'s guard | `UpdV` / `Upd` | D3 | Inside `wp` the two are the same proposition (`wp_eq_wpU`) |
| `⦇ρ⦈`, rows 5.20–5.22 | `ExS`, `AgW`, `ResU.Flat` | `[repair]` §12.36, G6 | The comprehensions are read as families indexed by locations. No clause changes |
| `⋈`, row 5.14 | `CellU.CompatR` | `[repair]` §12.35 | Read as the domain of `○`. Clause (5), `imm ○ own = imm`, is as printed |
| `ℓ ↦ Imm α P̂`, row 5.30 | `Fig16.BoLo.ptoImm` | `[variant]` §12.67(a), `⊓β̄` for `⊔β̄` | The argument reads no lifetime, so it is the same at either bound |
| `Imm̲`, row 2.49 | `Ty.immReborrow` | `[as printed]` | Clauses (5) and (6) are `immReborrow_ref` and `immReborrow_imm` (`rfl`) |
| 6.34, 6.38, 6.64 | `ResU.six34`, `ResU.six38`, `wp_I_frameX` | proved | Used as printed |

No entry in `docs/adjudications.md` changes `↭`, `ag`, 6.38, the frame rules or `reb_α` in a way
that this argument depends on. §12.67(b), the subset reading of `reb_α`'s `imm` clause, affects
only the images that 6.150 makes. Those images live inside a scope and are never returned.
`[TR]` 6.40 is the one untranscribed row in §6.2. Nothing here uses it, and the frame rules do
not cite it.

## 3. Verdict: (a), the exclusion is printed

The rule that forces it is the right-to-left direction of `↭`'s `imm` clause ([CONF] Fig. 18b
(1); [TR] p. 5 read under §12.39), applied in `[TR]` p. 6's `wp` conjunct `ρ ↭ ρ′ ● ρ⁺`. That
`⦇·⦈` of an `Imm @a (Ref T)` cell holds the pointee as `own` follows from 4.7, 4.8 and `ag`'s
third factor. `[TR]` 6.38 gives the same conclusion at a 6.64 frame. Each claim below is
machine-checked, with every hypothesis discharged.

`Extensions/Views/Pointee.lean`, at the literal printed definitions:

- `upd_imm_of_top`: if `ρ ↭ π` and `π(m)` is `imm`, then `⦇ρ⦈(m)` is `imm` with the same value
  and witness.
- `wp_view_preexists`: `wp e {Q̂}` at a valid `ρ` has a run whose `ρ′` satisfies `Q̂`, and every
  top-level `imm` cell of that `ρ′` is such a cell of `⦇ρ⦈`.
- `ptrBorrow_vDen`, `ptrBorrow_valid`: `ℓ ↦ imm({α}, ℓ₁, ℓ₁ ↦ own(()))` is a valid member of
  `𝒱⟦Imm @a (Ref 1)⟧δ(ℓ)` (validity via 6.34).
- `no_view_of_pointee`: for every `e`, every `@b` and every `δ′`,
  `¬ wp e {𝒱⟦Imm @b 1⟧δ′}` at that resource. `@b = @a` is included, and so is any shorter
  lifetime.
- `no_closed_projection`: `𝒱⟦Imm @a (Ref 1) ⊸ Imm @b 1⟧δ` has no member at `∅`.
- `frame_view_excluded`, `ptrBorrow_frame_excluded`: 6.38 at a frame whose borrow is the whole
  resource. A borrow `ℓ ↦ imm({α}, v, ρv)` updates to no own-free resource with a cell where
  `ρv` holds `own`.
- `mut_view_excluded`: the `mut` clause excludes a new `mut` cell at a location the witness of
  a `mut` borrow owns, at every lifetime and predicate. This is the `Mut` analogue (`Mut @a
  (Ref T) → Mut @a T`), and it excludes the two-way split as well.

`Extensions/Views/Typed.lean`, at the typed world (§12.72):

- `Typed.no_projection`: no `proj` meets the specification "from `vP (Imm 'x (Ref 1 ⊗ Ref 1))`
  at `ℓ`, `wpTS (proj ℓ)` returns `vP (Imm 'x 1)` at the pair's first component". The
  configuration is built from `TW.empty`: three `wpTS_alloc` runs, then `TW.immFrame` (6.64's
  entry). The last step is `frame_view_excluded`.

**Why a frame-exit change cannot lift it.** `no_view_of_pointee` mentions no frame, no typed
world and no 6.38. It is refuted at the run that would return the view, through `wp`'s own `↭`
conjunct. A change to 6.64's exit, such as subtracting the frame's image at its own lifetime, is
reached only after that run has ended. So it leaves the refutation as it is. The repaired relation
(`SemX`/`wpTS`) keeps the conjunct verbatim and restricts only the frames `ρ_f`, so it excludes
the view too (`Typed.no_projection`). To admit the view, `wp`'s `↭` conjunct itself would have to
change, at every run. That is a different logic. Bind (6.49), 6.38/6.39 in the frame rules and
6.59 in the reborrow rule all consume the conjunct. No printed reading gives such a relation, and
none is proposed here.

## 4. Practical consequence

The obstruction is a property of `wp` and holds at every type. So it carries over to any
extension (records, `μ`) that keeps `[TR]` p. 6's `wp`.

- **A stored iterator over a borrowed, `Ref`-linked list**, whose state is a view of the rest at
  `@a`: not typable, and semantically uninhabited. Each step through an owned link is a
  `withload` at a fresh `'b` that is strictly shorter than the last. A view at `'b` lives only
  inside its callback, so the iterator's state has no fixed type across steps. Inside one
  callback, a view at `'b` can be used and stored at `'b` for that callback's extent.
- **`fold_imm` returning views of nodes reached through owned links**: excluded in the same way.
  The callback's result `['b] T₂` cannot mention `'b`, and `no_view_of_pointee` excludes every
  semantic substitute.
- **What is admitted.** A structure whose links are themselves borrows keeps its lifetime at
  each step. With `Imm̲ 'b (Imm @a T) ≜ Imm @a T` and [CONF] p. 415:9's derived `load`, a list
  whose tail field has type `Imm @a Node` can be traversed at the fixed type `Imm @a Node`, and
  those inner borrows can be returned at `@a`. The cost is that such a spine must be built out
  of borrows, by borrowing each node separately. It cannot be read off an owned `Ref`-linked
  list, because that reading is exactly the excluded view.
