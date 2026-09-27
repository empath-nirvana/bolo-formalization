import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S3_Dynamics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S5_Model.Definitions
import Support.Dynamics.Machine
import Support.Dynamics.Fresh
import Support.Dynamics.Policy
import Support.Lifetimes.Interpretation
import Support.LogicalRelation.ClosingSubstitutions
import Support.Model.Notation
import Support.TypedWorld.Records

/-!
# Support — TypedWorld — World

`[about ours]`.  The typed worlds: value shapes `vShape`, the family `TW` of configurations the printed proofs' operations produce, tagging, and `[TR]` p. 6's `wp` over them (`wpTS`, row 5.33's repair).
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `𝒱⟦T⟧`'s shape: `vDen` with the `⊸` and `∀` clauses dropped (no `wp`, so no world
family), and the `Mut` clause asking the stored predicate to be *contained in* the shape
rather than equal to it.  A record or a `TW` premise at `vShape` mentions no `TW`.
`[about ours: our wp-free payload predicate]` -/
def vShape : Ty → LSub → Val → WProp
  | .unit, _, v => ⌜v = .unit⌝
  | .tensor T₁ T₂, δ, v =>
      ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆ vShape T₁ δ v₁ ⋆ vShape T₂ δ v₂
  | .sum T₁ T₂, δ, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vShape T₁ δ v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vShape T₂ δ v₂)
  | .lolli _ _, _, _ => fun _ => True
  | .all _ _ _, _, _ => fun _ => True
  | .box a T, δ, v => atLife δ a fun α => box α (vShape T δ v)
  | .ref T, δ, v => ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vShape T δ v'
  | .imm a T, δ, v => atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆ ptoImm ℓ α (vShape T δ)
  | .mut a T, δ, v => atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
      fun ρ => ∃ P, ptoMut ℓ α P ρ ∧ ∀ u σ, P u σ → vShape T δ u σ
  | .unk, _, _ => emp

/-!
Row 5.33 · `wp (e) {Q̂} (ρ) ≜ ∀ρ_f # ρ. ∃ρ′ # ρ_f, ρ⁺ # (ρ_f ● ρ′), v. (⟦ρ_f ● ρ⟧,e) →* (⟦ρ_f ● ρ′ ● ρ⁺⟧,v) ∧ ρ ↭ ρ′ ● ρ⁺ ∧ ρ⁺∣own = ∅ ∧ Q̂(v)(ρ′)` · `[repair]`; the printed row is in `Paper/S5_Model/Definitions.lean`.
-/
/-- The typed world.  `TW W ps rs`: the configuration `W` — every frame together with the
resource a `wp` runs at, `[TR]` p. 6's `ρ_f ● ρ` — is reached from `∅` by the operations the
printed proofs perform, and `ps` are the frames `[TR]` 6.64 has taken and not ended, `rs` those
frames with every sub-record of their lineages.  One constructor per operation: `alloc`
(6.141), `free` (6.142), `store` (6.145), `immFrame`/`immEnd` (6.64's entry and exit, recording
the frame and its lineage and dropping them), `mutFold`/`mutUnfold` (6.65 and 6.66), and
`reb`/`rebDeep` with `rebEnd`/`rebEndDeep` (6.150's entry and exit, at a record's cell or at a
chain view of one, at any record, a sub-record included).  `reb`'s `β` is below every lifetime
of the world, as 6.150's H11 takes it.  The typing premises are at `vShape`, `𝒱⟦T⟧`'s wp-free
shape: a premise at the program's relation would put `TW` under the negative occurrence of
`wpTS` in that relation's `⊸` clause.
`[about ours: the configurations §6 quantifies over, as a family; docs/adjudications.md §12.72]` -/
inductive TW : WRes → List FrameRec → List FrameRec → Prop
  | empty : TW PMap.empty [] []
  | alloc {W W' : WRes} {ps rs : List FrameRec} {μ : BoCa.BoLo.Heap} {l : Loc} {v : Val} :
      TW W ps rs → ResU.Lower W μ → μ l = none →
      ResU.CompS W (ResU.single l (CellU.ownOf v)) W' → ResU.Valid W' → TW W' ps rs
  | immFrame {W X Z R W' : WRes} {ps rs ds : List FrameRec} {l : Loc} {v : Val} {α : Life}
      (T : Ty) (δ : LSub) (h : R.InStratum (LSet.singleton α).join) :
      TW W ps rs → AdmWf T δ → ResU.CompS (ResU.single l (CellU.ownOf v)) R X →
      ResU.CompS X Z W → vShape T δ v R →
      ResU.CompS (ResU.single l (CellU.immOf (LSet.singleton α) v R h)) Z W' →
      ResU.Valid W' → (∀ d, d ∈ ds ↔ Desc ⟨l, v, R, T, δ⟩ d) →
      TW W' (⟨l, v, R, T, δ⟩ :: ps) (⟨l, v, R, T, δ⟩ :: (ds ++ rs))
  | reb {W W' c : WRes} {ps rs : List FrameRec} (r : FrameRec) {le : Loc} {s : LSet}
      {β : Life} {hs : r.R.InStratum s.join} (x : LifeVar) :
      TW W ps rs → r ∈ rs → W.get le = some (CellU.immOf s r.v r.R hs) →
      ¬ LFree x r.T → ResU.Reb β r.R c →
      vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v c →
      W.InStratum β → ResU.CompS W c W' → ResU.Valid W' → TW W' ps rs
  | rebDeep {W W' c : WRes} {ps rs : List FrameRec} (r : FrameRec) {p : Option Loc} {l₀ : Loc}
      {S₀ : Ty} {u₀ : Val} {s : LSet} {w₀ : WRes} {hs : w₀.InStratum s.join} {β : Life}
      (x : LifeVar) :
      TW W ps rs → r ∈ rs → Chain r.R r.T r.v p l₀ S₀ u₀ →
      W.get l₀ = some (CellU.immOf s u₀ w₀ hs) → ¬ LFree x S₀ → ResU.Reb β w₀ c →
      vShape (S₀.immReborrow (.var x)) (r.δ.extend x β) u₀ c →
      W.InStratum β → ResU.CompS W c W' → ResU.Valid W' → TW W' ps rs
  | mutFold {W X Z ρ W' : WRes} {ps rs : List FrameRec} {l : Loc} {v : Val} {b : Life}
      {hstr : ρ.InStratum b} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρ, hstr⟩} :
      TW W ps rs → ResU.CompS (ResU.single l (CellU.ownOf v)) ρ X → ResU.CompS X Z W →
      ResU.CompS (ResU.single l (CellU.mutOf b v ρ hstr P hw)) Z W' → ResU.Valid W' →
      TW W' ps rs
  | mutUnfold {W X Z ρ W' : WRes} {ps rs : List FrameRec} {l : Loc} {v : Val} {b : Life}
      {hstr : ρ.InStratum b} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρ, hstr⟩} :
      TW W ps rs → ResU.CompS (ResU.single l (CellU.mutOf b v ρ hstr P hw)) Z W →
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρ X → ResU.CompS X Z W' → ResU.Valid W' →
      TW W' ps rs
  | free {W W' : WRes} {ps rs : List FrameRec} {l : Loc} {v : Val} :
      TW W ps rs → ResU.CompS (ResU.single l (CellU.ownOf v)) W' W → ResU.Valid W' →
      TW W' ps rs
  | store {W Z W' : WRes} {ps rs : List FrameRec} {l : Loc} {v₁ v₂ : Val} :
      TW W ps rs → ResU.CompS (ResU.single l (CellU.ownOf v₁)) Z W →
      ResU.CompS (ResU.single l (CellU.ownOf v₂)) Z W' → ResU.Valid W' → TW W' ps rs
  | immEnd {W Y X' W' : WRes} {ps rs ps' rs' : List FrameRec} (r : FrameRec) {s : LSet}
      {hs : r.R.InStratum s.join} :
      TW W ps rs → r ∈ ps → ResU.CompS (ResU.single r.le (CellU.immOf s r.v r.R hs)) Y W →
      ResU.CompS (ResU.single r.le (CellU.ownOf r.v)) r.R X' → ResU.CompS X' Y W' →
      ResU.Valid W' → (∀ r', r' ∈ ps' ↔ (r' ∈ ps ∧ r' ≠ r)) →
      (∀ d, d ∈ rs' ↔ ∃ p ∈ ps', DescR p d) → TW W' ps' rs'
  | rebEnd {W W' c : WRes} {ps rs : List FrameRec} (r : FrameRec) {le : Loc} {s : LSet}
      {β : Life} {hs : r.R.InStratum s.join} :
      TW W ps rs → r ∈ rs → W'.get le = some (CellU.immOf s r.v r.R hs) →
      ResU.Reb β r.R c → ResU.CompS W' (c.restrictDom r.R.exclPart) W →
      W'.InStratum β → TW W' ps rs
  | rebEndDeep {W W' c : WRes} {ps rs : List FrameRec} (r : FrameRec) {p : Option Loc}
      {l₀ : Loc} {S₀ : Ty} {u₀ : Val} {s : LSet} {w₀ : WRes} {hs : w₀.InStratum s.join}
      {β : Life} :
      TW W ps rs → r ∈ rs → Chain r.R r.T r.v p l₀ S₀ u₀ →
      W'.get l₀ = some (CellU.immOf s u₀ w₀ hs) → ResU.Reb β w₀ c →
      ResU.CompS W' (c.restrictDom w₀.exclPart) W → W'.InStratum β → TW W' ps rs

/-- A tagged list agrees with the world: each record's tag is the frame lifetime of a
record proper whose lineage holds it.  `[about ours: our tag discipline]` -/
def Tagged (W : WRes) (ps : List FrameRec) (ls : List SRec) : Prop :=
  ∀ x ∈ ls, ∃ p ∈ ps, DescR p x.1 ∧ FrameLife W p x.2

/-- A class of runs `wp` may exhibit, indexed by `I`: closed under the operations `wp`'s rules
build runs with.  Plugging a run into an evaluation context `K` may change the index
(`shift K`).  `stepsRel` is every run, `[TR]` p. 6's `(⟦ρ_f ● ρ⟧, e) →* (…, v)`; `polRel pol` is
the runs under an allocation policy; `freshRel` the runs avoiding a finite list of locations and
every location the configuration names.  `[about ours: docs/adjudications.md §12.74]` -/
structure RunRel where
  I : Type
  R : I → Heap → Expr → Heap → Expr → Prop
  refl : ∀ (i : I) (μ : Heap) (e : Expr), R i μ e μ e
  cons : ∀ {i : I} {μ μ₁ μ' : Heap} {e e₁ e' : Expr}, Step1 μ e μ₁ e₁ →
    (∀ ℓ, μ₁ ℓ ≠ none → μ ℓ ≠ none) → R i μ₁ e₁ μ' e' → R i μ e μ' e'
  alloc : ∀ (i : I) (μ : Heap) (v : Val), Fig16.FinDom μ →
    ∃ l, μ l = none ∧ R i μ (.app (.val (.prim .alloc)) (.val v)) (μ.upd l v) (.val (.loc l))
  shift : Kont → I → I
  plug : ∀ (K : Kont) {i : I} {μ μ' : Heap} {e e' : Expr}, R (shift K i) μ e μ' e' →
    R i μ (K.plug e) μ' (K.plug e')
  trans : ∀ {i : I} {μ μ₁ μ' : Heap} {e e₁ e' : Expr}, R i μ e μ₁ e₁ → R i μ₁ e₁ μ' e' →
    R i μ e μ' e'
  toSteps : ∀ {i : I} {μ μ' : Heap} {e e' : Expr}, R i μ e μ' e' → Steps μ e μ' e'

/-- A finite memory misses a location. -/
theorem exists_fresh_loc {μ : Heap} (h : Fig16.FinDom μ) : ∃ l, μ l = none := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d.sum + 1, ?_⟩
  by_contra hne
  exact Nat.not_succ_le_self _ (List.le_sum_of_mem (hd _ hne))

/-- Every run: `[TR]` p. 6's `→*`. -/
def stepsRel : RunRel where
  I := Unit
  R := fun _ => Steps
  refl := fun _ μ e => .refl μ e
  cons := fun h _ t => .more h t
  alloc := fun _ μ v hfin => by
    obtain ⟨l, hl⟩ := exists_fresh_loc hfin
    exact ⟨l, hl, .one (Step1.head (Head.alloc μ v l hl))⟩
  shift := fun _ i => i
  plug := fun K _ _ _ _ _ h => h.plug K
  trans := fun h₁ h₂ => h₁.trans h₂
  toSteps := fun h => h

/-- The runs under the allocation policy `pol`. -/
def polRel (pol : BoLo.Policy) : RunRel where
  I := Unit
  R := fun _ => BoLo.PolRun pol
  refl := fun _ μ e => .refl μ e
  cons := fun h hdom t => BoLo.PolRun.cons h hdom t
  alloc := fun _ μ v hfin => ⟨pol.pick μ, pol.fresh μ hfin, BoLo.PolRun.alloc pol μ v hfin⟩
  shift := fun _ i => i
  plug := fun K _ _ _ _ _ h => BoLo.PolRun.plug K h
  trans := fun h₁ h₂ => BoLo.PolRun.trans h₁ h₂
  toSteps := fun h => h.toSteps

/-- The fresh runs avoiding a finite list `N` of locations.  Plugged into `K`, a run must also
avoid the locations of `K`. -/
def freshRel : RunRel where
  I := List Loc
  R := BoLo.FreshRunN
  refl := fun _ μ e => .refl μ e
  cons := fun h hdom t => BoLo.FreshRunN.cons h hdom t
  alloc := fun N μ v hfin => BoLo.FreshRunN.alloc N μ v hfin
  shift := fun K N => N ++ (K.plug .unit).locs
  plug := fun K _ _ _ _ _ h => BoLo.FreshRunN.plug K h
  trans := fun h₁ h₂ => BoLo.FreshRunN.trans h₁ h₂
  toSteps := fun h => h.toSteps

/-!
Row 4.11 · `ℰ⟦T⟧δ(v) ≜ wp (e) {𝒱⟦T⟧δ}` · `[repair]`; the printed row is in `Paper/S4_LogicalRelation/Definitions.lean`.

Row 5.33, continued.
-/
/-- `[TR]` p. 6's `wp` at a tagged typed world, with its run drawn from the class `R`.  The
frame quantifier ranges over the completions `ρ_f ● ρ` that are `TW` worlds at the list's
records, tagged, and the post-configuration is one too, with the same records proper and the
same list members: a record 6.64 creates inside a run is ended before the run returns.  Every
other conjunct is `Fig16.BoLo.wp`'s, verbatim.  `[about ours: [TR] p. 6's wp relativised to
tagged typed worlds; docs/adjudications.md §12.72, §12.74]` -/
def wpTSR (RR : RunRel) (ls : List SRec) (e : Expr) (Q : List SRec → Val → WProp) : WProp :=
  fun ρ =>
  ∀ (ρf fρ : WRes) (ps : List FrameRec), ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ →
    TW fρ ps (rsOf ls) → Tagged fρ ps ls → ∀ i : RR.I,
    ∃ (ρ' ρp fρ' fρ'p π : WRes) (v : Val) (μ μ' : Heap) (ps' : List FrameRec)
      (ls' : List SRec),
      ResU.Hash ρ' ρf ∧
      ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧
      ResU.Lower fρ μ ∧
      ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧
      RR.R i μ e μ' (.val v) ∧
      ResU.CompS ρ' ρp π ∧ ResU.UpdV ρ π ∧
      NoOwn ρp ∧
      TW fρ'p ps' (rsOf ls') ∧ Tagged fρ'p ps' ls' ∧
      (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls) ∧ Q ls' v ρ'

/-- `[TR]` p. 6's `wp` at a tagged typed world: `wpTSR` at every run.
`[about ours: [TR] p. 6's wp relativised to tagged typed worlds; docs/adjudications.md §12.72]` -/
abbrev wpTS : List SRec → Expr → (List SRec → Val → WProp) → WProp := wpTSR stepsRel

end BoCa.Fig16.LogRel.Typed

end
