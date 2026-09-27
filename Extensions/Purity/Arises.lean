import Purity.Independence

/-!
# Purity — arguments that arise from well-typed code

§6 quantifies over the resources that arise from the calculus ([CONF] 415:21: *"Conceptually,
in a valid resource, every pair of aliases map to the same object and each has an immutable
ancestor"*; docs/adjudications.md §12.72).  The arguments a pure-fragment function receives
from well-typed code are the values a well-typed program computes.  `Arises` names them.

**The notion.**  A tuple `γ` of argument values at types `Ts`, with the world and heap it lives
in, *arises* when it is a post-state of a well-typed *producer* `p : Δ; ∅ ⊢ p : Ts₁ ⊗ … ⊗ 1`
(`tupTy`) run from a tagged typed world completing `∅`: a fresh run of `p` ends at the heap,
returning the tuple, and the post-world completes the tuple's resource, as the Fundamental
Property at the fresh runs states it.  `arises_of_producer` shows that every well-typed producer,
from every such world, has an arising post-state; this is `Typed.fundamentalR` at `freshRel`.
A producer at a context `Δ` may return borrows (`Imm @a S`, `'a ∈ Δ`), so a call site inside a
borrow's scope is covered: the code up to the call is the producer.

**What it gives.**  An arising `γ` is in the context relation at the fresh runs
(`Arises.gDenX`), at every argument type — `Imm @a (Mut @b (1 ⊸ 1))` included.  So a program of the
pure fragment applied to arising arguments has a fresh run that gives the heap back, and every
run from that heap, or from any heap agreeing on what the arguments reach, returns one
plain-data value (`arising_pure_every_run`).  `arising_producer_pure` composes the two: producer
then consumer, from every world.

**The corner is empty** (`Arises.mut_pred`): in an arising argument at `Imm @a (Mut @b T)`, the
`Mut` cell under the borrow stores the relation at the fresh runs, `vX (wpTSR freshRel) true T`.
The difference `vX_lolli_depends` records between the relations at every run and at the fresh
runs is never met by an arising argument.

`[about ours]`: an extension, not a transcription.
-/

noncomputable section

namespace BoCa.Purity
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont FreshRunN)
open BoCa.Fig16.LogRel.Typed
open BoCa.Lifetime (LifeCtx LSub)

/-! ### Tuples -/

/-- `T₁ ⊗ (T₂ ⊗ (… ⊗ 1))`. -/
def tupTy : List Ty → Ty
  | [] => .unit
  | T :: Ts => .tensor T (tupTy Ts)

/-- `(v₁, (v₂, (…, ())))`. -/
def tupVal : List Val → Val
  | [] => .unit
  | v :: vs => .pair v (tupVal vs)

theorem tupVal_inj : ∀ {γ γ' : List Val}, tupVal γ = tupVal γ' → γ = γ'
  | [], [], _ => rfl
  | [], _ :: _, h => absurd (congrArg Subtype.val h) (by simp [tupVal, Val.pair, Val.unit])
  | _ :: _, [], h => absurd (congrArg Subtype.val h) (by simp [tupVal, Val.pair, Val.unit])
  | v :: γ, v' :: γ', h => by
      have h' := congrArg Subtype.val h
      simp only [tupVal, Val.pair, Expr.pair.injEq] at h'
      rw [Subtype.ext h'.1, tupVal_inj (Subtype.ext h'.2)]

/-- The context of live slots at `Ts`. -/
def liveCtx (Ts : List Ty) : Ctx Ty := Ts.map fun T => ⟨T, true⟩

/-- A tuple in the relation is a tuple of values each in the relation, composed. -/
theorem vPR_tup {RR : RunRel} {ls : List SRec} {δ : LSub} :
    ∀ (Ts : List Ty) {v : Val} {ρ : WRes}, vPR RR (tupTy Ts) ls δ v ρ →
      ∃ γ : List Val, v = tupVal γ ∧ γ.length = Ts.length ∧ gSepXR RR ls δ (liveCtx Ts) γ ρ
  | [], v, ρ, h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], rfl, rfl, by simp only [liveCtx, List.map, gSepXR]; exact ⟨rfl, trivial⟩⟩
  | T :: Ts, v, ρ, h => by
      obtain ⟨v₁, v₂, ρa, ρb, hc, ⟨rfl, rfl⟩, ρ₁, ρ₂, hc₂, h₁, h₂⟩ := h
      obtain ⟨γ, rfl, hlen, hγ⟩ := vPR_tup Ts h₂
      obtain rfl : ρb = ρ := ResU.eq_of_comp_empty_left hc
      refine ⟨v₁ :: γ, rfl, by simp [hlen], ?_⟩
      simp only [liveCtx, List.map, gSepXR, if_pos]
      exact ⟨ρ₁, ρ₂, hc₂, h₁, hγ⟩

theorem liveWithin_liveCtx : ∀ (Ts : List Ty) (γ : List Val), γ.length = Ts.length →
    Ctx.LiveWithin (liveCtx Ts) γ
  | [], _, _ => by simp [liveCtx]
  | _ :: Ts, [], h => by simp at h
  | _ :: Ts, _ :: γ, h => by
      simp only [liveCtx, List.map, Ctx.LiveWithin]
      exact liveWithin_liveCtx Ts γ (by simpa using h)

/-! ### Arising -/

/-- **`γ` arises**, at types `Ts` and lifetime context `Δ` read at `δ`, in the world `fρ` with
list `ls`, frames `ps` and heap `μ`, holding the resource `ρ`: a well-typed producer computes
it.  From the heap `μ₀` of a tagged typed world completing `∅`, a fresh run of the producer
ends at `μ`, returning the tuple; the world `fρ` completes `ρ` and is tagged typed; and the tuple
is in the relation at `ρ`, as the Fundamental Property at the fresh runs states of what the
producer returns.  `[about ours: the arising reading of §6, docs/adjudications.md §12.72]` -/
def Arises (Δ : LifeCtx) (δ : LSub) (Ts : List Ty) (γ : List Val) (ls : List SRec)
    (ρ fρ : WRes) (ps : List FrameRec) (μ : Heap) : Prop :=
  ∃ (p : Expr) (μ₀ : Heap) (ρf : WRes),
    DerivesWf Δ [] p (tupTy Ts) ∧ FreshRun μ₀ p μ (tupVal γ).1 ∧
    ResU.Hash ρf ρ ∧ ResU.CompS ρf ρ fρ ∧ TW fρ ps (rsOf ls) ∧ Tagged fρ ps ls ∧
    ResU.Lower fρ μ ∧ vPR freshRel (tupTy Ts) ls δ (tupVal γ) ρ

/-- **Every well-typed producer has an arising post-state**, from every tagged typed world
completing `∅`: `Typed.fundamentalR` at `freshRel`, at the empty list of locations to avoid. -/
theorem arises_of_producer {Δ : LifeCtx} {δ : LSub} {Ts : List Ty} {p : Expr}
    (hp : DerivesWf Δ [] p (tupTy Ts)) (hΔ : Δ.Ok) (hδ : Δ.Models δ) {ls : List SRec}
    {ρf₀ fρ₀ : WRes} {ps₀ : List FrameRec} {μ₀ : Heap} (hf : ResU.Hash ρf₀ PMap.empty)
    (hc : ResU.CompS ρf₀ PMap.empty fρ₀) (hT : TW fρ₀ ps₀ (rsOf ls)) (htg : Tagged fρ₀ ps₀ ls)
    (hμ : ResU.Lower fρ₀ μ₀) :
    ∃ (γ : List Val) (ls' : List SRec) (ρ fρ : WRes) (ps : List FrameRec) (μ : Heap),
      FreshRun μ₀ p μ (tupVal γ).1 ∧ γ.length = Ts.length ∧ Arises Δ δ Ts γ ls' ρ fρ ps μ := by
  have hsem := fundamentalR freshRel Δ [] p (tupTy Ts) hp hΔ (fun s hs => absurd hs (by simp))
  have hw := hsem δ [] ls PMap.empty hδ (gDenX_nil (RR := freshRel) ls δ)
  rw [LogRel.substAll, Adequacy.psub_nil] at hw
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, h₈, -, -, -,
    hT', htg', -, -, hQ⟩ := hw ρf₀ fρ₀ ps₀ hf hc hT htg []
  cases ResU.Lower.functional h₅ hμ
  obtain ⟨γ, rfl, hlen, -⟩ := vPR_tup Ts hQ
  -- the post-world completes `ρ′` with the frame `ρ_f ● ρ⁺`
  obtain ⟨z, hzp, hz⟩ := (hash_shift ρp ρf₀ ρ').mp ⟨fρ', h₂, h₃⟩
  obtain ⟨z₀, hz₀, hY⟩ := compS_exch h₂ h₆
  have hzY : ResU.CompS z ρ' fρ'p := by
    rwa [ResU.CompS.functional hz₀ (ResU.CompS.comm hzp)] at hY
  have hrun := FreshRunN.toFreshRun h₈
  exact ⟨γ, ls', ρ', fρ'p, ps', μ', hrun, hlen,
    ⟨p, μ₀, z, hp, hrun, hz, hzY, hT', htg', h₇, hQ⟩⟩

/-- **An arising tuple is in the context relation at the fresh runs**, at every argument type. -/
theorem Arises.gDenX {Δ : LifeCtx} {δ : LSub} {Ts : List Ty} {γ : List Val} {ls : List SRec}
    {ρ fρ : WRes} {ps : List FrameRec} {μ : Heap} (h : Arises Δ δ Ts γ ls ρ fρ ps μ) :
    gDenXR freshRel ls δ (liveCtx Ts) γ ρ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hQ⟩ := h
  obtain ⟨γ', he, hlen, hg⟩ := vPR_tup Ts hQ
  have : γ' = γ := tupVal_inj he.symm
  subst this
  exact gDenX_mk (liveWithin_liveCtx Ts γ' hlen) hg

/-- **The pure fragment on arising arguments, on every run**, at every argument type: a fresh
run gives the heap back and returns a plain-data value `v`; every run from the heap returns `v`;
and every run from any heap agreeing on what the arguments reach returns `v`. -/
theorem arising_pure_every_run {Δ : LifeCtx} {δ : LSub} {Ts : List Ty} {γ : List Val}
    {ls : List SRec} {ρ fρ : WRes} {ps : List FrameRec} {μ : Heap} {e : Expr} {T : Ty}
    (hP : PureTyping Δ (liveCtx Ts) e T) (hδ : Δ.Models δ)
    (h : Arises Δ δ Ts γ ls ρ fρ ps μ) :
    ∃ v : Val, LocFree v.1 ∧ FreshRun μ (LogRel.substAll γ e) μ (.val v) ∧
      (∀ (μ' : Heap) (w : Val), Steps μ (LogRel.substAll γ e) μ' w.1 → w = v) ∧
      ∀ (μ₂ μ₂' : Heap) (w : Val),
        (∀ x, Reach μ (ArgLocs γ) x → μ x ≠ none → μ₂ x = μ x) →
        Steps μ₂ (LogRel.substAll γ e) μ₂' w.1 → w = v := by
  have hγ := h.gDenX
  obtain ⟨-, -, ρf, -, -, hf, hc, hT, htg, hμ, -⟩ := h
  exact pure_result_every_run_fresh hP hδ hγ hf hc hT htg hμ

/-- **Producer, then pure consumer.**  From every tagged typed world completing `∅`, a
well-typed producer has a fresh run to a tuple `γ` and a heap `μ` from which every run of the
consumer `γ(e)`, and every run from any heap agreeing with `μ` on what `γ` reaches, returns one
plain-data value; a fresh run of `γ(e)` gives `μ` back. -/
theorem arising_producer_pure {Δ : LifeCtx} {δ : LSub} {Ts : List Ty} {p e : Expr} {T : Ty}
    (hp : DerivesWf Δ [] p (tupTy Ts)) (hP : PureTyping Δ (liveCtx Ts) e T) (hδ : Δ.Models δ)
    {ls : List SRec} {ρf₀ fρ₀ : WRes} {ps₀ : List FrameRec} {μ₀ : Heap}
    (hf : ResU.Hash ρf₀ PMap.empty) (hc : ResU.CompS ρf₀ PMap.empty fρ₀)
    (hT : TW fρ₀ ps₀ (rsOf ls)) (htg : Tagged fρ₀ ps₀ ls) (hμ : ResU.Lower fρ₀ μ₀) :
    ∃ (γ : List Val) (μ : Heap) (v : Val), FreshRun μ₀ p μ (tupVal γ).1 ∧ LocFree v.1 ∧
      FreshRun μ (LogRel.substAll γ e) μ (.val v) ∧
      (∀ (μ' : Heap) (w : Val), Steps μ (LogRel.substAll γ e) μ' w.1 → w = v) ∧
      ∀ (μ₂ μ₂' : Heap) (w : Val),
        (∀ x, Reach μ (ArgLocs γ) x → μ x ≠ none → μ₂ x = μ x) →
        Steps μ₂ (LogRel.substAll γ e) μ₂' w.1 → w = v := by
  obtain ⟨γ, ls', ρ, fρ, ps, μ, hrun, -, har⟩ :=
    arises_of_producer hp hP.ok hδ hf hc hT htg hμ
  obtain ⟨v, h₁, h₂, h₃, h₄⟩ := arising_pure_every_run hP hδ har
  exact ⟨γ, μ, v, hrun, h₁, h₂, h₃, h₄⟩

/-! ### The corner is empty -/

/-- **In an arising argument at `Imm @a (Mut @b S)`, the `Mut` cell under the borrow stores the
relation at the fresh runs.**  The argument is a location whose `imm` cell's payload is a
location `ℓ'` holding a `mut` cell (`ptoMutS`) whose stored predicate is
`vX (wpTSR freshRel) true S` at the cell's list. -/
theorem Arises.mut_pred {Δ : LifeCtx} {δ : LSub} {a b : Lifetime.Life} {S : Ty} {w : Val}
    {ls : List SRec} {ρ fρ : WRes} {ps : List FrameRec} {μ : Heap}
    (h : Arises Δ δ [.imm a (.mut b S)] [w] ls ρ fρ ps μ) :
    ∃ (ℓ ℓ' : Loc) (β : Life) (ls₀ : List SRec) (σ : WRes),
      w = .loc ℓ ∧ ptoMutS ℓ' β ls₀ (fun ls₁ => vX (wpTSR freshRel) true S ls₁ δ) σ := by
  have hγ := h.gDenX
  obtain ⟨ρ₁, ρ₂, -, -, hs⟩ := hγ
  simp only [liveCtx, List.map, gSepXR, if_pos] at hs
  obtain ⟨ρa, ρb, -, hv, -⟩ := hs
  obtain ⟨α, -, ℓ, ρc, ρd, -, ⟨-, hw, -⟩, s, u, σ, hσ, ls₀, -, hpay, -, -⟩ := hv
  obtain ⟨β, -, ℓ', σ₁, σ₂, -, ⟨-, -⟩, hm⟩ := hpay
  exact ⟨ℓ, ℓ', β, ls₀, σ₂, hw, hm⟩

end BoCa.Purity

end
