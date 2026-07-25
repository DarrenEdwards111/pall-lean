import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGodMoveFace
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthWilliamsPpolyCashout

/-!
# The tree unifies the faces: Williams' cash-out *is* the holographic two-observer clash

Darren's observation, machine-checked: the Williams cash-out
(`WilliamsPpolyCashout.williams_cashout`) and the God-Move observer duality
(`GodMoveFace.godmove_face`) are **the same skeleton** — a holographic two-observer clash on the
computation **tree** — and the barrier-threading that makes Williams special is exactly a *relocation*
of the open piece across that duality.

## The dictionary (all exact, not analogy)

The object both faces act on is the **tree**: the exponential nondeterministic computation, `2^n`
branches — the holographic *bulk*.

| holography / tree | Williams | God-Move |
|---|---|---|
| bulk (`2^n` tree) | NEXP truth tables | the NP object |
| boundary (poly DAG) | easy-witness circuit | the P-compilation |
| **projection** bulk⟶boundary | IKW easy-witness — **proven** | `Π★` — **open, far shore** |
| **inside observer** reads boundary | Circuit-SAT algorithm — **open** | low-rank reading — proven |
| **outside observer** floors bulk | nondet time hierarchy — proven | high-rank reading — proven |
| the clash | fast read undercuts the floor | rank gap `low < high` |

`Compressible` (`NEXP ⊆ P/poly`) means the exponential tree *shares* down to a poly boundary — the
tree/DAG duality of `TreeDagDuality`, in the Williams key.  The hierarchy floor is the tree's
irreducible cost; Williams says *compress the tree (easy witness) **and** read it fast (algorithm)*
would undercut that floor — the `dag_undercuts_tree` shape, turned into a contradiction.

## What is proved here

* **`two_observer_clash` (proved, axiom-free)** — the shared skeleton: a hypothesis `H`, a holographic
  projection `H → M` to a boundary reading, and an observer `M → False`, give `¬ H`.  Everything below
  is an instance.
* **`holographic_williams` (proved, axiom-free)** — Williams in holographic / tree vocabulary, factored
  through `two_observer_clash`.
* **`holographic_is_williams_cashout` (proved, axiom-free)** — the recast is *exact*: it discharges by
  applying the committed `williams_cashout` under the renaming.  Not a metaphor — the same theorem.
* **`godmove_via_clash` (proved)** — the God-Move face is the *same* `two_observer_clash`, with the
  numeric rank-gap as the observer.

## The relocation — the honest point

In `godmove_via_clash` the socket (the unproved input) is the **projection** `Π★`; in
`holographic_williams` the projection is proven and the socket sits in the **inside reader** (the
algorithm).  Same clash, open piece moved from the projection to the reader — which is the
machine-visible reason Williams **threads the natural-proofs barrier**: what is missing is an
*algorithm*, not a *property*.

**Honest scope.**  This unifies the barrier-threading route with the observer-duality faces into one
proved shape; it **crosses nothing**.  The open ingredient is still there — it has only moved to the
inside observer (the Circuit-SAT algorithm nobody has), and the output ceiling is still `NEXP`, not
`NP`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverClashViaTree

open PallLean.Paper93.DeepMath.PathB.GodMoveFace
open PallLean.Paper93.DeepMath.PathB.WilliamsPpolyCashout

/-- **The shared skeleton (proved, axiom-free).**  A two-observer holographic clash: from hypothesis
`H`, a holographic projection to a boundary reading `M`, and an observer that refutes any such reading,
conclude `¬ H`.  Both Williams and the God-Move face are instances. -/
theorem two_observer_clash {H M : Prop} (projection : H → M) (observer : M → False) : ¬ H :=
  fun h => observer (projection h)

/-- **Williams, holographically (proved, axiom-free).**  `Compressible` = the exponential tree (bulk)
compresses to a poly boundary = `NEXP ⊆ P/poly`.  `holographicProjection` = the IKW easy-witness map
(bulk ⟶ boundary), **proven**.  `boundaryReader` = the inside observer reading the boundary *given the
algorithm* — the **open** socket lives here.  `bulkFloor` = the outside observer, the nondet time
hierarchy.  The clash yields `¬ Compressible` = `NEXP ⊄ P/poly`. -/
theorem holographic_williams
    (Compressible Boundary FastBulk Algorithm : Prop)
    (holographicProjection : Compressible → Boundary)
    (boundaryReader : Algorithm → Boundary → FastBulk)
    (bulkFloor : FastBulk → False)
    (hAlg : Algorithm) :
    ¬ Compressible :=
  two_observer_clash holographicProjection (fun b => bulkFloor (boundaryReader hAlg b))

/-- **The recast is exact (proved, axiom-free).**  `holographic_williams` is not an analogy to the
Williams cash-out — it *is* it: this discharges by applying the committed `williams_cashout` under the
dictionary `Compressible↦NEXPinPpoly, Boundary↦EasyWitness, FastBulk↦FastNEXPAlg, Algorithm↦CircuitSATFast`. -/
theorem holographic_is_williams_cashout
    (Compressible Boundary FastBulk Algorithm : Prop)
    (holographicProjection : Compressible → Boundary)
    (boundaryReader : Algorithm → Boundary → FastBulk)
    (bulkFloor : FastBulk → False)
    (hAlg : Algorithm) :
    ¬ Compressible :=
  williams_cashout Compressible Algorithm Boundary FastBulk
    holographicProjection boundaryReader bulkFloor hAlg

/-- **The God-Move face is the same clash (proved).**  Instantiate `two_observer_clash` with the
holographic bulk being the abstract objects: the projection produces the clashing witness (the extracted
object read both high by the outside observer and, via `Π★`-monotonicity, low by the inside observer),
and the observer is the numeric rank-gap `low < high`.  Here the **open** socket is the projection `Π★`
— the relocation dual to Williams, whose open socket is the reader. -/
theorem godmove_via_clash {Obj : Type} (rank : Obj → ℕ)
    (PeqNP : Prop) (low high : ℕ) (hgap : low < high)
    (compile : PeqNP → Obj)
    (inside_low : ∀ h : PeqNP, rank (compile h) ≤ low)
    (Pi : GodMove Obj rank)
    (outside_high : ∀ h : PeqNP, high ≤ rank (Pi.piStar (compile h))) :
    ¬ PeqNP :=
  two_observer_clash
    (M := ∃ o : Obj, high ≤ rank (Pi.piStar o) ∧ rank o ≤ low)
    (fun h => ⟨compile h, outside_high h, inside_low h⟩)
    (fun hclash => by
      obtain ⟨o, hhi, hlo⟩ := hclash
      have hmono := Pi.monotone o
      omega)

end PallLean.Paper93.DeepMath.PathB.ObserverClashViaTree

#print axioms PallLean.Paper93.DeepMath.PathB.ObserverClashViaTree.two_observer_clash
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverClashViaTree.holographic_williams
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverClashViaTree.holographic_is_williams_cashout
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverClashViaTree.godmove_via_clash
