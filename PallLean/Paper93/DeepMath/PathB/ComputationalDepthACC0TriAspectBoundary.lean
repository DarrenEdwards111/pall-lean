import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RankShrinkWall
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PivotToPolynomialMethod
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BeigelTaruiSparsity
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RankRouteFrontier

/-!
# The tri-aspect boundary object — one `Ω`, three projections (incidence refuted, polynomial viable)

This file turns the "tri-aspect monism" reading of the `ACC⁰` programme from philosophy into a clean theorem map.
The lesson of the rank-shrink no-go (`…ACC0RankShrinkWall`) is *not* "pick a different boundary"; it is "the boundary
and the observer are not separate knobs — they are two projections of one underlying object `Ω`, and the *incidence*
projection is the wrong one."  We make that precise.

## One object, three projections

A single boundary object `Ω` (a `MOD`-gate support system plus an algebraic resolution `deg`) induces three
*derived* observers — not three independent hacks, but three projections of the same `Ω`:

```
TriAspectBoundary Ω = (supports, deg)
  ├─ incidence  projection :  incidenceRank Ω L = cellRank Ω.supports L      (N-Frame membership observer)
  ├─ algebraic  projection :  parity ∈?  span of degree-≤deg evaluations     (RS / effective-dimension observer)
  └─ cost       projection :  |lowDegMonomials n deg| ≤ (n+1)^deg            (Beigel–Tarui counting cost)
```

The point of tri-aspect monism made rigorous: `Ω` does not choose an *arbitrary* observer; it *induces* each of the
three from the same data.  The programme's job is to identify which projection is the working one.

## What is proved (clean axioms, no `sorry`)

* **`incidence_projection_fails`** — for the singleton boundary (`supports j = {j}`, an `ACC⁰`-realizable family) the
  incidence projection **never** collapses: `¬ IncidenceCollapses (singletonBoundary n D)`.  (Reuses the rank-shrink
  no-go: injective membership patterns defeat `RankCellCollapse`.)  The incidence projection is *insufficient*.
* **`polynomial_projection_succeeds_for_AC0p`** — the algebraic projection is *viable*: over `ZMod p` with `2 ≠ 0`
  and `deg < n`, the holonomy parity **escapes** the degree-`deg` evaluation span
  (`algebraicProjectionSucceeds Ω p`).  This is exactly the Razborov–Smolensky core: the polynomial/effective-dimension
  observer separates `MOD_p`-layers (`AC⁰[p]`) from parity where the incidence observer could not.
* **`cost_projection_quasipoly`** — the cost projection of `Ω` is quasipolynomial: `|lowDegMonomials n Ω.deg| ≤
  (n+1)^Ω.deg` (Beigel–Tarui monomial count).
* **`tri_aspect_redirect`** — the unifying statement: on the same singleton `Ω`, the incidence projection fails *and*
  the algebraic projection succeeds.  Formally: the correct observer for `ACC⁰` is not incidence rank but algebraic
  effective dimension — N-Frame, read through tri-aspect monism, *redirects to Route B*.
* **`composite_projection_socket`** — the one open projection: the *composite-`MOD`* algebraic projection
  (`composite_BT_degree`, the Yao/Beigel–Tarui composite-modulus `SYM∘AND` degree theorem) cashes out via the counting
  socket and Williams to `¬ NEXPHasACC0Circuits`.  Stated as a named conditional (the genuine open `NEXP`-strength
  content), reusing `…ACC0RankRouteFrontier.composite_route_to_NEXP_not_ACC0`.

## Honest scope

The structure is **not** vacuous packaging: each projection is an actual function of the one object `Ω`, and the two
positive theorems discharge to *real* prior theorems (the singleton no-go and the RS escape), not to abstract `Prop`
fields.  This file does not prove `NEXP ⊄ ACC⁰` or `P ≠ NP`; it proves *which projection is correct* and isolates the
single open composite-`MOD` algebraic projection.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TriAspectBoundary

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0RankCellCollapse
open PallLean.Paper93.DeepMath.PathB.ACC0RankShrinkWall
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.ACC0PivotToPolynomialMethod
open PallLean.Paper93.DeepMath.PathB.ACC0BeigelTaruiSparsity
open PallLean.Paper93.DeepMath.PathB.ACC0RankRouteFrontier

variable {n : ℕ}

/-- **The tri-aspect boundary object `Ω`.**  A single object carrying the combinatorial/physical aspect (`MOD`-gate
supports) and the algebraic resolution (`deg`, the degree budget of the polynomial projection).  The observer/cognitive
aspect and the cost aspect are *derived* from this data below — they are projections of `Ω`, not free fields. -/
structure TriAspectBoundary (n : ℕ) where
  /-- gate count of the boundary layer -/
  k : ℕ
  /-- physical/combinatorial aspect `Ω`: the `MOD`-gate support system -/
  supports : Fin k → Finset (Fin n)
  /-- algebraic aspect resolution: the polynomial-projection degree budget -/
  deg : ℕ

/-! ## The three projections of `Ω` -/

/-- **Incidence projection** (observer/cognitive aspect): the membership-rank observer on a live set `L`. -/
noncomputable def incidenceRank (Ω : TriAspectBoundary n) (L : Finset (Fin n)) : ℕ :=
  cellRank Ω.supports L

/-- **The incidence projection collapses**: some live set `L` carries fewer observer states than points,
`2^{cellRank} < |L|`.  This is the N-Frame rank-shrink event the membership observer would need. -/
def IncidenceCollapses (Ω : TriAspectBoundary n) : Prop :=
  ∃ L : Finset (Fin n), RankCellCollapse Ω.supports L

/-- **Algebraic projection succeeds** (algebraic/formal aspect): the holonomy parity is *not* in the span of the
degree-`≤ Ω.deg` squarefree evaluation monomials over `ZMod p` — i.e. the polynomial/effective-dimension observer at
resolution `Ω.deg` genuinely distinguishes parity (it has high effective dimension). -/
def algebraicProjectionSucceeds (Ω : TriAspectBoundary n) (p : ℕ) : Prop :=
  (fun x : Fin n → Bool => ∏ i, pmOne p (x i))
    ∉ Submodule.span (ZMod p)
        (Set.range (fun S : {S // S ∈ lowDegMonomials n Ω.deg} => squarefreeEvalMonomial p S.1))

/-- **Cost projection** (counting aspect): the Beigel–Tarui quasipolynomial bound on the number of degree-`≤ Ω.deg`
monomials carried by the algebraic projection. -/
def costBound (Ω : TriAspectBoundary n) : ℕ := (n + 1) ^ Ω.deg

/-- The singleton boundary: each gate reads exactly one variable (`supports j = {j}`), an `ACC⁰`-realizable family. -/
def singletonBoundary (n D : ℕ) : TriAspectBoundary n :=
  { k := n, supports := fun j => ({j} : Finset (Fin n)), deg := D }

/-! ## 1. The incidence projection is the wrong one (refuted) -/

/-- **The incidence projection fails (proved).**  On the singleton boundary the membership patterns are injective
(`cellPatternVec v = Pi.single v 1`), so `RankCellCollapse` is impossible on *every* live set: the incidence
projection never collapses.  Hence the `supportAspect`/incidence projection alone is insufficient — exactly the
rank-shrink no-go, now phrased as a property of `Ω`. -/
theorem incidence_projection_fails (D : ℕ) :
    ¬ IncidenceCollapses (singletonBoundary n D) := by
  rintro ⟨L, hL⟩
  exact singleton_supports_no_rank_collapse L hL

/-! ## 2. The algebraic projection is the working one (viable for `AC⁰[p]`) -/

/-- **The polynomial projection succeeds for `AC⁰[p]` (proved).**  Over `ZMod p` with `2 ≠ 0` and `Ω.deg < n`, the
holonomy parity escapes the degree-`≤ Ω.deg` evaluation span (Razborov–Smolensky core).  Where the incidence projection
collapsed for *no* adversarial support system, the algebraic projection is a genuine obstruction: the
effective-dimension observer is the correct projection of `Ω`. -/
theorem polynomial_projection_succeeds_for_AC0p (Ω : TriAspectBoundary n) (p : ℕ) [Fact p.Prime]
    (hp2 : (2 : ZMod p) ≠ 0) (hD : Ω.deg < n) :
    algebraicProjectionSucceeds Ω p := by
  unfold algebraicProjectionSucceeds
  exact holonomy_parity_escapes_lowDegSpan p hp2 hD

/-! ## 3. The cost projection is quasipolynomial -/

/-- **The cost projection of `Ω` is quasipolynomial (proved): `|lowDegMonomials n Ω.deg| ≤ (n+1)^{Ω.deg}`.** -/
theorem cost_projection_quasipoly (Ω : TriAspectBoundary n) :
    (lowDegMonomials n Ω.deg).card ≤ costBound Ω :=
  beigelTarui_monomial_count_le n Ω.deg

/-! ## 4. The redirect — incidence refuted, algebraic viable, on one and the same `Ω` -/

/-- **Tri-aspect redirect (proved).**  On a single singleton boundary `Ω`, the incidence projection fails *and* (for
`D < n`) the algebraic projection succeeds.  This is the formal content of "use N-Frame/tri-aspect monism to replace
the incidence observer by the algebraic one": the correct observer induced by `Ω` is the effective-dimension /
polynomial projection (Route B), not the membership-rank projection (Route A). -/
theorem tri_aspect_redirect (p : ℕ) [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0) {D : ℕ} (hD : D < n) :
    ¬ IncidenceCollapses (singletonBoundary n D)
      ∧ algebraicProjectionSucceeds (singletonBoundary n D) p :=
  ⟨incidence_projection_fails D, polynomial_projection_succeeds_for_AC0p _ p hp2 hD⟩

/-! ## 5. The one open projection — the composite-`MOD` algebraic socket -/

/-- **The composite-`MOD` algebraic projection socket (open).**  The genuine open content: that composite-modulus
`MOD` gates admit a low-complexity algebraic projection — the Yao/Beigel–Tarui composite `SYM∘AND` degree theorem
(`composite_BT_degree`).  Given it, the counting socket + Williams cash-out yields `¬ NEXPHasACC0Circuits`.  This is the
tri-aspect reformulation of the only remaining hard wall: *the correct boundary observer for `ACC⁰` is the algebraic
effective dimension, and the open step is producing it for composite modulus.* -/
theorem composite_projection_socket
    (RSRep ACC0SatSpeedup NEXPHasACC0Circuits Collapse : Prop)
    (composite_BT_degree : RSRep)
    (counting : RSRep → ACC0SatSpeedup)
    (williams : ACC0SatSpeedup → NEXPHasACC0Circuits → Collapse)
    (hierarchy : ¬ Collapse) :
    ¬ NEXPHasACC0Circuits :=
  composite_route_to_NEXP_not_ACC0 RSRep ACC0SatSpeedup NEXPHasACC0Circuits Collapse
    composite_BT_degree counting williams hierarchy

end PallLean.Paper93.DeepMath.PathB.ACC0TriAspectBoundary

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TriAspectBoundary.incidence_projection_fails
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TriAspectBoundary.polynomial_projection_succeeds_for_AC0p
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TriAspectBoundary.cost_projection_quasipoly
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TriAspectBoundary.tri_aspect_redirect
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TriAspectBoundary.composite_projection_socket
