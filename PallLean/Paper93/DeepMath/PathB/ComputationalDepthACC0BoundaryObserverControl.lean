import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0MODResidualObserver
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PivotToPolynomialMethod
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0WilliamsCashoutFromPolynomial

/-!
# The boundary selects the observer — the N-frame as a contextual control process

The observer arc showed that "observer" is **not a fixed mechanism**: the *boundary / thermodynamic context* of a gate
decides which observer (which state space) is appropriate and whether its state can shrink.  This file makes that
contextual thesis concrete, routing the already-proved routes by the boundary their gates induce, with every arrow
grounded in a proved fact.

```
GateKind  ──boundarySelect──▶  BoundaryContext          state space / outcome
   AND/OR              absorbing        refined cell states — a fixed absorbing input deactivates the gate
   MOD/sym             linearResidual   residual states — but these REDUCE TO MEMBERSHIP (bounded), so …
   (MOD)               polynomialSpan   … the low-degree evaluation span (RS) is the observer that bites
   any                 countingState    Williams' sparse-counting view (the SAT-speedup cash-out)
```

The `countingState` observer is realised concretely elsewhere: in `…ACC0OracleControl`, an `AC⁰` control over `m`
`MOD` oracles has state count `≤ 2^{depth}` of its decision tree, and the composite is **SAT-searchable below `2ⁿ`**
once that depth drops below `n` (`oracle_control_over_mod_searchable`, proved for `2^m < 2^n`); the open rung
`random_restriction_makes_control_shallow` is exactly the *state-shrinkage* the contextual process needs.

## What is proved / routed (clean axioms, no `sorry`)

* `GateKind` / `BoundaryContext` / **`boundarySelect`** — the contextual observer-selection function.
* **`boundarySelect_andOr_iff_absorbing`** — the absorbing observer is selected exactly by `AND`/`OR`.
* **`andOr_boundary_absorbing`** / **`mod_boundary_not_absorbing`** — the selection grounded in gate semantics
  (`AND` has an absorbing value; `MOD` is constant only when its support is entirely fixed).
* **`mod_observer_reduces_to_membership`** — why the `linearResidual` observer is bounded for `MOD`.
* **`mod_polynomial_observer_separates`** — why the `polynomialSpan` observer bites on the `MOD` target.
* **`counting_state_cashes_out`** — the `countingState` boundary routes to the Williams cash-out (counting socket open).

## Honest scope

A **unification / routing** layer, not new hard content: it records which observer each boundary selects and ties each
selection to a proved fact.  The single load-bearing open input remains the **state-shrinkage / counting socket**
(`random_restriction_makes_control_shallow` ⤳ sub-`2ⁿ` `ACC⁰`-SAT — Williams' algorithmic heart).  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BoundaryObserverControl

open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountRoute
open PallLean.Paper93.DeepMath.PathB.ACC0RefinedObserverModel
open PallLean.Paper93.DeepMath.PathB.ACC0MODResidualObserver
open PallLean.Paper93.DeepMath.PathB.ACC0PivotToPolynomialMethod
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsCashoutFromPolynomial

/-- The kinds of gate whose boundary behaviour differs. -/
inductive GateKind where
  | andOr
  | mod (q : ℕ)
  | symmetric
  deriving DecidableEq

/-- The boundary / thermodynamic context that selects an observer. -/
inductive BoundaryContext where
  | absorbing       -- AND/OR: a fixed absorbing input deactivates the gate
  | linearResidual  -- MOD/parity: partial assignment preserves residual algebraic state
  | polynomialSpan  -- RS low-degree evaluation span
  | countingState   -- Williams' sparse-counting / SAT-speedup view
  deriving DecidableEq

/-- **The boundary selects the observer.**  `AND`/`OR` admit the absorbing observer; `MOD`/symmetric gates do not —
their boundary is the residual regime (which then routes to the polynomial / counting observers). -/
def boundarySelect : GateKind → BoundaryContext
  | .andOr => .absorbing
  | .mod _ => .linearResidual
  | .symmetric => .linearResidual

/-- **The absorbing observer is selected exactly by `AND`/`OR` (proved).**  The contextual process is well-defined and
`AND`/`OR` is the only kind whose boundary is absorbing. -/
theorem boundarySelect_andOr_iff_absorbing (gk : GateKind) :
    boundarySelect gk = BoundaryContext.absorbing ↔ gk = GateKind.andOr := by
  cases gk <;> simp [boundarySelect]

/-- **AND/OR → absorbing, grounded (proved).**  A fixed absorbing (`false`) input deactivates an `AND` gate even with
free inputs remaining, so the absorbing observer (refined cell-merging) applies. -/
theorem andOr_boundary_absorbing {n : ℕ} (ρ : Restriction n) (S : Finset (Fin n))
    (h : ∃ i ∈ S, ρ i = some false) : AndConstant ρ S :=
  and_constant_of_absorbing ρ S h

/-- **MOD → not absorbing, grounded (proved).**  A parity/`MOD` gate is constant only when its support is *entirely*
fixed: there is no single absorbing value, so the absorbing observer is unavailable. -/
theorem mod_boundary_not_absorbing {n : ℕ} (ρ : Restriction n) (S : Finset (Fin n))
    (h : ParityConstant ρ S) : ∀ i ∈ S, ρ i ≠ none :=
  (parity_constant_iff_support_fully_fixed ρ S).mp h

/-- **Why the `linearResidual` observer is bounded for `MOD` (proved).**  The residual observer of a free coordinate
is its membership pattern, so the `MOD` residual state space is the membership cell space — with the proved
hard-regime ceiling.  The cell-merging observer cannot do `MOD`. -/
theorem mod_observer_reduces_to_membership {k n : ℕ} (ρ : Restriction n)
    (supports : Fin k → Finset (Fin n)) (v : Fin n) (hv : ρ v = none) :
    residualSignature ρ supports v = cellPatternVec supports v :=
  residual_eq_membership_of_free ρ supports v hv

/-- **Why the `polynomialSpan` observer bites on `MOD` (proved).**  A degree-`<n` polynomial cannot equal the holonomy
parity on the cube (effective-dimension escape) — the observer the `MOD` boundary actually routes to. -/
theorem mod_polynomial_observer_separates {n : ℕ} (p : ℕ) [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    {D : ℕ} (hD : D < n) (h : MvPolynomial (Fin n) (ZMod p)) (hdeg : h.totalDegree ≤ D) :
    (fun x : Fin n → Bool => MvPolynomial.eval (fun i => Layer3.boolToZMod p (x i)) h)
      ≠ (fun x : Fin n → Bool => ∏ i, Layer3.pmOne p (x i)) :=
  lowDegree_poly_ne_holonomy_parity p hp2 hD h hdeg

/-- **The `countingState` boundary cashes out (proved logic).**  The polynomial (`SYM∘AND`) representation feeds the
sparse-counting observer; given the *counting* socket, the Williams collapse, and the time hierarchy, this refutes
`NEXP ⊆ ACC⁰`.  The representation half is discharged; the counting socket is the single open algorithmic input. -/
theorem counting_state_cashes_out
    (ACC0SatSpeedup NEXPHasACC0Circuits Collapse : Prop)
    (counting : RSMonoANDRepresentation → ACC0SatSpeedup)
    (williams : ACC0SatSpeedup → NEXPHasACC0Circuits → Collapse)
    (hierarchy : ¬ Collapse) :
    ¬ NEXPHasACC0Circuits :=
  williams_cashout_from_polynomial ACC0SatSpeedup NEXPHasACC0Circuits Collapse
    counting williams hierarchy

end PallLean.Paper93.DeepMath.PathB.ACC0BoundaryObserverControl

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundaryObserverControl.boundarySelect_andOr_iff_absorbing
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundaryObserverControl.andOr_boundary_absorbing
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundaryObserverControl.mod_boundary_not_absorbing
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundaryObserverControl.mod_observer_reduces_to_membership
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundaryObserverControl.mod_polynomial_observer_separates
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundaryObserverControl.counting_state_cashes_out
