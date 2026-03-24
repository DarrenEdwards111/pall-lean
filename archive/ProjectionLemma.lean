/-
  ProjectionLemma.lean — multilinearInterp f as projection of V_{M,n}

  When M decides f, there exists a partial assignment σ
  (setting computation variables to their trace values) such that:
    aeval σ (V_{M,n}) relates to multilinearInterp f

  More precisely: V_{M,n}(x, τ*(x)) = 0 for all x, where τ*(x)
  is the correct computation trace. The OUTPUT BIT of the computation
  is determined by τ*(x), and multilinearInterp f is the multilinear
  polynomial encoding this output.

  The SPDP rank of multilinearInterp f is bounded by the SPDP rank
  of V_{M,n} because projection (partial evaluation) is rank-nonincreasing.

  However, the relationship is more subtle than just "f = projection of V":
  - V_{M,n} = 0 on correct traces (it's a violation polynomial)
  - f is the ACCEPTANCE function, which is a separate variable
  - The connection goes through the ACCEPT variable in the tableau

  The paper's approach: the compiled polynomial P_{M,n} has bounded
  SPDP rank. Any function decidable by M has SPDP rank bounded by
  that of P_{M,n}, because the function's truth table is "encoded" in
  the constraint structure.

  For the formalization: we show that the compilation captures f by
  proving that the SPDP generators of multilinearInterp f are images
  of SPDP generators of V_{M,n} under the projection map.
-/
import PallLean.TuringMachine
import PallLean.SPDPDefs
import PallLean.SPDPProjection
import PallLean.Depth4Simulation
import PallLean.RestrictedSPDP
import PallLean.Restriction
import PallLean.UniversalRestriction
import Mathlib.Tactic

namespace ProjectionLemma

open TuringMachine MvPolynomial SPDP

/-! ## The projection map: computation trace assignment

  For a DTM M deciding f on inputs of length n:
  - Run M on each input x ∈ {0,1}^n
  - Record the computation trace τ*(x) at each time step
  - τ*(x) assigns values to all computation variables (tape/state/head)

  The projection map σ_f sends:
  - Input variables x_i → X_i (keep as variables)
  - Computation variables → their trace values (constants from τ*(x))

  But σ_f depends on x! This is NOT a single partial assignment.
  Instead, it's a family of assignments indexed by x.

  The paper's resolution: work with the POLYNOMIAL V_{M,n} directly.
  The key fact: for ANY partial assignment to computation variables,
  the resulting polynomial on input variables has SPDP rank ≤ SPDP rank of V.
  This is the projection monotonicity from SPDPProjection.
-/

/-! ## The accept variable

  M's acceptance is encoded in a specific variable: the accept bit
  at the final time step. Define:
    accept_var : Fin(numVars M n κ)

  The function f(x) = M(x) is:
    f(x) = 1 iff the accept variable is 1 in the correct trace τ*(x)

  The multilinear interpolation of f is related to the projection
  of V_{M,n} through the accept variable's trace values.
-/

-- The accept variable: last state bit at final time step
noncomputable def acceptVar (M : DTM) (n κ : ℕ) :
    Fin (numVars M n κ) :=
  stateIdx M n κ ⟨0, by unfold tapeSize timeSteps; positivity⟩ ⟨0, by have := M.hStates; omega⟩

/-! ## The key relationship (paper §3.1, property 4)

  V_{M,n}(x, τ) = 0 iff τ is a valid computation trace of M on x.

  This is the CORRECTNESS of the Cook-Levin encoding.
  It means: the violation polynomial vanishes exactly on correct traces.

  Consequence: for the CORRECT trace τ*(x), all constraints are satisfied,
  so V(x, τ*(x)) = 0.

  For INCORRECT traces: at least one constraint is violated,
  so V(x, τ) > 0 (since V is a sum of squares).
-/

-- The correctness of Cook-Levin encoding:
-- V_{M,n}(x, τ) = 0 ↔ τ is correct trace of M on x
-- This is the fundamental property of the compilation.
-- cook_levin_correctness: V_{M,n}(x,τ) = 0 ↔ τ is valid trace
-- This requires defining allRealConstraints and isValidTrace,
-- which is the full Cook-Levin encoding formalization.
-- Left as the key sub-theorem to prove.

-- For now, we axiomatize the end result:
-- The SPDP rank of f's multilinear interpolation is bounded by
-- the SPDP rank of V_{M,n} (modulo restriction/partition adaptation).

/-! ## Summary: the full bridge

  multilinearInterp f
    = projection of the accept variable through V_{M,n}
    → spdpRank(multilinearInterp f) ≤ spdpRank(V_{M,n})
    → restrictedSpdpRank(multilinearInterp f, ρ) ≤ blockedSpdpRankQ(V_{M,n}, B)
    → ≤ (log n)^35  (profile compression, PROVED)
    → ≤ √n  (theorem92, PROVED)

  The gap: formalizing the first arrow (projection step).
  This requires:
  1. cook_levin_correctness (axiom above)
  2. SPDPProjection.pderiv_restrictPoly_comm (sorry)
  3. SPDPProjection.restrictedSpdpRank_le_spdpRank (sorry)
  4. A lemma connecting blocked and restricted SPDP variants

  Items 2-3 are mathematically clear (derivation/hom commutation).
  Item 4 is a parameter-matching exercise.
  Item 1 is the Cook-Levin theorem (correctness of the encoding).
-/

end ProjectionLemma
