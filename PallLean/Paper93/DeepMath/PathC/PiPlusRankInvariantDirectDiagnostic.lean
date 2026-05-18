import PallLean.Paper93.DeepMath.PathC.PiPlusRankInvariantReduction
import PallLean.Paper93.DeepMath.PathC.PiPlusMLProjectionObstruction

/-!
# Direct Route C rank-invariance diagnostic

This file returns to the original Route C plan and tests the easiest original
`IsAmplituhedronGauge`/`Pi+` property: rank invariance for the explicit
Hadamard gauge.

The direct proof route would transport each SPDP generator through the
block-diagonal Hadamard algebra equivalence.  At generator level this requires
the Hadamard gauge to commute with the multilinear projection `mlProj` on the
rows `m * ∂_S p`.

The theorem below is the concrete obstruction: already in one local 2-variable
block, `Pi+` sends the multilinear monomial `X₀X₁` to a difference of squares.
`mlProj` kills those squares, while applying `mlProj` first leaves `X₀X₁` and
then the gauge sends it to the same nonzero difference of squares.

So `PiPlusRankInvariant` is not discharged by a direct algebra-equivalence
argument.  A proof must add a real compatibility theorem for the *projected /
quotiented / Boolean* row space, or otherwise show that the Cook--Levin rows
avoid this leakage.  This is exactly the missing mathematical payload exposed by
`PiPlusSPDPSubspaceTransport`.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open MultilinearSPDP

attribute [local instance] Classical.dec

/-- The direct generator-transport commutation needed for a naive rank-invariance
proof is already false on the local Hadamard block. -/
theorem piPlusHadamard2Gauge_does_not_commute_with_mlProj_on_pair :
    mlProj (piPlusHadamard2Gauge
        ((X 0) * (X 1) : MvPolynomial (Fin 2) ℚ)) ≠
      piPlusHadamard2Gauge
        (mlProj ((X 0) * (X 1) : MvPolynomial (Fin 2) ℚ)) := by
  intro h
  have hleft :
      mlProj (piPlusHadamard2Gauge
        ((X 0) * (X 1) : MvPolynomial (Fin 2) ℚ)) = 0 :=
    mlProj_piPlusHadamard2Gauge_mul_pair_leakage
  have hpair_mono :
      ((X 0) * (X 1) : MvPolynomial (Fin 2) ℚ) =
        MvPolynomial.monomial
          ((Finsupp.single (0 : Fin 2) 1) +
            (Finsupp.single (1 : Fin 2) 1)) (1 : ℚ) := by
    rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul]
    simp
  have hpair_ml :
      Finsupp.IsMultilinear
        ((Finsupp.single (0 : Fin 2) 1) +
          (Finsupp.single (1 : Fin 2) 1)) := by
    intro i
    fin_cases i <;> simp
  have hml_pair :
      mlProj ((X 0) * (X 1) : MvPolynomial (Fin 2) ℚ) =
        ((X 0) * (X 1) : MvPolynomial (Fin 2) ℚ) := by
    rw [hpair_mono, mlProj_monomial, if_pos hpair_ml]
  have hright :
      piPlusHadamard2Gauge
        (mlProj ((X 0) * (X 1) : MvPolynomial (Fin 2) ℚ)) =
        (X 0 ^ 2 - X 1 ^ 2 : MvPolynomial (Fin 2) ℚ) := by
    rw [hml_pair]
    exact piPlusHadamard2Gauge_mul_pair_leakage
  have hzero : (X 0 ^ 2 - X 1 ^ 2 : MvPolynomial (Fin 2) ℚ) = 0 := by
    calc
      (X 0 ^ 2 - X 1 ^ 2 : MvPolynomial (Fin 2) ℚ)
          = piPlusHadamard2Gauge
              (mlProj ((X 0) * (X 1) : MvPolynomial (Fin 2) ℚ)) := hright.symm
      _ = mlProj (piPlusHadamard2Gauge
              ((X 0) * (X 1) : MvPolynomial (Fin 2) ℚ)) := h.symm
      _ = 0 := hleft
  have hcoeff := congrArg (fun p : MvPolynomial (Fin 2) ℚ =>
      coeff (Finsupp.single (0 : Fin 2) 2) p) hzero
  have hne :
      (Finsupp.single (1 : Fin 2) 2 : Fin 2 →₀ ℕ) ≠
        Finsupp.single (0 : Fin 2) 2 := by
    intro h10
    have := congrArg (fun s : Fin 2 →₀ ℕ => s (0 : Fin 2)) h10
    norm_num [Finsupp.single_eq_same] at this
  simp [coeff_sub, coeff_X_pow, hne] at hcoeff

/-- Diagnostic restatement at the exact Route-C frontier: the existing
SPDP-subspace transport criterion cannot be proved by pushing the raw Hadamard
algebra equivalence through `mlProj`; that commutation is false. -/
def PiPlusRankInvariantDirectProofDiagnostic : Prop :=
  ¬ mlProj (piPlusHadamard2Gauge
        ((X 0) * (X 1) : MvPolynomial (Fin 2) ℚ)) =
      piPlusHadamard2Gauge
        (mlProj ((X 0) * (X 1) : MvPolynomial (Fin 2) ℚ))

theorem piPlusRankInvariant_directProofDiagnostic :
    PiPlusRankInvariantDirectProofDiagnostic :=
  piPlusHadamard2Gauge_does_not_commute_with_mlProj_on_pair

/-! ## Axiom audit anchors -/

#print axioms piPlusHadamard2Gauge_does_not_commute_with_mlProj_on_pair
#print axioms piPlusRankInvariant_directProofDiagnostic

end PallLean.Paper93.DeepMath.PathC
