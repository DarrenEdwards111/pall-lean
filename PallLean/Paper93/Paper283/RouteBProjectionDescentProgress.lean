import PallLean.Paper93.Paper283.RouteBRicherGaugeConcreteMultilinearResidual

/-!
# Projection-descent progress for the concrete multilinear tail

This file records the current Route B projection frontier for the concrete
multilinear-tail finite-row projection.

The broad multilinear tail makes every SPDP generator row a selected finite-row
output.  Consequently the paper-faithful projection-descent condition is
equivalent to the stronger-looking residual-generator-zero condition, and to
annihilation of every admissible generator on the arbitrary projection kernel.
The theorems below expose that equivalence directly at the projection-escape
surface, without adding an axiom or asserting the condition.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- For the concrete multilinear-tail finite-row projection, descent is
equivalent to generator annihilation on the projection kernel.

This is the kernel-form obstruction behind the residual-generator-zero
condition: the broad tail makes projected generator rows fixed, so all remaining
work is exactly the generator action on the arbitrary complement selected as
the kernel of the finite-row projection. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_kernelGenerator_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns ↔
      RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZero
        M n hn2 htb hns := by
  rw [
    routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_residualGenerator_zero,
    routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_iff_kernelGenerator_zero]

/-- Projection escape for the concrete multilinear-tail projection is exactly
failure of residual-generator-zero. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_residualGenerator_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns ↔
      ¬ RouteBRicherConcreteNPPrependedMultilinearResidualGeneratorZero
        M n hn2 htb hns := by
  calc
    RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns
        ↔ ¬ RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
          M n hn2 htb hns :=
      routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_projectionDescent
        M n hn2 htb hns
    _ ↔ ¬ RouteBRicherConcreteNPPrependedMultilinearResidualGeneratorZero
          M n hn2 htb hns :=
      not_congr
        (routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_residualGenerator_zero
          M n hn2 htb hns)

/-- Projection escape for the concrete multilinear-tail projection is exactly
failure of kernel-generator annihilation on the selected projection kernel. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_kernelGenerator_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns ↔
      ¬ RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZero
        M n hn2 htb hns := by
  calc
    RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns
        ↔ ¬ RouteBRicherConcreteNPPrependedMultilinearResidualGeneratorZero
          M n hn2 htb hns :=
      routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_residualGenerator_zero
        M n hn2 htb hns
    _ ↔ ¬ RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZero
          M n hn2 htb hns :=
      not_congr
        (routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_iff_kernelGenerator_zero
          M n hn2 htb hns)

/-- Absence of concrete projection escape is exactly residual-generator-zero.

Thus the escape-free branch does not avoid the residual obstruction; for the
broad multilinear tail it is the same theorem. -/
theorem routeBRicherConcreteNPPrependedMultilinear_no_projectionEscapeWitness_iff_residualGenerator_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    (¬ RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns) ↔
      RouteBRicherConcreteNPPrependedMultilinearResidualGeneratorZero
        M n hn2 htb hns := by
  calc
    (¬ RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns)
        ↔ RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
          M n hn2 htb hns :=
      (routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_no_projectionEscapeWitness
        M n hn2 htb hns).symm
    _ ↔ RouteBRicherConcreteNPPrependedMultilinearResidualGeneratorZero
          M n hn2 htb hns :=
      routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_residualGenerator_zero
        M n hn2 htb hns

/-- Absence of concrete projection escape is exactly kernel-generator
annihilation on the selected projection kernel. -/
theorem routeBRicherConcreteNPPrependedMultilinear_no_projectionEscapeWitness_iff_kernelGenerator_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    (¬ RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns) ↔
      RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZero
        M n hn2 htb hns := by
  calc
    (¬ RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns)
        ↔ RouteBRicherConcreteNPPrependedMultilinearResidualGeneratorZero
          M n hn2 htb hns :=
      routeBRicherConcreteNPPrependedMultilinear_no_projectionEscapeWitness_iff_residualGenerator_zero
        M n hn2 htb hns
    _ ↔ RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZero
          M n hn2 htb hns :=
      routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_iff_kernelGenerator_zero
        M n hn2 htb hns

/-- A kernel vector with nonzero multilinear part gives a concrete projection
escape witness.  This upgrades the residual no-go criterion to the actual
projection-descent frontier. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_of_kernel_mlProj_ne_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      exists p : SATDeciderGaugeSpace M n hn2 htb hns,
        routeBRicherConcreteNPPrependedMultilinearProjection
          M n hn2 htb hns p = 0 ∧ mlProj p ≠ 0) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
      M n hn2 htb hns :=
  (routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_residualGenerator_zero
    M n hn2 htb hns).mpr
    (routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_noGo_of_kernel_mlProj_ne_zero
      M n hn2 htb hns hbad)

/-- If the selected projection changes the multilinear part of some
polynomial, then the concrete multilinear-tail projection has an escape
witness. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_of_mlProj_projection_ne
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      exists p : SATDeciderGaugeSpace M n hn2 htb hns,
        mlProj
            (routeBRicherConcreteNPPrependedMultilinearProjection
              M n hn2 htb hns p) ≠
          mlProj p) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
      M n hn2 htb hns :=
  (routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_residualGenerator_zero
    M n hn2 htb hns).mpr
    (routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_noGo_of_mlProj_projection_ne
      M n hn2 htb hns hbad)

/-- If there is no concrete projection escape, the selected projection must
preserve the canonical multilinear part of every polynomial. -/
theorem routeBRicherConcreteNPPrependedMultilinear_mlProj_projection_eq_of_no_projectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hno :
      ¬ RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    mlProj
        (routeBRicherConcreteNPPrependedMultilinearProjection
          M n hn2 htb hns p) =
      mlProj p :=
  routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_implies_mlProj_projection_eq
    M n hn2 htb hns
    ((routeBRicherConcreteNPPrependedMultilinear_no_projectionEscapeWitness_iff_residualGenerator_zero
      M n hn2 htb hns).mp hno)
    p

/-- If there is no concrete projection escape, the kernel of the selected
projection must be contained in the kernel of `mlProj`. -/
theorem routeBRicherConcreteNPPrependedMultilinear_kernel_mlProj_zero_of_no_projectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hno :
      ¬ RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (hker :
      routeBRicherConcreteNPPrependedMultilinearProjection
        M n hn2 htb hns p = 0) :
    mlProj p = 0 :=
  routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_implies_kernel_mlProj_zero
    M n hn2 htb hns
    ((routeBRicherConcreteNPPrependedMultilinear_no_projectionEscapeWitness_iff_residualGenerator_zero
      M n hn2 htb hns).mp hno)
    p hker

/-! ## First-square transfer obstruction -/

/-- The singleton first-coordinate SPDP generator row of the first-square
probe has visible coefficient `2` at the first linear monomial.  This is the
raw nonzero row behind the designed coefficient-dual escape witness, stated
without using the designed projection. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_singletonRow_coeff_firstVar
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeFirstVar M n hn2 htb hns) 1)
        (routeBSPDPGeneratorRow M n hn2 htb hns
          (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
            M n hn2 htb hns)
          [satDeciderGaugeFirstVar M n hn2 htb hns]
          (1 : SATDeciderGaugeSpace M n hn2 htb hns)) =
      (2 : Rat) := by
  rw [routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_singletonRow_eq]
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_X']
  simp

/-- The singleton first-coordinate SPDP generator row of the first-square
probe is nonzero. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_singletonRow_ne_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns)
        [satDeciderGaugeFirstVar M n hn2 htb hns]
        (1 : SATDeciderGaugeSpace M n hn2 htb hns) ≠ 0 := by
  intro hzero
  have hcoeffZero :
      MvPolynomial.coeff
          (Finsupp.single (satDeciderGaugeFirstVar M n hn2 htb hns) 1)
          (routeBSPDPGeneratorRow M n hn2 htb hns
            (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
              M n hn2 htb hns)
            [satDeciderGaugeFirstVar M n hn2 htb hns]
            (1 : SATDeciderGaugeSpace M n hn2 htb hns)) = 0 := by
    rw [hzero]
    simp
  have hcoeffTwo :=
    routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_singletonRow_coeff_firstVar
      M n hn2 htb hns
  norm_num [hcoeffZero] at hcoeffTwo

/-- The first-square probe has visible pure-square coefficient `1` at the
first Cook-Levin coordinate. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_coeff_firstVar_square
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeFirstVar M n hn2 htb hns) 2)
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns) =
      (1 : Rat) := by
  rw [routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_eq_monomial,
    MvPolynomial.coeff_monomial]
  simp

/-- The first-square probe itself is nonzero. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_ne_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns ≠ 0 := by
  intro hzero
  have hcoeffZero :
      MvPolynomial.coeff
          (Finsupp.single (satDeciderGaugeFirstVar M n hn2 htb hns) 2)
          (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
            M n hn2 htb hns) = 0 := by
    rw [hzero]
    simp
  have hcoeffOne :=
    routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_coeff_firstVar_square
      M n hn2 htb hns
  norm_num [hcoeffZero] at hcoeffOne

/-! ## Selected-projection behavior on the first-square probe -/

/-- The selected arbitrary finite-row projection sends the first-square probe
into the concrete row span.  This is the row-span component chosen by the
noncomputable complement behind the finite-row projection. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_mem_rowSpan
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    routeBRicherConcreteNPPrependedMultilinearProjection
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns) ∈
      finiteRowsSubmodule
        (routeBRicherConcreteNPPrependedMultilinearRows
          M n hn2 htb hns) := by
  simpa [routeBRicherConcreteNPPrependedMultilinearProjection,
    routeBRicherConcreteNPPrependedMultilinearGauge] using
    routeBRicherFiniteRowsCandidateGauge_projected_mem_finiteRowsSubmodule
      M n hn2 htb hns
      (routeBRicherConcreteNPPrependedMultilinearRows
        M n hn2 htb hns)
      (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns)

/-- The first-square probe lies in the concrete row span exactly when the
selected arbitrary finite-row projection fixes it. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_mem_rowSpan_iff_projection_eq_self
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns ∈
        finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns) ↔
      routeBRicherConcreteNPPrependedMultilinearProjection
          M n hn2 htb hns
          (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
            M n hn2 htb hns) =
        routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns := by
  constructor
  · intro hrow
    simpa [routeBRicherConcreteNPPrependedMultilinearProjection,
      routeBRicherConcreteNPPrependedMultilinearGauge] using
      routeBRicherFiniteRowsCandidateGauge_fixed_of_mem
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns)
        hrow
  · intro hfix
    rw [← hfix]
    exact
      routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_mem_rowSpan
        M n hn2 htb hns

/-- If the first-square probe is already in the concrete row span, the
selected projection fixes it. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_eq_self_of_mem_rowSpan
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hrow :
      routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns ∈
        finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns)) :
    routeBRicherConcreteNPPrependedMultilinearProjection
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns) =
      routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns :=
  (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_mem_rowSpan_iff_projection_eq_self
    M n hn2 htb hns).mp hrow

/-- Row-span membership is a sufficient condition for avoiding the
first-square kernel obstruction. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_ne_zero_of_mem_rowSpan
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hrow :
      routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns ∈
        finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns)) :
    routeBRicherConcreteNPPrependedMultilinearProjection
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns) ≠ 0 := by
  rw [
    routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_eq_self_of_mem_rowSpan
      M n hn2 htb hns hrow]
  exact
    routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_ne_zero
      M n hn2 htb hns

/-- The first-square probe is killed by the selected arbitrary finite-row
projection exactly when it lies in the arbitrary complement selected as the
projection kernel. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_eq_zero_iff_mem_selectedComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    routeBRicherConcreteNPPrependedMultilinearProjection
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns) = 0 ↔
      routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns ∈
        finiteSubmoduleProjectionComplement
          (finiteRowsSubmodule
            (routeBRicherConcreteNPPrependedMultilinearRows
              M n hn2 htb hns)) := by
  simpa [routeBRicherConcreteNPPrependedMultilinearProjection,
    routeBRicherConcreteNPPrependedMultilinearGauge] using
    routeBRicherFiniteRowsCandidateGauge_projection_apply_eq_zero_iff
      M n hn2 htb hns
      (routeBRicherConcreteNPPrependedMultilinearRows
        M n hn2 htb hns)
      (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns)

/-- The selected projection decomposes the first-square probe into a row-span
component and a selected-kernel residual. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_residual_mem_selectedComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns -
      routeBRicherConcreteNPPrependedMultilinearProjection
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns) ∈
        finiteSubmoduleProjectionComplement
          (finiteRowsSubmodule
            (routeBRicherConcreteNPPrependedMultilinearRows
              M n hn2 htb hns)) := by
  let Pi :=
    routeBRicherConcreteNPPrependedMultilinearProjection M n hn2 htb hns
  let probe :=
    routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
      M n hn2 htb hns
  have hPiPi : Pi (Pi probe) = Pi probe := by
    have hidem :=
      (routeBRicherConcreteNPPrependedMultilinearGauge
        M n hn2 htb hns).is_idempotent
    have happ := congrArg (fun L => L probe) hidem
    simpa [Pi, routeBRicherConcreteNPPrependedMultilinearProjection,
      LinearMap.comp_apply] using happ
  have hzero : Pi (probe - Pi probe) = 0 := by
    simp [Pi, map_sub, hPiPi]
  simpa [Pi, probe, routeBRicherConcreteNPPrependedMultilinearProjection,
    routeBRicherConcreteNPPrependedMultilinearGauge] using
    (routeBRicherFiniteRowsCandidateGauge_projection_apply_eq_zero_iff
      M n hn2 htb hns
      (routeBRicherConcreteNPPrependedMultilinearRows
        M n hn2 htb hns)
      (probe - Pi probe)).mp hzero

/-- The first-square probe cannot be simultaneously in the concrete row span
and in the selected projection kernel. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_not_mem_rowSpan_and_selectedComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    ¬ (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns ∈
          finiteRowsSubmodule
            (routeBRicherConcreteNPPrependedMultilinearRows
              M n hn2 htb hns) ∧
        routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns ∈
          finiteSubmoduleProjectionComplement
            (finiteRowsSubmodule
              (routeBRicherConcreteNPPrependedMultilinearRows
                M n hn2 htb hns))) := by
  rintro ⟨hrow, hkernel⟩
  have hprojZero :=
    (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_eq_zero_iff_mem_selectedComplement
      M n hn2 htb hns).mpr hkernel
  exact
    (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_ne_zero_of_mem_rowSpan
      M n hn2 htb hns hrow) hprojZero

/-- Transfer obstruction from the designed coefficient-dual projection to the
arbitrary finite-row projection: if the selected arbitrary projection also
kills the first-square probe, then kernel-generator-zero is false. -/
theorem routeBRicherConcreteNPPrependedMultilinear_not_kernelGenerator_zero_of_firstSquareProbe_kernel
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hker :
      routeBRicherConcreteNPPrependedMultilinearProjection
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns) = 0) :
    ¬ RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZero
        M n hn2 htb hns := by
  intro hzero
  have hrowZero :=
    hzero 1 0
      (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns)
      [satDeciderGaugeFirstVar M n hn2 htb hns]
      (1 : SATDeciderGaugeSpace M n hn2 htb hns)
      (by simp)
      (by simp [MvPolynomial.totalDegree_one])
      (by simp [MvPolynomial.vars_one])
      (by
        constructor
        · simp
        · intro b
          simpa using
            (List.length_filter_le
              (fun i =>
                (cook_levin_compilation M n hn2 htb hns).partition.assign i = b)
              [satDeciderGaugeFirstVar M n hn2 htb hns]))
      hker
  exact
    (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_singletonRow_ne_zero
      M n hn2 htb hns) hrowZero

/-- If the arbitrary finite-row projection kills the first-square probe, then
the concrete multilinear-tail projection has an escape witness. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_of_firstSquareProbe_kernel
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hker :
      routeBRicherConcreteNPPrependedMultilinearProjection
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns) = 0) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
      M n hn2 htb hns :=
  (routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_kernelGenerator_zero
    M n hn2 htb hns).mpr
    (routeBRicherConcreteNPPrependedMultilinear_not_kernelGenerator_zero_of_firstSquareProbe_kernel
      M n hn2 htb hns hker)

/-- Equivalently, killing the first-square probe refutes projection descent
for the selected arbitrary finite-row projection. -/
theorem routeBRicherConcreteNPPrependedMultilinear_not_projectionDescent_of_firstSquareProbe_kernel
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hker :
      routeBRicherConcreteNPPrependedMultilinearProjection
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns) = 0) :
    ¬ RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns :=
  (routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_projectionDescent
    M n hn2 htb hns).mp
    (routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_of_firstSquareProbe_kernel
      M n hn2 htb hns hker)

/-- Any successful projection-descent proof for the selected arbitrary
finite-row projection must therefore keep the first-square probe out of the
projection kernel. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_ne_zero_of_projectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdesc :
      RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns) :
    routeBRicherConcreteNPPrependedMultilinearProjection
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns) ≠ 0 := by
  intro hker
  exact
    (routeBRicherConcreteNPPrependedMultilinear_not_projectionDescent_of_firstSquareProbe_kernel
      M n hn2 htb hns hker) hdesc

/-- Equivalently, descent forces the selected arbitrary complement/kernel not
to contain the first-square probe. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_not_mem_selectedComplement_of_projectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdesc :
      RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns) :
    routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns ∉
      finiteSubmoduleProjectionComplement
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns)) := by
  intro hkernel
  exact
    (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_ne_zero_of_projectionDescent
      M n hn2 htb hns hdesc)
      ((routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_eq_zero_iff_mem_selectedComplement
        M n hn2 htb hns).mpr hkernel)

/-- Conversely, if the selected arbitrary complement/kernel contains the
first-square probe, the selected projection cannot satisfy descent. -/
theorem routeBRicherConcreteNPPrependedMultilinear_not_projectionDescent_of_firstSquareProbe_mem_selectedComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hkernel :
      routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns ∈
        finiteSubmoduleProjectionComplement
          (finiteRowsSubmodule
            (routeBRicherConcreteNPPrependedMultilinearRows
              M n hn2 htb hns))) :
    ¬ RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns :=
  routeBRicherConcreteNPPrependedMultilinear_not_projectionDescent_of_firstSquareProbe_kernel
    M n hn2 htb hns
    ((routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_eq_zero_iff_mem_selectedComplement
      M n hn2 htb hns).mpr hkernel)

/-- Under projection descent, the selected arbitrary finite-row projection
cannot equal the displayed coefficient-dual projection: the latter kills the
first-square probe, while descent forces the former not to. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjection_ne_explicitProjection_of_projectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdesc :
      RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns) :
    routeBRicherConcreteNPPrependedMultilinearProjection M n hn2 htb hns ≠
      (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
        M n hn2 htb hns).projection := by
  intro hEq
  have hker :
      routeBRicherConcreteNPPrependedMultilinearProjection
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns) = 0 := by
    rw [hEq]
    exact
      routeBRicherConcreteNPPrependedMultilinearExplicitProjection_firstSquareProbe_eq_zero
        M n hn2 htb hns
  exact
    (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_ne_zero_of_projectionDescent
      M n hn2 htb hns hdesc) hker

/-- Direct complement-transfer obstruction: if the arbitrary finite-row
projection's kernel contains the displayed coefficient-dual complement, then
kernel-generator-zero is false. -/
theorem routeBRicherConcreteNPPrependedMultilinear_not_kernelGenerator_zero_of_explicitComplement_le_projectionKernel
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (htransfer :
      forall p : SATDeciderGaugeSpace M n hn2 htb hns,
        p ∈
          (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
            M n hn2 htb hns).complement ->
        routeBRicherConcreteNPPrependedMultilinearProjection
          M n hn2 htb hns p = 0) :
    ¬ RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZero
        M n hn2 htb hns :=
  routeBRicherConcreteNPPrependedMultilinear_not_kernelGenerator_zero_of_firstSquareProbe_kernel
    M n hn2 htb hns
    (htransfer
      (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns)
      (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_mem_complement
        M n hn2 htb hns))

/-- A stronger complement-transfer obstruction: under projection descent, the
kernel of the selected arbitrary finite-row projection cannot contain the
whole displayed complement of the coefficient-dual projection. -/
theorem routeBRicherConcreteNPPrependedMultilinear_not_explicitComplement_le_projectionKernel_of_projectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdesc :
      RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns) :
    ¬ (forall p : SATDeciderGaugeSpace M n hn2 htb hns,
      p ∈
        (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
          M n hn2 htb hns).complement ->
      routeBRicherConcreteNPPrependedMultilinearProjection
        M n hn2 htb hns p = 0) := by
  intro htransfer
  exact
    (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_ne_zero_of_projectionDescent
      M n hn2 htb hns hdesc)
      (htransfer
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns)
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_mem_complement
          M n hn2 htb hns))

/-! ## Axiom audit anchors -/

#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_kernelGenerator_zero
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_residualGenerator_zero
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_kernelGenerator_zero
#print axioms routeBRicherConcreteNPPrependedMultilinear_no_projectionEscapeWitness_iff_residualGenerator_zero
#print axioms routeBRicherConcreteNPPrependedMultilinear_no_projectionEscapeWitness_iff_kernelGenerator_zero
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_of_kernel_mlProj_ne_zero
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_of_mlProj_projection_ne
#print axioms routeBRicherConcreteNPPrependedMultilinear_mlProj_projection_eq_of_no_projectionEscapeWitness
#print axioms routeBRicherConcreteNPPrependedMultilinear_kernel_mlProj_zero_of_no_projectionEscapeWitness
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_singletonRow_coeff_firstVar
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_singletonRow_ne_zero
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_coeff_firstVar_square
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_ne_zero
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_mem_rowSpan
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_mem_rowSpan_iff_projection_eq_self
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_eq_self_of_mem_rowSpan
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_ne_zero_of_mem_rowSpan
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_eq_zero_iff_mem_selectedComplement
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_residual_mem_selectedComplement
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_not_mem_rowSpan_and_selectedComplement
#print axioms routeBRicherConcreteNPPrependedMultilinear_not_kernelGenerator_zero_of_firstSquareProbe_kernel
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_of_firstSquareProbe_kernel
#print axioms routeBRicherConcreteNPPrependedMultilinear_not_projectionDescent_of_firstSquareProbe_kernel
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_ne_zero_of_projectionDescent
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_not_mem_selectedComplement_of_projectionDescent
#print axioms routeBRicherConcreteNPPrependedMultilinear_not_projectionDescent_of_firstSquareProbe_mem_selectedComplement
#print axioms routeBRicherConcreteNPPrependedMultilinearProjection_ne_explicitProjection_of_projectionDescent
#print axioms routeBRicherConcreteNPPrependedMultilinear_not_kernelGenerator_zero_of_explicitComplement_le_projectionKernel
#print axioms routeBRicherConcreteNPPrependedMultilinear_not_explicitComplement_le_projectionKernel_of_projectionDescent

end PallLean.Paper93.Paper283
