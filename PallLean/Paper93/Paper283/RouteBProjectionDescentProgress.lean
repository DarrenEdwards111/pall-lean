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

/-- Kernel-generator-zero is exactly generator annihilation on the arbitrary
complement selected as the kernel of the finite-row projection. -/
theorem routeBRicherConcreteNPPrependedMultilinearKernelGeneratorZero_iff_selectedComplement_generator_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZero
        M n hn2 htb hns ↔
      forall (spdpKappa ell : Nat)
        (p : SATDeciderGaugeSpace M n hn2 htb hns)
        (support : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        support.length = spdpKappa ->
        shift.totalDegree <= ell ->
        shift.vars <= support.toFinset ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition support ->
        p ∈
          finiteSubmoduleProjectionComplement
            (finiteRowsSubmodule
              (routeBRicherConcreteNPPrependedMultilinearRows
                M n hn2 htb hns)) ->
        routeBSPDPGeneratorRow M n hn2 htb hns p support shift = 0 := by
  let rows := routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns
  constructor
  · intro hzero spdpKappa ell p support shift hSlen hshiftDegree hshiftVars hadm hp
    have hproj :
        routeBRicherConcreteNPPrependedMultilinearProjection
          M n hn2 htb hns p = 0 := by
      simpa [rows, routeBRicherConcreteNPPrependedMultilinearProjection,
        routeBRicherConcreteNPPrependedMultilinearGauge] using
        (routeBRicherFiniteRowsCandidateGauge_projection_apply_eq_zero_iff
          M n hn2 htb hns rows p).mpr hp
    exact hzero spdpKappa ell p support shift
      hSlen hshiftDegree hshiftVars hadm hproj
  · intro hzero spdpKappa ell p support shift hSlen hshiftDegree hshiftVars hadm hproj
    have hp :
        p ∈
          finiteSubmoduleProjectionComplement
            (finiteRowsSubmodule rows) := by
      simpa [rows, routeBRicherConcreteNPPrependedMultilinearProjection,
        routeBRicherConcreteNPPrependedMultilinearGauge] using
        (routeBRicherFiniteRowsCandidateGauge_projection_apply_eq_zero_iff
          M n hn2 htb hns rows p).mp hproj
    exact hzero spdpKappa ell p support shift
      hSlen hshiftDegree hshiftVars hadm hp

/-- Projection descent is exactly generator annihilation on the arbitrary
selected complement.  This is the complement-policy form of the descent
frontier; it does not assert any pointwise avoidance property for the
`Classical.choose` complement. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_selectedComplement_generator_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns ↔
      forall (spdpKappa ell : Nat)
        (p : SATDeciderGaugeSpace M n hn2 htb hns)
        (support : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        support.length = spdpKappa ->
        shift.totalDegree <= ell ->
        shift.vars <= support.toFinset ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition support ->
        p ∈
          finiteSubmoduleProjectionComplement
            (finiteRowsSubmodule
              (routeBRicherConcreteNPPrependedMultilinearRows
                M n hn2 htb hns)) ->
        routeBSPDPGeneratorRow M n hn2 htb hns p support shift = 0 := by
  rw [
    routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_kernelGenerator_zero,
    routeBRicherConcreteNPPrependedMultilinearKernelGeneratorZero_iff_selectedComplement_generator_zero]

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

private theorem routeBProjectionDescentProgress_coeff_single_two_mul {N : Nat}
    (v : Fin N) (p q : MvPolynomial (Fin N) Rat) :
    MvPolynomial.coeff (Finsupp.single v 2) (p * q) =
      MvPolynomial.coeff (Finsupp.single v 1) p *
          MvPolynomial.coeff (Finsupp.single v 1) q +
        (MvPolynomial.coeff (Finsupp.single v 2) q * MvPolynomial.coeff 0 p +
          MvPolynomial.coeff (Finsupp.single v 2) p * MvPolynomial.coeff 0 q) := by
  rw [MvPolynomial.coeff_mul, Finsupp.antidiagonal_single]
  have hanti :
      Finset.antidiagonal 2 =
        ({(0, 2), (1, 1), (2, 0)} : Finset (Nat × Nat)) := by
    decide
  rw [hanti]
  simp only [Finset.map_insert, Finset.map_singleton]
  rw [Finset.sum_insert]
  · rw [Finset.sum_insert]
    · rw [Finset.sum_singleton]
      simp [Function.Embedding.prodMap]
      ring
    · intro hmem
      unfold Function.Embedding.prodMap at hmem
      simp only [Function.Embedding.coeFn_mk, Prod.map_apply] at hmem
      simp at hmem
  · intro hmem
    unfold Function.Embedding.prodMap at hmem
    simp only [Function.Embedding.coeFn_mk, Prod.map_apply] at hmem
    simp at hmem
    rcases hmem with ⟨hzero, _⟩
    have hval := congrArg (fun a : Fin N →₀ Nat => a v) hzero
    simp at hval

/-- The concrete NP head row has pure-square coefficient `1` at the first
Cook-Levin coordinate as well. -/
theorem routeBRicherConcreteNPWitnessRows_zero_coeff_firstVar_square
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeFirstVar M n hn2 htb hns) 2)
        (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) = (1 : Rat) := by
  rw [routeBRicherConcreteNPWitnessRows_eq_embed,
    routeBRicherConcreteNPWitnessQ_embed_eq_compiledPoly]
  rw [CompiledBoolFactorBridge.compiledPoly_eq_boolFactorFullProd_mul_rest
    M n hn2 htb hns]
  rw [routeBProjectionDescentProgress_coeff_single_two_mul]
  have hbool2 := boolFactorFullProd_coeff_single_two n
    (satDeciderGaugeFirstVar M n hn2 htb hns)
  have hbool1 := boolFactorFullProd_coeff_single n
    (satDeciderGaugeFirstVar M n hn2 htb hns)
  have hrest0 := restFactorProd'_const_one M n
  have hrest1 := restFactorProd_coeff_single_eq_zero M n
    (satDeciderGaugeFirstVar M n hn2 htb hns)
  have hrest2 := restFactorProd_coeff_single_two_eq_zero M n
    (satDeciderGaugeFirstVar M n hn2 htb hns)
  rw [hbool2, hbool1, hrest0, hrest1, hrest2]
  ring

/-- Every broad multilinear tail row has zero pure-square coefficient at any
Cook-Levin coordinate. -/
theorem routeBRicherMultilinearTailRows_coeff_var_square
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (v : Fin (RouteBCookLevinDim M n hn2 htb hns))
    (j : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns)) :
    MvPolynomial.coeff
        (Finsupp.single v 2)
        (routeBRicherMultilinearTailRows M n hn2 htb hns j) = 0 := by
  rw [routeBRicherMultilinearTailRows_eq_monomial_tailCoeffAlpha,
    MvPolynomial.coeff_monomial]
  rw [if_neg]
  intro hsq
  have hml :
      Finsupp.IsMultilinear
        (routeBRicherMultilinearTailCoeffAlpha M n hn2 htb hns j) := by
    simpa [routeBRicherMultilinearTailCoeffAlpha] using
      SymmetricPower.tagMonomial_isMultilinear
        (routeBRicherMultilinearTailSupportSet M n hn2 htb hns j)
  have hv := hml v
  rw [hsq] at hv
  norm_num at hv

/-- Every broad multilinear tail row has zero pure-square coefficient at the
first Cook-Levin coordinate. -/
theorem routeBRicherMultilinearTailRows_coeff_firstVar_square
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (j : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns)) :
    MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeFirstVar M n hn2 htb hns) 2)
        (routeBRicherMultilinearTailRows M n hn2 htb hns j) = 0 :=
  routeBRicherMultilinearTailRows_coeff_var_square
    M n hn2 htb hns
    (satDeciderGaugeFirstVar M n hn2 htb hns) j

/-- Each concrete prepended multilinear row has matching first-square and
second-square coefficients.  The head row has both coefficients equal to `1`;
the multilinear tail rows have both equal to `0`. -/
theorem routeBRicherConcreteNPPrependedMultilinearRows_coeff_firstVar_square_eq_secondVar_square
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (i : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1)) :
    MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeFirstVar M n hn2 htb hns) 2)
        (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns i) =
      MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 2)
        (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns i) := by
  refine Fin.cases ?head ?tail i
  · simp [routeBRicherConcreteNPPrependedMultilinearRows,
      routeBRicherConcreteNPPrependedRows,
      routeBRicherConcreteNPWitnessRows_zero_coeff_firstVar_square,
      routeBRicherConcreteNPWitnessRows_zero_coeff_secondVar_square]
  · intro j
    simp [routeBRicherConcreteNPPrependedMultilinearRows,
      routeBRicherConcreteNPPrependedRows,
      routeBRicherMultilinearTailRows_coeff_firstVar_square,
      routeBRicherMultilinearTailRows_coeff_secondVar_square]

/-- Every vector in the concrete prepended multilinear row span has matching
first-square and second-square coefficients. -/
theorem routeBRicherConcreteNPPrependedMultilinear_rowSpan_coeff_firstVar_square_eq_secondVar_square
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {p : SATDeciderGaugeSpace M n hn2 htb hns}
    (hp :
      p ∈ finiteRowsSubmodule
        (routeBRicherConcreteNPPrependedMultilinearRows
          M n hn2 htb hns)) :
    MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeFirstVar M n hn2 htb hns) 2) p =
      MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 2) p := by
  let rows := routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns
  let firstAlpha :=
    Finsupp.single (satDeciderGaugeFirstVar M n hn2 htb hns) 2
  let secondAlpha :=
    Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 2
  have hp' : p ∈ Submodule.span Rat (Set.range rows) := by
    simpa [finiteRowsSubmodule, rows] using hp
  change MvPolynomial.coeff firstAlpha p = MvPolynomial.coeff secondAlpha p
  exact
    Submodule.span_induction
      (s := Set.range rows)
      (p := fun q _ =>
        MvPolynomial.coeff firstAlpha q = MvPolynomial.coeff secondAlpha q)
      (by
        rintro q ⟨i, rfl⟩
        simpa [firstAlpha, secondAlpha, rows] using
          routeBRicherConcreteNPPrependedMultilinearRows_coeff_firstVar_square_eq_secondVar_square
            M n hn2 htb hns i)
      (by simp)
      (by
        intro x y _ _ hx hy
        simp [MvPolynomial.coeff_add, hx, hy])
      (by
        intro a x _ hx
        simp [MvPolynomial.coeff_smul, hx])
      hp'

/-- The first-square probe is not in the concrete prepended multilinear row
span.  Its first-square coefficient is `1`, while its second-square coefficient
is `0`, contradicting the row-span coefficient equality above. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_not_mem_rowSpan
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns ∉
      finiteRowsSubmodule
        (routeBRicherConcreteNPPrependedMultilinearRows
          M n hn2 htb hns) := by
  intro hrow
  have heq :=
    routeBRicherConcreteNPPrependedMultilinear_rowSpan_coeff_firstVar_square_eq_secondVar_square
      M n hn2 htb hns hrow
  have hfirst :=
    routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_coeff_firstVar_square
      M n hn2 htb hns
  have hsecond :=
    routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_coeff_secondVar_square
      M n hn2 htb hns
  rw [hfirst, hsecond] at heq
  norm_num at heq

private theorem routeBProjectionDescentProgress_exists_complement_containing_of_not_mem
    {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (S : Submodule K V) {p : V} (hp : p ∉ S) :
    ∃ C : Submodule K V, IsCompl S C ∧ p ∈ C := by
  have hdis : Disjoint (K ∙ p) S := by
    rw [disjoint_comm]
    exact Submodule.disjoint_span_singleton_of_notMem hp
  rcases hdis.exists_isCompl with ⟨C, hspan_le_C, hcompl⟩
  exact ⟨C, hcompl.symm, hspan_le_C (Submodule.mem_span_singleton_self p)⟩

private theorem routeBProjectionDescentProgress_exists_complement_avoiding_of_not_mem_of_exists_ne_zero
    {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (S : Submodule K V) {p : V} (hp : p ∉ S)
    (hne : ∃ s : V, s ∈ S ∧ s ≠ 0) :
    ∃ C : Submodule K V, IsCompl S C ∧ p ∉ C := by
  rcases hne with ⟨s, hsS, hs_ne_zero⟩
  have hps_not_mem : p + s ∉ S := by
    intro hps
    have hpS : p ∈ S := by
      have hsub : p + s - s ∈ S := S.sub_mem hps hsS
      simpa using hsub
    exact hp hpS
  have hdis : Disjoint (K ∙ (p + s)) S := by
    rw [disjoint_comm]
    exact Submodule.disjoint_span_singleton_of_notMem hps_not_mem
  rcases hdis.exists_isCompl with ⟨C, hspan_le_C, hcompl⟩
  refine ⟨C, hcompl.symm, ?_⟩
  intro hpC
  have hpsC : p + s ∈ C :=
    hspan_le_C (Submodule.mem_span_singleton_self (p + s))
  have hsC : s ∈ C := by
    have hsub : p + s - p ∈ C := C.sub_mem hpsC hpC
    simpa using hsub
  have hsInf : s ∈ C ⊓ S := ⟨hsC, hsS⟩
  have hs_zero : s = 0 := by
    have hsBot : s ∈ (⊥ : Submodule K V) := by
      simpa [IsCompl.inf_eq_bot hcompl] using hsInf
    simpa using hsBot
  exact hs_ne_zero hs_zero

/-- Row-span nonmembership alone cannot enforce first-square avoidance by an
arbitrary complement: there is a valid complement to the concrete row span
which contains the first-square probe. -/
theorem routeBRicherConcreteNPPrependedMultilinear_exists_rowSpanComplement_mem_firstSquareProbe
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    ∃ C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns),
      IsCompl
          (finiteRowsSubmodule
            (routeBRicherConcreteNPPrependedMultilinearRows
              M n hn2 htb hns))
          C ∧
        routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns ∈ C :=
  routeBProjectionDescentProgress_exists_complement_containing_of_not_mem
    (finiteRowsSubmodule
      (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns))
    (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_not_mem_rowSpan
      M n hn2 htb hns)

/-- Consequently, some admissible explicit complement policy for the same row
span kills the first-square probe.  This is not a statement about the selected
`finiteSubmoduleProjectionComplement`; it records why a complement policy is
needed before asserting avoidance. -/
theorem routeBRicherConcreteNPPrependedMultilinear_exists_complementPolicy_kills_firstSquareProbe
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    ∃ (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
      (hC :
        IsCompl
          (finiteRowsSubmodule
            (routeBRicherConcreteNPPrependedMultilinearRows
              M n hn2 htb hns))
          C),
      finiteSubmoduleProjectionWithComplement
          (finiteRowsSubmodule
            (routeBRicherConcreteNPPrependedMultilinearRows
              M n hn2 htb hns))
          C hC
          (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
            M n hn2 htb hns) = 0 := by
  rcases
    routeBRicherConcreteNPPrependedMultilinear_exists_rowSpanComplement_mem_firstSquareProbe
      M n hn2 htb hns with
    ⟨C, hC, hprobe⟩
  refine ⟨C, hC, ?_⟩
  exact
    (finiteSubmoduleProjectionWithComplement_apply_eq_zero_iff
      (finiteRowsSubmodule
        (routeBRicherConcreteNPPrependedMultilinearRows
          M n hn2 htb hns))
      C hC
      (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns)).mpr hprobe

/-! ## Explicit first-square-avoiding complement policies -/

/-- The concrete prepended multilinear head row has visible pure-square
coefficient `1` at the first Cook-Levin coordinate. -/
theorem routeBRicherConcreteNPPrependedMultilinearRows_zero_coeff_firstVar_square
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeFirstVar M n hn2 htb hns) 2)
        (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns
          (0 : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1))) =
      (1 : Rat) := by
  simp [routeBRicherConcreteNPPrependedMultilinearRows,
    routeBRicherConcreteNPPrependedRows,
    routeBRicherConcreteNPWitnessRows_zero_coeff_firstVar_square]

/-- The concrete prepended multilinear row span contains a nonzero vector. -/
theorem routeBRicherConcreteNPPrependedMultilinear_rowSpan_exists_ne_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    ∃ p : SATDeciderGaugeSpace M n hn2 htb hns,
      p ∈
          finiteRowsSubmodule
            (routeBRicherConcreteNPPrependedMultilinearRows
              M n hn2 htb hns) ∧
        p ≠ 0 := by
  let row :=
    routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns
      (0 : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1))
  refine ⟨row, ?_, ?_⟩
  · exact Submodule.subset_span
      ⟨(0 : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1)), rfl⟩
  · intro hzero
    have hcoeffZero :
        MvPolynomial.coeff
            (Finsupp.single (satDeciderGaugeFirstVar M n hn2 htb hns) 2)
            row = 0 := by
      rw [hzero]
      simp
    have hcoeffOne :=
      routeBRicherConcreteNPPrependedMultilinearRows_zero_coeff_firstVar_square
        M n hn2 htb hns
    have hcoeffZero' :
        MvPolynomial.coeff
            (Finsupp.single (satDeciderGaugeFirstVar M n hn2 htb hns) 2)
            (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns
              (0 : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1))) = 0 := by
      simpa [row] using hcoeffZero
    norm_num [hcoeffZero'] at hcoeffOne

/-- There is a valid complement to the concrete prepended multilinear row span
that avoids the first-square probe.  The construction uses both facts already
available in this file: the probe is not in the row span, and the row span has
a nonzero concrete head row. -/
theorem routeBRicherConcreteNPPrependedMultilinear_exists_rowSpanComplement_not_mem_firstSquareProbe
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    ∃ C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns),
      IsCompl
          (finiteRowsSubmodule
            (routeBRicherConcreteNPPrependedMultilinearRows
              M n hn2 htb hns))
          C ∧
        routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns ∉ C :=
  routeBProjectionDescentProgress_exists_complement_avoiding_of_not_mem_of_exists_ne_zero
    (finiteRowsSubmodule
      (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns))
    (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_not_mem_rowSpan
      M n hn2 htb hns)
    (routeBRicherConcreteNPPrependedMultilinear_rowSpan_exists_ne_zero
      M n hn2 htb hns)

/-- The concrete multilinear-tail finite-row projection built from an
explicit complement policy rather than the arbitrary `Classical.choose`
complement. -/
noncomputable def routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C) :
    SATDeciderGaugeSpace M n hn2 htb hns →ₗ[Rat]
      SATDeciderGaugeSpace M n hn2 htb hns :=
  routeBNFrameCandidateAsSATGauge M n hn2 htb hns
    (routeBRicherFiniteRowsCandidateGaugeWithComplement
      M n hn2 htb hns
      (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns)
      C hC)

/-- Paper-faithful descent stated for an explicit-complement projection
policy.  This is the same commutation condition as the selected finite-row
descent surface, but with the supplied complement deciding the projection. -/
def RouteBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C) : Prop :=
  forall (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    routeBSPDPGeneratorRow M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement
          M n hn2 htb hns C hC p)
        S shift =
      routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement
        M n hn2 htb hns C hC
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)

/-- The explicit complement realizes the currently selected finite-row policy
only if its projection map is equal to the selected projection map.  This is
the checked replacement criterion; it is intentionally not asserted for an
arbitrary complement. -/
def RouteBRicherConcreteNPPrependedMultilinearComplementRealizesSelectedProjection
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C) : Prop :=
  routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement
      M n hn2 htb hns C hC =
    routeBRicherConcreteNPPrependedMultilinearProjection M n hn2 htb hns

/-- Pointwise zero criterion for the concrete explicit-complement projection
policy. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement_apply_eq_zero_iff
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement
        M n hn2 htb hns C hC p = 0 ↔
      p ∈ C := by
  simpa [routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement] using
    routeBRicherFiniteRowsCandidateGaugeWithComplement_projection_apply_eq_zero_iff
      M n hn2 htb hns
      (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns)
      C hC p

/-- For an explicit complement policy, first-square nonvanishing is exactly
avoidance of that complement. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement_firstSquareProbe_ne_zero_iff_not_mem
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C) :
    routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement
        M n hn2 htb hns C hC
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns) ≠ 0 ↔
      routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns ∉ C :=
  not_congr
    (routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement_apply_eq_zero_iff
      M n hn2 htb hns C hC
      (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns))

/-- Any explicit complement policy that avoids the first-square probe has a
nonzero concrete explicit-complement projection value on that probe. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement_firstSquareProbe_ne_zero_of_not_mem
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (hprobe :
      routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns ∉ C) :
    routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement
        M n hn2 htb hns C hC
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns) ≠ 0 :=
  (routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement_firstSquareProbe_ne_zero_iff_not_mem
    M n hn2 htb hns C hC).mpr hprobe

/-- Any explicit complement policy that avoids the first-square probe has a
nonzero `finiteSubmoduleProjectionWithComplement` value on that probe. -/
theorem routeBRicherConcreteNPPrependedMultilinear_projectionWithComplement_firstSquareProbe_ne_zero_of_not_mem
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (hprobe :
      routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns ∉ C) :
    finiteSubmoduleProjectionWithComplement
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C hC
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns) ≠ 0 := by
  intro hzero
  exact hprobe
    ((finiteSubmoduleProjectionWithComplement_apply_eq_zero_iff
      (finiteRowsSubmodule
        (routeBRicherConcreteNPPrependedMultilinearRows
          M n hn2 htb hns))
      C hC
      (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns)).mp hzero)

/-- There is an explicit-complement projection policy for the concrete row
span that is nonzero on the first-square probe.  This is a policy-existence
statement for `finiteSubmoduleProjectionWithComplement`, not a statement about
the arbitrary `Classical.choose` complement selected by
`finiteSubmoduleProjectionComplement`. -/
theorem routeBRicherConcreteNPPrependedMultilinear_exists_complementPolicy_projection_ne_zero_firstSquareProbe
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    ∃ (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
      (hC :
        IsCompl
          (finiteRowsSubmodule
            (routeBRicherConcreteNPPrependedMultilinearRows
              M n hn2 htb hns))
          C),
      finiteSubmoduleProjectionWithComplement
          (finiteRowsSubmodule
            (routeBRicherConcreteNPPrependedMultilinearRows
              M n hn2 htb hns))
          C hC
          (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
            M n hn2 htb hns) ≠ 0 := by
  rcases
    routeBRicherConcreteNPPrependedMultilinear_exists_rowSpanComplement_not_mem_firstSquareProbe
      M n hn2 htb hns with
    ⟨C, hC, hprobe⟩
  exact
    ⟨C, hC,
      routeBRicherConcreteNPPrependedMultilinear_projectionWithComplement_firstSquareProbe_ne_zero_of_not_mem
        M n hn2 htb hns C hC hprobe⟩

/-- There is an explicit-complement concrete projection policy for the row
span that is nonzero on the first-square probe. -/
theorem routeBRicherConcreteNPPrependedMultilinear_exists_complementPolicy_projectionWithComplement_ne_zero_firstSquareProbe
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    ∃ (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
      (hC :
        IsCompl
          (finiteRowsSubmodule
            (routeBRicherConcreteNPPrependedMultilinearRows
              M n hn2 htb hns))
          C),
      routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement
          M n hn2 htb hns C hC
          (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
            M n hn2 htb hns) ≠ 0 := by
  rcases
    routeBRicherConcreteNPPrependedMultilinear_exists_rowSpanComplement_not_mem_firstSquareProbe
      M n hn2 htb hns with
    ⟨C, hC, hprobe⟩
  exact
    ⟨C, hC,
      routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement_firstSquareProbe_ne_zero_of_not_mem
        M n hn2 htb hns C hC hprobe⟩

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

/-- Since the first-square probe is not in the concrete row span, the selected
finite-row projection cannot fix it. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_ne_self
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    routeBRicherConcreteNPPrependedMultilinearProjection
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns) ≠
      routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns := by
  intro hfix
  exact
    (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_not_mem_rowSpan
      M n hn2 htb hns)
      ((routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_mem_rowSpan_iff_projection_eq_self
        M n hn2 htb hns).mpr hfix)

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

/-- Avoiding the first-square selected-complement obstruction is exactly the
same as the selected projection being nonzero on the first-square probe. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_ne_zero_iff_not_mem_selectedComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    routeBRicherConcreteNPPrependedMultilinearProjection
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns) ≠ 0 ↔
      routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns ∉
        finiteSubmoduleProjectionComplement
          (finiteRowsSubmodule
            (routeBRicherConcreteNPPrependedMultilinearRows
              M n hn2 htb hns)) :=
  not_congr
    (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_eq_zero_iff_mem_selectedComplement
      M n hn2 htb hns)

/-! ## Explicit-policy replacement criteria -/

/-- Under the checked policy-realization equality, explicit-complement
descent is exactly descent for the selected finite-row projection. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement_iff_selectedProjectionDescent_of_realizesSelectedProjection
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (hpolicy :
      RouteBRicherConcreteNPPrependedMultilinearComplementRealizesSelectedProjection
        M n hn2 htb hns C hC) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement
        M n hn2 htb hns C hC ↔
      RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns := by
  dsimp [RouteBRicherConcreteNPPrependedMultilinearComplementRealizesSelectedProjection] at hpolicy
  constructor
  · intro hdesc spdpKappa ell p S shift
      hSlen hshiftDegree hshiftVars hadm
    change routeBSPDPGeneratorRow M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearProjection
          M n hn2 htb hns p)
        S shift =
      routeBRicherConcreteNPPrependedMultilinearProjection M n hn2 htb hns
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)
    rw [← hpolicy]
    exact hdesc spdpKappa ell p S shift
      hSlen hshiftDegree hshiftVars hadm
  · intro hdesc spdpKappa ell p S shift
      hSlen hshiftDegree hshiftVars hadm
    rw [hpolicy]
    exact hdesc spdpKappa ell p S shift
      hSlen hshiftDegree hshiftVars hadm

/-- Explicit-complement descent transfers to the selected projection only
after the explicit projection has been checked to realize the selected
policy. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionDescent_of_projectionWithComplementDescent_of_realizesSelectedProjection
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (hpolicy :
      RouteBRicherConcreteNPPrependedMultilinearComplementRealizesSelectedProjection
        M n hn2 htb hns C hC)
    (hdesc :
      RouteBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement
        M n hn2 htb hns C hC) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns :=
  (routeBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement_iff_selectedProjectionDescent_of_realizesSelectedProjection
    M n hn2 htb hns C hC hpolicy).mp hdesc

/-- Conversely, selected-projection descent can be restated for an explicit
policy once that policy has been checked to realize the selected projection. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionWithComplementDescent_of_projectionDescent_of_realizesSelectedProjection
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (hpolicy :
      RouteBRicherConcreteNPPrependedMultilinearComplementRealizesSelectedProjection
        M n hn2 htb hns C hC)
    (hdesc :
      RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement
        M n hn2 htb hns C hC :=
  (routeBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement_iff_selectedProjectionDescent_of_realizesSelectedProjection
    M n hn2 htb hns C hC hpolicy).mpr hdesc

/-- If an explicit first-square-avoiding complement is checked to be the
selected projection policy, then the selected projection is nonzero on the
first-square probe. -/
theorem routeBRicherConcreteNPPrependedMultilinear_selectedProjection_firstSquareProbe_ne_zero_of_realizesSelectedProjection
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (hpolicy :
      RouteBRicherConcreteNPPrependedMultilinearComplementRealizesSelectedProjection
        M n hn2 htb hns C hC)
    (hprobe :
      routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns ∉ C) :
    routeBRicherConcreteNPPrependedMultilinearProjection
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns) ≠ 0 := by
  dsimp [RouteBRicherConcreteNPPrependedMultilinearComplementRealizesSelectedProjection] at hpolicy
  rw [← hpolicy]
  exact
    routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement_firstSquareProbe_ne_zero_of_not_mem
      M n hn2 htb hns C hC hprobe

/-- The same checked replacement criterion gives first-square avoidance for
the selected complement. -/
theorem routeBRicherConcreteNPPrependedMultilinear_selectedComplement_firstSquareProbe_not_mem_of_realizesSelectedProjection
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (hpolicy :
      RouteBRicherConcreteNPPrependedMultilinearComplementRealizesSelectedProjection
        M n hn2 htb hns C hC)
    (hprobe :
      routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns ∉ C) :
    routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns ∉
      finiteSubmoduleProjectionComplement
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns)) :=
  (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_ne_zero_iff_not_mem_selectedComplement
    M n hn2 htb hns).mp
    (routeBRicherConcreteNPPrependedMultilinear_selectedProjection_firstSquareProbe_ne_zero_of_realizesSelectedProjection
      M n hn2 htb hns C hC hpolicy hprobe)

/-- There is an explicit first-square-avoiding complement policy; to replace
the arbitrary selected projection by that policy, one must additionally prove
that the explicit projection realizes the selected projection map. -/
theorem routeBRicherConcreteNPPrependedMultilinear_exists_firstSquareAvoidingComplementPolicy_with_selectedReplacementCriterion
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    ∃ (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
      (hC :
        IsCompl
          (finiteRowsSubmodule
            (routeBRicherConcreteNPPrependedMultilinearRows
              M n hn2 htb hns))
          C),
      routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns ∉ C ∧
        (RouteBRicherConcreteNPPrependedMultilinearComplementRealizesSelectedProjection
            M n hn2 htb hns C hC ->
          routeBRicherConcreteNPPrependedMultilinearProjection
              M n hn2 htb hns
              (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
                M n hn2 htb hns) ≠ 0 ∧
            routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
                M n hn2 htb hns ∉
              finiteSubmoduleProjectionComplement
                (finiteRowsSubmodule
                  (routeBRicherConcreteNPPrependedMultilinearRows
                    M n hn2 htb hns))) := by
  rcases
    routeBRicherConcreteNPPrependedMultilinear_exists_rowSpanComplement_not_mem_firstSquareProbe
      M n hn2 htb hns with
    ⟨C, hC, hprobe⟩
  refine ⟨C, hC, hprobe, ?_⟩
  intro hpolicy
  exact
    ⟨routeBRicherConcreteNPPrependedMultilinear_selectedProjection_firstSquareProbe_ne_zero_of_realizesSelectedProjection
        M n hn2 htb hns C hC hpolicy hprobe,
      routeBRicherConcreteNPPrependedMultilinear_selectedComplement_firstSquareProbe_not_mem_of_realizesSelectedProjection
        M n hn2 htb hns C hC hpolicy hprobe⟩

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

/-- The selected-kernel residual of the first-square probe is nonzero: the
selected projection cannot fix a probe that is not in the row span. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_residual_ne_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns -
      routeBRicherConcreteNPPrependedMultilinearProjection
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns) ≠ 0 := by
  intro hzero
  have hfix :
      routeBRicherConcreteNPPrependedMultilinearProjection
          M n hn2 htb hns
          (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
            M n hn2 htb hns) =
        routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns := by
    exact (sub_eq_zero.mp hzero).symm
  exact
    (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_ne_self
      M n hn2 htb hns) hfix

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

/-- Under projection descent, the first-square probe must split nontrivially:
the selected row-span component is nonzero but not the whole probe, while the
selected complement contains exactly the nonzero residual rather than the
probe itself. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_nontrivial_split_of_projectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdesc :
      RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns) :
    routeBRicherConcreteNPPrependedMultilinearProjection
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns) ∈
        finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns) ∧
      routeBRicherConcreteNPPrependedMultilinearProjection
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns) ≠ 0 ∧
      routeBRicherConcreteNPPrependedMultilinearProjection
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns) ≠
        routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns ∧
      routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns -
        routeBRicherConcreteNPPrependedMultilinearProjection
          M n hn2 htb hns
          (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
            M n hn2 htb hns) ∈
          finiteSubmoduleProjectionComplement
            (finiteRowsSubmodule
              (routeBRicherConcreteNPPrependedMultilinearRows
                M n hn2 htb hns)) ∧
      routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns ∉
        finiteSubmoduleProjectionComplement
          (finiteRowsSubmodule
            (routeBRicherConcreteNPPrependedMultilinearRows
              M n hn2 htb hns)) := by
  exact
    ⟨routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_mem_rowSpan
        M n hn2 htb hns,
      routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_ne_zero_of_projectionDescent
        M n hn2 htb hns hdesc,
      routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_ne_self
        M n hn2 htb hns,
      routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_residual_mem_selectedComplement
        M n hn2 htb hns,
      routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_not_mem_selectedComplement_of_projectionDescent
        M n hn2 htb hns hdesc⟩

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

/-- Descent is equivalent to the kernel-generator criterion together with
first-square avoidance by the selected complement.  The avoidance conjunct is
therefore a consequence of descent, not a consequence of row-span
nonmembership alone. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_kernelGenerator_zero_and_firstSquareProbe_not_mem_selectedComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns ↔
      RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZero
          M n hn2 htb hns ∧
        routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns ∉
          finiteSubmoduleProjectionComplement
            (finiteRowsSubmodule
              (routeBRicherConcreteNPPrependedMultilinearRows
                M n hn2 htb hns)) := by
  constructor
  · intro hdesc
    exact
      ⟨(routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_kernelGenerator_zero
          M n hn2 htb hns).mp hdesc,
        routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_not_mem_selectedComplement_of_projectionDescent
          M n hn2 htb hns hdesc⟩
  · intro h
    exact
      (routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_kernelGenerator_zero
        M n hn2 htb hns).mpr h.1

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
#print axioms routeBRicherConcreteNPPrependedMultilinearKernelGeneratorZero_iff_selectedComplement_generator_zero
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_selectedComplement_generator_zero
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
#print axioms routeBRicherConcreteNPWitnessRows_zero_coeff_firstVar_square
#print axioms routeBRicherMultilinearTailRows_coeff_var_square
#print axioms routeBRicherMultilinearTailRows_coeff_firstVar_square
#print axioms routeBRicherConcreteNPPrependedMultilinearRows_coeff_firstVar_square_eq_secondVar_square
#print axioms routeBRicherConcreteNPPrependedMultilinear_rowSpan_coeff_firstVar_square_eq_secondVar_square
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_not_mem_rowSpan
#print axioms routeBRicherConcreteNPPrependedMultilinear_exists_rowSpanComplement_mem_firstSquareProbe
#print axioms routeBRicherConcreteNPPrependedMultilinear_exists_complementPolicy_kills_firstSquareProbe
#print axioms routeBRicherConcreteNPPrependedMultilinearRows_zero_coeff_firstVar_square
#print axioms routeBRicherConcreteNPPrependedMultilinear_rowSpan_exists_ne_zero
#print axioms routeBRicherConcreteNPPrependedMultilinear_exists_rowSpanComplement_not_mem_firstSquareProbe
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement
#print axioms RouteBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement
#print axioms RouteBRicherConcreteNPPrependedMultilinearComplementRealizesSelectedProjection
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement_apply_eq_zero_iff
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement_firstSquareProbe_ne_zero_iff_not_mem
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement_firstSquareProbe_ne_zero_of_not_mem
#print axioms routeBRicherConcreteNPPrependedMultilinear_projectionWithComplement_firstSquareProbe_ne_zero_of_not_mem
#print axioms routeBRicherConcreteNPPrependedMultilinear_exists_complementPolicy_projection_ne_zero_firstSquareProbe
#print axioms routeBRicherConcreteNPPrependedMultilinear_exists_complementPolicy_projectionWithComplement_ne_zero_firstSquareProbe
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_mem_rowSpan
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_mem_rowSpan_iff_projection_eq_self
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_ne_self
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_eq_self_of_mem_rowSpan
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_ne_zero_of_mem_rowSpan
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_eq_zero_iff_mem_selectedComplement
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_ne_zero_iff_not_mem_selectedComplement
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement_iff_selectedProjectionDescent_of_realizesSelectedProjection
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionDescent_of_projectionWithComplementDescent_of_realizesSelectedProjection
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionWithComplementDescent_of_projectionDescent_of_realizesSelectedProjection
#print axioms routeBRicherConcreteNPPrependedMultilinear_selectedProjection_firstSquareProbe_ne_zero_of_realizesSelectedProjection
#print axioms routeBRicherConcreteNPPrependedMultilinear_selectedComplement_firstSquareProbe_not_mem_of_realizesSelectedProjection
#print axioms routeBRicherConcreteNPPrependedMultilinear_exists_firstSquareAvoidingComplementPolicy_with_selectedReplacementCriterion
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_residual_mem_selectedComplement
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_residual_ne_zero
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_not_mem_rowSpan_and_selectedComplement
#print axioms routeBRicherConcreteNPPrependedMultilinear_not_kernelGenerator_zero_of_firstSquareProbe_kernel
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_of_firstSquareProbe_kernel
#print axioms routeBRicherConcreteNPPrependedMultilinear_not_projectionDescent_of_firstSquareProbe_kernel
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_projection_ne_zero_of_projectionDescent
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_not_mem_selectedComplement_of_projectionDescent
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_nontrivial_split_of_projectionDescent
#print axioms routeBRicherConcreteNPPrependedMultilinear_not_projectionDescent_of_firstSquareProbe_mem_selectedComplement
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_kernelGenerator_zero_and_firstSquareProbe_not_mem_selectedComplement
#print axioms routeBRicherConcreteNPPrependedMultilinearProjection_ne_explicitProjection_of_projectionDescent
#print axioms routeBRicherConcreteNPPrependedMultilinear_not_kernelGenerator_zero_of_explicitComplement_le_projectionKernel
#print axioms routeBRicherConcreteNPPrependedMultilinear_not_explicitComplement_le_projectionKernel_of_projectionDescent

end PallLean.Paper93.Paper283
