import PallLean.Paper93.Paper283.RouteBExplicitComplementProjectionPolicyProgress

/-!
# Route B explicit-complement kernel progress

This file sharpens the explicit-complement projection frontier.  The
first-square-avoiding complement removes the old immediate singleton-kernel
obstruction, but it does not by itself prove generator annihilation on the
whole chosen complement.  The results below record the exact necessary
conditions and the direct downstream wrappers available once that kernel
generator-zero condition is supplied.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- If generator-zero holds on an explicit complement, every vector in that
complement has zero multilinear projection.

This is the degree-zero generator test (`S = []`, `shift = 1`).  It is the
first unavoidable compatibility condition for any successful explicit
first-square-avoiding policy. -/
theorem routeBRicherConcreteNPPrependedMultilinearKernelGeneratorZeroWithComplement_implies_complement_mlProj_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (hzero :
      RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZeroWithComplement
        M n hn2 htb hns C hC)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (hpC : p ∈ C) :
    mlProj p = 0 := by
  have hrow :=
    hzero 0 0 p
      ([] : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
      (1 : SATDeciderGaugeSpace M n hn2 htb hns)
      (by simp)
      (by simp [MvPolynomial.totalDegree_one])
      (by simp [MvPolynomial.vars_one])
      (by simp [SPDP.isBlockAdmissible])
      hpC
  simpa [routeBSPDPGeneratorRow] using hrow

/-- A single complement vector with nonzero multilinear projection refutes
explicit-complement generator-zero. -/
theorem routeBRicherConcreteNPPrependedMultilinear_not_kernelGeneratorZeroWithComplement_of_complement_mlProj_ne_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (hbad :
      ∃ p : SATDeciderGaugeSpace M n hn2 htb hns,
        p ∈ C ∧ mlProj p ≠ 0) :
    ¬ RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZeroWithComplement
        M n hn2 htb hns C hC := by
  intro hzero
  rcases hbad with ⟨p, hpC, hml⟩
  exact hml
    (routeBRicherConcreteNPPrependedMultilinearKernelGeneratorZeroWithComplement_implies_complement_mlProj_zero
      M n hn2 htb hns C hC hzero p hpC)

/-- If an explicit complement contains the first-square probe, generator-zero
is impossible: the singleton derivative row is visibly nonzero. -/
theorem routeBRicherConcreteNPPrependedMultilinear_not_kernelGeneratorZeroWithComplement_of_firstSquareProbe_mem
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (hprobeC :
      routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns ∈ C) :
    ¬ RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZeroWithComplement
        M n hn2 htb hns C hC := by
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
      hprobeC
  exact
    (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_singletonRow_ne_zero
      M n hn2 htb hns) hrowZero

/-- Therefore first-square avoidance is not just convenient: it is necessary
for explicit-complement generator-zero. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_not_mem_of_kernelGeneratorZeroWithComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (hzero :
      RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZeroWithComplement
        M n hn2 htb hns C hC) :
    routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns ∉ C := by
  intro hprobeC
  exact
    (routeBRicherConcreteNPPrependedMultilinear_not_kernelGeneratorZeroWithComplement_of_firstSquareProbe_mem
      M n hn2 htb hns C hC hprobeC) hzero

/-- Projection descent for an explicit complement also forces that complement
to lie in the kernel of the canonical multilinear projection. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement_implies_complement_mlProj_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (hdesc :
      RouteBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement
        M n hn2 htb hns C hC)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (hpC : p ∈ C) :
    mlProj p = 0 :=
  routeBRicherConcreteNPPrependedMultilinearKernelGeneratorZeroWithComplement_implies_complement_mlProj_zero
    M n hn2 htb hns C hC
    ((routeBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement_iff_kernelGenerator_zeroWithComplement
      M n hn2 htb hns C hC).mp hdesc)
    p hpC

/-- The first-square residual determined by an explicit complement. -/
noncomputable def routeBRicherConcreteNPPrependedMultilinearFirstSquareResidualWithComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C) :
    SATDeciderGaugeSpace M n hn2 htb hns :=
  routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
      M n hn2 htb hns -
    routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement
      M n hn2 htb hns C hC
      (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns)

/-- The explicit-complement first-square residual lies in the supplied
complement. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareResidualWithComplement_mem
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C) :
    routeBRicherConcreteNPPrependedMultilinearFirstSquareResidualWithComplement
        M n hn2 htb hns C hC ∈ C := by
  let Pi :=
    routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement
      M n hn2 htb hns C hC
  let probe :=
    routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
      M n hn2 htb hns
  have hPiPi : Pi (Pi probe) = Pi probe := by
    have hidem :=
      (routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement
        M n hn2 htb hns C hC).is_idempotent
    have happ := congrArg (fun L => L probe) hidem
    simpa [Pi, routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement,
      routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement,
      LinearMap.comp_apply] using happ
  have hzero : Pi (probe - Pi probe) = 0 := by
    simp [Pi, map_sub, hPiPi]
  simpa [Pi, probe,
    routeBRicherConcreteNPPrependedMultilinearFirstSquareResidualWithComplement] using
    (routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement_apply_eq_zero_iff
      M n hn2 htb hns C hC (probe - Pi probe)).mp hzero

private theorem routeBExplicitComplementKernel_coeff_single_pderiv_eq_two_mul_coeff_square
    {N : Nat} (v : Fin N) (p : MvPolynomial (Fin N) Rat) :
    MvPolynomial.coeff (Finsupp.single v 1) (MvPolynomial.pderiv v p) =
      (2 : Rat) * MvPolynomial.coeff (Finsupp.single v 2) p := by
  classical
  conv_lhs => rw [p.as_sum, map_sum, MvPolynomial.coeff_sum]
  conv_rhs => rw [p.as_sum, MvPolynomial.coeff_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro α hα
  simp only [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial]
  by_cases hαsquare : α = Finsupp.single v 2
  · subst α
    have hsub :
        (Finsupp.single v 2 - Finsupp.single v 1 : Fin N →₀ Nat) =
          Finsupp.single v 1 := by
      ext i
      by_cases hi : i = v
      · subst i
        simp
      · simp [Finsupp.single_eq_of_ne hi]
    simp [hsub, mul_comm]
  · by_cases hsub : α - Finsupp.single v 1 = Finsupp.single v 1
    · have hα_eq : α = Finsupp.single v 2 := by
        ext i
        by_cases hi : i = v
        · subst i
          have hcoord := congrArg (fun β : Fin N →₀ Nat => β v) hsub
          have hcoord' : α v - 1 = 1 := by
            simpa [Finsupp.single_eq_same] using hcoord
          have hv : α v = 2 := by omega
          simpa [Finsupp.single_eq_same] using hv
        · have hcoord := congrArg (fun β : Fin N →₀ Nat => β i) hsub
          simpa [Finsupp.single_eq_of_ne hi] using hcoord
      exact False.elim (hαsquare hα_eq)
    · simp [hαsquare, hsub]

private theorem routeBExplicitComplementKernel_coeff_singletonRow_eq_two_mul_squareCoeff
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (v : Fin (RouteBCookLevinDim M n hn2 htb hns))
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    MvPolynomial.coeff (Finsupp.single v 1)
        (routeBSPDPGeneratorRow M n hn2 htb hns p [v]
          (1 : SATDeciderGaugeSpace M n hn2 htb hns)) =
      (2 : Rat) * MvPolynomial.coeff (Finsupp.single v 2) p := by
  change
    MvPolynomial.coeff (Finsupp.single v 1)
        (mlProj
          ((1 : SATDeciderGaugeSpace M n hn2 htb hns) *
            SPDP.iterDerivList [v] p)) =
      (2 : Rat) * MvPolynomial.coeff (Finsupp.single v 2) p
  rw [one_mul]
  rw [MultilinearSPDP.coeff_mlProj_of_isMultilinear_mono]
  · unfold SPDP.iterDerivList
    exact routeBExplicitComplementKernel_coeff_single_pderiv_eq_two_mul_coeff_square v p
  · intro i
    by_cases hi : i = v
    · subst i
      simp
    · simp [Finsupp.single_eq_of_ne hi]

/-- Generator-zero forces the first-square residual's singleton generator row
to vanish.  This is the actual residual condition left after choosing a
first-square-avoiding complement. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareResidualWithComplement_singletonGenerator_zero_of_kernelGeneratorZeroWithComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (hzero :
      RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZeroWithComplement
        M n hn2 htb hns C hC) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareResidualWithComplement
          M n hn2 htb hns C hC)
        [satDeciderGaugeFirstVar M n hn2 htb hns]
        (1 : SATDeciderGaugeSpace M n hn2 htb hns) = 0 :=
  hzero 1 0
    (routeBRicherConcreteNPPrependedMultilinearFirstSquareResidualWithComplement
      M n hn2 htb hns C hC)
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
    (routeBRicherConcreteNPPrependedMultilinearFirstSquareResidualWithComplement_mem
      M n hn2 htb hns C hC)

/-- Any explicit-complement generator-zero proof is blocked by the
first/second pure-square residual.

The argument uses the common-kernel condition, not just first-square
avoidance.  The residual of the first-square probe lies in the supplied
complement.  Generator-zero would force both its first and second singleton
derivative rows to vanish.  The first singleton row then forces the projected
row-span component to have first-square coefficient `1`; the concrete row-span
coefficient equality forces its second-square coefficient to be `1` as well;
but the original probe has second-square coefficient `0`, so the second
singleton row is visibly nonzero. -/
theorem routeBRicherConcreteNPPrependedMultilinear_not_kernelGeneratorZeroWithComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C) :
    ¬ RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZeroWithComplement
        M n hn2 htb hns C hC := by
  intro hzero
  let rows := routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns
  let Pi :=
    routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement
      M n hn2 htb hns C hC
  let probe :=
    routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
      M n hn2 htb hns
  let residual :=
    routeBRicherConcreteNPPrependedMultilinearFirstSquareResidualWithComplement
      M n hn2 htb hns C hC
  let first := satDeciderGaugeFirstVar M n hn2 htb hns
  let second := satDeciderGaugeSecondVar M n hn2 htb hns
  have hresC : residual ∈ C := by
    simpa [residual] using
      routeBRicherConcreteNPPrependedMultilinearFirstSquareResidualWithComplement_mem
        M n hn2 htb hns C hC
  have hPiMem :
      Pi probe ∈ finiteRowsSubmodule rows := by
    have hrange :=
      routeBRicherFiniteRowsCandidateGaugeWithComplement_range
        M n hn2 htb hns rows C hC
    have hmemRange :
        Pi probe ∈
          LinearMap.range
            (routeBRicherFiniteRowsCandidateGaugeWithComplement
              M n hn2 htb hns rows C hC).projection := by
      exact ⟨probe, rfl⟩
    simpa [Pi, rows, routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement,
      routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement] using
      (by simpa [hrange] using hmemRange)
  have hrowCoeffEq :=
    routeBRicherConcreteNPPrependedMultilinear_rowSpan_coeff_firstVar_square_eq_secondVar_square
      M n hn2 htb hns hPiMem
  have hfirstRowZero :
      routeBSPDPGeneratorRow M n hn2 htb hns residual [first]
          (1 : SATDeciderGaugeSpace M n hn2 htb hns) = 0 := by
    exact
      hzero 1 0 residual [first]
        (1 : SATDeciderGaugeSpace M n hn2 htb hns)
        (by simp [first])
        (by simp [MvPolynomial.totalDegree_one])
        (by simp [MvPolynomial.vars_one])
        (by
          constructor
          · simp [first]
          · intro b
            simpa [first] using
              (List.length_filter_le
                (fun i =>
                  (cook_levin_compilation M n hn2 htb hns).partition.assign i = b)
                [satDeciderGaugeFirstVar M n hn2 htb hns]))
        hresC
  have hfirstSquareResidual_zero :
      MvPolynomial.coeff (Finsupp.single first 2) residual = 0 := by
    have hcoeffZero :
        MvPolynomial.coeff (Finsupp.single first 1)
            (routeBSPDPGeneratorRow M n hn2 htb hns residual [first]
              (1 : SATDeciderGaugeSpace M n hn2 htb hns)) = 0 := by
      rw [hfirstRowZero]
      simp
    rw [routeBExplicitComplementKernel_coeff_singletonRow_eq_two_mul_squareCoeff
      M n hn2 htb hns first residual] at hcoeffZero
    nlinarith
  have hPiFirst :
      MvPolynomial.coeff (Finsupp.single first 2) (Pi probe) = 1 := by
    have hfirstProbe :=
      routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_coeff_firstVar_square
        M n hn2 htb hns
    have hres :
        MvPolynomial.coeff (Finsupp.single first 2) (probe - Pi probe) = 0 := by
      simpa [residual,
        routeBRicherConcreteNPPrependedMultilinearFirstSquareResidualWithComplement,
        Pi, probe, first] using hfirstSquareResidual_zero
    rw [MvPolynomial.coeff_sub] at hres
    have hprobeFirst :
        MvPolynomial.coeff (Finsupp.single first 2) probe = 1 := by
      simpa [probe, first] using hfirstProbe
    nlinarith
  have hPiSecond :
      MvPolynomial.coeff (Finsupp.single second 2) (Pi probe) = 1 := by
    simpa [first, second] using hrowCoeffEq.symm.trans hPiFirst
  have hsecondSquareResidual :
      MvPolynomial.coeff (Finsupp.single second 2) residual = -1 := by
    have hsecondProbe :=
      routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_coeff_secondVar_square
        M n hn2 htb hns
    have hres :
        MvPolynomial.coeff (Finsupp.single second 2) residual =
          MvPolynomial.coeff (Finsupp.single second 2) probe -
            MvPolynomial.coeff (Finsupp.single second 2) (Pi probe) := by
      simp [residual,
        routeBRicherConcreteNPPrependedMultilinearFirstSquareResidualWithComplement,
        Pi, probe, second, MvPolynomial.coeff_sub]
    rw [hres]
    have hprobeSecond :
        MvPolynomial.coeff (Finsupp.single second 2) probe = 0 := by
      simpa [probe, second] using hsecondProbe
    nlinarith
  have hsecondRowZero :
      routeBSPDPGeneratorRow M n hn2 htb hns residual [second]
          (1 : SATDeciderGaugeSpace M n hn2 htb hns) = 0 := by
    exact
      hzero 1 0 residual [second]
        (1 : SATDeciderGaugeSpace M n hn2 htb hns)
        (by simp [second])
        (by simp [MvPolynomial.totalDegree_one])
        (by simp [MvPolynomial.vars_one])
        (by
          constructor
          · simp [second]
          · intro b
            simpa [second] using
              (List.length_filter_le
                (fun i =>
                  (cook_levin_compilation M n hn2 htb hns).partition.assign i = b)
                [satDeciderGaugeSecondVar M n hn2 htb hns]))
        hresC
  have hsecondCoeffZero :
      MvPolynomial.coeff (Finsupp.single second 1)
          (routeBSPDPGeneratorRow M n hn2 htb hns residual [second]
            (1 : SATDeciderGaugeSpace M n hn2 htb hns)) = 0 := by
    rw [hsecondRowZero]
    simp
  rw [routeBExplicitComplementKernel_coeff_singletonRow_eq_two_mul_squareCoeff
    M n hn2 htb hns second residual] at hsecondCoeffZero
  rw [hsecondSquareResidual] at hsecondCoeffZero
  norm_num at hsecondCoeffZero

/-- Consequently, no explicit-complement projection can satisfy the concrete
multilinear-tail descent condition. -/
theorem routeBRicherConcreteNPPrependedMultilinear_not_projectionDescentWithComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C) :
    ¬ RouteBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement
        M n hn2 htb hns C hC := by
  intro hdesc
  exact
    (routeBRicherConcreteNPPrependedMultilinear_not_kernelGeneratorZeroWithComplement
      M n hn2 htb hns C hC)
      ((routeBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement_iff_kernelGenerator_zeroWithComplement
        M n hn2 htb hns C hC).mp hdesc)

/-- There is no complement to the concrete prepended multilinear row span that
lies in the common kernel of all Route B SPDP generator maps. -/
theorem routeBRicherConcreteNPPrependedMultilinear_no_rowSpanComplement_kernelGeneratorZeroWithComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    ¬ ∃ (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
        (hC :
          IsCompl
            (finiteRowsSubmodule
              (routeBRicherConcreteNPPrependedMultilinearRows
                M n hn2 htb hns))
            C),
        RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZeroWithComplement
          M n hn2 htb hns C hC := by
  rintro ⟨C, hC, hzero⟩
  exact
    (routeBRicherConcreteNPPrependedMultilinear_not_kernelGeneratorZeroWithComplement
      M n hn2 htb hns C hC) hzero

/-- The arbitrary complement selected by `finiteSubmoduleProjectionComplement`
realizes the selected finite-row projection policy. -/
theorem routeBRicherConcreteNPPrependedMultilinear_selectedComplement_realizesSelectedProjection
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherConcreteNPPrependedMultilinearComplementRealizesSelectedProjection
      M n hn2 htb hns
      (finiteSubmoduleProjectionComplement
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns)))
      (finiteSubmoduleProjection_isCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))) := by
  rfl

/-- The selected finite-row complement for the broad multilinear tail cannot
lie in the common kernel of all Route B SPDP generator maps. -/
theorem routeBRicherConcreteNPPrependedMultilinear_not_kernelGenerator_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    ¬ RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZero
        M n hn2 htb hns := by
  intro hzero
  let rows := routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns
  let C :=
    finiteSubmoduleProjectionComplement
      (finiteRowsSubmodule rows)
  let hC : IsCompl (finiteRowsSubmodule rows) C :=
    finiteSubmoduleProjection_isCompl (finiteRowsSubmodule rows)
  have hzeroC :
      RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZeroWithComplement
        M n hn2 htb hns C hC := by
    intro spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm hpC
    have hproj :
        routeBRicherConcreteNPPrependedMultilinearProjection
          M n hn2 htb hns p = 0 := by
      simpa [rows, C, hC, routeBRicherConcreteNPPrependedMultilinearProjection,
        routeBRicherConcreteNPPrependedMultilinearGauge] using
        (routeBRicherFiniteRowsCandidateGauge_projection_apply_eq_zero_iff
          M n hn2 htb hns rows p).mpr hpC
    exact hzero spdpKappa ell p S shift
      hSlen hshiftDegree hshiftVars hadm hproj
  exact
    (routeBRicherConcreteNPPrependedMultilinear_not_kernelGeneratorZeroWithComplement
      M n hn2 htb hns C hC) hzeroC

/-- The selected finite-row kernel compatibility condition is false for the
current broad multilinear-tail row target. -/
theorem routeBRicherConcreteNPPrependedMultilinearRows_not_kernelCompatibility
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    ¬ RouteBRicherGaugeFiniteRowsSPDPKernelCompatibility M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns) := by
  intro hker
  have hres :
      RouteBRicherConcreteNPPrependedMultilinearResidualGeneratorZero
        M n hn2 htb hns :=
    (routeBRicherConcreteNPPrependedMultilinearRows_kernelCompatibility_iff_residualGenerator_zero
      M n hn2 htb hns).mp hker
  exact
    (routeBRicherConcreteNPPrependedMultilinear_not_kernelGenerator_zero
      M n hn2 htb hns)
      ((routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_iff_kernelGenerator_zero
        M n hn2 htb hns).mp hres)

/-- Therefore the current selected finite-row projection for the broad
multilinear tail cannot satisfy projection descent/kernel compatibility. -/
theorem routeBRicherConcreteNPPrependedMultilinear_not_projectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    ¬ RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns := by
  intro hdesc
  exact
    (routeBRicherConcreteNPPrependedMultilinear_not_kernelGenerator_zero
      M n hn2 htb hns)
      ((routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_kernelGenerator_zero
        M n hn2 htb hns).mp hdesc)

/-- The selected broad multilinear-tail projection has a concrete admissible
generator row witnessing projection escape. -/
theorem routeBRicherConcreteNPPrependedMultilinear_projectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns :=
  (routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_projectionDescent
    M n hn2 htb hns).mpr
    (routeBRicherConcreteNPPrependedMultilinear_not_projectionDescent
      M n hn2 htb hns)

/-- Kernel-generator-zero gives the direct explicit-complement map-preimage
surface, without identifying the explicit projection with the selected
projection. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement_spdpMapPreimage_of_kernelGenerator_zeroWithComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (hzero :
      RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZeroWithComplement
        M n hn2 htb hns C hC) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionWithComplementSPDPMapPreimage
        M n hn2 htb hns C hC :=
  routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement_spdpMapPreimage_of_projectionWithComplementDescent
    M n hn2 htb hns C hC
    ((routeBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement_iff_kernelGenerator_zeroWithComplement
      M n hn2 htb hns C hC).mpr hzero)

/-- Existential explicit-complement policy package with the direct downstream
SPDP surfaces.  The package keeps the remaining obligation as generator-zero
on the same explicit complement; it does not claim that the selected
projection has been realized. -/
theorem routeBRicherConcreteNPPrependedMultilinear_exists_firstSquareAvoidingComplementPolicy_with_kernelNecessaryConditions_and_directSPDP
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
        (RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZeroWithComplement
            M n hn2 htb hns C hC ->
          (forall p : SATDeciderGaugeSpace M n hn2 htb hns,
            p ∈ C -> mlProj p = 0) ∧
          RouteBRicherConcreteNPPrependedMultilinearProjectionWithComplementSPDPMapPreimage
            M n hn2 htb hns C hC ∧
          RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
            (routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement
              M n hn2 htb hns C hC)) := by
  rcases
    routeBRicherConcreteNPPrependedMultilinear_exists_rowSpanComplement_not_mem_firstSquareProbe
      M n hn2 htb hns with
    ⟨C, hC, hprobe⟩
  refine ⟨C, hC, hprobe, ?_⟩
  intro hzero
  exact
    ⟨fun p hpC =>
        routeBRicherConcreteNPPrependedMultilinearKernelGeneratorZeroWithComplement_implies_complement_mlProj_zero
          M n hn2 htb hns C hC hzero p hpC,
      routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement_spdpMapPreimage_of_kernelGenerator_zeroWithComplement
        M n hn2 htb hns C hC hzero,
      routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_spdpSubspaceContainment_of_kernelGenerator_zeroWithComplement
        M n hn2 htb hns C hC hzero⟩

/-! ## Axiom audit anchors -/

#print axioms routeBRicherConcreteNPPrependedMultilinearKernelGeneratorZeroWithComplement_implies_complement_mlProj_zero
#print axioms routeBRicherConcreteNPPrependedMultilinear_not_kernelGeneratorZeroWithComplement_of_complement_mlProj_ne_zero
#print axioms routeBRicherConcreteNPPrependedMultilinear_not_kernelGeneratorZeroWithComplement_of_firstSquareProbe_mem
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_not_mem_of_kernelGeneratorZeroWithComplement
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement_implies_complement_mlProj_zero
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareResidualWithComplement_mem
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareResidualWithComplement_singletonGenerator_zero_of_kernelGeneratorZeroWithComplement
#print axioms routeBRicherConcreteNPPrependedMultilinear_not_kernelGeneratorZeroWithComplement
#print axioms routeBRicherConcreteNPPrependedMultilinear_not_projectionDescentWithComplement
#print axioms routeBRicherConcreteNPPrependedMultilinear_no_rowSpanComplement_kernelGeneratorZeroWithComplement
#print axioms routeBRicherConcreteNPPrependedMultilinear_selectedComplement_realizesSelectedProjection
#print axioms routeBRicherConcreteNPPrependedMultilinear_not_kernelGenerator_zero
#print axioms routeBRicherConcreteNPPrependedMultilinearRows_not_kernelCompatibility
#print axioms routeBRicherConcreteNPPrependedMultilinear_not_projectionDescent
#print axioms routeBRicherConcreteNPPrependedMultilinear_projectionEscapeWitness
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement_spdpMapPreimage_of_kernelGenerator_zeroWithComplement
#print axioms routeBRicherConcreteNPPrependedMultilinear_exists_firstSquareAvoidingComplementPolicy_with_kernelNecessaryConditions_and_directSPDP

end PallLean.Paper93.Paper283
