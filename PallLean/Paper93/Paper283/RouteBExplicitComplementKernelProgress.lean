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
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement_spdpMapPreimage_of_kernelGenerator_zeroWithComplement
#print axioms routeBRicherConcreteNPPrependedMultilinear_exists_firstSquareAvoidingComplementPolicy_with_kernelNecessaryConditions_and_directSPDP

end PallLean.Paper93.Paper283
