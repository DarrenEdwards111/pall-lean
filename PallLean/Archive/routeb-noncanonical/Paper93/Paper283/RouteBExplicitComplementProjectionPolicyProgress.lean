import PallLean.Paper93.Paper283.RouteBExplicitComplementProjectionAssembly

/-!
# Route B explicit-complement projection policy progress

This file keeps the Route B projection policy on the explicit-complement
surface.  It does not assert that the caller-supplied complement is the
arbitrary selected finite-row complement.  Instead it exposes the direct
with-complement SPDP containment statement and the exact generator-compatibility
obligation for that chosen complement.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- The explicit-complement concrete multilinear-tail finite-row gauge. -/
noncomputable abbrev routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C) :
    PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns) :=
  routeBRicherFiniteRowsCandidateGaugeWithComplement M n hn2 htb hns
    (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns)
    C hC

/-- The explicit-complement finite-row gauge fixes every row-span element,
not only the named finite rows. -/
theorem routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_fixed_of_mem
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    {p : SATDeciderGaugeSpace M n hn2 htb hns}
    (hp :
      p ∈
        finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns)) :
    (routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement
        M n hn2 htb hns C hC).projection p = p := by
  haveI :
      Module.Finite Rat
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns)) :=
    finiteRowsSubmodule_finite
      (routeBRicherConcreteNPPrependedMultilinearRows
        M n hn2 htb hns)
  simpa [routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement,
    routeBRicherFiniteRowsCandidateGaugeWithComplement] using
    candidateGaugeOfFiniteSubmoduleWithComplement_fixed_of_mem
      (finiteRowsSubmodule
        (routeBRicherConcreteNPPrependedMultilinearRows
          M n hn2 htb hns))
      C hC hp

/-- Explicit-complement generator annihilation on the chosen complement.

This is the policy-local analogue of the selected-kernel generator-zero
frontier.  The input is membership in the caller-supplied complement `C`, not
membership in the arbitrary `Classical.choose` complement. -/
def RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZeroWithComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (_hC :
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
    p ∈ C ->
    routeBSPDPGeneratorRow M n hn2 htb hns p S shift = 0

/-- Explicit-complement descent is exactly generator annihilation on the
caller-supplied complement.

The proof uses the broad concrete multilinear-tail row family: every generator
row lands in the finite row span, so the explicit projection fixes it after
the complement-side residual is killed. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement_iff_kernelGenerator_zeroWithComplement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement
        M n hn2 htb hns C hC ↔
      RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZeroWithComplement
        M n hn2 htb hns C hC := by
  constructor
  · intro hdesc spdpKappa ell p S shift
      hSlen hshiftDegree hshiftVars hadm hpC
    let Pi :=
      routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement
        M n hn2 htb hns C hC
    have hker : Pi p = 0 := by
      simpa [Pi] using
        (routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement_apply_eq_zero_iff
          M n hn2 htb hns C hC p).mpr hpC
    have hdescP :=
      hdesc spdpKappa ell p S shift
        hSlen hshiftDegree hshiftVars hadm
    have hleft :
        routeBSPDPGeneratorRow M n hn2 htb hns
            (Pi p) S shift = 0 := by
      rw [hker]
      exact routeBSPDPGeneratorRow_zero M n hn2 htb hns S shift
    have hprojZero :
        Pi (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) = 0 := by
      rw [hleft] at hdescP
      exact hdescP.symm
    have hmem :
        routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∈
          finiteRowsSubmodule
            (routeBRicherConcreteNPPrependedMultilinearRows
              M n hn2 htb hns) := by
      exact
        routeBRicherConcreteNPPrependedMultilinearRows_mlProj_mem
          M n hn2 htb hns
          (shift * SPDP.iterDerivList S p)
    have hfixed :
        Pi (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) =
          routeBSPDPGeneratorRow M n hn2 htb hns p S shift := by
      simpa [Pi, routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement] using
        routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_fixed_of_mem
          M n hn2 htb hns C hC hmem
    rwa [hfixed] at hprojZero
  · intro hzero spdpKappa ell p S shift
      hSlen hshiftDegree hshiftVars hadm
    let Pi :=
      routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement
        M n hn2 htb hns C hC
    have hPiPi : Pi (Pi p) = Pi p := by
      have hidem :=
        (routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement
          M n hn2 htb hns C hC).is_idempotent
      have happ := congrArg (fun L => L p) hidem
      simpa [Pi, routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement,
        routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement,
        LinearMap.comp_apply] using happ
    have hresKer : Pi (p - Pi p) = 0 := by
      simp [Pi, map_sub, hPiPi]
    have hresC : p - Pi p ∈ C := by
      simpa [Pi] using
        (routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement_apply_eq_zero_iff
          M n hn2 htb hns C hC (p - Pi p)).mp hresKer
    have hrowZero :
        routeBSPDPGeneratorRow M n hn2 htb hns
            (p - Pi p) S shift = 0 :=
      hzero spdpKappa ell (p - Pi p) S shift
        hSlen hshiftDegree hshiftVars hadm hresC
    have hdecomp : Pi p + (p - Pi p) = p := by
      simp [sub_eq_add_neg, add_left_comm]
    have hrowDecomp :
        routeBSPDPGeneratorRow M n hn2 htb hns p S shift =
          routeBSPDPGeneratorRow M n hn2 htb hns (Pi p) S shift := by
      have hadd :=
        routeBSPDPGeneratorRow_add
          M n hn2 htb hns (Pi p) (p - Pi p) S shift
      rw [hdecomp] at hadd
      rw [hadd, hrowZero, add_zero]
    have hmem :
        routeBSPDPGeneratorRow M n hn2 htb hns (Pi p) S shift ∈
          finiteRowsSubmodule
            (routeBRicherConcreteNPPrependedMultilinearRows
              M n hn2 htb hns) := by
      exact
        routeBRicherConcreteNPPrependedMultilinearRows_mlProj_mem
          M n hn2 htb hns
          (shift * SPDP.iterDerivList S (Pi p))
    have hfixed :
        Pi (routeBSPDPGeneratorRow M n hn2 htb hns (Pi p) S shift) =
          routeBSPDPGeneratorRow M n hn2 htb hns (Pi p) S shift := by
      simpa [Pi, routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement] using
        routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_fixed_of_mem
          M n hn2 htb hns C hC hmem
    rw [hrowDecomp]
    exact hfixed.symm

/-- Explicit-complement descent gives SPDP containment for the explicit
with-complement finite-row gauge directly.

This bypasses the arbitrary selected finite-row projection.  It is the
projection-policy surface needed by any downstream Route B wrapper that is
parametrized by the chosen explicit complement. -/
theorem routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_spdpSubspaceContainment_of_projectionWithComplementDescent
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
        M n hn2 htb hns C hC) :
    RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
      (routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement
        M n hn2 htb hns C hC) := by
  intro spdpKappa ell p
  apply Submodule.span_le.mpr
  rintro q ⟨S, shift, hSlen, hshiftDegree, hshiftVars, hadm, hq⟩
  rw [hq]
  have preimage :
      RouteBRicherConcreteNPPrependedMultilinearProjectionWithComplementSPDPMapPreimage
        M n hn2 htb hns C hC :=
    routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement_spdpMapPreimage_of_projectionWithComplementDescent
      M n hn2 htb hns C hC hdesc
  rcases preimage.map_preimage
      spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm with
    ⟨raw, hraw, hmap⟩
  refine Submodule.mem_map.mpr ⟨raw, hraw, ?_⟩
  simpa [routeBRicherConcreteNPPrependedMultilinearProjectionWithComplement,
    routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement] using hmap

/-- Generator-annihilation on the chosen complement is enough for direct
explicit-complement SPDP containment. -/
theorem routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_spdpSubspaceContainment_of_kernelGenerator_zeroWithComplement
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
    RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
      (routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement
        M n hn2 htb hns C hC) :=
  routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_spdpSubspaceContainment_of_projectionWithComplementDescent
    M n hn2 htb hns C hC
    ((routeBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement_iff_kernelGenerator_zeroWithComplement
      M n hn2 htb hns C hC).mpr hzero)

/-- There is a first-square-avoiding explicit complement policy, and for any
such chosen policy the remaining SPDP obligation is exactly generator
annihilation on that same complement.

This packages the faithful projection-policy fork without claiming that the
arbitrary selected finite-row projection realizes the displayed complement. -/
theorem routeBRicherConcreteNPPrependedMultilinear_exists_firstSquareAvoidingComplementPolicy_with_directSPDPFrontier
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
        (RouteBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement
            M n hn2 htb hns C hC ↔
          RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZeroWithComplement
            M n hn2 htb hns C hC) ∧
        (RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZeroWithComplement
            M n hn2 htb hns C hC ->
          RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
            (routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement
              M n hn2 htb hns C hC)) := by
  rcases
    routeBRicherConcreteNPPrependedMultilinear_exists_rowSpanComplement_not_mem_firstSquareProbe
      M n hn2 htb hns with
    ⟨C, hC, hprobe⟩
  refine ⟨C, hC, hprobe, ?_, ?_⟩
  · exact
      routeBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement_iff_kernelGenerator_zeroWithComplement
        M n hn2 htb hns C hC
  · intro hzero
    exact
      routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_spdpSubspaceContainment_of_kernelGenerator_zeroWithComplement
        M n hn2 htb hns C hC hzero

/-! ## Axiom audit anchors -/

#print axioms routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_fixed_of_mem
#print axioms RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZeroWithComplement
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionDescentWithComplement_iff_kernelGenerator_zeroWithComplement
#print axioms routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_spdpSubspaceContainment_of_projectionWithComplementDescent
#print axioms routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_spdpSubspaceContainment_of_kernelGenerator_zeroWithComplement
#print axioms routeBRicherConcreteNPPrependedMultilinear_exists_firstSquareAvoidingComplementPolicy_with_directSPDPFrontier

end PallLean.Paper93.Paper283
