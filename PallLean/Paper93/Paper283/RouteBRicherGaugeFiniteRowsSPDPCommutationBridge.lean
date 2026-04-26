import PallLean.Paper93.Paper283.RouteBRicherGaugeFiniteRowsSPDPFrontier

/-!
# Finite-row SPDP map-preimage from generator commutation

This file adds the focused bridge from finite-row generator commutation to the
map-preimage SPDP surface consumed by the finite-row Route B certificate.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.BridgeB
open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Finite-row specialization of generator commutation, stated directly in
terms of the concrete Route B SPDP generator row. -/
def RouteBRicherGaugeFiniteRowsSPDPGeneratorCommutation
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) : Prop :=
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
        ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)) p)
        S shift =
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows))
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)

/-- Kernel/complement compatibility for the finite-row projection.

This is the real extra content needed to turn finite-row fixedness into
generator commutation: after subtracting the projected component of `p`, each
SPDP generator row from the remaining complement must be killed by the
finite-row projection. -/
def RouteBRicherGaugeFiniteRowsSPDPKernelCompatibility
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) : Prop :=
  forall (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows))
      (routeBSPDPGeneratorRow M n hn2 htb hns
        (p -
          (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
            (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)) p)
        S shift) = 0

/-- The general richer-gauge generator commutation criterion specializes to
the finite-row concrete generator-row commutation condition. -/
theorem routeBRicherGaugeFiniteRowsSPDPGeneratorCommutation_of_generatorCommutation
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcomm :
      RouteBRicherGaugeGeneratorCommutation M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)) :
    RouteBRicherGaugeFiniteRowsSPDPGeneratorCommutation
      M n hn2 htb hns rows := by
  intro spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm
  exact hcomm spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm

/-- Finite-row span membership plus kernel/complement compatibility proves
finite-row generator commutation.

The decomposition is
`p = projection p + (p - projection p)`.  The first summand is fixed because
its generator row lies in the selected finite span; the second summand is
killed by the explicit kernel-compatibility hypothesis. -/
theorem routeBRicherGaugeFiniteRowsSPDPGeneratorCommutation_of_projectedGeneratorMem_kernelCompatibility
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hmem :
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
            ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
              (routeBRicherFiniteRowsCandidateGauge
                M n hn2 htb hns rows)) p)
            S shift ∈ finiteRowsSubmodule rows)
    (hker :
      RouteBRicherGaugeFiniteRowsSPDPKernelCompatibility
        M n hn2 htb hns rows) :
    RouteBRicherGaugeFiniteRowsSPDPGeneratorCommutation
      M n hn2 htb hns rows := by
  intro spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm
  let Pi :=
    routeBNFrameCandidateAsSATGauge M n hn2 htb hns
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
  let projected := routeBSPDPGeneratorRow M n hn2 htb hns (Pi p) S shift
  let residual :=
    routeBSPDPGeneratorRow M n hn2 htb hns (p - Pi p) S shift
  have hfixed : Pi projected = projected := by
    simpa [Pi, projected] using
      routeBRicherFiniteRowsCandidateGauge_fixed_of_mem
        M n hn2 htb hns rows
        (hmem spdpKappa ell p S shift
          hSlen hshiftDegree hshiftVars hadm)
  have hresidual : Pi residual = 0 := by
    simpa [Pi, residual] using
      hker spdpKappa ell p S shift
        hSlen hshiftDegree hshiftVars hadm
  have hdecomp :
      routeBSPDPGeneratorRow M n hn2 htb hns p S shift =
        projected + residual := by
    have hp :
        p = Pi p + (p - Pi p) := by
      abel
    calc
      routeBSPDPGeneratorRow M n hn2 htb hns p S shift
          = routeBSPDPGeneratorRow M n hn2 htb hns
              (Pi p + (p - Pi p)) S shift := by
            exact
              congrArg
                (fun q =>
                  routeBSPDPGeneratorRow M n hn2 htb hns q S shift)
                hp
      _ = projected + residual := by
        simpa [projected, residual] using
          routeBSPDPGeneratorRow_add M n hn2 htb hns
            (Pi p) (p - Pi p) S shift
  calc
    projected = Pi projected := hfixed.symm
    _ = Pi (projected + residual) := by
      simp [hresidual]
    _ = Pi (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) := by
      rw [← hdecomp]

/-- Same reduction, stated in the general richer-gauge commutation vocabulary
consumed by the corrected Route B assembly. -/
theorem routeBRicherGaugeGeneratorCommutation_of_projectedGeneratorMem_kernelCompatibility
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hmem :
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
            ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
              (routeBRicherFiniteRowsCandidateGauge
                M n hn2 htb hns rows)) p)
            S shift ∈ finiteRowsSubmodule rows)
    (hker :
      RouteBRicherGaugeFiniteRowsSPDPKernelCompatibility
        M n hn2 htb hns rows) :
    RouteBRicherGaugeGeneratorCommutation M n hn2 htb hns
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows) :=
  routeBRicherGaugeFiniteRowsSPDPGeneratorCommutation_of_projectedGeneratorMem_kernelCompatibility
    M n hn2 htb hns rows hmem hker

/-- Finite-row closure plus kernel/complement compatibility proves the general
commutation hypothesis for the finite-row richer gauge. -/
theorem routeBRicherGaugeGeneratorCommutation_of_spdpClosure_kernelCompatibility
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (closure :
      RouteBRicherGaugeFiniteRowsSPDPClosure M n hn2 htb hns rows)
    (hker :
      RouteBRicherGaugeFiniteRowsSPDPKernelCompatibility
        M n hn2 htb hns rows) :
    RouteBRicherGaugeGeneratorCommutation M n hn2 htb hns
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows) := by
  refine
    routeBRicherGaugeGeneratorCommutation_of_projectedGeneratorMem_kernelCompatibility
      M n hn2 htb hns rows ?_ hker
  intro spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm
  rcases closure.finite_row_closure spdpKappa ell p S shift
      hSlen hshiftDegree hshiftVars hadm with
    ⟨coeff, hcoeff⟩
  exact
    (mem_finiteRowsSubmodule_iff_exists_linearCombination rows
      (routeBSPDPGeneratorRow M n hn2 htb hns
        ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)) p)
        S shift)).2
      ⟨coeff, hcoeff⟩

/-- Finite-row generator commutation supplies the map-preimage witness needed
for SPDP image containment. -/
theorem routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_generatorRowCommutation
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcomm :
      RouteBRicherGaugeFiniteRowsSPDPGeneratorCommutation
        M n hn2 htb hns rows) :
    RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns rows := by
  constructor
  intro spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm
  refine
    ⟨routeBSPDPGeneratorRow M n hn2 htb hns p S shift, ?_, ?_⟩
  · exact
      Submodule.subset_span
        ⟨S, shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩
  · exact (hcomm spdpKappa ell p S shift
      hSlen hshiftDegree hshiftVars hadm).symm

/-- General richer-gauge generator commutation gives the finite-row
map-preimage SPDP surface. -/
theorem routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_generatorCommutation
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcomm :
      RouteBRicherGaugeGeneratorCommutation M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)) :
    RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns rows :=
  routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_generatorRowCommutation
    M n hn2 htb hns rows
    (routeBRicherGaugeFiniteRowsSPDPGeneratorCommutation_of_generatorCommutation
      M n hn2 htb hns rows hcomm)

/-- Concrete finite-row Route B assembly with the SPDP side discharged by
finite-row generator commutation. -/
theorem routeBPerInstanceCertificate_of_finiteRowsSPDPGeneratorCommutation_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hN : 1 <= N) (hrowCount : m <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (hcomm :
      RouteBRicherGaugeFiniteRowsSPDPGeneratorCommutation
        M n hn2 htb hns rows)
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (i : Fin m)
    (hrow :
      rows i =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_finiteRowsSPDPMapPreimage_deltaEqRateKappa
    (N := N) (d := d)
    M n hn2 htb hns alpha beta alpha0 kappa gadgetN G chi Phi
    rows hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    (routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_generatorRowCommutation
      M n hn2 htb hns rows hcomm)
    cover Q i hrow hextract hsource

/-- Concrete finite-row Route B assembly with the SPDP side discharged by the
general richer-gauge generator commutation criterion. -/
theorem routeBPerInstanceCertificate_of_finiteRowsSPDPGeneralCommutation_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hN : 1 <= N) (hrowCount : m <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (hcomm :
      RouteBRicherGaugeGeneratorCommutation M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows))
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (i : Fin m)
    (hrow :
      rows i =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_finiteRowsSPDPGeneratorCommutation_deltaEqRateKappa
    (N := N) (d := d)
    M n hn2 htb hns alpha beta alpha0 kappa gadgetN G chi Phi
    rows hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    (routeBRicherGaugeFiniteRowsSPDPGeneratorCommutation_of_generatorCommutation
      M n hn2 htb hns rows hcomm)
    cover Q i hrow hextract hsource

/-! ## Axiom audit anchors -/

#print axioms RouteBRicherGaugeFiniteRowsSPDPGeneratorCommutation
#print axioms RouteBRicherGaugeFiniteRowsSPDPKernelCompatibility
#print axioms routeBRicherGaugeFiniteRowsSPDPGeneratorCommutation_of_generatorCommutation
#print axioms routeBRicherGaugeFiniteRowsSPDPGeneratorCommutation_of_projectedGeneratorMem_kernelCompatibility
#print axioms routeBRicherGaugeGeneratorCommutation_of_projectedGeneratorMem_kernelCompatibility
#print axioms routeBRicherGaugeGeneratorCommutation_of_spdpClosure_kernelCompatibility
#print axioms routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_generatorRowCommutation
#print axioms routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_generatorCommutation
#print axioms routeBPerInstanceCertificate_of_finiteRowsSPDPGeneratorCommutation_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_finiteRowsSPDPGeneralCommutation_deltaEqRateKappa

end PallLean.Paper93.Paper283
