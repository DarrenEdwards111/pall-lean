import PallLean.Paper93.Paper283.RouteBRicherGaugeFiniteSpan
import PallLean.Paper93.Paper283.RouteBRicherGaugePSideTransport

/-!
# Finite-span criteria for Route B richer-gauge SPDP containment

This file gives checked generator criteria for the finite-span Route B
candidate gauges.  The criteria reduce the SPDP image-containment field to
row-level obligations: each projected SPDP generator must be fixed by the
candidate projection and already lie in the corresponding unprojected SPDP
subspace.  For finite submodule projections, fixedness is discharged by
membership in the chosen finite submodule; for finite row spans, membership can
be supplied by explicit finite linear combinations of the selected rows.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- The concrete Route B SPDP generator row associated to a base polynomial,
derivative list, and shift polynomial. -/
noncomputable abbrev routeBSPDPGeneratorRow
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns) :
    SATDeciderGaugeSpace M n hn2 htb hns :=
  mlProj (shift * SPDP.iterDerivList S p)

/-- If each projected generator is fixed by the candidate projection and is
already in the unprojected SPDP subspace, then the candidate satisfies the
Route B SPDP subspace-containment field. -/
theorem routeBRicherGauge_spdpSubspaceContainment_of_projectedGenerator_fixed_mem
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hgen :
      forall (kappa ell : Nat)
        (p : SATDeciderGaugeSpace M n hn2 htb hns)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = kappa ->
        shift.totalDegree <= ell ->
        shift.vars <= S.toFinset ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ->
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
            (routeBSPDPGeneratorRow M n hn2 htb hns
              ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) p)
              S shift) =
          routeBSPDPGeneratorRow M n hn2 htb hns
            ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) p)
            S shift
        ∧
        routeBSPDPGeneratorRow M n hn2 htb hns
            ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) p)
            S shift
          ∈
          mlBlockedSpdpSubspace
            (cook_levin_compilation M n hn2 htb hns).partition
            kappa ell p) :
    RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns Pi := by
  intro kappa ell p
  apply Submodule.span_le.mpr
  rintro q ⟨S, shift, hSlen, hshiftDegree, hshiftVars, hadm, hq⟩
  rw [hq]
  have hrow :=
    hgen kappa ell p S shift hSlen hshiftDegree hshiftVars hadm
  rcases hrow with ⟨hfixed, hunprojected⟩
  refine Submodule.mem_map.mpr ?_
  refine ⟨routeBSPDPGeneratorRow M n hn2 htb hns
      ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) p)
      S shift, hunprojected, ?_⟩
  exact hfixed

/-- Finite-submodule criterion: it is enough to show that every projected
generator lies in the selected finite submodule and in the unprojected SPDP
subspace.  The finite-submodule projection then fixes that generator, giving
the required image preimage. -/
theorem routeBRicherGaugeSPDPSubspaceContainment_of_finiteSubmodule_projectedGenerator_mem
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (U : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    [Module.Finite Rat U]
    (hgen :
      forall (kappa ell : Nat)
        (p : SATDeciderGaugeSpace M n hn2 htb hns)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = kappa ->
        shift.totalDegree <= ell ->
        shift.vars <= S.toFinset ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ->
        routeBSPDPGeneratorRow M n hn2 htb hns
            ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
              (candidateGaugeOfFiniteSubmodule U)) p)
            S shift
          ∈ U
        ∧
        routeBSPDPGeneratorRow M n hn2 htb hns
            ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
              (candidateGaugeOfFiniteSubmodule U)) p)
            S shift
          ∈
          mlBlockedSpdpSubspace
            (cook_levin_compilation M n hn2 htb hns).partition
            kappa ell p) :
    RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
      (candidateGaugeOfFiniteSubmodule U) := by
  apply
    routeBRicherGauge_spdpSubspaceContainment_of_projectedGenerator_fixed_mem
      M n hn2 htb hns (candidateGaugeOfFiniteSubmodule U)
  intro kappa ell p S shift hSlen hshiftDegree hshiftVars hadm
  have hrow := hgen kappa ell p S shift hSlen hshiftDegree hshiftVars hadm
  rcases hrow with ⟨hmemU, hunprojected⟩
  exact ⟨candidateGaugeOfFiniteSubmodule_fixed_of_mem U hmemU,
    hunprojected⟩

/-- The finite-rows candidate fixes every element of the span of its selected
rows, not only the individual rows. -/
theorem finiteRowsCandidateGauge_fixed_of_mem {N m : Nat}
    (rows : Fin m -> MvPolynomial (Fin N) Rat)
    {p : MvPolynomial (Fin N) Rat}
    (hp : p ∈ finiteRowsSubmodule rows) :
    (finiteRowsCandidateGauge rows).projection p = p := by
  haveI : Module.Finite Rat (finiteRowsSubmodule rows) :=
    finiteRowsSubmodule_finite rows
  unfold finiteRowsCandidateGauge
  exact candidateGaugeOfFiniteSubmodule_fixed_of_mem
    (finiteRowsSubmodule rows) hp

/-- The Route B finite-row candidate fixes every element of the finite row
span. -/
theorem routeBRicherFiniteRowsCandidateGauge_fixed_of_mem
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    {p : SATDeciderGaugeSpace M n hn2 htb hns}
    (hp : p ∈ finiteRowsSubmodule rows) :
    (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows).projection p =
      p := by
  unfold routeBRicherFiniteRowsCandidateGauge
  exact finiteRowsCandidateGauge_fixed_of_mem rows hp

/-- Finite-row-span criterion for the Route B finite-rows candidate. -/
theorem routeBRicherFiniteRowsCandidateGauge_spdpSubspaceContainment_of_projectedGenerator_mem_span
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hgen :
      forall (kappa ell : Nat)
        (p : SATDeciderGaugeSpace M n hn2 htb hns)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = kappa ->
        shift.totalDegree <= ell ->
        shift.vars <= S.toFinset ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ->
        routeBSPDPGeneratorRow M n hn2 htb hns
            ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
              (routeBRicherFiniteRowsCandidateGauge
                M n hn2 htb hns rows)) p)
            S shift
          ∈ finiteRowsSubmodule rows
        ∧
        routeBSPDPGeneratorRow M n hn2 htb hns
            ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
              (routeBRicherFiniteRowsCandidateGauge
                M n hn2 htb hns rows)) p)
            S shift
          ∈
          mlBlockedSpdpSubspace
            (cook_levin_compilation M n hn2 htb hns).partition
            kappa ell p) :
    RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows) := by
  apply
    routeBRicherGauge_spdpSubspaceContainment_of_projectedGenerator_fixed_mem
      M n hn2 htb hns
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
  intro kappa ell p S shift hSlen hshiftDegree hshiftVars hadm
  have hrow := hgen kappa ell p S shift hSlen hshiftDegree hshiftVars hadm
  rcases hrow with ⟨hmemSpan, hunprojected⟩
  exact
    ⟨routeBRicherFiniteRowsCandidateGauge_fixed_of_mem
        M n hn2 htb hns rows hmemSpan,
      hunprojected⟩

/-- An explicit finite linear combination of the chosen rows is a member of
their finite row span. -/
theorem mem_finiteRowsSubmodule_of_linearCombination {N m : Nat}
    (rows : Fin m -> MvPolynomial (Fin N) Rat)
    {p : MvPolynomial (Fin N) Rat}
    (coeff : Fin m -> Rat)
    (hp : p = Finset.univ.sum (fun i => coeff i • rows i)) :
    p ∈ finiteRowsSubmodule rows := by
  rw [hp]
  refine Submodule.sum_mem _ ?_
  intro i _hi
  exact Submodule.smul_mem _ (coeff i)
    (Submodule.subset_span ⟨i, rfl⟩)

/-- Coefficient-level finite-row criterion.  Instead of proving abstract span
membership, it suffices to exhibit coefficients expressing each projected
generator as a finite linear combination of the selected rows, and separately
show that the same generator lies in the unprojected SPDP subspace. -/
theorem routeBRicherFiniteRowsCandidateGauge_spdpSubspaceContainment_of_projectedGenerator_linearCombination
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hgen :
      forall (kappa ell : Nat)
        (p : SATDeciderGaugeSpace M n hn2 htb hns)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = kappa ->
        shift.totalDegree <= ell ->
        shift.vars <= S.toFinset ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ->
        ∃ coeff : Fin m -> Rat,
          routeBSPDPGeneratorRow M n hn2 htb hns
              ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
                (routeBRicherFiniteRowsCandidateGauge
                  M n hn2 htb hns rows)) p)
              S shift =
            Finset.univ.sum (fun i => coeff i • rows i)
          ∧
          routeBSPDPGeneratorRow M n hn2 htb hns
              ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
                (routeBRicherFiniteRowsCandidateGauge
                  M n hn2 htb hns rows)) p)
              S shift
            ∈
            mlBlockedSpdpSubspace
              (cook_levin_compilation M n hn2 htb hns).partition
              kappa ell p) :
    RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows) := by
  apply
    routeBRicherFiniteRowsCandidateGauge_spdpSubspaceContainment_of_projectedGenerator_mem_span
      M n hn2 htb hns rows
  intro kappa ell p S shift hSlen hshiftDegree hshiftVars hadm
  rcases hgen kappa ell p S shift hSlen hshiftDegree hshiftVars hadm with
    ⟨coeff, hlinear, hunprojected⟩
  exact
    ⟨mem_finiteRowsSubmodule_of_linearCombination rows coeff hlinear,
      hunprojected⟩

/-! ## Axiom audit anchors -/

#print axioms routeBRicherGauge_spdpSubspaceContainment_of_projectedGenerator_fixed_mem
#print axioms routeBRicherGaugeSPDPSubspaceContainment_of_finiteSubmodule_projectedGenerator_mem
#print axioms finiteRowsCandidateGauge_fixed_of_mem
#print axioms routeBRicherFiniteRowsCandidateGauge_fixed_of_mem
#print axioms routeBRicherFiniteRowsCandidateGauge_spdpSubspaceContainment_of_projectedGenerator_mem_span
#print axioms mem_finiteRowsSubmodule_of_linearCombination
#print axioms routeBRicherFiniteRowsCandidateGauge_spdpSubspaceContainment_of_projectedGenerator_linearCombination

end PallLean.Paper93.Paper283
