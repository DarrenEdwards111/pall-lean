import PallLean.Paper93.Paper283.RouteBRicherGaugeConcreteNP
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPContainmentFiniteSpan
import PallLean.GaugeMonotonicity

/-!
# Concrete coefficient reductions for Route B finite-row SPDP containment

This module attacks the finite-row side of Route B SPDP containment.  The main
point is that, for a finite-row candidate, the projected base polynomial already
lies in the selected row span.  Since the Route B SPDP generator row is linear
in its base polynomial, it is enough to check SPDP closure on the selected rows
themselves.

For the concrete one-row NP witness family, the same criterion reduces the row
span membership check to the scalar-multiple question for the single witness
row.  The unprojected SPDP-preimage half remains a separate assumption: this
file only closes/reduces the finite-row coefficient containment half.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- The Route B SPDP generator row is additive in the base row. -/
theorem routeBSPDPGeneratorRow_add
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (p q : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns) :
    routeBSPDPGeneratorRow M n hn2 htb hns (p + q) S shift =
      routeBSPDPGeneratorRow M n hn2 htb hns p S shift +
        routeBSPDPGeneratorRow M n hn2 htb hns q S shift := by
  unfold routeBSPDPGeneratorRow
  rw [SPDP.iterDerivList_add, mul_add, MultilinearSPDP.mlProj_add]

/-- The Route B SPDP generator row is homogeneous in the base row. -/
theorem routeBSPDPGeneratorRow_smul
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (c : Rat) (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns) :
    routeBSPDPGeneratorRow M n hn2 htb hns (c • p) S shift =
      c • routeBSPDPGeneratorRow M n hn2 htb hns p S shift := by
  unfold routeBSPDPGeneratorRow
  rw [GaugeMonotonicity.iterDerivList_smul]
  have hmul :
      shift * (c • SPDP.iterDerivList S p) =
        c • (shift * SPDP.iterDerivList S p) := by
    simp
  rw [hmul, MultilinearSPDP.mlProj_smul]

/-- The Route B SPDP generator row sends zero to zero. -/
theorem routeBSPDPGeneratorRow_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns) :
    routeBSPDPGeneratorRow M n hn2 htb hns 0 S shift = 0 := by
  simpa using
    (routeBSPDPGeneratorRow_smul M n hn2 htb hns 0
      (0 : SATDeciderGaugeSpace M n hn2 htb hns) S shift)

/-- The Route B SPDP generator row as a linear map in its base row. -/
noncomputable def routeBSPDPGeneratorRowLinearMap
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns) :
    SATDeciderGaugeSpace M n hn2 htb hns →ₗ[Rat]
      SATDeciderGaugeSpace M n hn2 htb hns where
  toFun p := routeBSPDPGeneratorRow M n hn2 htb hns p S shift
  map_add' p q := routeBSPDPGeneratorRow_add M n hn2 htb hns p q S shift
  map_smul' c p := routeBSPDPGeneratorRow_smul M n hn2 htb hns c p S shift

/-- Applying the linear-map package is definitionally the concrete generator
row. -/
theorem routeBSPDPGeneratorRowLinearMap_apply
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift p : SATDeciderGaugeSpace M n hn2 htb hns) :
    routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift p =
      routeBSPDPGeneratorRow M n hn2 htb hns p S shift :=
  rfl

/-- A member of a finite row span is exactly a finite linear combination of
the indexed rows. -/
theorem mem_finiteRowsSubmodule_iff_exists_linearCombination {N m : Nat}
    (rows : Fin m -> MvPolynomial (Fin N) Rat)
    (p : MvPolynomial (Fin N) Rat) :
    p ∈ finiteRowsSubmodule rows ↔
      ∃ coeff : Fin m -> Rat,
        p = Finset.univ.sum (fun i => coeff i • rows i) := by
  constructor
  · intro hp
    unfold finiteRowsSubmodule at hp
    rcases (Submodule.mem_span_range_iff_exists_fun Rat (v := rows)
        (x := p)).mp hp with ⟨coeff, hcoeff⟩
    exact ⟨coeff, hcoeff.symm⟩
  · rintro ⟨coeff, hcoeff⟩
    exact mem_finiteRowsSubmodule_of_linearCombination rows coeff hcoeff

/-- The finite-row projection always lands in the selected finite row span. -/
theorem routeBRicherFiniteRowsCandidateGauge_projected_mem_finiteRowsSubmodule
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    routeBNFrameCandidateAsSATGauge M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows) p
      ∈ finiteRowsSubmodule rows := by
  change
    (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows).projection p
      ∈ finiteRowsSubmodule rows
  rw [← routeBRicherFiniteRowsCandidateGauge_range M n hn2 htb hns rows]
  exact ⟨p, rfl⟩

/-- If every selected row is sent back into the selected row span by one SPDP
generator operator, then every base row in the selected span is also sent back
into that span. -/
theorem routeBSPDPGeneratorRow_mem_finiteRowsSubmodule_of_mem_of_rowClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns)
    {p : SATDeciderGaugeSpace M n hn2 htb hns}
    (hp : p ∈ finiteRowsSubmodule rows)
    (hrowClosure :
      forall i,
        routeBSPDPGeneratorRow M n hn2 htb hns (rows i) S shift
          ∈ finiteRowsSubmodule rows) :
    routeBSPDPGeneratorRow M n hn2 htb hns p S shift
      ∈ finiteRowsSubmodule rows := by
  unfold finiteRowsSubmodule at hp ⊢
  exact Submodule.span_induction
    (s := Set.range rows)
    (p := fun q (_hq : q ∈ Submodule.span Rat (Set.range rows)) =>
      routeBSPDPGeneratorRow M n hn2 htb hns q S shift
        ∈ Submodule.span Rat (Set.range rows))
    (by
      rintro q ⟨i, rfl⟩
      exact hrowClosure i)
    (by
      change
        routeBSPDPGeneratorRow M n hn2 htb hns
            (0 : SATDeciderGaugeSpace M n hn2 htb hns) S shift
          ∈ Submodule.span Rat (Set.range rows)
      rw [routeBSPDPGeneratorRow_zero]
      exact Submodule.zero_mem _)
    (by
      intro q r _hq _hr hq hr
      rw [routeBSPDPGeneratorRow_add]
      exact Submodule.add_mem _ hq hr)
    (by
      intro c q _hq hq
      rw [routeBSPDPGeneratorRow_smul]
      exact Submodule.smul_mem _ c hq)
    hp

/-- Finite-row containment for an arbitrary projected base is reduced to SPDP
closure of the selected rows themselves. -/
theorem routeBSPDPGeneratorRow_projected_mem_finiteRowsSubmodule_of_rowClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns)
    (hrowClosure :
      forall i,
        routeBSPDPGeneratorRow M n hn2 htb hns (rows i) S shift
          ∈ finiteRowsSubmodule rows) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows) p)
        S shift
      ∈ finiteRowsSubmodule rows := by
  exact
    routeBSPDPGeneratorRow_mem_finiteRowsSubmodule_of_mem_of_rowClosure
      M n hn2 htb hns rows S shift
      (routeBRicherFiniteRowsCandidateGauge_projected_mem_finiteRowsSubmodule
        M n hn2 htb hns rows p)
      hrowClosure

/-- A row-closure criterion for the finite-row Route B SPDP containment
obligation.  This closes the finite-row span half of the coefficient criterion
from checks on the selected rows; the unprojected SPDP preimage half is left as
the explicit remaining assumption. -/
theorem routeBRicherFiniteRowsCandidateGauge_spdpSubspaceContainment_of_rowClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hrowClosure :
      forall (kappa ell : Nat)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = kappa ->
        shift.totalDegree <= ell ->
        shift.vars <= S.toFinset ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ->
        forall i,
          routeBSPDPGeneratorRow M n hn2 htb hns (rows i) S shift
            ∈ finiteRowsSubmodule rows)
    (hunprojected :
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
            (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
              (routeBRicherFiniteRowsCandidateGauge
                M n hn2 htb hns rows) p)
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
  exact
    ⟨routeBSPDPGeneratorRow_projected_mem_finiteRowsSubmodule_of_rowClosure
        M n hn2 htb hns rows p S shift
        (hrowClosure kappa ell S shift hSlen hshiftDegree hshiftVars hadm),
      hunprojected kappa ell p S shift hSlen hshiftDegree hshiftVars hadm⟩

/-! ## One-row concrete witness specialization -/

/-- In a one-row finite span, membership is exactly being a scalar multiple of
the single row. -/
theorem mem_finiteRowsSubmodule_one_iff_exists_scalar {N : Nat}
    (rows : Fin 1 -> MvPolynomial (Fin N) Rat)
    (p : MvPolynomial (Fin N) Rat) :
    p ∈ finiteRowsSubmodule rows ↔ ∃ c : Rat, p = c • rows 0 := by
  rw [mem_finiteRowsSubmodule_iff_exists_linearCombination rows p]
  constructor
  · rintro ⟨coeff, hcoeff⟩
    refine ⟨coeff 0, ?_⟩
    simpa using hcoeff
  · rintro ⟨c, hc⟩
    refine ⟨fun _ => c, ?_⟩
    simpa using hc

/-- For the concrete one-row NP witness family, a scalar closure proof for the
single witness row proves finite-row span membership for every projected SPDP
generator row. -/
theorem routeBRicherConcreteNPWitnessRows_projectedGenerator_mem_span_of_witnessGenerator_scalar
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns)
    (hscalar :
      ∃ c : Rat,
        routeBSPDPGeneratorRow M n hn2 htb hns
            (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) S shift =
          c • routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
            (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)) p)
        S shift
      ∈ finiteRowsSubmodule
          (routeBRicherConcreteNPWitnessRows M n hn2 htb hns) := by
  apply
    routeBSPDPGeneratorRow_projected_mem_finiteRowsSubmodule_of_rowClosure
      M n hn2 htb hns
      (routeBRicherConcreteNPWitnessRows M n hn2 htb hns) p S shift
  intro i
  fin_cases i
  exact
    (mem_finiteRowsSubmodule_one_iff_exists_scalar
      (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)
      (routeBSPDPGeneratorRow M n hn2 htb hns
        (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) S shift)).mpr
      hscalar

/-- Scalar form of the preceding concrete one-row reduction. -/
theorem routeBRicherConcreteNPWitnessRows_projectedGenerator_exists_scalar_of_witnessGenerator_scalar
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns)
    (hscalar :
      ∃ c : Rat,
        routeBSPDPGeneratorRow M n hn2 htb hns
            (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) S shift =
          c • routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) :
    ∃ c : Rat,
      routeBSPDPGeneratorRow M n hn2 htb hns
          (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
            (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
              (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)) p)
          S shift =
        c • routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0 := by
  exact
    (mem_finiteRowsSubmodule_one_iff_exists_scalar
      (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)
      (routeBSPDPGeneratorRow M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
            (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)) p)
        S shift)).mp
      (routeBRicherConcreteNPWitnessRows_projectedGenerator_mem_span_of_witnessGenerator_scalar
        M n hn2 htb hns p S shift hscalar)

/-! ## Axiom audit anchors -/

#print axioms routeBSPDPGeneratorRow_add
#print axioms routeBSPDPGeneratorRow_smul
#print axioms routeBSPDPGeneratorRow_zero
#print axioms routeBSPDPGeneratorRowLinearMap
#print axioms mem_finiteRowsSubmodule_iff_exists_linearCombination
#print axioms routeBRicherFiniteRowsCandidateGauge_projected_mem_finiteRowsSubmodule
#print axioms routeBSPDPGeneratorRow_mem_finiteRowsSubmodule_of_mem_of_rowClosure
#print axioms routeBSPDPGeneratorRow_projected_mem_finiteRowsSubmodule_of_rowClosure
#print axioms routeBRicherFiniteRowsCandidateGauge_spdpSubspaceContainment_of_rowClosure
#print axioms mem_finiteRowsSubmodule_one_iff_exists_scalar
#print axioms routeBRicherConcreteNPWitnessRows_projectedGenerator_mem_span_of_witnessGenerator_scalar
#print axioms routeBRicherConcreteNPWitnessRows_projectedGenerator_exists_scalar_of_witnessGenerator_scalar

end PallLean.Paper93.Paper283
