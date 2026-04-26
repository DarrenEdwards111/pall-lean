import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPConcreteCoefficients

/-!
# Concrete scalar-row closure for the one-row Route B witness

This module isolates the scalar row-closure obligation for the concrete
one-row NP witness.  The row itself is definitionally the flat embedded
coupled-sheet witness, and the existing concrete NP module proves that this
embedded row is exactly `compiledPoly`.  Consequently the scalar closure
needed by the finite-row SPDP reduction is precisely the concrete polynomial
identity

`mlProj (shift * iterDerivList S compiledPoly) = c • compiledPoly`.

The final theorem below consumes that named polynomial identity, together with
the already separate unprojected SPDP-preimage obligation, to supply
`RouteBRicherGaugeSPDPSubspaceContainment` for the one-row concrete witness.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- The single concrete witness row is exactly the Cook-Levin compiled
polynomial. -/
theorem routeBRicherConcreteNPWitnessRows_zero_eq_compiledPoly
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0 =
      compiledPoly (cook_levin_compilation M n hn2 htb hns) := by
  rw [routeBRicherConcreteNPWitnessRows_eq_embed,
    routeBRicherConcreteNPWitnessQ_embed_eq_compiledPoly]

/-- The concrete witness-row scalar obligation is exactly the corresponding
scalar identity for `compiledPoly`. -/
theorem routeBRicherConcreteNPWitnessRows_witnessGenerator_scalar_iff_compiledPoly
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns) :
    (∃ c : Rat,
      routeBSPDPGeneratorRow M n hn2 htb hns
          (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) S shift =
        c • routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) ↔
    (∃ c : Rat,
      mlProj
          (shift *
            SPDP.iterDerivList S
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))) =
        c • compiledPoly (cook_levin_compilation M n hn2 htb hns)) := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    simpa [routeBSPDPGeneratorRow,
      routeBRicherConcreteNPWitnessRows_zero_eq_compiledPoly M n hn2 htb hns]
      using hc
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    simpa [routeBSPDPGeneratorRow,
      routeBRicherConcreteNPWitnessRows_zero_eq_compiledPoly M n hn2 htb hns]
      using hc

/-- Named remaining scalar-polynomial identity for the one-row concrete
witness.  This is the smallest scalar-row closure input used in this module. -/
def RouteBRicherConcreteNPCompiledPolyScalarRowClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  forall (kappa ell : Nat)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = kappa ->
    shift.totalDegree <= ell ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    ∃ c : Rat,
      mlProj
          (shift *
            SPDP.iterDerivList S
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))) =
        c • compiledPoly (cook_levin_compilation M n hn2 htb hns)

/-- The same scalar-row closure input, stated directly on the witness row. -/
def RouteBRicherConcreteNPWitnessScalarRowClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  forall (kappa ell : Nat)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = kappa ->
    shift.totalDegree <= ell ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    ∃ c : Rat,
      routeBSPDPGeneratorRow M n hn2 htb hns
          (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) S shift =
        c • routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0

/-- The direct witness-row scalar closure and the concrete `compiledPoly`
identity are equivalent. -/
theorem routeBRicherConcreteNPWitnessScalarRowClosure_iff_compiledPoly
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherConcreteNPWitnessScalarRowClosure M n hn2 htb hns ↔
      RouteBRicherConcreteNPCompiledPolyScalarRowClosure M n hn2 htb hns := by
  constructor
  · intro h kappa ell S shift hSlen hshiftDegree hshiftVars hadm
    exact
      (routeBRicherConcreteNPWitnessRows_witnessGenerator_scalar_iff_compiledPoly
        M n hn2 htb hns S shift).mp
        (h kappa ell S shift hSlen hshiftDegree hshiftVars hadm)
  · intro h kappa ell S shift hSlen hshiftDegree hshiftVars hadm
    exact
      (routeBRicherConcreteNPWitnessRows_witnessGenerator_scalar_iff_compiledPoly
        M n hn2 htb hns S shift).mpr
        (h kappa ell S shift hSlen hshiftDegree hshiftVars hadm)

/-- The named scalar-polynomial identity supplies finite-row span membership
for every projected generator of the concrete one-row witness. -/
theorem routeBRicherConcreteNPWitnessRows_projectedGenerator_mem_span_of_compiledPoly_scalar
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns)
    (hscalar :
      ∃ c : Rat,
        mlProj
            (shift *
              SPDP.iterDerivList S
                (compiledPoly (cook_levin_compilation M n hn2 htb hns))) =
          c • compiledPoly (cook_levin_compilation M n hn2 htb hns)) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
            (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)) p)
        S shift
      ∈ finiteRowsSubmodule
          (routeBRicherConcreteNPWitnessRows M n hn2 htb hns) := by
  exact
    routeBRicherConcreteNPWitnessRows_projectedGenerator_mem_span_of_witnessGenerator_scalar
      M n hn2 htb hns p S shift
      ((routeBRicherConcreteNPWitnessRows_witnessGenerator_scalar_iff_compiledPoly
        M n hn2 htb hns S shift).mpr hscalar)

/-- The separate unprojected-preimage half of the Route B SPDP containment
criterion for the concrete one-row witness. -/
def RouteBRicherConcreteNPUnprojectedSPDPPreimageClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
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
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
            (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)) p)
        S shift
      ∈
      mlBlockedSpdpSubspace
        (cook_levin_compilation M n hn2 htb hns).partition
        kappa ell p

/-- Concrete one-row Route B SPDP containment from the reduced scalar
`compiledPoly` identity and the separate unprojected-preimage obligation. -/
theorem routeBRicherConcreteNPWitnessRows_spdpSubspaceContainment_of_compiledPolyScalarRowClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hscalar :
      RouteBRicherConcreteNPCompiledPolyScalarRowClosure M n hn2 htb hns)
    (hunprojected :
      RouteBRicherConcreteNPUnprojectedSPDPPreimageClosure M n hn2 htb hns) :
    RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
        (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)) := by
  apply
    routeBRicherFiniteRowsCandidateGauge_spdpSubspaceContainment_of_rowClosure
      M n hn2 htb hns
      (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)
  · intro kappa ell S shift hSlen hshiftDegree hshiftVars hadm i
    fin_cases i
    exact
      (mem_finiteRowsSubmodule_one_iff_exists_scalar
        (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)
        (routeBSPDPGeneratorRow M n hn2 htb hns
          (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) S shift)).mpr
        ((routeBRicherConcreteNPWitnessRows_witnessGenerator_scalar_iff_compiledPoly
          M n hn2 htb hns S shift).mpr
          (hscalar kappa ell S shift hSlen hshiftDegree hshiftVars hadm))
  · intro kappa ell p S shift hSlen hshiftDegree hshiftVars hadm
    exact hunprojected kappa ell p S shift hSlen hshiftDegree hshiftVars hadm

/-! ## Axiom audit anchors -/

#print axioms routeBRicherConcreteNPWitnessRows_zero_eq_compiledPoly
#print axioms routeBRicherConcreteNPWitnessRows_witnessGenerator_scalar_iff_compiledPoly
#print axioms RouteBRicherConcreteNPCompiledPolyScalarRowClosure
#print axioms RouteBRicherConcreteNPWitnessScalarRowClosure
#print axioms routeBRicherConcreteNPWitnessScalarRowClosure_iff_compiledPoly
#print axioms routeBRicherConcreteNPWitnessRows_projectedGenerator_mem_span_of_compiledPoly_scalar
#print axioms RouteBRicherConcreteNPUnprojectedSPDPPreimageClosure
#print axioms routeBRicherConcreteNPWitnessRows_spdpSubspaceContainment_of_compiledPolyScalarRowClosure

end PallLean.Paper93.Paper283
