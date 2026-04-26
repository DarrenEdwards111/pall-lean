import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPConcreteCoefficients
import PallLean.CrossTermVanishing
import PallLean.Paper93.DeepMath.PathB.ZeroProfileScalarClosure

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

/-- The first-variable shifted first derivative of the concrete Cook-Levin
polynomial has nonzero `X_0` coefficient after multilinear projection. -/
theorem routeBRicherConcreteNPCompiledPoly_coeff_singleton_shift_deriv_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    let i : Fin n := ⟨0, by omega⟩
    MvPolynomial.coeff (Finsupp.single i 1)
      (mlProj
        (MvPolynomial.X i *
          SPDP.iterDerivList [i]
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) =
      (-1 : Rat) := by
  intro i
  rw [coeff_mlProj_of_isMultilinear_mono]
  · conv_lhs => arg 1; rw [← add_zero (Finsupp.single i 1)]
    rw [MvPolynomial.coeff_X_mul]
    have htag0 :
        SymmetricPower.tagMonomial (∅ : Finset (Fin n)) =
          (0 : Fin n →₀ Nat) := by
      ext v
      rw [SymmetricPower.tagMonomial_apply]
      simp
    rw [← htag0]
    set V : Finset (Fin n) :=
      Finset.univ.filter (fun v : Fin n => 3 ∣ v.val)
    rw [CrossTermVanishing.coeff_iterDeriv_compiledPoly_eq_boolFactor
      M hn2 htb hns [i] (∅ : Finset (Fin n)) V]
    · rw [htag0]
      unfold SymmetricPower.boolFactorFullProd
      rw [SymmetricPower.iterDerivList_boolFactor_prod]
      · have hgen :=
          SymmetricPower.coeff_tag_iterDeriv_boolFactor_prod_general
            (∅ : Finset (Fin n)) ({i} : Finset (Fin n))
        simpa using hgen
      · simp
      · intro v hv
        simp at hv
        exact hv.symm ▸ Finset.mem_univ v
    · intro s hs
      simp at hs
      subst hs
      simp [V]
      change 3 ∣ (0 : Nat)
      omega
    · intro v hv
      simp at hv
    · intro v hv
      simpa [V] using hv
  · intro v
    simp [Finsupp.single_apply]
    split_ifs <;> omega

/-- The concrete one-row scalar closure is false: the shifted first derivative
above cannot be a scalar multiple of `compiledPoly`. -/
theorem not_routeBRicherConcreteNPCompiledPolyScalarRowClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    ¬ RouteBRicherConcreteNPCompiledPolyScalarRowClosure M n hn2 htb hns := by
  intro hclosure
  let i : Fin n := ⟨0, by omega⟩
  obtain ⟨c, hc⟩ :=
    hclosure 1 1 [i] (MvPolynomial.X i)
      (by simp)
      (by simp [MvPolynomial.totalDegree_X])
      (by simp)
      (by
        constructor
        · simp
        · intro b
          by_cases hb :
              (cook_levin_compilation M n hn2 htb hns).partition.assign i = b
          · simp [hb]
          · simp [hb])
  have hconst : c = 0 := by
    have hc0 :=
      congrArg (fun q =>
        MvPolynomial.coeff (0 : Fin n →₀ Nat) q) hc
    change
      MvPolynomial.coeff (0 : Fin n →₀ Nat)
          (mlProj
            (MvPolynomial.X i *
              SPDP.iterDerivList [i]
                (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) =
        MvPolynomial.coeff (0 : Fin n →₀ Nat)
          (c • compiledPoly (cook_levin_compilation M n hn2 htb hns)) at hc0
    rw [MvPolynomial.coeff_smul] at hc0
    rw [coeff_mlProj_of_isMultilinear_mono] at hc0
    · rw [MvPolynomial.coeff_X_mul'] at hc0
      have hnot : i ∉ (0 : Fin n →₀ Nat).support := by simp
      rw [if_neg hnot] at hc0
      have hp0 :
          MvPolynomial.coeff (0 : Fin n →₀ Nat)
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
            (1 : Rat) := by
        rw [← cookLevinZeroProfileBaseProduct_eq_compiledPoly
          M n hn2 htb hns]
        exact cookLevinZeroProfileBaseProduct_coeff_zero M n hn2 htb hns
      rw [hp0] at hc0
      simpa using hc0.symm
    · intro v
      simp
  have hsingle :=
    congrArg (fun q =>
      MvPolynomial.coeff (Finsupp.single i 1) q) hc
  change
    MvPolynomial.coeff (Finsupp.single i 1)
        (mlProj
          (MvPolynomial.X i *
            SPDP.iterDerivList [i]
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) =
      MvPolynomial.coeff (Finsupp.single i 1)
        (c • compiledPoly (cook_levin_compilation M n hn2 htb hns)) at hsingle
  rw [MvPolynomial.coeff_smul, hconst] at hsingle
  simp at hsingle
  have hlhs :
      MvPolynomial.coeff (Finsupp.single i 1)
          (mlProj
            (MvPolynomial.X i *
              SPDP.iterDerivList [i]
                (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) =
        (-1 : Rat) :=
    routeBRicherConcreteNPCompiledPoly_coeff_singleton_shift_deriv_zero
      M n hn2 htb hns
  have hlhs' :
      MvPolynomial.coeff (Finsupp.single i 1)
          (mlProj
            (MvPolynomial.X i *
              MvPolynomial.pderiv i
                (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) =
        (-1 : Rat) := by
    simpa [SPDP.iterDerivList] using hlhs
  rw [hlhs'] at hsingle
  norm_num at hsingle

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

/-- Smaller local form of the unprojected-preimage obstruction.  Since the
finite-row projection always lands in the one-dimensional span of
`compiledPoly`, it is enough to control the corresponding scalar multiple of
the raw `compiledPoly` generator in the original `p`-SPDP subspace. -/
def RouteBRicherConcreteNPProjectedRowSPDPPreimageClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  forall (kappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns)
    (c : Rat),
    S.length = kappa ->
    shift.totalDegree <= ell ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    routeBNFrameCandidateAsSATGauge M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
          (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)) p =
      c • compiledPoly (cook_levin_compilation M n hn2 htb hns) ->
    c • routeBSPDPGeneratorRow M n hn2 htb hns
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) S shift
      ∈
      mlBlockedSpdpSubspace
        (cook_levin_compilation M n hn2 htb hns).partition
        kappa ell p

/-- The local scalar preimage condition above is sufficient for the original
unprojected-preimage closure. -/
theorem routeBRicherConcreteNPUnprojectedSPDPPreimageClosure_of_projectedRow
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hpre :
      RouteBRicherConcreteNPProjectedRowSPDPPreimageClosure
        M n hn2 htb hns) :
    RouteBRicherConcreteNPUnprojectedSPDPPreimageClosure
      M n hn2 htb hns := by
  intro kappa ell p S shift hSlen hshiftDegree hshiftVars hadm
  have hmem :
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
            (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)) p
        ∈ finiteRowsSubmodule
            (routeBRicherConcreteNPWitnessRows M n hn2 htb hns) :=
    routeBRicherFiniteRowsCandidateGauge_projected_mem_finiteRowsSubmodule
      M n hn2 htb hns
      (routeBRicherConcreteNPWitnessRows M n hn2 htb hns) p
  rcases
    (mem_finiteRowsSubmodule_one_iff_exists_scalar
      (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
          (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)) p)).mp hmem with
    ⟨c, hprojRow⟩
  have hproj :
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
            (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)) p =
        c • compiledPoly (cook_levin_compilation M n hn2 htb hns) := by
    simpa [routeBRicherConcreteNPWitnessRows_zero_eq_compiledPoly
      M n hn2 htb hns] using hprojRow
  rw [hproj, routeBSPDPGeneratorRow_smul]
  exact hpre kappa ell p S shift c
    hSlen hshiftDegree hshiftVars hadm hproj

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
#print axioms routeBRicherConcreteNPCompiledPoly_coeff_singleton_shift_deriv_zero
#print axioms not_routeBRicherConcreteNPCompiledPolyScalarRowClosure
#print axioms RouteBRicherConcreteNPWitnessScalarRowClosure
#print axioms routeBRicherConcreteNPWitnessScalarRowClosure_iff_compiledPoly
#print axioms routeBRicherConcreteNPWitnessRows_projectedGenerator_mem_span_of_compiledPoly_scalar
#print axioms RouteBRicherConcreteNPUnprojectedSPDPPreimageClosure
#print axioms RouteBRicherConcreteNPProjectedRowSPDPPreimageClosure
#print axioms routeBRicherConcreteNPUnprojectedSPDPPreimageClosure_of_projectedRow
#print axioms routeBRicherConcreteNPWitnessRows_spdpSubspaceContainment_of_compiledPolyScalarRowClosure

end PallLean.Paper93.Paper283
