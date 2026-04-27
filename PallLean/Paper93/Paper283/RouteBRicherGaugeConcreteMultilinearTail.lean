import PallLean.Paper93.Paper283.RouteBRicherGaugePrependedCorrectedMapPreimage
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateComplement
import PallLean.Paper93.Paper283.RouteBRicherGaugeConcreteWImport

/-!
# Concrete multilinear tail rows for the Route B richer gauge

The one-row concrete NP witness is not SPDP-row closed by itself: the scalar
closure target is false.  This module supplies a concrete finite richer tail
that closes the finite-row part honestly: all multilinear monomials in the
Cook-Levin ambient variable set.

This is intentionally a broad finite tail.  It discharges the selected-row
closure package because every Route B SPDP generator row is an `mlProj` output,
and hence lies in the span of the multilinear monomial basis.  The separate
map-preimage/P-window obligations remain explicit.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open SymmetricPowerBound
open WithinProfileBound
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- The concrete multilinear monomial tail basis in the Route B Cook-Levin
ambient row space. -/
noncomputable def routeBRicherMultilinearTailBasis
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Finset (SATDeciderGaugeSpace M n hn2 htb hns) :=
  MlProjFar.mlMonomialBasis
    (Finset.univ : Finset (Fin (RouteBCookLevinDim M n hn2 htb hns)))

/-- Number of concrete multilinear monomial tail rows. -/
noncomputable abbrev routeBRicherMultilinearTailRowCount
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Nat :=
  (routeBRicherMultilinearTailBasis M n hn2 htb hns).card

/-- The broad multilinear tail has the expected coarse exponential row-count
bound in the Cook-Levin ambient dimension. -/
theorem routeBRicherMultilinearTailRowCount_le_two_pow_dim
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    routeBRicherMultilinearTailRowCount M n hn2 htb hns <=
      2 ^ RouteBCookLevinDim M n hn2 htb hns := by
  simpa [routeBRicherMultilinearTailRowCount,
    routeBRicherMultilinearTailBasis] using
    MlProjFar.mlMonomialBasis_card
      (Finset.univ :
        Finset (Fin (RouteBCookLevinDim M n hn2 htb hns)))

/-- A usable row-budget side condition for the concrete multilinear tail. -/
theorem routeBRicherConcreteNPPrependedMultilinearRows_rowCount_le_of_two_pow_dim
    {N : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hNrows :
      2 ^ RouteBCookLevinDim M n hn2 htb hns + 1 <= N) :
    routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1 <= N :=
  (Nat.add_le_add_right
    (routeBRicherMultilinearTailRowCount_le_two_pow_dim
      M n hn2 htb hns) 1).trans hNrows

/-- Concrete richer tail rows: an enumeration of all multilinear monomials in
the Cook-Levin ambient row space. -/
noncomputable def routeBRicherMultilinearTailRows
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns) ->
      SATDeciderGaugeSpace M n hn2 htb hns :=
  fun i =>
    ((Finset.equivFin
      (routeBRicherMultilinearTailBasis M n hn2 htb hns)).symm i).1

/-- The enumerated broad multilinear monomial tail rows are linearly
independent. -/
theorem routeBRicherMultilinearTailRows_linearIndependent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    LinearIndependent Rat
      (routeBRicherMultilinearTailRows M n hn2 htb hns) := by
  classical
  have hli :
      LinearIndependent Rat
        (fun p : (routeBRicherMultilinearTailBasis M n hn2 htb hns) =>
          (p : SATDeciderGaugeSpace M n hn2 htb hns)) := by
    simpa [routeBRicherMultilinearTailBasis] using
      MlProjFar.mlMonomialBasis_linearIndependent
        (Finset.univ :
          Finset (Fin (RouteBCookLevinDim M n hn2 htb hns)))
  simpa [routeBRicherMultilinearTailRows, Function.comp_def] using
    hli.comp
      ((Finset.equivFin
        (routeBRicherMultilinearTailBasis M n hn2 htb hns)).symm)
      (Finset.equivFin
        (routeBRicherMultilinearTailBasis M n hn2 htb hns)).symm.injective

/-- Each enumerated multilinear tail row comes from an actual support set of
Cook-Levin variables. -/
theorem routeBRicherMultilinearTailRows_exists_supportSet
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (i : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns)) :
    ∃ T : Finset (Fin (RouteBCookLevinDim M n hn2 htb hns)),
      T ∈ (Finset.univ :
        Finset (Fin (RouteBCookLevinDim M n hn2 htb hns))).powerset ∧
      T.prod (fun k =>
          (MvPolynomial.X k : SATDeciderGaugeSpace M n hn2 htb hns)) =
        routeBRicherMultilinearTailRows M n hn2 htb hns i := by
  classical
  let basis := routeBRicherMultilinearTailBasis M n hn2 htb hns
  let rowSub := (Finset.equivFin basis).symm i
  have hrow_mem : (rowSub : SATDeciderGaugeSpace M n hn2 htb hns) ∈
      MlProjFar.mlMonomialBasis
        (Finset.univ : Finset (Fin (RouteBCookLevinDim M n hn2 htb hns))) := by
    have := rowSub.property
    simp [basis, routeBRicherMultilinearTailBasis] at this ⊢
  rw [MlProjFar.mlMonomialBasis] at hrow_mem
  obtain ⟨T, hT, hrow⟩ := Finset.mem_image.mp hrow_mem
  refine ⟨T, hT, ?_⟩
  simpa [routeBRicherMultilinearTailRows, basis, rowSub] using hrow

/-- The support set chosen for an enumerated multilinear tail row. -/
noncomputable def routeBRicherMultilinearTailSupportSet
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (i : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns)) :
    Finset (Fin (RouteBCookLevinDim M n hn2 htb hns)) :=
  Classical.choose
    (routeBRicherMultilinearTailRows_exists_supportSet M n hn2 htb hns i)

/-- The chosen support set really reconstructs the enumerated tail row. -/
theorem routeBRicherMultilinearTailRows_eq_prod_supportSet
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (i : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns)) :
    (routeBRicherMultilinearTailSupportSet M n hn2 htb hns i).prod
        (fun k =>
          (MvPolynomial.X k : SATDeciderGaugeSpace M n hn2 htb hns)) =
      routeBRicherMultilinearTailRows M n hn2 htb hns i :=
  (Classical.choose_spec
    (routeBRicherMultilinearTailRows_exists_supportSet
      M n hn2 htb hns i)).2

/-- The visible coefficient coordinate associated to a multilinear tail row. -/
noncomputable def routeBRicherMultilinearTailCoeffAlpha
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (i : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns)) :
    Fin (RouteBCookLevinDim M n hn2 htb hns) →₀ Nat :=
  SymmetricPower.tagMonomial
    (routeBRicherMultilinearTailSupportSet M n hn2 htb hns i)

/-- Every enumerated tail row is the monomial at its visible coefficient
coordinate. -/
theorem routeBRicherMultilinearTailRows_eq_monomial_tailCoeffAlpha
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (i : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns)) :
    routeBRicherMultilinearTailRows M n hn2 htb hns i =
      MvPolynomial.monomial
        (routeBRicherMultilinearTailCoeffAlpha M n hn2 htb hns i)
        (1 : Rat) := by
  rw [← routeBRicherMultilinearTailRows_eq_prod_supportSet]
  rw [routeBRicherMultilinearTailCoeffAlpha, MlProjFar.prod_X_eq_monomial_tag]

/-- The row enumeration is injective because it is the inverse of
`Finset.equivFin` on the concrete basis. -/
theorem routeBRicherMultilinearTailRows_injective
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Function.Injective
      (routeBRicherMultilinearTailRows M n hn2 htb hns) := by
  classical
  intro i j hrow
  let basis := routeBRicherMultilinearTailBasis M n hn2 htb hns
  have hsub :
      (Finset.equivFin basis).symm i =
        (Finset.equivFin basis).symm j := by
    apply Subtype.ext
    simpa [routeBRicherMultilinearTailRows, basis] using hrow
  exact (Finset.equivFin basis).symm.injective hsub

/-- The visible coefficient coordinates are injective on the enumerated tail
rows. -/
theorem routeBRicherMultilinearTailCoeffAlpha_injective
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Function.Injective
      (routeBRicherMultilinearTailCoeffAlpha M n hn2 htb hns) := by
  classical
  intro i j halpha
  apply routeBRicherMultilinearTailRows_injective M n hn2 htb hns
  rw [routeBRicherMultilinearTailRows_eq_monomial_tailCoeffAlpha,
    routeBRicherMultilinearTailRows_eq_monomial_tailCoeffAlpha, halpha]

/-- The visible tail coefficient probes diagonalize the broad multilinear
tail rows. -/
theorem routeBRicherMultilinearTailRows_coeff_tailCoeffAlpha
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (i j : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns)) :
    MvPolynomial.coeff
        (routeBRicherMultilinearTailCoeffAlpha M n hn2 htb hns i)
        (routeBRicherMultilinearTailRows M n hn2 htb hns j) =
      if i = j then 1 else 0 := by
  classical
  rw [routeBRicherMultilinearTailRows_eq_monomial_tailCoeffAlpha,
    MvPolynomial.coeff_monomial]
  by_cases hij : i = j
  · subst j
    simp
  · have hne :
        ¬ routeBRicherMultilinearTailCoeffAlpha M n hn2 htb hns j =
          routeBRicherMultilinearTailCoeffAlpha M n hn2 htb hns i := by
      intro hji
      exact hij
        ((routeBRicherMultilinearTailCoeffAlpha_injective
          M n hn2 htb hns hji).symm)
    rw [if_neg hne, if_neg hij]

/-- The concrete prepended row family: the Cook-Levin NP witness followed by
the multilinear monomial tail. -/
noncomputable abbrev routeBRicherConcreteNPPrependedMultilinearRows
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1) ->
      SATDeciderGaugeSpace M n hn2 htb hns :=
  routeBRicherConcreteNPPrependedRows M n hn2 htb hns
    (routeBRicherMultilinearTailRows M n hn2 htb hns)

/-- Full prepended-row independence reduces to a head-separating monomial
coefficient: the coefficient must be nonzero on the concrete NP head row and
vanish on every broad multilinear tail row. -/
theorem routeBRicherConcreteNPPrependedMultilinearRows_linearIndependent_of_headCoeff_vanishesOnTail
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (headAlpha :
      Fin (RouteBCookLevinDim M n hn2 htb hns) →₀ Nat)
    (hhead :
      MvPolynomial.coeff headAlpha
        (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) ≠ 0)
    (hhead_tail :
      forall j : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns),
        MvPolynomial.coeff headAlpha
          (routeBRicherMultilinearTailRows M n hn2 htb hns j) = 0) :
    LinearIndependent Rat
      (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns) := by
  classical
  let tail := routeBRicherMultilinearTailRows M n hn2 htb hns
  let head := routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0
  have htail_li : LinearIndependent Rat tail := by
    simpa [tail] using
      routeBRicherMultilinearTailRows_linearIndependent M n hn2 htb hns
  have hhead_notMem : head ∉ Submodule.span Rat (Set.range tail) := by
    intro hmem
    have hvanish_span :
        ∀ q ∈ Submodule.span Rat (Set.range tail),
          MvPolynomial.coeff headAlpha q = 0 := by
      intro q hq
      exact Submodule.span_induction
        (s := Set.range tail)
        (p := fun q _ => MvPolynomial.coeff headAlpha q = 0)
        (by
          rintro q ⟨j, rfl⟩
          exact hhead_tail j)
        (by simp)
        (by
          intro x y _ _ hx hy
          simp [MvPolynomial.coeff_add, hx, hy])
        (by
          intro a x _ hx
          simp [MvPolynomial.coeff_smul, hx])
        hq
    exact hhead (hvanish_span head hmem)
  have hfull : LinearIndependent Rat (Fin.cons head tail) :=
    (linearIndependent_fin_cons).mpr ⟨htail_li, hhead_notMem⟩
  simpa [routeBRicherConcreteNPPrependedMultilinearRows,
    routeBRicherConcreteNPPrependedRows, head, tail] using hfull

/-- The finite-row candidate gauge generated by the concrete NP row plus the
multilinear monomial tail. -/
noncomputable abbrev routeBRicherConcreteNPPrependedMultilinearGauge
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns) :=
  routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
    (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns)

/-- The SAT-side projection map associated to the concrete NP row plus the
multilinear monomial tail. -/
noncomputable abbrev routeBRicherConcreteNPPrependedMultilinearProjection
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    SATDeciderGaugeSpace M n hn2 htb hns →ₗ[ℚ]
      SATDeciderGaugeSpace M n hn2 htb hns :=
  routeBNFrameCandidateAsSATGauge M n hn2 htb hns
    (routeBRicherConcreteNPPrependedMultilinearGauge M n hn2 htb hns)

/-- Actual dual coordinate maps for the concrete NP head row plus the
multilinear monomial tail, once the full prepended row family has been proved
linearly independent. -/
noncomputable def routeBRicherConcreteNPPrependedMultilinearDualCoordinates
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hli :
      LinearIndependent Rat
        (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns)) :
    Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1) ->
      SATDeciderGaugeSpace M n hn2 htb hns →ₗ[Rat] Rat :=
  finiteDualCoordinatesOfLinearIndependent
    (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns) hli

/-- The concrete multilinear-tail dual coordinates have the exact
Kronecker-duality matrix against the concrete prepended rows. -/
theorem routeBRicherConcreteNPPrependedMultilinearDualCoordinates_apply_row
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hli :
      LinearIndependent Rat
        (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns))
    (i j : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1)) :
    routeBRicherConcreteNPPrependedMultilinearDualCoordinates
        M n hn2 htb hns hli i
        (routeBRicherConcreteNPPrependedMultilinearRows
          M n hn2 htb hns j) =
      if i = j then 1 else 0 :=
  finiteDualCoordinatesOfLinearIndependent_apply_row
    (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns) hli i j

/-- The concrete multilinear tail gets explicit projection data from the
actual dual coordinate maps once row independence is supplied. -/
noncomputable def routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData_of_linearIndependentRows
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hli :
      LinearIndependent Rat
        (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns)) :
    RouteBRicherSPDPStableCandidateExplicitProjectionData
      M n hn2 htb hns
      (routeBRicherMultilinearTailRows M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidateExplicitProjectionData_of_linearIndependentRows
    M n hn2 htb hns
    (routeBRicherMultilinearTailRows M n hn2 htb hns)
    (by
      simpa [routeBRicherConcreteNPPrependedMultilinearRows,
        routeBRicherSPDPStableCandidateRows] using hli)

/-- Concrete multilinear-tail projection data from caller-supplied coefficient
probes.  This is the coefficient-probe analogue of the row-LI constructor:
the head probe must be nonzero on the concrete NP head and vanish on all
multilinear tail rows, while the tail probes diagonalize the enumerated
multilinear tail. -/
noncomputable def routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData_of_coefficientDualCoordinates
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (headAlpha :
      Fin (RouteBCookLevinDim M n hn2 htb hns) →₀ Nat)
    (tailAlpha :
      Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns) ->
        Fin (RouteBCookLevinDim M n hn2 htb hns) →₀ Nat)
    (hhead :
      MvPolynomial.coeff headAlpha
        (routeBRicherConcreteNPPrependedMultilinearRows
          M n hn2 htb hns 0) ≠ 0)
    (hhead_tail :
      forall j : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns),
        MvPolynomial.coeff headAlpha
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns (Fin.succ j)) = 0)
    (htail_tail :
      forall i j : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns),
        MvPolynomial.coeff (tailAlpha i)
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns (Fin.succ j)) =
          if i = j then 1 else 0) :
    RouteBRicherSPDPStableCandidateExplicitProjectionData
      M n hn2 htb hns
      (routeBRicherMultilinearTailRows M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidateExplicitProjectionData_of_coefficientDualCoordinates
    M n hn2 htb hns
    (routeBRicherMultilinearTailRows M n hn2 htb hns)
    headAlpha tailAlpha
    (by
      simpa [routeBRicherConcreteNPPrependedMultilinearRows,
        routeBRicherSPDPStableCandidateRows] using hhead)
    (by
      intro j
      simpa [routeBRicherConcreteNPPrependedMultilinearRows,
        routeBRicherSPDPStableCandidateRows] using hhead_tail j)
    (by
      intro i j
      simpa [routeBRicherConcreteNPPrependedMultilinearRows,
        routeBRicherSPDPStableCandidateRows] using htail_tail i j)

/-- Every tail-basis row is in the finite span of the enumerated tail rows. -/
theorem routeBRicherMultilinearTailRows_mem_span_of_mem_basis
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {p : SATDeciderGaugeSpace M n hn2 htb hns}
    (hp : p ∈ routeBRicherMultilinearTailBasis M n hn2 htb hns) :
    p ∈ finiteRowsSubmodule
      (routeBRicherMultilinearTailRows M n hn2 htb hns) := by
  apply Submodule.subset_span
  refine
    ⟨(Finset.equivFin
        (routeBRicherMultilinearTailBasis M n hn2 htb hns)) ⟨p, hp⟩, ?_⟩
  simp [routeBRicherMultilinearTailRows]

/-- Every `mlProj` output lies in the span of the multilinear monomial tail. -/
theorem routeBRicherMultilinearTailRows_mlProj_mem
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    mlProj p ∈ finiteRowsSubmodule
      (routeBRicherMultilinearTailRows M n hn2 htb hns) := by
  have hle :
      Submodule.span ℚ
          (↑(routeBRicherMultilinearTailBasis M n hn2 htb hns) :
            Set (SATDeciderGaugeSpace M n hn2 htb hns)) ≤
        finiteRowsSubmodule
          (routeBRicherMultilinearTailRows M n hn2 htb hns) := by
    apply Submodule.span_le.mpr
    intro q hq
    exact
      routeBRicherMultilinearTailRows_mem_span_of_mem_basis
        M n hn2 htb hns hq
  exact hle (WithinProfileBound.mlProj_mem_span_mlMonomialBasis p)

/-- The tail span is contained in the span after the concrete NP row is
prepended. -/
theorem finiteRowsSubmodule_le_concreteNPPrependedRows_tail
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    finiteRowsSubmodule tail ≤
      finiteRowsSubmodule
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail) := by
  apply Submodule.span_le.mpr
  rintro p ⟨i, rfl⟩
  apply Submodule.subset_span
  exact ⟨Fin.succ i, rfl⟩

/-- Every `mlProj` output lies in the span after prepending the concrete NP
row to the multilinear tail. -/
theorem routeBRicherConcreteNPPrependedMultilinearRows_mlProj_mem
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    mlProj p ∈ finiteRowsSubmodule
      (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns) := by
  exact
    finiteRowsSubmodule_le_concreteNPPrependedRows_tail
      M n hn2 htb hns
      (routeBRicherMultilinearTailRows M n hn2 htb hns)
      (routeBRicherMultilinearTailRows_mlProj_mem M n hn2 htb hns p)

/-! ## Coefficient collision for the concrete NP head monomial -/

/-- The multilinear tail contains the linear monomial at the second
Cook-Levin variable, i.e. the same monomial currently exposed as a nonzero
coefficient of the concrete NP head row. -/
theorem routeBRicherMultilinearTailBasis_mem_X_secondVar
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    (MvPolynomial.X (satDeciderGaugeSecondVar M n hn2 htb hns) :
      SATDeciderGaugeSpace M n hn2 htb hns) ∈
      routeBRicherMultilinearTailBasis M n hn2 htb hns := by
  simp [routeBRicherMultilinearTailBasis, MlProjFar.mlMonomialBasis]
  exact ⟨{satDeciderGaugeSecondVar M n hn2 htb hns}, by simp⟩

/-- The tail-row index of the second-variable linear monomial. -/
noncomputable def routeBRicherMultilinearTailHeadCoeffIndex
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns) :=
  Finset.equivFin
    (routeBRicherMultilinearTailBasis M n hn2 htb hns)
    ⟨MvPolynomial.X (satDeciderGaugeSecondVar M n hn2 htb hns),
      routeBRicherMultilinearTailBasis_mem_X_secondVar M n hn2 htb hns⟩

/-- At that explicit index, the multilinear tail row is exactly the
second-variable linear monomial. -/
theorem routeBRicherMultilinearTailRows_headCoeffIndex_eq_X_secondVar
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    routeBRicherMultilinearTailRows M n hn2 htb hns
        (routeBRicherMultilinearTailHeadCoeffIndex M n hn2 htb hns) =
      MvPolynomial.X (satDeciderGaugeSecondVar M n hn2 htb hns) := by
  simp [routeBRicherMultilinearTailRows,
    routeBRicherMultilinearTailHeadCoeffIndex]

/-- Therefore the known head-normalizing coefficient does not separate the
concrete NP head from the multilinear tail: one tail row has coefficient `1`
at the same monomial. -/
theorem routeBRicherMultilinearTailRows_headCoeffIndex_coeff_secondVar
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 1)
        (routeBRicherMultilinearTailRows M n hn2 htb hns
          (routeBRicherMultilinearTailHeadCoeffIndex M n hn2 htb hns)) =
      (1 : Rat) := by
  rw [routeBRicherMultilinearTailRows_headCoeffIndex_eq_X_secondVar]
  simp [MvPolynomial.X]

/-! ## Non-multilinear head separator for the broad multilinear tail -/

/-- Every broad multilinear tail row has zero pure-square coefficient at the
second Cook-Levin variable. -/
theorem routeBRicherMultilinearTailRows_coeff_secondVar_square
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (j : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns)) :
    MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 2)
        (routeBRicherMultilinearTailRows M n hn2 htb hns j) = 0 := by
  classical
  let basis := routeBRicherMultilinearTailBasis M n hn2 htb hns
  let rowSub := (Finset.equivFin basis).symm j
  change MvPolynomial.coeff
      (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 2)
      (rowSub : SATDeciderGaugeSpace M n hn2 htb hns) = 0
  have hrow_mem : (rowSub : SATDeciderGaugeSpace M n hn2 htb hns) ∈
      MlProjFar.mlMonomialBasis
        (Finset.univ : Finset (Fin (RouteBCookLevinDim M n hn2 htb hns))) := by
    have := rowSub.property
    simp [basis, routeBRicherMultilinearTailBasis] at this ⊢
  rw [MlProjFar.mlMonomialBasis] at hrow_mem
  obtain ⟨T, _hT, hrow⟩ := Finset.mem_image.mp hrow_mem
  rw [← hrow, MlProjFar.prod_X_eq_monomial_tag, MvPolynomial.coeff_monomial]
  rw [if_neg]
  intro hsq
  have hsecond := DFunLike.congr_fun hsq
    (satDeciderGaugeSecondVar M n hn2 htb hns)
  rw [SymmetricPower.tagMonomial_apply] at hsecond
  by_cases hmem : satDeciderGaugeSecondVar M n hn2 htb hns ∈ T
  · simp [hmem] at hsecond
  · simp [hmem] at hsecond

/-- The concrete NP head row has pure-square coefficient `1` at the second
Cook-Levin variable. -/
theorem routeBRicherConcreteNPWitnessRows_zero_coeff_secondVar_square
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 2)
        (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) = (1 : Rat) := by
  rw [routeBRicherConcreteNPWitnessRows_eq_embed,
    routeBRicherConcreteNPWitnessQ_embed_eq_compiledPoly]
  exact compiledPoly_coeff_secondVar_square M n hn2 htb hns

/-- The concrete NP head row has a nonzero pure-square coefficient at the
second Cook-Levin variable. -/
theorem routeBRicherConcreteNPWitnessRows_zero_coeff_secondVar_square_ne_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 2)
        (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) ≠ 0 := by
  rw [routeBRicherConcreteNPWitnessRows_zero_coeff_secondVar_square]
  norm_num

/-- The concrete NP row prepended to the broad multilinear tail is linearly
independent, separated by the non-multilinear square coefficient. -/
theorem routeBRicherConcreteNPPrependedMultilinearRows_linearIndependent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    LinearIndependent Rat
      (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns) :=
  routeBRicherConcreteNPPrependedMultilinearRows_linearIndependent_of_headCoeff_vanishesOnTail
    M n hn2 htb hns
    (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 2)
    (routeBRicherConcreteNPWitnessRows_zero_coeff_secondVar_square_ne_zero
      M n hn2 htb hns)
    (routeBRicherMultilinearTailRows_coeff_secondVar_square
      M n hn2 htb hns)

/-- The concrete broad multilinear-tail projection data, now instantiated
without caller-supplied independence or coefficient-probe premises. -/
noncomputable def routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateExplicitProjectionData
      M n hn2 htb hns
      (routeBRicherMultilinearTailRows M n hn2 htb hns) :=
  routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData_of_coefficientDualCoordinates
    M n hn2 htb hns
    (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 2)
    (routeBRicherMultilinearTailCoeffAlpha M n hn2 htb hns)
    (by
      simpa [routeBRicherConcreteNPPrependedMultilinearRows,
        routeBRicherConcreteNPPrependedRows] using
        routeBRicherConcreteNPWitnessRows_zero_coeff_secondVar_square_ne_zero
          M n hn2 htb hns)
    (by
      intro j
      simpa [routeBRicherConcreteNPPrependedMultilinearRows,
        routeBRicherConcreteNPPrependedRows] using
        routeBRicherMultilinearTailRows_coeff_secondVar_square
          M n hn2 htb hns j)
    (by
      intro i j
      simpa [routeBRicherConcreteNPPrependedMultilinearRows,
        routeBRicherConcreteNPPrependedRows] using
        routeBRicherMultilinearTailRows_coeff_tailCoeffAlpha
          M n hn2 htb hns i j)

/-! ## Designed coefficient-dual complement criterion -/

/-- If the displayed pure-square head coefficient and every displayed
multilinear-tail coefficient vanish on `p`, then `p` lies in the kernel
complement of the designed coefficient-dual projection. -/
theorem routeBRicherConcreteNPPrependedMultilinearExplicitProjection_mem_complement_of_coeff_vanish
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (hhead :
      MvPolynomial.coeff
          (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 2)
          p = 0)
    (htail :
      forall i : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns),
        MvPolynomial.coeff
          (routeBRicherMultilinearTailCoeffAlpha M n hn2 htb hns i)
          p = 0) :
    p ∈
      (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
        M n hn2 htb hns).complement := by
  classical
  let tail := routeBRicherMultilinearTailRows M n hn2 htb hns
  let rows := routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail
  let headAlpha :
      Fin (RouteBCookLevinDim M n hn2 htb hns) →₀ Nat :=
    Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 2
  let tailAlpha :
      Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns) ->
        Fin (RouteBCookLevinDim M n hn2 htb hns) →₀ Nat :=
    routeBRicherMultilinearTailCoeffAlpha M n hn2 htb hns
  let coord :=
    routeBRicherSPDPStableCandidateCoefficientDualCoordinates
      M n hn2 htb hns tail headAlpha tailAlpha
  let D :=
    routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
      M n hn2 htb hns
  have hcoord_zero :
      forall i : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1),
        coord i p = 0 := by
    intro i
    refine Fin.cases ?head ?tailCase i
    · have hhead_row :
          MvPolynomial.coeff headAlpha (rows 0) = (1 : Rat) := by
        simpa [headAlpha, rows, tail, routeBRicherSPDPStableCandidateRows,
          routeBRicherConcreteNPPrependedRows] using
          routeBRicherConcreteNPWitnessRows_zero_coeff_secondVar_square
            M n hn2 htb hns
      simp [coord, routeBRicherSPDPStableCandidateCoefficientDualCoordinates,
        headAlpha, rows, hhead_row, hhead]
    · intro i
      have hhead_row :
          MvPolynomial.coeff headAlpha (rows 0) = (1 : Rat) := by
        simpa [headAlpha, rows, tail, routeBRicherSPDPStableCandidateRows,
          routeBRicherConcreteNPPrependedRows] using
          routeBRicherConcreteNPWitnessRows_zero_coeff_secondVar_square
            M n hn2 htb hns
      simp [coord, routeBRicherSPDPStableCandidateCoefficientDualCoordinates,
        headAlpha, tailAlpha, rows, hhead_row, hhead, htail i]
  have hproj_zero : D.projection p = 0 := by
    have hsum :
        routeBRicherSPDPStableCandidateDualCoordinateProjection
            M n hn2 htb hns tail coord p = 0 := by
      rw [routeBRicherSPDPStableCandidateDualCoordinateProjection_apply]
      simp [hcoord_zero]
    simpa [D, coord, headAlpha, tailAlpha, tail,
      routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData,
      routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData_of_coefficientDualCoordinates,
      routeBRicherSPDPStableCandidateExplicitProjectionData_of_coefficientDualCoordinates,
      routeBRicherSPDPStableCandidateExplicitProjectionData_of_dualCoordinates,
      RouteBRicherSPDPStableCandidateExplicitProjectionData.ofProjection,
      RouteBRicherSPDPStableCandidateExplicitProjectionData.ofProjectionWithKernel] using hsum
  exact (D.projection_apply_eq_zero_iff p).mp hproj_zero

/-- The displayed complement of the designed coefficient-dual projection is
exactly the common zero locus of the pure-square head probe and all concrete
multilinear-tail coefficient probes. -/
theorem routeBRicherConcreteNPPrependedMultilinearExplicitProjection_mem_complement_iff_coeff_vanish
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    p ∈
        (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
          M n hn2 htb hns).complement ↔
      MvPolynomial.coeff
          (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 2)
          p = 0 ∧
        forall i : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns),
          MvPolynomial.coeff
            (routeBRicherMultilinearTailCoeffAlpha M n hn2 htb hns i)
            p = 0 := by
  classical
  constructor
  · intro hp
    let tail := routeBRicherMultilinearTailRows M n hn2 htb hns
    let rows := routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail
    let headAlpha :
        Fin (RouteBCookLevinDim M n hn2 htb hns) →₀ Nat :=
      Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 2
    let tailAlpha :
        Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns) ->
          Fin (RouteBCookLevinDim M n hn2 htb hns) →₀ Nat :=
      routeBRicherMultilinearTailCoeffAlpha M n hn2 htb hns
    let coord :=
      routeBRicherSPDPStableCandidateCoefficientDualCoordinates
        M n hn2 htb hns tail headAlpha tailAlpha
    let D :=
      routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
        M n hn2 htb hns
    have hpZero : D.projection p = 0 :=
      (D.projection_apply_eq_zero_iff p).mpr hp
    have hhead_row :
        MvPolynomial.coeff headAlpha (rows 0) = (1 : Rat) := by
      simpa [headAlpha, rows, tail, routeBRicherSPDPStableCandidateRows,
        routeBRicherConcreteNPPrependedRows] using
        routeBRicherConcreteNPWitnessRows_zero_coeff_secondVar_square
          M n hn2 htb hns
    have hsumZero :
        routeBRicherSPDPStableCandidateDualCoordinateProjection
            M n hn2 htb hns tail coord p = 0 := by
      simpa [D, coord, headAlpha, tailAlpha, tail,
        routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData,
        routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData_of_coefficientDualCoordinates,
        routeBRicherSPDPStableCandidateExplicitProjectionData_of_coefficientDualCoordinates,
        routeBRicherSPDPStableCandidateExplicitProjectionData_of_dualCoordinates,
        RouteBRicherSPDPStableCandidateExplicitProjectionData.ofProjection,
        RouteBRicherSPDPStableCandidateExplicitProjectionData.ofProjectionWithKernel] using hpZero
    have hdual :
        forall i j,
          coord i (routeBRicherSPDPStableCandidateRows
            M n hn2 htb hns tail j) =
            if i = j then 1 else 0 := by
      exact
        routeBRicherSPDPStableCandidateCoefficientDualCoordinates_hdual
          M n hn2 htb hns tail headAlpha tailAlpha
          (by
            simpa [headAlpha, tail, routeBRicherSPDPStableCandidateRows,
              routeBRicherConcreteNPPrependedRows] using
              routeBRicherConcreteNPWitnessRows_zero_coeff_secondVar_square_ne_zero
                M n hn2 htb hns)
          (by
            intro j
            simpa [headAlpha, tail, routeBRicherSPDPStableCandidateRows,
              routeBRicherConcreteNPPrependedRows] using
              routeBRicherMultilinearTailRows_coeff_secondVar_square
                M n hn2 htb hns j)
          (by
            intro i j
            simpa [tailAlpha, tail, routeBRicherSPDPStableCandidateRows,
              routeBRicherConcreteNPPrependedRows] using
              routeBRicherMultilinearTailRows_coeff_tailCoeffAlpha
                M n hn2 htb hns i j)
    have hcoord_zero :
        forall i : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1),
          coord i p = 0 :=
      (routeBRicherSPDPStableCandidateDualCoordinateProjection_apply_eq_zero_iff
        M n hn2 htb hns tail coord hdual p).mp hsumZero
    have hhead :
        MvPolynomial.coeff headAlpha p = 0 := by
      have h0 := hcoord_zero 0
      simpa [coord, routeBRicherSPDPStableCandidateCoefficientDualCoordinates,
        headAlpha, rows, hhead_row] using h0
    refine ⟨by simpa [headAlpha] using hhead, ?_⟩
    intro i
    have hi := hcoord_zero (Fin.succ i)
    simpa [coord, routeBRicherSPDPStableCandidateCoefficientDualCoordinates,
      headAlpha, tailAlpha, rows, hhead_row, hhead] using hi
  · rintro ⟨hhead, htail⟩
    exact
      routeBRicherConcreteNPPrependedMultilinearExplicitProjection_mem_complement_of_coeff_vanish
        M n hn2 htb hns p hhead htail

/-- Coefficient-level generator stability for the designed coefficient-dual
projection: every admissible generator row of a vector in the displayed
complement still has zero pure-square head coefficient and zero values at all
displayed multilinear tail probes. -/
def RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionGeneratorCoeffVanishes
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  forall (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    p ∈
      (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
        M n hn2 htb hns).complement ->
    MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 2)
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) = 0 ∧
      forall i : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns),
        MvPolynomial.coeff
          (routeBRicherMultilinearTailCoeffAlpha M n hn2 htb hns i)
          (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) = 0

/-- The coefficient-vanishing criterion proves operator-level stability of
the designed coefficient-dual complement. -/
theorem routeBRicherConcreteNPPrependedMultilinearExplicitProjectionStableGeneratorMaps_of_generatorCoeffVanishes
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hvanish :
      RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionGeneratorCoeffVanishes
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateExplicitComplementStableGeneratorMaps
      M n hn2 htb hns
      (routeBRicherMultilinearTailRows M n hn2 htb hns)
      (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
        M n hn2 htb hns).complement := by
  intro spdpKappa ell S shift hSlen hshiftDegree hshiftVars hadm q hq
  rcases hq with ⟨p, hpComplement, rfl⟩
  obtain ⟨hhead, htail⟩ :=
    hvanish spdpKappa ell p S shift
      hSlen hshiftDegree hshiftVars hadm hpComplement
  simpa [routeBSPDPGeneratorRowLinearMap_apply] using
    routeBRicherConcreteNPPrependedMultilinearExplicitProjection_mem_complement_of_coeff_vanish
      M n hn2 htb hns
      (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)
      hhead htail

/-! ## Designed explicit-projection descent surface -/

/-- Descent for the designed coefficient-dual multilinear projection.

Unlike the ambient finite-row projection interface below, this is stated
against the concrete projection data whose coordinates are displayed
coefficient probes: the pure-square head probe and the multilinear monomial
tail probes. -/
def RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
    M n hn2 htb hns).ProjectionDescent

/-- Escape witness for the designed coefficient-dual multilinear projection:
a vector in the displayed complement whose admissible generator row becomes
visible after applying the designed projection. -/
def RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
    M n hn2 htb hns).ProjectionEscapeWitness

/-- Coordinate-visible escape for the designed coefficient-dual multilinear
projection.  This exposes the exact coefficient check needed to instantiate
`ProjectionEscapeWitness` for the displayed projection data. -/
def RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionVisibleCoefficientEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  exists (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns)
    (μ : Fin (RouteBCookLevinDim M n hn2 htb hns) →₀ Nat),
    S.length = spdpKappa ∧
    shift.totalDegree <= ell ∧
    shift.vars <= S.toFinset ∧
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ∧
    (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
      M n hn2 htb hns).projection p = 0 ∧
    MvPolynomial.coeff μ
      ((routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
        M n hn2 htb hns).projection
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)) ≠ 0

/-- Constructor from an explicit complement vector and visible projected
coefficient into the designed coefficient-dual projection escape witness. -/
theorem routeBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness_of_explicitCoeff
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns)
    (μ : Fin (RouteBCookLevinDim M n hn2 htb hns) →₀ Nat)
    (hSlen : S.length = spdpKappa)
    (hshiftDegree : shift.totalDegree <= ell)
    (hshiftVars : shift.vars <= S.toFinset)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition S)
    (hpZero :
      (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
        M n hn2 htb hns).projection p = 0)
    (hcoeff :
      MvPolynomial.coeff μ
        ((routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
          M n hn2 htb hns).projection
          (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)) ≠ 0) :
    RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness
      M n hn2 htb hns := by
  let D :=
    routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
      M n hn2 htb hns
  refine ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hshiftVars, hadm, ?_, ?_⟩
  · exact (D.projection_apply_eq_zero_iff p).mp hpZero
  · intro hrowZero
    exact hcoeff (by simp [hrowZero])

/-- A visible coefficient witness instantiates the designed projection escape
branch. -/
theorem routeBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness_of_visibleCoefficientEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hcoord :
      RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionVisibleCoefficientEscapeWitness
        M n hn2 htb hns) :
    RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness
      M n hn2 htb hns := by
  rcases hcoord with ⟨spdpKappa, ell, p, S, shift, μ,
    hSlen, hshiftDegree, hshiftVars, hadm, hpZero, hcoeff⟩
  exact
    routeBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness_of_explicitCoeff
      M n hn2 htb hns spdpKappa ell p S shift μ
      hSlen hshiftDegree hshiftVars hadm hpZero hcoeff

/-- The first-square probe for the designed coefficient-dual multilinear
projection.  It is the smallest non-multilinear monomial avoiding the
second-variable pure-square head probe. -/
noncomputable def routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    SATDeciderGaugeSpace M n hn2 htb hns :=
  MvPolynomial.X (satDeciderGaugeFirstVar M n hn2 htb hns) *
    MvPolynomial.X (satDeciderGaugeFirstVar M n hn2 htb hns)

/-- The first Cook-Levin coordinate is distinct from the second. -/
theorem satDeciderGaugeFirstVar_ne_secondVar
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    satDeciderGaugeFirstVar M n hn2 htb hns ≠
      satDeciderGaugeSecondVar M n hn2 htb hns := by
  intro h
  have hval := congrArg Fin.val h
  norm_num [satDeciderGaugeFirstVar, satDeciderGaugeSecondVar] at hval

/-- The first-square probe is the pure square monomial at the first
Cook-Levin coordinate. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_eq_monomial
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns =
      MvPolynomial.monomial
        (Finsupp.single (satDeciderGaugeFirstVar M n hn2 htb hns) 2)
        (1 : Rat) := by
  unfold routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
  let first := satDeciderGaugeFirstVar M n hn2 htb hns
  change
    MvPolynomial.monomial (Finsupp.single first 1) (1 : Rat) *
        MvPolynomial.monomial (Finsupp.single first 1) (1 : Rat) =
      MvPolynomial.monomial (Finsupp.single first 2) (1 : Rat)
  rw [MvPolynomial.monomial_mul, mul_one]
  have hsingle :
      Finsupp.single first 1 + Finsupp.single first 1 =
        (Finsupp.single first 2 :
          Fin (RouteBCookLevinDim M n hn2 htb hns) →₀ Nat) := by
    ext i
    by_cases hi : i = first
    · subst i
      simp
    · simp [Finsupp.single_eq_of_ne hi]
  rw [hsingle]

/-- The first-square probe has zero value at the designed pure-square head
coefficient, which is attached to the second Cook-Levin coordinate. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_coeff_secondVar_square
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 2)
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns) = 0 := by
  rw [routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_eq_monomial,
    MvPolynomial.coeff_monomial]
  rw [if_neg]
  intro hsq
  have hne := satDeciderGaugeFirstVar_ne_secondVar M n hn2 htb hns
  have hcoord := DFunLike.congr_fun hsq
    (satDeciderGaugeSecondVar M n hn2 htb hns)
  simp [hne] at hcoord

/-- The first-square probe has zero value at every displayed multilinear tail
coefficient. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_coeff_tailCoeffAlpha
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (i : Fin (routeBRicherMultilinearTailRowCount M n hn2 htb hns)) :
    MvPolynomial.coeff
        (routeBRicherMultilinearTailCoeffAlpha M n hn2 htb hns i)
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns) = 0 := by
  rw [routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_eq_monomial,
    MvPolynomial.coeff_monomial]
  rw [if_neg]
  intro hsq
  have hml :
      Finsupp.IsMultilinear
        (routeBRicherMultilinearTailCoeffAlpha M n hn2 htb hns i) := by
    simpa [routeBRicherMultilinearTailCoeffAlpha] using
      SymmetricPower.tagMonomial_isMultilinear
        (routeBRicherMultilinearTailSupportSet M n hn2 htb hns i)
  have hfirst := hml (satDeciderGaugeFirstVar M n hn2 htb hns)
  rw [← hsq] at hfirst
  norm_num at hfirst

/-- The first-square probe is in the displayed complement of the designed
coefficient-dual multilinear projection. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_mem_complement
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns ∈
      (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
        M n hn2 htb hns).complement :=
  routeBRicherConcreteNPPrependedMultilinearExplicitProjection_mem_complement_of_coeff_vanish
    M n hn2 htb hns
    (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
      M n hn2 htb hns)
    (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_coeff_secondVar_square
      M n hn2 htb hns)
    (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_coeff_tailCoeffAlpha
      M n hn2 htb hns)

/-- Equivalently, the designed projection kills the first-square probe. -/
theorem routeBRicherConcreteNPPrependedMultilinearExplicitProjection_firstSquareProbe_eq_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
      M n hn2 htb hns).projection
      (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns) = 0 := by
  let D :=
    routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
      M n hn2 htb hns
  exact
    (D.projection_apply_eq_zero_iff
      (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns)).mpr
      (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_mem_complement
        M n hn2 htb hns)

/-- The singleton first-coordinate derivative of the first-square probe is the
visible linear row `2 • X_first` after multilinear projection. -/
theorem routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_singletonRow_eq
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
          M n hn2 htb hns)
        [satDeciderGaugeFirstVar M n hn2 htb hns]
        (1 : SATDeciderGaugeSpace M n hn2 htb hns) =
      (2 : Rat) •
        MvPolynomial.X (satDeciderGaugeFirstVar M n hn2 htb hns) := by
  let first := satDeciderGaugeFirstVar M n hn2 htb hns
  have hderiv :
      SPDP.iterDerivList [first]
          (MvPolynomial.X first * MvPolynomial.X first :
            SATDeciderGaugeSpace M n hn2 htb hns) =
        (2 : Rat) • MvPolynomial.X first := by
    unfold SPDP.iterDerivList
    change MvPolynomial.pderiv first
        (MvPolynomial.X first * MvPolynomial.X first :
          SATDeciderGaugeSpace M n hn2 htb hns) =
      (2 : Rat) • MvPolynomial.X first
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self]
    simp [two_smul]
  change
    mlProj
        ((1 : SATDeciderGaugeSpace M n hn2 htb hns) *
          SPDP.iterDerivList [first]
            (MvPolynomial.X first * MvPolynomial.X first :
              SATDeciderGaugeSpace M n hn2 htb hns)) =
      (2 : Rat) • MvPolynomial.X first
  rw [hderiv, one_mul, MultilinearSPDP.mlProj_smul,
    SymmetricPower.mlProj_X]

/-- The designed projection sees a nonzero first-linear coefficient on the
singleton derivative row of the first-square complement probe. -/
theorem routeBRicherConcreteNPPrependedMultilinearExplicitProjection_firstSquare_singletonCoeff_ne_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeFirstVar M n hn2 htb hns) 1)
        ((routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
          M n hn2 htb hns).projection
          (routeBSPDPGeneratorRow M n hn2 htb hns
            (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
              M n hn2 htb hns)
            [satDeciderGaugeFirstVar M n hn2 htb hns]
            (1 : SATDeciderGaugeSpace M n hn2 htb hns))) ≠ 0 := by
  let D :=
    routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
      M n hn2 htb hns
  let row :=
    routeBSPDPGeneratorRow M n hn2 htb hns
      (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns)
      [satDeciderGaugeFirstVar M n hn2 htb hns]
      (1 : SATDeciderGaugeSpace M n hn2 htb hns)
  have hrowMem :
      row ∈
        RouteBRicherSPDPStableCandidateRowSpan
          M n hn2 htb hns
          (routeBRicherMultilinearTailRows M n hn2 htb hns) := by
    change row ∈
      finiteRowsSubmodule
        (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns)
    dsimp [row, routeBSPDPGeneratorRow]
    exact
      routeBRicherConcreteNPPrependedMultilinearRows_mlProj_mem
        M n hn2 htb hns
        ((1 : SATDeciderGaugeSpace M n hn2 htb hns) *
          SPDP.iterDerivList
            [satDeciderGaugeFirstVar M n hn2 htb hns]
            (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
              M n hn2 htb hns))
  have hfix : D.projection row = row :=
    D.projection_fixes_of_mem_rowSpan hrowMem
  rw [show
      (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
        M n hn2 htb hns).projection row = row by
        simpa [D] using hfix]
  dsimp [row]
  rw [routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_singletonRow_eq]
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_X']
  simp

/-- Sharp one-line reduction for the concrete first-square branch.

If the singleton derivative row of the first-square complement probe has a
visible first-linear coefficient after applying the designed projection, then
the designed projection escape witness is instantiated with `p = X_first^2`,
`S = [first]`, and `shift = 1`. -/
theorem routeBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness_of_firstSquare_singletonCoeff
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hcoeff :
      MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeFirstVar M n hn2 htb hns) 1)
        ((routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
          M n hn2 htb hns).projection
          (routeBSPDPGeneratorRow M n hn2 htb hns
            (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
              M n hn2 htb hns)
            [satDeciderGaugeFirstVar M n hn2 htb hns]
            (1 : SATDeciderGaugeSpace M n hn2 htb hns))) ≠ 0) :
    RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness
      M n hn2 htb hns := by
  refine
    routeBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness_of_explicitCoeff
      M n hn2 htb hns
      1 0
      (routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
        M n hn2 htb hns)
      [satDeciderGaugeFirstVar M n hn2 htb hns]
      (1 : SATDeciderGaugeSpace M n hn2 htb hns)
      (Finsupp.single (satDeciderGaugeFirstVar M n hn2 htb hns) 1)
      ?_ ?_ ?_ ?_
      (routeBRicherConcreteNPPrependedMultilinearExplicitProjection_firstSquareProbe_eq_zero
        M n hn2 htb hns)
      hcoeff
  · simp
  · simp [MvPolynomial.totalDegree_one]
  · simp [MvPolynomial.vars_one]
  · constructor
    · simp
    · intro b
      simpa using
        (List.length_filter_le
          (fun i =>
            (cook_levin_compilation M n hn2 htb hns).partition.assign i = b)
          [satDeciderGaugeFirstVar M n hn2 htb hns])

/-- Concrete escape witness for the designed coefficient-dual multilinear
projection, using the first-square complement probe and singleton derivative
row. -/
theorem routeBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness_firstSquare_singleton
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness
      M n hn2 htb hns :=
  routeBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness_of_firstSquare_singletonCoeff
    M n hn2 htb hns
    (routeBRicherConcreteNPPrependedMultilinearExplicitProjection_firstSquare_singletonCoeff_ne_zero
      M n hn2 htb hns)

/-- Descent for the designed projection is exactly invariance of its displayed
coefficient-dual complement. -/
theorem routeBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent_iff_explicitComplementInvariant
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent
        M n hn2 htb hns ↔
      RouteBRicherSPDPStableCandidateExplicitComplementInvariant
        M n hn2 htb hns
        (routeBRicherMultilinearTailRows M n hn2 htb hns)
        (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
          M n hn2 htb hns).complement := by
  simpa [RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent] using
    (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
      M n hn2 htb hns).projectionDescent_iff_explicitComplementInvariant

/-- Operator-level stability of the designed complement proves the
paper-faithful projection-descent condition. -/
theorem routeBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent_of_stableGeneratorMaps
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hstable :
      RouteBRicherSPDPStableCandidateExplicitComplementStableGeneratorMaps
        M n hn2 htb hns
        (routeBRicherMultilinearTailRows M n hn2 htb hns)
        (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
          M n hn2 htb hns).complement) :
    RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent
      M n hn2 htb hns := by
  exact
    (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent_iff_explicitComplementInvariant
      M n hn2 htb hns).mpr
      (routeBRicherSPDPStableCandidate_explicitComplementInvariant_of_generatorRowLinearMap_maps_complement
        M n hn2 htb hns
        (routeBRicherMultilinearTailRows M n hn2 htb hns)
        (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
          M n hn2 htb hns).complement
        hstable)

/-- The coefficient-vanishing criterion closes descent for the designed
coefficient-dual multilinear projection. -/
theorem routeBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent_of_generatorCoeffVanishes
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hvanish :
      RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionGeneratorCoeffVanishes
        M n hn2 htb hns) :
    RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent
      M n hn2 htb hns :=
  routeBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent_of_stableGeneratorMaps
    M n hn2 htb hns
    (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionStableGeneratorMaps_of_generatorCoeffVanishes
      M n hn2 htb hns hvanish)

/-- Designed projection escape is exactly failure of designed projection
descent. -/
theorem routeBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness_iff_not_projectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness
        M n hn2 htb hns ↔
      ¬ RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent
        M n hn2 htb hns := by
  simpa [
    RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness,
    RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent] using
    (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
      M n hn2 htb hns).projectionEscapeWitness_iff_not_projectionDescent

/-- The first-square singleton escape refutes descent for the designed
coefficient-dual projection. -/
theorem routeBRicherConcreteNPPrependedMultilinearExplicitProjection_not_descent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    ¬ RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent
        M n hn2 htb hns :=
  (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness_iff_not_projectionDescent
    M n hn2 htb hns).mp
    (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness_firstSquare_singleton
      M n hn2 htb hns)

/-- Therefore the actual stable-generator-map condition is false for the
designed coefficient-dual complement. -/
theorem routeBRicherConcreteNPPrependedMultilinearExplicitProjection_not_stableGeneratorMaps
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    ¬ RouteBRicherSPDPStableCandidateExplicitComplementStableGeneratorMaps
        M n hn2 htb hns
        (routeBRicherMultilinearTailRows M n hn2 htb hns)
        (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
          M n hn2 htb hns).complement := by
  intro hstable
  exact
    routeBRicherConcreteNPPrependedMultilinearExplicitProjection_not_descent
      M n hn2 htb hns
      (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent_of_stableGeneratorMaps
        M n hn2 htb hns hstable)

/-- The coefficient-vanishing stability criterion cannot hold for this
designed complement, because it would imply the refuted descent theorem. -/
theorem routeBRicherConcreteNPPrependedMultilinearExplicitProjection_not_generatorCoeffVanishes
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    ¬ RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionGeneratorCoeffVanishes
        M n hn2 htb hns := by
  intro hvanish
  exact
    routeBRicherConcreteNPPrependedMultilinearExplicitProjection_not_descent
      M n hn2 htb hns
      (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent_of_generatorCoeffVanishes
        M n hn2 htb hns hvanish)

/-- Paper-admissibility package for the designed coefficient-dual projection.

This deliberately bundles the three Route B sides that the projection would
have to satisfy in order to be usable as a paper-faithful admissible
projection: rank-monotonicity, stability of the displayed complement under all
admissible SPDP generator maps, and the corresponding projection-descent
equation. -/
structure RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionPaperAdmissible
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop where
  rank_monotone :
    GaugeMonotonicity.IsRankMonotoneGauge
      (cook_levin_compilation M n hn2 htb hns).partition
      (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
        M n hn2 htb hns).projection
  stable_generator_maps :
    RouteBRicherSPDPStableCandidateExplicitComplementStableGeneratorMaps
      M n hn2 htb hns
      (routeBRicherMultilinearTailRows M n hn2 htb hns)
      (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
        M n hn2 htb hns).complement
  descent :
    RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent
      M n hn2 htb hns

/-- Any escape witness excludes paper-admissibility for the designed
coefficient-dual projection: the rank-monotone and stability fields cannot
rescue a projection whose required descent equation already fails. -/
theorem routeBRicherConcreteNPPrependedMultilinearExplicitProjection_not_paperAdmissible_of_escapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hescape :
      RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness
        M n hn2 htb hns) :
    ¬ RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionPaperAdmissible
        M n hn2 htb hns := by
  intro hadm
  exact
    ((routeBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness_iff_not_projectionDescent
      M n hn2 htb hns).mp hescape) hadm.descent

/-- The first-square singleton escape proves that the designed coefficient-dual
projection is not a paper-admissible Route B projection.  In particular it
cannot simultaneously satisfy the rank-monotone, stable-generator-map, and
descent obligations needed by the paper-faithful Route B side. -/
theorem routeBRicherConcreteNPPrependedMultilinearExplicitProjection_not_paperAdmissible
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    ¬ RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionPaperAdmissible
        M n hn2 htb hns :=
  routeBRicherConcreteNPPrependedMultilinearExplicitProjection_not_paperAdmissible_of_escapeWitness
    M n hn2 htb hns
    (routeBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness_firstSquare_singleton
      M n hn2 htb hns)

/-- The designed coefficient-dual projection has the honest Route B fork:
either it descends through all admissible generator rows, or Lean exposes a
projection-escape witness in the displayed complement. -/
theorem routeBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent_or_escapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent
        M n hn2 htb hns ∨
      RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness
        M n hn2 htb hns := by
  by_cases hdesc :
      RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent
        M n hn2 htb hns
  · exact Or.inl hdesc
  · exact Or.inr
      ((routeBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness_iff_not_projectionDescent
        M n hn2 htb hns).mpr hdesc)

/-- The concrete NP row plus multilinear monomial tail satisfies the explicit
head/tail SPDP row-closure package. -/
theorem routeBRicherConcreteNPPrependedMultilinearRows_spdpRowClosurePackage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
      M n hn2 htb hns
      (routeBRicherMultilinearTailRows M n hn2 htb hns) where
  concrete_row_closure := by
    intro _spdpKappa _ell S shift _hSlen _hshiftDegree _hshiftVars _hadm
    exact
      routeBRicherConcreteNPPrependedMultilinearRows_mlProj_mem
        M n hn2 htb hns
        (shift *
          SPDP.iterDerivList S
            (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0))
  tail_row_closure := by
    intro _spdpKappa _ell S shift _hSlen _hshiftDegree _hshiftVars _hadm i
    exact
      routeBRicherConcreteNPPrependedMultilinearRows_mlProj_mem
        M n hn2 htb hns
        (shift *
          SPDP.iterDerivList S
            (routeBRicherMultilinearTailRows M n hn2 htb hns i))

/-- The concrete NP row plus multilinear monomial tail satisfies the
finite-row SPDP closure half. -/
theorem routeBRicherConcreteNPPrependedMultilinearRows_spdpClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherGaugeFiniteRowsSPDPClosure M n hn2 htb hns
      (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns) :=
  routeBRicherConcreteNPPrependedRows_spdpClosure_of_rowClosurePackage
    M n hn2 htb hns
    (routeBRicherMultilinearTailRows M n hn2 htb hns)
    (routeBRicherConcreteNPPrependedMultilinearRows_spdpRowClosurePackage
      M n hn2 htb hns)

/-- For the concrete multilinear-tail gauge, kernel/complement compatibility
is equivalent to saying that every SPDP generator row of the projection
residual vanishes.

This is the sharp obstruction exposed by using the full multilinear tail:
every SPDP generator row is an `mlProj` output, hence lies in the selected
finite row span and is fixed by the finite-row projection.  Therefore the
generic "projection kills the residual generator" condition can only hold if
the residual generator is already zero. -/
theorem routeBRicherConcreteNPPrependedMultilinearRows_kernelCompatibility_iff_residualGenerator_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherGaugeFiniteRowsSPDPKernelCompatibility M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns) ↔
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
          (p -
            routeBRicherConcreteNPPrependedMultilinearProjection
              M n hn2 htb hns p)
          S shift = 0 := by
  constructor
  · intro hker spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm
    let rows :=
      routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns
    let Pi :=
      routeBRicherConcreteNPPrependedMultilinearProjection M n hn2 htb hns
    let residualRow :=
      routeBSPDPGeneratorRow M n hn2 htb hns (p - Pi p) S shift
    have hmem : residualRow ∈ finiteRowsSubmodule rows := by
      dsimp [residualRow]
      exact
        routeBRicherConcreteNPPrependedMultilinearRows_mlProj_mem
          M n hn2 htb hns
          (shift * SPDP.iterDerivList S (p - Pi p))
    have hfixed : Pi residualRow = residualRow := by
      simpa [Pi, rows,
        routeBRicherConcreteNPPrependedMultilinearProjection,
        routeBRicherConcreteNPPrependedMultilinearGauge] using
        routeBRicherFiniteRowsCandidateGauge_fixed_of_mem
          M n hn2 htb hns rows hmem
    have hzero : Pi residualRow = 0 := by
      simpa [Pi, rows, residualRow,
        routeBRicherConcreteNPPrependedMultilinearProjection,
        routeBRicherConcreteNPPrependedMultilinearGauge] using
        hker spdpKappa ell p S shift
          hSlen hshiftDegree hshiftVars hadm
    rwa [hfixed] at hzero
  · intro hzero spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm
    have hrowzero :
        routeBSPDPGeneratorRow M n hn2 htb hns
          (p -
            routeBNFrameCandidateAsSATGauge M n hn2 htb hns
              (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
                (routeBRicherConcreteNPPrependedMultilinearRows
                  M n hn2 htb hns)) p)
          S shift = 0 := by
      simpa [routeBRicherConcreteNPPrependedMultilinearProjection,
        routeBRicherConcreteNPPrependedMultilinearGauge] using
        hzero spdpKappa ell p S shift
          hSlen hshiftDegree hshiftVars hadm
    rw [hrowzero]
    simp

/-- The concrete multilinear-tail map-preimage target follows from the sharp
residual-annihilation condition above. -/
theorem routeBRicherConcreteNPPrependedMultilinearRows_spdpMapPreimage_of_residualGenerator_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hzero :
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
          (p -
            routeBRicherConcreteNPPrependedMultilinearProjection
              M n hn2 htb hns p)
          S shift = 0) :
    RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns
      (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns) :=
  routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_spdpClosure_kernelCompatibility
    M n hn2 htb hns
    (routeBRicherMultilinearTailRows M n hn2 htb hns)
    (routeBRicherConcreteNPPrependedMultilinearRows_spdpClosure
      M n hn2 htb hns)
    ((routeBRicherConcreteNPPrependedMultilinearRows_kernelCompatibility_iff_residualGenerator_zero
      M n hn2 htb hns).mpr hzero)

/-- Equivalently, the concrete multilinear-tail SPDP image-containment field
follows from residual SPDP-generator annihilation. -/
theorem routeBRicherConcreteNPPrependedMultilinearGauge_spdpSubspaceContainment_of_residualGenerator_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hzero :
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
          (p -
            routeBRicherConcreteNPPrependedMultilinearProjection
              M n hn2 htb hns p)
          S shift = 0) :
    RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
      (routeBRicherConcreteNPPrependedMultilinearGauge M n hn2 htb hns) :=
  by
    simpa [routeBRicherConcreteNPPrependedMultilinearGauge] using
      routeBRicherFiniteRowsCandidateGauge_spdpSubspaceContainment_of_mapPreimage
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns)
        (routeBRicherConcreteNPPrependedMultilinearRows_spdpMapPreimage_of_residualGenerator_zero
          M n hn2 htb hns hzero)

/-! ## Paper-faithful projection descent fork -/

/-- Paper-faithful descent for the concrete multilinear-tail projection.

This is the holographic invariance condition for the selected finite-row
observer: every admissible SPDP generator row descends through the projection.
It is weaker and more faithful than asking the whole projection residual to be
annihilated before projection. -/
def RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  RouteBRicherGaugeFiniteRowsSPDPGeneratorCommutation M n hn2 htb hns
    (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns)

/-- A concrete projection-escape witness for the multilinear-tail projection:
one admissible generator row fails to descend through the selected projection. -/
def RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  exists (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ∧
    shift.totalDegree <= ell ∧
    shift.vars <= S.toFinset ∧
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ∧
    routeBSPDPGeneratorRow M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearProjection
          M n hn2 htb hns p) S shift ≠
      routeBRicherConcreteNPPrependedMultilinearProjection M n hn2 htb hns
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift)

/-- Projection descent gives exactly the finite-row map-preimage statement
needed by the corrected Route B SPDP image-containment surface. -/
theorem routeBRicherConcreteNPPrependedMultilinearRows_spdpMapPreimage_of_projectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdesc :
      RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns) :
    RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns
      (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns) :=
  routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_generatorRowCommutation
    M n hn2 htb hns
    (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns)
    hdesc

/-- Paper-faithful concrete multilinear-tail SPDP containment from projection
descent, without the stronger residual-annihilation hypothesis. -/
theorem routeBRicherConcreteNPPrependedMultilinearGauge_spdpSubspaceContainment_of_projectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdesc :
      RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns) :
    RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
      (routeBRicherConcreteNPPrependedMultilinearGauge M n hn2 htb hns) :=
  by
    simpa [routeBRicherConcreteNPPrependedMultilinearGauge] using
      routeBRicherFiniteRowsCandidateGauge_spdpSubspaceContainment_of_mapPreimage
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns)
        (routeBRicherConcreteNPPrependedMultilinearRows_spdpMapPreimage_of_projectionDescent
          M n hn2 htb hns hdesc)

/-- A projection escape witness is exactly a failure of the concrete
multilinear-tail projection descent condition. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_projectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns ↔
      ¬ RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns := by
  constructor
  · rintro ⟨spdpKappa, ell, p, S, shift,
      hSlen, hshiftDegree, hshiftVars, hadm, hne⟩ hdesc
    exact hne
      (hdesc spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm)
  · intro hnot
    by_contra hno
    apply hnot
    intro spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm
    by_contra hne
    exact hno ⟨spdpKappa, ell, p, S, shift,
      hSlen, hshiftDegree, hshiftVars, hadm, hne⟩

/-- Failure of projection descent produces the concrete admissible generator
row where the multilinear-tail projection escapes. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_of_not_projectionDescent
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hnot :
      ¬ RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
      M n hn2 htb hns :=
  (routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_projectionDescent
    M n hn2 htb hns).mpr hnot

/-- Excluding concrete projection escape is exactly the paper-faithful descent
condition for the multilinear-tail projection. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_no_projectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns ↔
      ¬ RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns := by
  constructor
  · intro hdesc hbad
    exact
      ((routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_projectionDescent
        M n hn2 htb hns).mp hbad) hdesc
  · intro hno
    by_contra hnot
    exact hno
      (routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_of_not_projectionDescent
        M n hn2 htb hns hnot)

/-- No concrete projection escape closes the paper-faithful descent branch. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionDescent_of_no_projectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hno :
      ¬ RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
      M n hn2 htb hns :=
  (routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_no_projectionEscapeWitness
    M n hn2 htb hns).mpr hno

/-- The concrete multilinear-tail fork is complete at the logical level: either
the selected projection descends through all admissible SPDP generators, or
Lean exposes a concrete projection-escape witness. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionDescent_or_projectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns ∨
      RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns := by
  by_cases hdesc :
      RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns
  · exact Or.inl hdesc
  · exact Or.inr
      (routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_of_not_projectionDescent
        M n hn2 htb hns hdesc)

/-- No concrete projection escape gives the SPDP containment theorem through the
paper-faithful descent route. -/
theorem routeBRicherConcreteNPPrependedMultilinearGauge_spdpSubspaceContainment_of_no_projectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hno :
      ¬ RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns) :
    RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
      (routeBRicherConcreteNPPrependedMultilinearGauge M n hn2 htb hns) :=
  routeBRicherConcreteNPPrependedMultilinearGauge_spdpSubspaceContainment_of_projectionDescent
    M n hn2 htb hns
    (routeBRicherConcreteNPPrependedMultilinearProjectionDescent_of_no_projectionEscapeWitness
      M n hn2 htb hns hno)

/-- A concrete projection escape witness refutes the paper-faithful descent
condition for the selected multilinear finite-row projection. -/
theorem routeBRicherConcreteNPPrependedMultilinear_not_projectionDescent_of_projectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns) :
    ¬ RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
      M n hn2 htb hns :=
  (routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_projectionDescent
    M n hn2 htb hns).mp hbad

/-- With the separate unprojected-preimage side supplied, the concrete NP row
plus multilinear monomial tail gives the finite-row map-preimage surface. -/
theorem routeBRicherConcreteNPPrependedMultilinearRows_spdpMapPreimage_of_unprojectedPreimage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPUnprojectedPreimage M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns)) :
    RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns
      (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns) :=
  routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_rowClosurePackage_unprojectedPreimage
    M n hn2 htb hns
    (routeBRicherMultilinearTailRows M n hn2 htb hns)
    (routeBRicherConcreteNPPrependedMultilinearRows_spdpRowClosurePackage
      M n hn2 htb hns)
    preimage

/-- For the concrete multilinear-tail gauge, the map-preimage SPDP target is
equivalent to the Route B SPDP image-containment field itself.

This is the corrected surface for the remaining projection work: the broad
multilinear tail closes finite-row closure, while the SPDP content is exactly
image containment for the selected finite-rank projection. -/
theorem routeBRicherConcreteNPPrependedMultilinearRows_spdpMapPreimage_iff_spdpSubspaceContainment
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns) ↔
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearGauge M n hn2 htb hns) := by
  simpa [routeBRicherConcreteNPPrependedMultilinearGauge] using
    routeBRicherGaugeFiniteRowsSPDPMapPreimage_iff_spdpSubspaceContainment
      M n hn2 htb hns
      (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns)

/-- Concrete-tail Route B certificate from the map-preimage SPDP side and the
corrected active-blocker/non-scalar P-window cover.

Unlike the older unprojected-preimage wrapper, this consumes the weaker
`RouteBRicherGaugeFiniteRowsSPDPMapPreimage` field directly, which is the
actual image-containment witness needed by the finite-row assembly. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_mapPreimage_activeBlockersZeroNonScalarCover_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    (hN : 1 <= N)
    (hrowCount :
      routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1 <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (hbound :
      cookLevinZeroProfileNonScalarCardBound M n hn2 htb hns <=
        withinProfileBound (Nat.log 2 n))
    (hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns)) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_activeBlockersZeroNonScalarCover_deltaEqRateKappa
    (N := N) (d := d)
    M n hn hn2 htb hns hn4
    alpha beta alpha0 kappa gadgetN G chi Phi
    (routeBRicherMultilinearTailRows M n hn2 htb hns)
    hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    hbound hactive preimage

/-- Concrete-tail Route B certificate from the map-preimage SPDP side, with
P-window inputs reduced to the primitive per-type spanning package and the
zero-profile support-card finite-sum side condition. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_mapPreimage_perTypeSpanning_zeroSupportCardSum_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    (hN : 1 <= N)
    (hrowCount :
      routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1 <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (W : ConstraintType -> Submodule Rat (MvPolynomial (Fin n) Rat))
    (hW_fin : forall tau, Module.Finite Rat (W tau))
    (hW_dim : forall tau, Module.finrank Rat (W tau) <= 3)
    (hSpan :
      PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
        M n hn2 htb hns W)
    (hzero :
      CookLevinZeroProfileSupportCardSumSideCondition M n hn2 htb hns)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns)) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_perTypeSpanning_zeroSupportCardSum_deltaEqRateKappa
    (N := N) (d := d)
    M n hn hn2 htb hns hn4
    alpha beta alpha0 kappa gadgetN G chi Phi
    (routeBRicherMultilinearTailRows M n hn2 htb hns)
    hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    W hW_fin hW_dim hSpan hzero preimage

/-- Concrete-tail Route B certificate from the map-preimage SPDP side, with
the P-window inputs reduced to per-type spanning plus the literal non-scalar
zero-profile cardinal bound.

This avoids the broader finite-sum side condition
`CookLevinZeroProfileSupportCardSumSideCondition`; callers may provide the
smaller budget statement actually consumed by the corrected P-window cover. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_mapPreimage_perTypeSpanning_zeroNonScalarCardBound_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    (hN : 1 <= N)
    (hrowCount :
      routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1 <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (W : ConstraintType -> Submodule Rat (MvPolynomial (Fin n) Rat))
    (hW_fin : forall tau, Module.Finite Rat (W tau))
    (hW_dim : forall tau, Module.finrank Rat (W tau) <= 3)
    (hSpan :
      PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
        M n hn2 htb hns W)
    (hzeroBound :
      cookLevinZeroProfileNonScalarCardBound M n hn2 htb hns <=
        withinProfileBound (Nat.log 2 n))
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns)) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_mapPreimage_activeBlockersZeroNonScalarCover_deltaEqRateKappa
    (N := N) (d := d)
    M n hn hn2 htb hns hn4
    alpha beta alpha0 kappa gadgetN G chi Phi
    hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    hzeroBound
    (cookLevinActiveProfileTypeCaseBlockers_of_perTypeSpanning
      M n hn2 htb hns W hW_fin hW_dim hSpan)
    preimage

/-- Concrete-tail Route B certificate with the SPDP side stated directly as
Route B image containment and the P-side reduced to the primitive per-type
spanning plus zero-profile support-card inputs. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_spdpContainment_perTypeSpanning_zeroSupportCardSum_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    (hN : 1 <= N)
    (hrowCount :
      routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1 <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (W : ConstraintType -> Submodule Rat (MvPolynomial (Fin n) Rat))
    (hW_fin : forall tau, Module.Finite Rat (W tau))
    (hW_dim : forall tau, Module.finrank Rat (W tau) <= 3)
    (hSpan :
      PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
        M n hn2 htb hns W)
    (hzero :
      CookLevinZeroProfileSupportCardSumSideCondition M n hn2 htb hns)
    (contain :
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearGauge M n hn2 htb hns)) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_mapPreimage_perTypeSpanning_zeroSupportCardSum_deltaEqRateKappa
    (N := N) (d := d)
    M n hn hn2 htb hns hn4
    alpha beta alpha0 kappa gadgetN G chi Phi
    hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    W hW_fin hW_dim hSpan hzero
    ((routeBRicherConcreteNPPrependedMultilinearRows_spdpMapPreimage_iff_spdpSubspaceContainment
      M n hn2 htb hns).mpr contain)

/-- Direct-containment sibling of
`routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_mapPreimage_perTypeSpanning_zeroNonScalarCardBound_deltaEqRateKappa`.

This is the reduced P-side surface for the concrete multilinear-tail gauge:
SPDP containment remains the projection/gauge obligation, while the
zero-profile side is the literal non-scalar cardinal bound rather than the
too-large support-card finite sum. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_spdpContainment_perTypeSpanning_zeroNonScalarCardBound_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    (hN : 1 <= N)
    (hrowCount :
      routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1 <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (W : ConstraintType -> Submodule Rat (MvPolynomial (Fin n) Rat))
    (hW_fin : forall tau, Module.Finite Rat (W tau))
    (hW_dim : forall tau, Module.finrank Rat (W tau) <= 3)
    (hSpan :
      PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
        M n hn2 htb hns W)
    (hzeroBound :
      cookLevinZeroProfileNonScalarCardBound M n hn2 htb hns <=
        withinProfileBound (Nat.log 2 n))
    (contain :
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearGauge M n hn2 htb hns)) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_mapPreimage_perTypeSpanning_zeroNonScalarCardBound_deltaEqRateKappa
    (N := N) (d := d)
    M n hn hn2 htb hns hn4
    alpha beta alpha0 kappa gadgetN G chi Phi
    hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    W hW_fin hW_dim hSpan hzeroBound
    ((routeBRicherConcreteNPPrependedMultilinearRows_spdpMapPreimage_iff_spdpSubspaceContainment
      M n hn2 htb hns).mpr contain)

/-- Concrete-tail Route B certificate with the SPDP side stated directly as
Route B image containment and the P-side supplied by the concreteW row
embedding package.

This is the strongest current P-window shortcut for the multilinear-tail
surface: it avoids exposing the separate zero-profile support-card arithmetic
when a full concreteW row-embedding package is already available. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_spdpContainment_rowEmbeddings_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    (hN : 1 <= N)
    (hrowCount :
      routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1 <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4)
    (contain :
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearGauge M n hn2 htb hns)) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_rowEmbeddings_deltaEqRateKappa
    (N := N) (d := d)
    M n hn hn2 htb hns hn4
    alpha beta alpha0 kappa gadgetN G chi Phi
    (routeBRicherMultilinearTailRows M n hn2 htb hns)
    hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    ((routeBRicherConcreteNPPrependedMultilinearRows_spdpMapPreimage_iff_spdpSubspaceContainment
      M n hn2 htb hns).mpr contain)
    hRowEmbeddings

/-- Concrete-tail Route B certificate with the P-window side reduced all the
way to the strongest imported direct concreteW branch assumptions:
branch-shape witnesses, canonical-row transport, H4 derivative closure, and
the I1/I2/I3 concreteW component interfaces.

The only remaining non-P-side input is the SPDP image-containment statement
for the selected multilinear finite-row gauge. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_spdpContainment_importedConcreteW_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    (hN : 1 <= N)
    (hrowCount :
      routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1 <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (hShape : CookLevinDirectBranchShapeWitnesses M n hn2 htb hns hn4)
    (hTransport : CookLevinConcreteWCanonicalRowTransport M n hn2 htb hns hn4)
    (hDeriv :
      PallLean.Paper93.Spanning.DerivClosurePerType (n := n)
        (fun tau =>
          PallLean.Paper93.Wiring.concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hI1 : ConcreteWProductGrouping n hn4)
    (hI2 : ConcreteWShiftClosure n hn4)
    (hI3 : ConcreteWMlprojClosure n hn4)
    (contain :
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearGauge M n hn2 htb hns)) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_prependedConcreteNP_finiteRowsSPDPMapPreimage_importedConcreteW_deltaEqRateKappa
    (N := N) (d := d)
    M n hn hn2 htb hns hn4
    alpha beta alpha0 kappa gadgetN G chi Phi
    (routeBRicherMultilinearTailRows M n hn2 htb hns)
    hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    ((routeBRicherConcreteNPPrependedMultilinearRows_spdpMapPreimage_iff_spdpSubspaceContainment
      M n hn2 htb hns).mpr contain)
    hShape hTransport hDeriv hI1 hI2 hI3

/-- Concrete-tail Route B certificate from the unprojected-preimage side and
an endpoint/charged P-window bridge. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_unprojectedPreimage_endpointChargedBridge_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4) (charge : ProfileCharge n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    (hN : 1 <= N)
    (hrowCount :
      routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1 <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (unprojectedPreimage :
      RouteBRicherGaugeFiniteRowsSPDPUnprojectedPreimage M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns))
    (bridge :
      RouteBRicherGaugeEndpointChargedPWindowBridge
        M n hn2 htb hns hn4 charge) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_unprojectedPreimage_endpointChargedBridge_deltaEqRateKappa
    (N := N) (d := d)
    M n hn hn2 htb hns hn4 charge
    alpha beta alpha0 kappa gadgetN G chi Phi
    (routeBRicherMultilinearTailRows M n hn2 htb hns)
    hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    (routeBRicherConcreteNPPrependedMultilinearRows_spdpRowClosurePackage
      M n hn2 htb hns)
    unprojectedPreimage bridge

/-- Concrete-tail Route B certificate from the unprojected-preimage side and
the active-blocker/non-scalar P-window cover. -/
theorem routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_unprojectedPreimage_activeBlockersZeroNonScalarCover_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    (hN : 1 <= N)
    (hrowCount :
      routeBRicherMultilinearTailRowCount M n hn2 htb hns + 1 <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (hbound :
      cookLevinZeroProfileNonScalarCardBound M n hn2 htb hns <=
        withinProfileBound (Nat.log 2 n))
    (hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns)
    (unprojectedPreimage :
      RouteBRicherGaugeFiniteRowsSPDPUnprojectedPreimage M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns)) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_prependedConcreteNP_rowClosurePackage_unprojectedPreimage_activeBlockersZeroNonScalarCover_deltaEqRateKappa
    (N := N) (d := d)
    M n hn hn2 htb hns hn4
    alpha beta alpha0 kappa gadgetN G chi Phi
    (routeBRicherMultilinearTailRows M n hn2 htb hns)
    hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
    hbound hactive
    (routeBRicherConcreteNPPrependedMultilinearRows_spdpRowClosurePackage
      M n hn2 htb hns)
    unprojectedPreimage

/-! ## Axiom audit anchors -/

#print axioms routeBRicherMultilinearTailRows_mem_span_of_mem_basis
#print axioms routeBRicherMultilinearTailRowCount_le_two_pow_dim
#print axioms routeBRicherConcreteNPPrependedMultilinearRows_rowCount_le_of_two_pow_dim
#print axioms routeBRicherMultilinearTailRows_linearIndependent
#print axioms routeBRicherMultilinearTailRows_exists_supportSet
#print axioms routeBRicherMultilinearTailSupportSet
#print axioms routeBRicherMultilinearTailRows_eq_prod_supportSet
#print axioms routeBRicherMultilinearTailCoeffAlpha
#print axioms routeBRicherMultilinearTailRows_eq_monomial_tailCoeffAlpha
#print axioms routeBRicherMultilinearTailRows_injective
#print axioms routeBRicherMultilinearTailCoeffAlpha_injective
#print axioms routeBRicherMultilinearTailRows_coeff_tailCoeffAlpha
#print axioms routeBRicherConcreteNPPrependedMultilinearRows_linearIndependent_of_headCoeff_vanishesOnTail
#print axioms routeBRicherConcreteNPPrependedMultilinearDualCoordinates
#print axioms routeBRicherConcreteNPPrependedMultilinearDualCoordinates_apply_row
#print axioms routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData_of_linearIndependentRows
#print axioms routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData_of_coefficientDualCoordinates
#print axioms routeBRicherMultilinearTailRows_mlProj_mem
#print axioms finiteRowsSubmodule_le_concreteNPPrependedRows_tail
#print axioms routeBRicherConcreteNPPrependedMultilinearRows_mlProj_mem
#print axioms routeBRicherMultilinearTailBasis_mem_X_secondVar
#print axioms routeBRicherMultilinearTailHeadCoeffIndex
#print axioms routeBRicherMultilinearTailRows_headCoeffIndex_eq_X_secondVar
#print axioms routeBRicherMultilinearTailRows_headCoeffIndex_coeff_secondVar
#print axioms routeBRicherMultilinearTailRows_coeff_secondVar_square
#print axioms routeBRicherConcreteNPWitnessRows_zero_coeff_secondVar_square
#print axioms routeBRicherConcreteNPWitnessRows_zero_coeff_secondVar_square_ne_zero
#print axioms routeBRicherConcreteNPPrependedMultilinearRows_linearIndependent
#print axioms routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData
#print axioms routeBRicherConcreteNPPrependedMultilinearExplicitProjection_mem_complement_of_coeff_vanish
#print axioms routeBRicherConcreteNPPrependedMultilinearExplicitProjection_mem_complement_iff_coeff_vanish
#print axioms RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionGeneratorCoeffVanishes
#print axioms routeBRicherConcreteNPPrependedMultilinearExplicitProjectionStableGeneratorMaps_of_generatorCoeffVanishes
#print axioms RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent
#print axioms RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness
#print axioms RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionVisibleCoefficientEscapeWitness
#print axioms routeBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness_of_explicitCoeff
#print axioms routeBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness_of_visibleCoefficientEscape
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe
#print axioms routeBRicherConcreteNPPrependedMultilinearFirstSquareProbe_singletonRow_eq
#print axioms routeBRicherConcreteNPPrependedMultilinearExplicitProjection_firstSquare_singletonCoeff_ne_zero
#print axioms routeBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness_of_firstSquare_singletonCoeff
#print axioms routeBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness_firstSquare_singleton
#print axioms routeBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent_iff_explicitComplementInvariant
#print axioms routeBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent_of_stableGeneratorMaps
#print axioms routeBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent_of_generatorCoeffVanishes
#print axioms routeBRicherConcreteNPPrependedMultilinearExplicitProjectionEscapeWitness_iff_not_projectionDescent
#print axioms routeBRicherConcreteNPPrependedMultilinearExplicitProjection_not_descent
#print axioms routeBRicherConcreteNPPrependedMultilinearExplicitProjection_not_stableGeneratorMaps
#print axioms routeBRicherConcreteNPPrependedMultilinearExplicitProjection_not_generatorCoeffVanishes
#print axioms RouteBRicherConcreteNPPrependedMultilinearExplicitProjectionPaperAdmissible
#print axioms routeBRicherConcreteNPPrependedMultilinearExplicitProjection_not_paperAdmissible_of_escapeWitness
#print axioms routeBRicherConcreteNPPrependedMultilinearExplicitProjection_not_paperAdmissible
#print axioms routeBRicherConcreteNPPrependedMultilinearExplicitProjectionDescent_or_escapeWitness
#print axioms routeBRicherConcreteNPPrependedMultilinearRows_spdpRowClosurePackage
#print axioms routeBRicherConcreteNPPrependedMultilinearRows_spdpClosure
#print axioms routeBRicherConcreteNPPrependedMultilinearRows_kernelCompatibility_iff_residualGenerator_zero
#print axioms routeBRicherConcreteNPPrependedMultilinearRows_spdpMapPreimage_of_residualGenerator_zero
#print axioms routeBRicherConcreteNPPrependedMultilinearGauge_spdpSubspaceContainment_of_residualGenerator_zero
#print axioms RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
#print axioms RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
#print axioms routeBRicherConcreteNPPrependedMultilinearRows_spdpMapPreimage_of_projectionDescent
#print axioms routeBRicherConcreteNPPrependedMultilinearGauge_spdpSubspaceContainment_of_projectionDescent
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_projectionDescent
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_of_not_projectionDescent
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_no_projectionEscapeWitness
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionDescent_of_no_projectionEscapeWitness
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionDescent_or_projectionEscapeWitness
#print axioms routeBRicherConcreteNPPrependedMultilinearGauge_spdpSubspaceContainment_of_no_projectionEscapeWitness
#print axioms routeBRicherConcreteNPPrependedMultilinear_not_projectionDescent_of_projectionEscapeWitness
#print axioms routeBRicherConcreteNPPrependedMultilinearRows_spdpMapPreimage_of_unprojectedPreimage
#print axioms routeBRicherConcreteNPPrependedMultilinearRows_spdpMapPreimage_iff_spdpSubspaceContainment
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_mapPreimage_activeBlockersZeroNonScalarCover_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_mapPreimage_perTypeSpanning_zeroSupportCardSum_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_mapPreimage_perTypeSpanning_zeroNonScalarCardBound_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_spdpContainment_perTypeSpanning_zeroSupportCardSum_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_spdpContainment_perTypeSpanning_zeroNonScalarCardBound_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_spdpContainment_rowEmbeddings_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_spdpContainment_importedConcreteW_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_unprojectedPreimage_endpointChargedBridge_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_prependedConcreteNP_multilinearTail_unprojectedPreimage_activeBlockersZeroNonScalarCover_deltaEqRateKappa

end PallLean.Paper93.Paper283
