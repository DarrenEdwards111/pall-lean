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
    simpa [basis, routeBRicherMultilinearTailBasis] using this
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
  routeBRicherConcreteNPPrependedMultilinearExplicitProjectionData_of_linearIndependentRows
    M n hn2 htb hns
    (routeBRicherConcreteNPPrependedMultilinearRows_linearIndependent
      M n hn2 htb hns)

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
