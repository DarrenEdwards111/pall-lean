import PallLean.Paper93.DeepMath.PathB.SingletonQuotientSPDPCompatible

/-!
# Residual-row seam for the singleton quotient

The residual of the singleton quotient is known to land in the zero-profile
singleton-shift subspace.  The projection kills that subspace.  Therefore the
`SingletonQuotientResidualRowsKilled` field reduces to one precise stability
claim: SPDP row operators must send the singleton-shift residual subspace into
something killed by the singleton quotient.  A stronger, more geometric version
is that they preserve the singleton-shift subspace itself.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine

/-- The Cook-Levin factor family used by the singleton quotient candidate. -/
noncomputable abbrev singletonQuotientCookLevinFactors
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Fin (WithinProfileBound.cookLevinFactorList M n hn2 htb hns).length →
      MvPolynomial (Fin n) Rat :=
  fun i => (WithinProfileBound.cookLevinFactorList M n hn2 htb hns).get i

/-- The singleton-shift residual subspace specialized to the Cook-Levin SAT
candidate. -/
noncomputable abbrev singletonQuotientResidualSubspace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns) :=
  zeroProfileSingletonShiftSubspace
    (singletonQuotientCookLevinFactors M n hn2 htb hns)

/-- The residual of the singleton quotient lands in the singleton-shift
subspace. -/
theorem singletonQuotientResidual_mem_residualSubspace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    singletonQuotientResidual M n hn2 htb hns p ∈
      singletonQuotientResidualSubspace M n hn2 htb hns := by
  unfold singletonQuotientResidual singletonQuotientProject singletonQuotientSATGauge
  exact zeroProfileQuotientBySingletonShiftProjection_residual_mem_singletonShiftSubspace
    (singletonQuotientCookLevinFactors M n hn2 htb hns) p

/-- The singleton quotient kills the whole residual subspace. -/
theorem singletonQuotientResidualSubspace_le_ker
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    singletonQuotientResidualSubspace M n hn2 htb hns ≤
      LinearMap.ker (singletonQuotientProject M n hn2 htb hns) := by
  unfold singletonQuotientResidualSubspace singletonQuotientProject singletonQuotientSATGauge
  exact zeroProfileQuotientBySingletonShiftProjection_singletonShiftSubspace_le_ker
    (singletonQuotientCookLevinFactors M n hn2 htb hns)

/-- Linearity of `iterDerivList` with respect to scalar multiplication. -/
theorem singletonQuotient_iterDerivList_smul
    {n : Nat} (S : List (Fin n)) (a : Rat)
    (p : MvPolynomial (Fin n) Rat) :
    SPDP.iterDerivList S (a • p) = a • SPDP.iterDerivList S p := by
  induction S generalizing p with
  | nil => simp [SPDP.iterDerivList]
  | cons i rest ih =>
      simp only [SPDP.iterDerivList, List.foldl_cons]
      rw [show List.foldl (fun r j => MvPolynomial.pderiv j r)
              (MvPolynomial.pderiv i (a • p)) rest =
            SPDP.iterDerivList rest (MvPolynomial.pderiv i (a • p)) from rfl,
          show List.foldl (fun r j => MvPolynomial.pderiv j r)
              (MvPolynomial.pderiv i p) rest =
            SPDP.iterDerivList rest (MvPolynomial.pderiv i p) from rfl]
      rw [(MvPolynomial.pderiv i).map_smul]
      exact ih _

/-- SPDP rows are additive in the polynomial input. -/
theorem singletonQuotientSPDPRow_add
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (S : List (Fin n)) (m : MvPolynomial (Fin n) Rat)
    (p q : SATDeciderGaugeSpace M n hn2 htb hns) :
    singletonQuotientSPDPRow S m (p + q) =
      singletonQuotientSPDPRow S m p + singletonQuotientSPDPRow S m q := by
  unfold singletonQuotientSPDPRow
  rw [SPDP.iterDerivList_add, mul_add, mlProj_add]

/-- SPDP rows commute with scalar multiplication in the polynomial input. -/
theorem singletonQuotientSPDPRow_smul
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (S : List (Fin n)) (m : MvPolynomial (Fin n) Rat)
    (a : Rat) (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    singletonQuotientSPDPRow S m (a • p) =
      a • singletonQuotientSPDPRow S m p := by
  unfold singletonQuotientSPDPRow
  rw [singletonQuotient_iterDerivList_smul]
  rw [mul_smul_comm, mlProj_smul]

/-- Direct kernel-stability condition needed for residual rows: every SPDP row
of a residual-subspace element is killed by the singleton quotient. -/
def SingletonQuotientResidualSPDPRowsKilledOnSubspace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (κ ℓ : Nat) (r : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin n)) (m : MvPolynomial (Fin n) Rat),
    r ∈ singletonQuotientResidualSubspace M n hn2 htb hns →
    S.length = κ →
    m.totalDegree ≤ ℓ →
    m.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S →
    (singletonQuotientProject M n hn2 htb hns)
      (singletonQuotientSPDPRow S m r) = 0

/-- Generator-level killed-row condition for the singleton residual: it is
enough to check the finite/ranged singleton-shift generators. -/
def SingletonQuotientResidualGeneratorRowsKilled
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (κ ℓ : Nat) (i : Fin n)
    (S : List (Fin n)) (m : MvPolynomial (Fin n) Rat),
    S.length = κ →
    m.totalDegree ≤ ℓ →
    m.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S →
    (singletonQuotientProject M n hn2 htb hns)
      (singletonQuotientSPDPRow S m
        (mlProj (MvPolynomial.X i *
          Finset.univ.prod
            (singletonQuotientCookLevinFactors M n hn2 htb hns)))) = 0

/-- Generator-level killed rows imply killed rows on the whole residual
subspace by span induction and linearity of the row operator. -/
theorem singletonQuotientResidualRowsKilledOnSubspace_of_generatorsKilled
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hgen : SingletonQuotientResidualGeneratorRowsKilled M n hn2 htb hns) :
    SingletonQuotientResidualSPDPRowsKilledOnSubspace M n hn2 htb hns := by
  intro κ ℓ r S m hr hS hm hmvars hadm
  unfold singletonQuotientResidualSubspace at hr
  unfold zeroProfileSingletonShiftSubspace at hr
  refine Submodule.span_induction
    (p := fun x _ =>
      (singletonQuotientProject M n hn2 htb hns)
        (singletonQuotientSPDPRow S m x) = 0)
    ?hgen ?hzero ?hadd ?hsmul hr
  · intro x hx
    rcases hx with ⟨i, rfl⟩
    exact hgen κ ℓ i S m hS hm hmvars hadm
  · change (singletonQuotientProject M n hn2 htb hns)
        (singletonQuotientSPDPRow S m
          (0 : SATDeciderGaugeSpace M n hn2 htb hns)) = 0
    unfold singletonQuotientSPDPRow SPDP.iterDerivList
    rw [SPDP.foldl_pderiv_zero, mul_zero, mlProj_zero, map_zero]
  · intro x y _hxmem _hymem hx hy
    rw [singletonQuotientSPDPRow_add, map_add, hx, hy, add_zero]
  · intro a x _hxmem hx
    rw [singletonQuotientSPDPRow_smul, map_smul, hx, smul_zero]

/-- Stronger geometric condition: SPDP rows preserve the singleton-shift
residual subspace. -/
def SingletonQuotientResidualSubspaceSPDPStable
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (κ ℓ : Nat) (r : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin n)) (m : MvPolynomial (Fin n) Rat),
    r ∈ singletonQuotientResidualSubspace M n hn2 htb hns →
    S.length = κ →
    m.totalDegree ≤ ℓ →
    m.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S →
    singletonQuotientSPDPRow S m r ∈
      singletonQuotientResidualSubspace M n hn2 htb hns

/-- Subspace preservation implies the direct killed-on-subspace condition,
because the singleton quotient kills the residual subspace. -/
theorem singletonQuotientResidualRowsKilledOnSubspace_of_spdpStable
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hstable : SingletonQuotientResidualSubspaceSPDPStable M n hn2 htb hns) :
    SingletonQuotientResidualSPDPRowsKilledOnSubspace M n hn2 htb hns := by
  intro κ ℓ r S m hr hS hm hmvars hadm
  exact LinearMap.mem_ker.mp
    ((singletonQuotientResidualSubspace_le_ker M n hn2 htb hns)
      (hstable κ ℓ r S m hr hS hm hmvars hadm))

/-- The direct killed-on-subspace condition closes
`SingletonQuotientResidualRowsKilled`, since the actual residual is in that
subspace. -/
theorem singletonQuotientResidualRowsKilled_of_killedOnSubspace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hkilled : SingletonQuotientResidualSPDPRowsKilledOnSubspace
      M n hn2 htb hns) :
    SingletonQuotientResidualRowsKilled M n hn2 htb hns := by
  intro κ ℓ p S m hS hm hmvars hadm
  exact hkilled κ ℓ (singletonQuotientResidual M n hn2 htb hns p) S m
    (singletonQuotientResidual_mem_residualSubspace M n hn2 htb hns p)
    hS hm hmvars hadm

/-- Generator-level killed rows close `SingletonQuotientResidualRowsKilled`. -/
theorem singletonQuotientResidualRowsKilled_of_generatorsKilled
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hgen : SingletonQuotientResidualGeneratorRowsKilled M n hn2 htb hns) :
    SingletonQuotientResidualRowsKilled M n hn2 htb hns :=
  singletonQuotientResidualRowsKilled_of_killedOnSubspace M n hn2 htb hns
    (singletonQuotientResidualRowsKilledOnSubspace_of_generatorsKilled
      M n hn2 htb hns hgen)

/-- The stronger subspace-stability condition closes
`SingletonQuotientResidualRowsKilled`. -/
theorem singletonQuotientResidualRowsKilled_of_spdpStable
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hstable : SingletonQuotientResidualSubspaceSPDPStable M n hn2 htb hns) :
    SingletonQuotientResidualRowsKilled M n hn2 htb hns :=
  singletonQuotientResidualRowsKilled_of_killedOnSubspace M n hn2 htb hns
    (singletonQuotientResidualRowsKilledOnSubspace_of_spdpStable
      M n hn2 htb hns hstable)

/-- If projected rows are fixed and the residual subspace is SPDP-stable, then
the full SPDP-compatible singleton-quotient interface follows. -/
theorem spdpCompatibleSingletonQuotient_of_projectedRowsFixed_and_residualStable
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hfix : SingletonQuotientProjectedRowsFixed M n hn2 htb hns)
    (hstable : SingletonQuotientResidualSubspaceSPDPStable M n hn2 htb hns) :
    SPDPCompatibleSingletonQuotient M n hn2 htb hns :=
  ⟨hfix,
    singletonQuotientResidualRowsKilled_of_spdpStable M n hn2 htb hns hstable⟩

/-- Residual-subspace SPDP stability plus projected-row fixedness closes the
candidate-specific rank obligation. -/
theorem singletonQuotientRankObligation_of_projectedRowsFixed_and_residualStable
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hfix : SingletonQuotientProjectedRowsFixed M n hn2 htb hns)
    (hstable : SingletonQuotientResidualSubspaceSPDPStable M n hn2 htb hns) :
    SingletonQuotientSATGaugeRankMonotonicityObligation M n hn2 htb hns :=
  singletonQuotientRankObligation_of_spdpCompatible M n hn2 htb hns
    (spdpCompatibleSingletonQuotient_of_projectedRowsFixed_and_residualStable
      M n hn2 htb hns hfix hstable)

/-! ## Axiom audit anchors -/
#print axioms singletonQuotientResidual_mem_residualSubspace
#print axioms singletonQuotientResidualSubspace_le_ker
#print axioms singletonQuotientSPDPRow_add
#print axioms singletonQuotientSPDPRow_smul
#print axioms singletonQuotientResidualRowsKilledOnSubspace_of_generatorsKilled
#print axioms singletonQuotientResidualRowsKilled_of_generatorsKilled
#print axioms singletonQuotientResidualRowsKilledOnSubspace_of_spdpStable
#print axioms singletonQuotientResidualRowsKilled_of_killedOnSubspace
#print axioms singletonQuotientResidualRowsKilled_of_spdpStable
#print axioms spdpCompatibleSingletonQuotient_of_projectedRowsFixed_and_residualStable
#print axioms singletonQuotientRankObligation_of_projectedRowsFixed_and_residualStable

end PallLean.Paper93.DeepMath.PathB
