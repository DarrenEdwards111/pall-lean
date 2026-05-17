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

/-- Exact kernel form: the singleton quotient kills precisely the residual
singleton-shift subspace, not a larger hidden space. -/
theorem singletonQuotientProject_apply_eq_zero_iff_mem_residualSubspace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (q : SATDeciderGaugeSpace M n hn2 htb hns) :
    (singletonQuotientProject M n hn2 htb hns) q = 0 ↔
      q ∈ singletonQuotientResidualSubspace M n hn2 htb hns := by
  let factors := singletonQuotientCookLevinFactors M n hn2 htb hns
  let h := zeroProfileSingletonShiftSubspace_isCompl_complement factors
  change (Submodule.IsCompl.projection h.symm) q = 0 ↔
    q ∈ zeroProfileSingletonShiftSubspace factors
  exact Submodule.IsCompl.projection_apply_eq_zero_iff h.symm

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

/-- Generator-row subspace preservation: each SPDP row of each finite
singleton-shift generator lands back in the singleton residual subspace.  This
is stronger than being killed by the quotient, but often the more geometric
finite check. -/
def SingletonQuotientResidualGeneratorRowsMemSubspace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (κ ℓ : Nat) (i : Fin n)
    (S : List (Fin n)) (m : MvPolynomial (Fin n) Rat),
    S.length = κ →
    m.totalDegree ≤ ℓ →
    m.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S →
    singletonQuotientSPDPRow S m
      (mlProj (MvPolynomial.X i *
        Finset.univ.prod
          (singletonQuotientCookLevinFactors M n hn2 htb hns))) ∈
      singletonQuotientResidualSubspace M n hn2 htb hns

/-- Generator-row subspace preservation implies the finite generator rows are
killed, because the singleton quotient kills the residual subspace. -/
theorem singletonQuotientResidualGeneratorRowsKilled_of_memSubspace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hmem : SingletonQuotientResidualGeneratorRowsMemSubspace
      M n hn2 htb hns) :
    SingletonQuotientResidualGeneratorRowsKilled M n hn2 htb hns := by
  intro κ ℓ i S m hS hm hmvars hadm
  exact
    (singletonQuotientProject_apply_eq_zero_iff_mem_residualSubspace
      M n hn2 htb hns _).mpr
      (hmem κ ℓ i S m hS hm hmvars hadm)

/-- Conversely, for this exact quotient, killed finite generator rows are not a
weaker condition: because the kernel is exactly the singleton residual subspace,
killing is equivalent to landing back in that subspace. -/
theorem singletonQuotientResidualGeneratorRowsMemSubspace_of_killed
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hkill : SingletonQuotientResidualGeneratorRowsKilled M n hn2 htb hns) :
    SingletonQuotientResidualGeneratorRowsMemSubspace M n hn2 htb hns := by
  intro κ ℓ i S m hS hm hmvars hadm
  exact
    (singletonQuotientProject_apply_eq_zero_iff_mem_residualSubspace
      M n hn2 htb hns _).mp
      (hkill κ ℓ i S m hS hm hmvars hadm)

/-- Exact equivalence for the finite residual-generator bottom seam. -/
theorem singletonQuotientResidualGeneratorRowsKilled_iff_memSubspace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SingletonQuotientResidualGeneratorRowsKilled M n hn2 htb hns ↔
      SingletonQuotientResidualGeneratorRowsMemSubspace M n hn2 htb hns := by
  constructor
  · exact singletonQuotientResidualGeneratorRowsMemSubspace_of_killed
      M n hn2 htb hns
  · exact singletonQuotientResidualGeneratorRowsKilled_of_memSubspace
      M n hn2 htb hns

/-- Generator-row subspace preservation implies killed rows on the whole
residual subspace. -/
theorem singletonQuotientResidualRowsKilledOnSubspace_of_generatorRowsMemSubspace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hmem : SingletonQuotientResidualGeneratorRowsMemSubspace
      M n hn2 htb hns) :
    SingletonQuotientResidualSPDPRowsKilledOnSubspace M n hn2 htb hns :=
  singletonQuotientResidualRowsKilledOnSubspace_of_generatorsKilled
    M n hn2 htb hns
    (singletonQuotientResidualGeneratorRowsKilled_of_memSubspace
      M n hn2 htb hns hmem)

/-- Generator-level killed rows close `SingletonQuotientResidualRowsKilled`. -/
theorem singletonQuotientResidualRowsKilled_of_generatorsKilled
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hgen : SingletonQuotientResidualGeneratorRowsKilled M n hn2 htb hns) :
    SingletonQuotientResidualRowsKilled M n hn2 htb hns :=
  singletonQuotientResidualRowsKilled_of_killedOnSubspace M n hn2 htb hns
    (singletonQuotientResidualRowsKilledOnSubspace_of_generatorsKilled
      M n hn2 htb hns hgen)

/-- Generator-row subspace preservation closes `SingletonQuotientResidualRowsKilled`. -/
theorem singletonQuotientResidualRowsKilled_of_generatorRowsMemSubspace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hmem : SingletonQuotientResidualGeneratorRowsMemSubspace
      M n hn2 htb hns) :
    SingletonQuotientResidualRowsKilled M n hn2 htb hns :=
  singletonQuotientResidualRowsKilled_of_generatorsKilled M n hn2 htb hns
    (singletonQuotientResidualGeneratorRowsKilled_of_memSubspace
      M n hn2 htb hns hmem)

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

/-- If projected rows are fixed and residual generator rows are killed, then
the full SPDP-compatible singleton-quotient interface follows. -/
theorem spdpCompatibleSingletonQuotient_of_projectedRowsFixed_and_residualGeneratorsKilled
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hfix : SingletonQuotientProjectedRowsFixed M n hn2 htb hns)
    (hgen : SingletonQuotientResidualGeneratorRowsKilled M n hn2 htb hns) :
    SPDPCompatibleSingletonQuotient M n hn2 htb hns :=
  ⟨hfix,
    singletonQuotientResidualRowsKilled_of_generatorsKilled
      M n hn2 htb hns hgen⟩

/-- If projected rows are fixed and residual generator rows land back in the
residual subspace, then the full SPDP-compatible singleton-quotient interface
follows. -/
theorem spdpCompatibleSingletonQuotient_of_projectedRowsFixed_and_generatorRowsMemSubspace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hfix : SingletonQuotientProjectedRowsFixed M n hn2 htb hns)
    (hmem : SingletonQuotientResidualGeneratorRowsMemSubspace M n hn2 htb hns) :
    SPDPCompatibleSingletonQuotient M n hn2 htb hns :=
  spdpCompatibleSingletonQuotient_of_projectedRowsFixed_and_residualGeneratorsKilled
    M n hn2 htb hns hfix
    (singletonQuotientResidualGeneratorRowsKilled_of_memSubspace
      M n hn2 htb hns hmem)

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

/-- Projected-row fixedness plus finite residual-generator killed rows closes
the candidate-specific rank obligation. -/
theorem singletonQuotientRankObligation_of_projectedRowsFixed_and_residualGeneratorsKilled
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hfix : SingletonQuotientProjectedRowsFixed M n hn2 htb hns)
    (hgen : SingletonQuotientResidualGeneratorRowsKilled M n hn2 htb hns) :
    SingletonQuotientSATGaugeRankMonotonicityObligation M n hn2 htb hns :=
  singletonQuotientRankObligation_of_spdpCompatible M n hn2 htb hns
    (spdpCompatibleSingletonQuotient_of_projectedRowsFixed_and_residualGeneratorsKilled
      M n hn2 htb hns hfix hgen)

/-- Projected-row fixedness plus finite residual-generator subspace
preservation closes the candidate-specific rank obligation. -/
theorem singletonQuotientRankObligation_of_projectedRowsFixed_and_generatorRowsMemSubspace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hfix : SingletonQuotientProjectedRowsFixed M n hn2 htb hns)
    (hmem : SingletonQuotientResidualGeneratorRowsMemSubspace M n hn2 htb hns) :
    SingletonQuotientSATGaugeRankMonotonicityObligation M n hn2 htb hns :=
  singletonQuotientRankObligation_of_projectedRowsFixed_and_residualGeneratorsKilled
    M n hn2 htb hns hfix
    (singletonQuotientResidualGeneratorRowsKilled_of_memSubspace
      M n hn2 htb hns hmem)

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


/-! ## Direct obstruction: the residual-generator stability target is false

The requested bottom proof cannot be completed for the current singleton
quotient as stated.  The obstruction is already visible in the admissible
one-derivative row `S = [i]`, multiplier `m = 1`, applied to the singleton
shift generator `mlProj (X i * P)`.  Its constant coefficient is `1`, while
every element of the singleton-shift residual subspace has constant coefficient
`0`.  Hence the row does **not** land back in the residual subspace, and the
finite residual-generator killed/membership condition is false for this
candidate.
-/

/-- Elements of the singleton-shift residual subspace have zero constant
coefficient. -/
theorem zeroProfileSingletonShiftSubspace_coeff_zero
    {n L : Nat}
    (factors : Fin L → MvPolynomial (Fin n) Rat)
    {q : MvPolynomial (Fin n) Rat}
    (hq : q ∈ zeroProfileSingletonShiftSubspace factors) :
    MvPolynomial.coeff (0 : Fin n →₀ Nat) q = 0 := by
  classical
  unfold zeroProfileSingletonShiftSubspace at hq
  refine Submodule.span_induction
    (p := fun q : MvPolynomial (Fin n) Rat => fun _ =>
      MvPolynomial.coeff (0 : Fin n →₀ Nat) q = 0) ?_ ?_ ?_ ?_ hq
  · intro row hrow
    rcases hrow with ⟨i, rfl⟩
    rw [MultilinearSPDP.coeff_mlProj_of_isMultilinear_mono]
    · rw [MvPolynomial.coeff_X_mul']
      simp
    · intro j
      simp
  · simp
  · intro p q _hp _hq hp0 hq0
    rw [MvPolynomial.coeff_add, hp0, hq0]
    simp
  · intro a p _hp hp0
    rw [MvPolynomial.coeff_smul, hp0]
    simp

/-- Constant-coefficient derivative identity used by the singleton obstruction. -/
theorem coeff_zero_pderiv_eq_coeff_single
    {n : Nat} (i : Fin n) (p : MvPolynomial (Fin n) Rat) :
    MvPolynomial.coeff (0 : Fin n →₀ Nat) (MvPolynomial.pderiv i p) =
      MvPolynomial.coeff (Finsupp.single i 1 : Fin n →₀ Nat) p := by
  classical
  conv_lhs => rw [p.as_sum, map_sum, MvPolynomial.coeff_sum]
  conv_rhs => rw [p.as_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial]
  by_cases hsi : s i = 0
  · simp only [hsi, Nat.cast_zero, mul_zero]
    by_cases heq : s = Finsupp.single i 1
    · exfalso
      have := Finsupp.ext_iff.mp heq i
      rw [Finsupp.single_eq_same] at this
      omega
    · simp [heq]
  · have cond_iff : s - (Finsupp.single i 1 : Fin n →₀ Nat) = 0 ↔
        s = (Finsupp.single i 1 : Fin n →₀ Nat) := by
      simp only [Finsupp.ext_iff, Finsupp.tsub_apply, Finsupp.single_apply]
      constructor
      · intro h j
        specialize h j
        by_cases hij : i = j
        · subst hij
          simp at h ⊢
          omega
        · simp [hij] at h ⊢
          omega
      · intro h j
        specialize h j
        by_cases hij : i = j
        · subst hij
          simp at h ⊢
          omega
        · simp [hij] at h ⊢
          omega
    by_cases heq : s = (Finsupp.single i 1 : Fin n →₀ Nat)
    · simp [cond_iff.mpr heq, heq]
    · have hsub_ne : s - (Finsupp.single i 1 : Fin n →₀ Nat) ≠ 0 := by
        intro h
        exact heq (cond_iff.mp h)
      simp [hsub_ne, heq]

/-- The one-derivative row of the singleton-shift generator has constant
coefficient `1`. -/
theorem singletonQuotientSPDPRow_singletonShiftGenerator_coeff_zero_one
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : Fin n) :
    MvPolynomial.coeff (0 : Fin n →₀ Nat)
      (@singletonQuotientSPDPRow M n hn2 htb hns [i] 1
        (mlProj (MvPolynomial.X i *
          Finset.univ.prod
            (singletonQuotientCookLevinFactors M n hn2 htb hns)))) = 1 := by
  classical
  unfold singletonQuotientSPDPRow SPDP.iterDerivList
  simp only [List.foldl_cons, List.foldl_nil, one_mul]
  rw [MultilinearSPDP.coeff_mlProj_of_isMultilinear_mono]
  · rw [coeff_zero_pderiv_eq_coeff_single]
    rw [MultilinearSPDP.coeff_mlProj_of_isMultilinear_mono]
    · rw [MvPolynomial.coeff_X_mul']
      simp only [Finsupp.mem_support_iff, Finsupp.single_eq_same, ne_eq,
        one_ne_zero, not_false_eq_true, ↓reduceIte]
      have hsub : (Finsupp.single i 1 : Fin n →₀ Nat) - Finsupp.single i 1 = 0 := by
        ext j
        simp
      rw [hsub]
      simpa [singletonQuotientCookLevinFactors, cookLevinZeroProfileBaseProduct] using
        cookLevinZeroProfileBaseProduct_coeff_zero M n hn2 htb hns
    · intro j
      by_cases hji : j = i
      · subst hji
        simp
      · simp [Finsupp.single_eq_of_ne hji]
  · intro j
    simp

/-- Any singleton list is block-admissible. -/
theorem isBlockAdmissible_singleton
    {n : Nat} (B : SPDP.BlockPartition n) (i : Fin n) :
    SPDP.isBlockAdmissible B [i] := by
  constructor
  · simp
  · intro b
    by_cases h : B.assign i = b
    · simp [h]
    · simp [h]

/-- The stronger residual-subspace membership bottom is false for the current
singleton quotient. -/
theorem not_SingletonQuotientResidualGeneratorRowsMemSubspace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ¬ SingletonQuotientResidualGeneratorRowsMemSubspace M n hn2 htb hns := by
  classical
  intro hmem
  let i : Fin n := ⟨0, by omega⟩
  have hadm : SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition [i] :=
    isBlockAdmissible_singleton _ i
  have hrowmem := hmem 1 0 i [i] 1 (by simp) (by simp) (by simp) hadm
  have hzero : MvPolynomial.coeff (0 : Fin n →₀ Nat)
      (@singletonQuotientSPDPRow M n hn2 htb hns [i] 1
        (mlProj (MvPolynomial.X i *
          Finset.univ.prod
            (singletonQuotientCookLevinFactors M n hn2 htb hns)))) = 0 :=
    zeroProfileSingletonShiftSubspace_coeff_zero
      (singletonQuotientCookLevinFactors M n hn2 htb hns) hrowmem
  have hone :=
    singletonQuotientSPDPRow_singletonShiftGenerator_coeff_zero_one
      M n hn2 htb hns i
  rw [hone] at hzero
  norm_num at hzero

/-- Because killed rows are equivalent to residual-subspace membership for the
exact quotient kernel, the finite killed-row bottom is also false. -/
theorem not_SingletonQuotientResidualGeneratorRowsKilled
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ¬ SingletonQuotientResidualGeneratorRowsKilled M n hn2 htb hns := by
  intro hkilled
  exact not_SingletonQuotientResidualGeneratorRowsMemSubspace M n hn2 htb hns
    (singletonQuotientResidualGeneratorRowsMemSubspace_of_killed
      M n hn2 htb hns hkilled)

/-! ## Axiom audit anchors -/
#print axioms singletonQuotientResidual_mem_residualSubspace
#print axioms singletonQuotientResidualSubspace_le_ker
#print axioms singletonQuotientProject_apply_eq_zero_iff_mem_residualSubspace
#print axioms singletonQuotientSPDPRow_add
#print axioms singletonQuotientSPDPRow_smul
#print axioms singletonQuotientResidualRowsKilledOnSubspace_of_generatorsKilled
#print axioms singletonQuotientResidualGeneratorRowsKilled_of_memSubspace
#print axioms singletonQuotientResidualGeneratorRowsMemSubspace_of_killed
#print axioms singletonQuotientResidualGeneratorRowsKilled_iff_memSubspace
#print axioms singletonQuotientResidualRowsKilledOnSubspace_of_generatorRowsMemSubspace
#print axioms singletonQuotientResidualRowsKilled_of_generatorsKilled
#print axioms singletonQuotientResidualRowsKilled_of_generatorRowsMemSubspace
#print axioms singletonQuotientResidualRowsKilledOnSubspace_of_spdpStable
#print axioms singletonQuotientResidualRowsKilled_of_killedOnSubspace
#print axioms singletonQuotientResidualRowsKilled_of_spdpStable
#print axioms spdpCompatibleSingletonQuotient_of_projectedRowsFixed_and_residualGeneratorsKilled
#print axioms spdpCompatibleSingletonQuotient_of_projectedRowsFixed_and_generatorRowsMemSubspace
#print axioms spdpCompatibleSingletonQuotient_of_projectedRowsFixed_and_residualStable
#print axioms singletonQuotientRankObligation_of_projectedRowsFixed_and_residualGeneratorsKilled
#print axioms singletonQuotientRankObligation_of_projectedRowsFixed_and_generatorRowsMemSubspace
#print axioms singletonQuotientRankObligation_of_projectedRowsFixed_and_residualStable
#print axioms zeroProfileSingletonShiftSubspace_coeff_zero
#print axioms coeff_zero_pderiv_eq_coeff_single
#print axioms singletonQuotientSPDPRow_singletonShiftGenerator_coeff_zero_one
#print axioms isBlockAdmissible_singleton
#print axioms not_SingletonQuotientResidualGeneratorRowsMemSubspace
#print axioms not_SingletonQuotientResidualGeneratorRowsKilled

end PallLean.Paper93.DeepMath.PathB
