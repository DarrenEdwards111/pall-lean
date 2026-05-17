import PallLean.Paper93.DeepMath.PathB.SingletonQuotientGeneratorLiftDecomposition

/-!
# SPDP-compatible singleton quotient interface

The arbitrary complement chosen by
`zeroProfileQuotientBySingletonShiftProjection` is not an algebra map and has no
reason, by itself, to commute with SPDP row generation.  The correct non-circular
next target is therefore an SPDP-compatible complement/projection: the projected
part is closed under SPDP rows and the residual singleton-shift part is killed
after taking SPDP rows.

This file proves that those two concrete invariance checks imply the row
commutator vanishes, hence close the already-isolated rank-monotonicity
obligation for the singleton quotient candidate.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine

/-- The residual removed by the singleton quotient. -/
noncomputable def singletonQuotientResidual
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    SATDeciderGaugeSpace M n hn2 htb hns :=
  p - (singletonQuotientProject M n hn2 htb hns) p

/-- SPDP row of an arbitrary polynomial, used to state image/residual
invariance without hiding the row operator inside the projection notation. -/
noncomputable def singletonQuotientSPDPRow
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (S : List (Fin n)) (m : MvPolynomial (Fin n) Rat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    SATDeciderGaugeSpace M n hn2 htb hns :=
  mlProj (m * SPDP.iterDerivList S p)

/-- The projected/image part of the singleton quotient is stable under every
SPDP row operator relevant to the rank matrix. -/
def SingletonQuotientProjectedRowsFixed
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (κ ℓ : Nat) (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin n)) (m : MvPolynomial (Fin n) Rat),
    S.length = κ →
    m.totalDegree ≤ ℓ →
    m.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S →
    (singletonQuotientProject M n hn2 htb hns)
      (singletonQuotientSPDPRow S m
        ((singletonQuotientProject M n hn2 htb hns) p)) =
      singletonQuotientSPDPRow S m
        ((singletonQuotientProject M n hn2 htb hns) p)

/-- The residual/kernel part removed by the singleton quotient remains killed
after every SPDP row operator relevant to the rank matrix. -/
def SingletonQuotientResidualRowsKilled
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (κ ℓ : Nat) (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin n)) (m : MvPolynomial (Fin n) Rat),
    S.length = κ →
    m.totalDegree ≤ ℓ →
    m.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S →
    (singletonQuotientProject M n hn2 htb hns)
      (singletonQuotientSPDPRow S m
        (singletonQuotientResidual M n hn2 htb hns p)) = 0

/-- The refined compatibility interface for the singleton quotient.  This is
not final-theorem strength: it only says the chosen singleton-shift complement
is invariant under the local SPDP row operators, and that the killed residual
stays killed under those operators. -/
def SPDPCompatibleSingletonQuotient
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  SingletonQuotientProjectedRowsFixed M n hn2 htb hns ∧
    SingletonQuotientResidualRowsKilled M n hn2 htb hns

/-- Row decomposition through the singleton quotient residual. -/
theorem singletonQuotientSPDPRow_decompose_project_residual
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n)) (m : MvPolynomial (Fin n) Rat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    singletonQuotientSPDPRow S m p =
      singletonQuotientSPDPRow S m
        ((singletonQuotientProject M n hn2 htb hns) p) +
      singletonQuotientSPDPRow S m
        (singletonQuotientResidual M n hn2 htb hns p) := by
  classical
  unfold singletonQuotientSPDPRow
  unfold singletonQuotientResidual
  have hp : p = (singletonQuotientProject M n hn2 htb hns) p +
      (p - (singletonQuotientProject M n hn2 htb hns) p) := by
    abel
  conv_lhs =>
    rw [hp, SPDP.iterDerivList_add, mul_add, mlProj_add]

/-- Projected-row fixedness plus killed residual rows force the row commutator
to vanish. -/
theorem singletonQuotient_commutatorVanishes_of_projected_fixed_and_residual_killed
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hfix : SingletonQuotientProjectedRowsFixed M n hn2 htb hns)
    (hkill : SingletonQuotientResidualRowsKilled M n hn2 htb hns) :
    SingletonQuotientSPDPRowCommutatorVanishes M n hn2 htb hns := by
  intro κ ℓ p S m hS hm hmvars hadm
  unfold singletonQuotientRowCommutator
  apply sub_eq_zero.mpr
  unfold singletonQuotientProjectedRow singletonQuotientImageOfOriginalRow
  change singletonQuotientSPDPRow S m
      ((singletonQuotientProject M n hn2 htb hns) p) =
    (singletonQuotientProject M n hn2 htb hns)
      (singletonQuotientSPDPRow S m p)
  rw [singletonQuotientSPDPRow_decompose_project_residual M n hn2 htb hns S m p]
  rw [map_add]
  rw [hfix κ ℓ p S m hS hm hmvars hadm]
  rw [hkill κ ℓ p S m hS hm hmvars hadm]
  simp

/-- The packaged compatibility interface closes row-commutator vanishing. -/
theorem singletonQuotient_commutatorVanishes_of_spdpCompatible
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcompat : SPDPCompatibleSingletonQuotient M n hn2 htb hns) :
    SingletonQuotientSPDPRowCommutatorVanishes M n hn2 htb hns :=
  singletonQuotient_commutatorVanishes_of_projected_fixed_and_residual_killed
    M n hn2 htb hns hcompat.1 hcompat.2

/-- SPDP-compatible singleton quotients close candidate rank monotonicity. -/
theorem singletonQuotientSATGauge_rankMonotonicity_of_spdpCompatible
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcompat : SPDPCompatibleSingletonQuotient M n hn2 htb hns) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns
      (singletonQuotientSATGauge M n hn2 htb hns) :=
  singletonQuotientSATGauge_rankMonotonicity_of_commutatorVanishes
    M n hn2 htb hns
    (singletonQuotient_commutatorVanishes_of_spdpCompatible
      M n hn2 htb hns hcompat)

/-- SPDP-compatible singleton quotients close the candidate-specific rank
obligation. -/
theorem singletonQuotientRankObligation_of_spdpCompatible
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcompat : SPDPCompatibleSingletonQuotient M n hn2 htb hns) :
    SingletonQuotientSATGaugeRankMonotonicityObligation M n hn2 htb hns :=
  singletonQuotientRankObligation_of_rowCommutatorBlocker
    M n hn2 htb hns
    (singletonQuotient_commutatorVanishes_of_spdpCompatible
      M n hn2 htb hns hcompat)

/-! ## Axiom audit anchors -/
#print axioms singletonQuotientSPDPRow_decompose_project_residual
#print axioms singletonQuotient_commutatorVanishes_of_projected_fixed_and_residual_killed
#print axioms singletonQuotient_commutatorVanishes_of_spdpCompatible
#print axioms singletonQuotientSATGauge_rankMonotonicity_of_spdpCompatible
#print axioms singletonQuotientRankObligation_of_spdpCompatible

end PallLean.Paper93.DeepMath.PathB
