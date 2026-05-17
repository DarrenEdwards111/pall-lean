import PallLean.Paper93.DeepMath.PathB.SingletonQuotientRankMonotonicity

/-!
# Singleton-quotient generator lift: commutator decomposition

The rank monotonicity blocker for `singletonQuotientSATGauge` is the row-level
statement

  `mlProj (m * ∂_S (Π p)) ∈ Π '' SPDPRows(p)`.

For substitution gauges (`piPhi`) this follows from proved commutation lemmas.
For the singleton quotient, Π is an arbitrary complement projection, so the
right object to prove is a concrete row-commutator/residual condition.

This file decomposes the blocker into the smallest checkable algebraic seam:
for every SPDP row, the projected row of `Π p` must equal Π applied to an
honest SPDP row of `p`.  Equivalently, the commutator residual vanishes.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine

/-- Local abbreviation for the singleton-quotient projection. -/
noncomputable abbrev singletonQuotientProject
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeMap M n hn2 htb hns :=
  singletonQuotientSATGauge M n hn2 htb hns

/-- The row produced after first projecting the polynomial and then taking an
SPDP row. -/
noncomputable def singletonQuotientProjectedRow
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n)) (m : MvPolynomial (Fin n) Rat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    SATDeciderGaugeSpace M n hn2 htb hns :=
  mlProj (m * SPDP.iterDerivList S
    ((singletonQuotientProject M n hn2 htb hns) p))

/-- The row obtained by first forming the original SPDP row and then applying
the singleton quotient. -/
noncomputable def singletonQuotientImageOfOriginalRow
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n)) (m : MvPolynomial (Fin n) Rat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    SATDeciderGaugeSpace M n hn2 htb hns :=
  (singletonQuotientProject M n hn2 htb hns)
    (mlProj (m * SPDP.iterDerivList S p))

/-- Row commutator residual for the singleton quotient.  Vanishing of this
residual is exactly the row-level commutation needed by the SPDP image-lift
proof. -/
noncomputable def singletonQuotientRowCommutator
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n)) (m : MvPolynomial (Fin n) Rat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    SATDeciderGaugeSpace M n hn2 htb hns :=
  singletonQuotientProjectedRow M n hn2 htb hns S m p -
    singletonQuotientImageOfOriginalRow M n hn2 htb hns S m p

/-- Row-commutation condition for the singleton quotient. -/
def SingletonQuotientSPDPRowCommutation
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (κ ℓ : Nat) (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin n)) (m : MvPolynomial (Fin n) Rat),
    S.length = κ →
    m.totalDegree ≤ ℓ →
    m.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S →
    singletonQuotientProjectedRow M n hn2 htb hns S m p =
      singletonQuotientImageOfOriginalRow M n hn2 htb hns S m p

/-- The same condition as vanishing of the explicit row commutator. -/
def SingletonQuotientSPDPRowCommutatorVanishes
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (κ ℓ : Nat) (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin n)) (m : MvPolynomial (Fin n) Rat),
    S.length = κ →
    m.totalDegree ≤ ℓ →
    m.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S →
    singletonQuotientRowCommutator M n hn2 htb hns S m p = 0

/-- Row commutation and row-commutator vanishing are equivalent. -/
theorem singletonQuotient_rowCommutation_iff_commutatorVanishes
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SingletonQuotientSPDPRowCommutation M n hn2 htb hns ↔
      SingletonQuotientSPDPRowCommutatorVanishes M n hn2 htb hns := by
  constructor
  · intro hcomm κ ℓ p S m hS hm hmvars hadm
    unfold singletonQuotientRowCommutator
    rw [hcomm κ ℓ p S m hS hm hmvars hadm]
    simp
  · intro hzero κ ℓ p S m hS hm hmvars hadm
    have hz := hzero κ ℓ p S m hS hm hmvars hadm
    unfold singletonQuotientRowCommutator at hz
    exact sub_eq_zero.mp hz

/-- Row commutation gives the generator lift.  The preimage witness is the
ordinary SPDP row `mlProj (m * ∂_S p)`. -/
theorem singletonQuotient_generatorLift_of_rowCommutation
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcomm : SingletonQuotientSPDPRowCommutation M n hn2 htb hns) :
    SingletonQuotientSPDPGeneratorLift M n hn2 htb hns := by
  intro κ ℓ p S m hS hm hmvars hadm
  change singletonQuotientProjectedRow M n hn2 htb hns S m p ∈
    Submodule.map (singletonQuotientSATGauge M n hn2 htb hns)
      (mlBlockedSpdpSubspace
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ p)
  rw [hcomm κ ℓ p S m hS hm hmvars hadm]
  unfold singletonQuotientImageOfOriginalRow singletonQuotientProject
  refine ⟨mlProj (m * SPDP.iterDerivList S p), ?_, rfl⟩
  exact Submodule.subset_span ⟨S, m, hS, hm, hmvars, hadm, rfl⟩

/-- Vanishing of the row commutator gives the generator lift. -/
theorem singletonQuotient_generatorLift_of_commutatorVanishes
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hzero : SingletonQuotientSPDPRowCommutatorVanishes M n hn2 htb hns) :
    SingletonQuotientSPDPGeneratorLift M n hn2 htb hns :=
  singletonQuotient_generatorLift_of_rowCommutation M n hn2 htb hns
    ((singletonQuotient_rowCommutation_iff_commutatorVanishes
      M n hn2 htb hns).mpr hzero)

/-- Final rank monotonicity from the explicit row-commutator vanishing seam. -/
theorem singletonQuotientSATGauge_rankMonotonicity_of_commutatorVanishes
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hzero : SingletonQuotientSPDPRowCommutatorVanishes M n hn2 htb hns) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns
      (singletonQuotientSATGauge M n hn2 htb hns) :=
  singletonQuotientSATGauge_rankMonotonicity_of_generatorLift
    M n hn2 htb hns
    (singletonQuotient_generatorLift_of_commutatorVanishes
      M n hn2 htb hns hzero)

/-- The remaining rank problem is exactly row-commutator control for the
singleton quotient. -/
def SingletonQuotientRowCommutatorBlocker
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  SingletonQuotientSPDPRowCommutatorVanishes M n hn2 htb hns

/-- Supplying row-commutator control closes the candidate-specific rank
obligation. -/
theorem singletonQuotientRankObligation_of_rowCommutatorBlocker
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (h : SingletonQuotientRowCommutatorBlocker M n hn2 htb hns) :
    SingletonQuotientSATGaugeRankMonotonicityObligation M n hn2 htb hns :=
  singletonQuotientRankObligation_of_blocker M n hn2 htb hns
    (singletonQuotient_generatorLift_of_commutatorVanishes
      M n hn2 htb hns h)

/-! ## Axiom audit anchors -/
#print axioms singletonQuotient_rowCommutation_iff_commutatorVanishes
#print axioms singletonQuotient_generatorLift_of_rowCommutation
#print axioms singletonQuotient_generatorLift_of_commutatorVanishes
#print axioms singletonQuotientSATGauge_rankMonotonicity_of_commutatorVanishes
#print axioms singletonQuotientRankObligation_of_rowCommutatorBlocker

end PallLean.Paper93.DeepMath.PathB
