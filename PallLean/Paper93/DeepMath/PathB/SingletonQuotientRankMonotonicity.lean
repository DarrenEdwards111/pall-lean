import PallLean.Paper93.DeepMath.PathB.NonflatSingletonQuotientCandidate

/-!
# Rank monotonicity gate for the singleton-quotient candidate

The singleton quotient is a genuine non-flat linear projection, but it is not a
substitution/algebra map like `piPhi`.  Therefore rank monotonicity does not
follow from the existing `piZero/piPhi` commutation lemmas.  This file isolates
and proves the exact smallest generator-level lift condition needed for the
candidate-specific rank field.

No final GodMove claim is made here.  The point is to turn the rank task into a
checkable generator theorem about the concrete quotient projection.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine

/-- Generator-level lift condition for the singleton-quotient projection.

Every SPDP generator of the projected polynomial must lie in the image, under
the singleton quotient, of the original SPDP subspace.  This is stronger than
rank monotonicity but is exactly the condition consumed by the general
`spdpSubspaceImageContainment_of_generator_image_mem` theorem. -/
def SingletonQuotientSPDPGeneratorLift
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (κ ℓ : Nat) (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin n)) (m : MvPolynomial (Fin n) Rat),
    S.length = κ →
    m.totalDegree ≤ ℓ →
    m.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S →
    mlProj (m * SPDP.iterDerivList S
      ((singletonQuotientSATGauge M n hn2 htb hns) p)) ∈
        Submodule.map (singletonQuotientSATGauge M n hn2 htb hns)
          (mlBlockedSpdpSubspace
            (cook_levin_compilation M n hn2 htb hns).partition κ ℓ p)

/-- The generator-level lift gives the image-containment obligation for the
singleton quotient. -/
theorem singletonQuotient_imageContainment_of_generatorLift
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hlift : SingletonQuotientSPDPGeneratorLift M n hn2 htb hns) :
    SingletonQuotientSATGaugeRankMonotonicityObligation M n hn2 htb hns := by
  unfold SingletonQuotientSATGaugeRankMonotonicityObligation
  unfold SATDeciderGaugeSPDPSubspaceImageContainment
  exact spdpSubspaceImageContainment_of_generator_image_mem
    (cook_levin_compilation M n hn2 htb hns).partition
    (singletonQuotientSATGauge M n hn2 htb hns)
    (hlift)

/-- The generator-level lift discharges the candidate-specific rank monotonicity
field. -/
theorem singletonQuotientSATGauge_rankMonotonicity_of_generatorLift
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hlift : SingletonQuotientSPDPGeneratorLift M n hn2 htb hns) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns
      (singletonQuotientSATGauge M n hn2 htb hns) :=
  singletonQuotientSATGauge_rankMonotonicity_of_imageContainment
    M n hn2 htb hns
    (singletonQuotient_imageContainment_of_generatorLift M n hn2 htb hns hlift)

/-- Equivalent rank-monotonicity status for the singleton quotient: the already
named image-containment obligation is precisely sufficient for the rank field,
and any rank proof via the reusable criterion should target this proposition.
-/
theorem singletonQuotient_rankMonotonicity_gate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SingletonQuotientSPDPGeneratorLift M n hn2 htb hns →
      SATDeciderGaugeRankMonotonicity M n hn2 htb hns
        (singletonQuotientSATGauge M n hn2 htb hns) :=
  singletonQuotientSATGauge_rankMonotonicity_of_generatorLift M n hn2 htb hns

/-- Why this is the right blocker: an arbitrary linear projection does not come
with this generator lift.  The proof of the lift must show that singleton
quotienting commutes with the SPDP row construction up to image of the original
row space. -/
def SingletonQuotientRankMonotonicityBlocker
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  SingletonQuotientSPDPGeneratorLift M n hn2 htb hns

/-- Once the blocker is supplied, the first of the three singleton-quotient
GodMove obligations is closed. -/
theorem singletonQuotientRankObligation_of_blocker
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (h : SingletonQuotientRankMonotonicityBlocker M n hn2 htb hns) :
    SingletonQuotientSATGaugeRankMonotonicityObligation M n hn2 htb hns :=
  singletonQuotient_imageContainment_of_generatorLift M n hn2 htb hns h

/-! ## Axiom audit anchors -/
#print axioms singletonQuotient_imageContainment_of_generatorLift
#print axioms singletonQuotientSATGauge_rankMonotonicity_of_generatorLift
#print axioms singletonQuotient_rankMonotonicity_gate
#print axioms singletonQuotientRankObligation_of_blocker

end PallLean.Paper93.DeepMath.PathB
