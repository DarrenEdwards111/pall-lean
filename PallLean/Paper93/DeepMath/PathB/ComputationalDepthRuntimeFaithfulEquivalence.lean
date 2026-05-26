import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRuntimeFaithfulConstructionNoGo

/-
# Runtime-faithful construction equivalence

This file completes the audit of the runtime-faithful God-Move construction
target.

The previous file proved:

  runtime-faithful super-polynomial frame -> DeepSATSearch.

Here we prove the converse in the current formal interface:

  DeepSATSearch -> runtime-faithful super-polynomial frame.

The construction is deliberately vacuous: if there are no correct polynomial
SAT searchers, the `liveSlots` and transport obligations, which are quantified
over correct searchers, have no cases.  The frame can then use a syntactic
super-polynomial layer of certified trivial satisfiable challenges.

This is not a positive P-vs-NP proof.  It proves that the current construction
target is exactly equivalent to the lower-bound theorem.  It also exposes the
next modeling weakness: a non-vacuous positive target must prevent duplicate or
trivial semantic challenge mass from being counted as irreducible God-Move mass.
-/

namespace SATDepthMachine

/-! ## Trivial satisfiable challenges with super-polynomial layer count -/

/-- Empty CNF over `n` variables, satisfiable by every length-`n` assignment. -/
def runtimeFaithfulEmptyCNF (n : Nat) : CNF where
  vars := n
  clauses := []

theorem runtimeFaithfulEmptyCNF_size
    (n : Nat) :
    (runtimeFaithfulEmptyCNF n).size = n := by
  simp [runtimeFaithfulEmptyCNF, CNF.size]

theorem runtimeFaithfulEmptyCNF_satisfies
    (n : Nat) :
    Satisfies (runtimeFaithfulEmptyCNF n) (List.replicate n false) := by
  simp [Satisfies, runtimeFaithfulEmptyCNF, CNF.eval]

/-- A certified trivial satisfiable God-Move challenge at size `n`. -/
def runtimeFaithfulTrivialChallenge (n : Nat) : GodMoveChallenge where
  formula := runtimeFaithfulEmptyCNF n
  witness := List.replicate n false
  witness_sat := runtimeFaithfulEmptyCNF_satisfies n

/-- The deliberately super-polynomial layer scale `(n+1)^(n+1)`. -/
def runtimeFaithfulVacuousMass (n : Nat) : Nat :=
  (n + 1) ^ (n + 1)

/-- The vacuous mass scale beats every fixed polynomial. -/
theorem runtimeFaithfulVacuousMass_beats_polynomial
    (k c : Nat) :
    ∃ n : Nat,
      c * (n + 1) ^ k < runtimeFaithfulVacuousMass n := by
  let n := k + c + 1
  refine ⟨n, ?_⟩
  have hc_le : c <= n + 1 := by
    dsimp [n]
    omega
  have hk_succ_lt : k + 1 < n + 1 := by
    dsimp [n]
    omega
  have hb_gt_one : 1 < n + 1 := by
    dsimp [n]
    omega
  have hmul :
      c * (n + 1) ^ k <= (n + 1) * (n + 1) ^ k :=
    Nat.mul_le_mul_right ((n + 1) ^ k) hc_le
  have hsucc :
      (n + 1) * (n + 1) ^ k = (n + 1) ^ (k + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have hpow :
      (n + 1) ^ (k + 1) < (n + 1) ^ (n + 1) :=
    Nat.pow_lt_pow_right hb_gt_one hk_succ_lt
  exact lt_of_le_of_lt (hmul.trans_eq hsucc) hpow

/-- A syntactic super-polynomial God-Move frame made of repeated trivial
certified challenges. -/
def vacuousSuperPolynomialGodMoveFrame : GodMoveFrame where
  layer := fun n =>
    List.replicate (runtimeFaithfulVacuousMass n)
      (runtimeFaithfulTrivialChallenge n)

theorem vacuousSuperPolynomialGodMoveFrame_familyMass
    (n : Nat) :
    vacuousSuperPolynomialGodMoveFrame.familyMass n =
      runtimeFaithfulVacuousMass n := by
  simp [GodMoveFrame.familyMass, vacuousSuperPolynomialGodMoveFrame]

/-- The vacuous frame has super-polynomial family mass. -/
theorem vacuousSuperPolynomialGodMoveFrame_lowerBound :
    GodMoveFamilyMassLowerBound vacuousSuperPolynomialGodMoveFrame := by
  intro B hBpoly
  rcases hBpoly with ⟨k, c, hpoly⟩
  rcases runtimeFaithfulVacuousMass_beats_polynomial k c with ⟨n, hlt⟩
  refine ⟨n, lt_of_le_of_lt (hpoly n) ?_⟩
  simpa [vacuousSuperPolynomialGodMoveFrame_familyMass n] using hlt

/-! ## Deep search gives a vacuous runtime-faithful construction -/

/-- Under `DeepSATSearch`, every obligation over correct searchers is vacuous,
so the syntactic super-polynomial frame becomes runtime-faithful. -/
def vacuousRuntimeFaithfulGodMoveFrame_of_deepSATSearch
    (C : CanonicalMachineSurface)
    (hdeep : DeepSATSearch C.toMachineModel) :
    RuntimeFaithfulGodMoveFrame C where
  frame := vacuousSuperPolynomialGodMoveFrame
  layerInput := runtimeFaithfulEmptyCNF
  layerInput_size := runtimeFaithfulEmptyCNF_size
  liveSlots := by
    intro M hM _n
    exact False.elim (hdeep ⟨M, hM⟩)
  transportedMass_le_liveSlots := by
    intro M hM _n
    exact False.elim (hdeep ⟨M, hM⟩)

/-- Deep SAT search implies the runtime-faithful lower-bound construction target
in the current interface. -/
theorem runtimeFaithfulGodMoveLowerBoundConstruction_of_deepSATSearch
    (C : CanonicalMachineSurface)
    (hdeep : DeepSATSearch C.toMachineModel) :
    RuntimeFaithfulGodMoveLowerBoundConstruction C := by
  exact ⟨vacuousRuntimeFaithfulGodMoveFrame_of_deepSATSearch C hdeep,
    vacuousSuperPolynomialGodMoveFrame_lowerBound⟩

/-- Final equivalence: with the current definitions, constructing a
runtime-faithful super-polynomial God-Move frame is exactly deep SAT search. -/
theorem runtimeFaithfulGodMoveLowerBoundConstruction_iff_deepSATSearch
    (C : CanonicalMachineSurface) :
    RuntimeFaithfulGodMoveLowerBoundConstruction C ↔
      DeepSATSearch C.toMachineModel := by
  constructor
  · exact deepSATSearch_of_runtimeFaithfulGodMoveLowerBoundConstruction C
  · exact runtimeFaithfulGodMoveLowerBoundConstruction_of_deepSATSearch C

/-- Therefore the construction target is equivalent to no canonical SAT
decision on the canonical surface. -/
theorem runtimeFaithfulGodMoveLowerBoundConstruction_iff_noCanonicalSATDecisionInP
    (C : CanonicalMachineSurface) :
    RuntimeFaithfulGodMoveLowerBoundConstruction C ↔
      ¬ CanonicalSATDecisionInP C := by
  rw [runtimeFaithfulGodMoveLowerBoundConstruction_iff_deepSATSearch]
  exact canonicalDeepSATSearch_iff_no_decider C

/-! ## Axiom trace -/

#print axioms runtimeFaithfulEmptyCNF_size
#print axioms runtimeFaithfulEmptyCNF_satisfies
#print axioms runtimeFaithfulVacuousMass_beats_polynomial
#print axioms vacuousSuperPolynomialGodMoveFrame_lowerBound
#print axioms runtimeFaithfulGodMoveLowerBoundConstruction_of_deepSATSearch
#print axioms runtimeFaithfulGodMoveLowerBoundConstruction_iff_deepSATSearch
#print axioms runtimeFaithfulGodMoveLowerBoundConstruction_iff_noCanonicalSATDecisionInP

end SATDepthMachine
