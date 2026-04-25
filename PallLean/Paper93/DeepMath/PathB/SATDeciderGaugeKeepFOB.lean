import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeCandidate

/-!
# First-of-block SAT-decider gauge candidate

This file records the paper-faithful first-of-block `piZero` projection as a
concrete flat `SATDeciderGaugeMap`.  It keeps exactly the Cook-Levin variables
whose flat index is divisible by `3`, and kills the other variables.

The file deliberately proves only structural and rank-monotonicity facts about
this candidate.  It does not claim NP-side preservation, P-side collapse, or a
final `PiStar` witness.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- Candidate gauge: keep the first variable of every Cook-Levin 3-block and
substitute all other variables by zero. -/
noncomputable def satDeciderGaugeKeepFOBProjection
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeMap M n hn2 htb hns :=
  PiStarConcrete.piZero PiStarConcrete.keepFOB

/-- The first-of-block projection fixes exactly variables whose flat index is
divisible by `3`. -/
theorem satDeciderGaugeKeepFOBProjection_apply_var_of_dvd
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : Fin (cook_levin_compilation M n hn2 htb hns).numVars)
    (hi : 3 ∣ i.val) :
    satDeciderGaugeKeepFOBProjection M n hn2 htb hns (X i) = X i := by
  unfold satDeciderGaugeKeepFOBProjection
  rw [PiStarConcrete.piZero_X]
  exact if_pos (by simpa [PiStarConcrete.keepFOB] using hi)

/-- The first-of-block projection kills exactly variables whose flat index is
not divisible by `3`. -/
theorem satDeciderGaugeKeepFOBProjection_apply_var_of_not_dvd
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : Fin (cook_levin_compilation M n hn2 htb hns).numVars)
    (hi : ¬ 3 ∣ i.val) :
    satDeciderGaugeKeepFOBProjection M n hn2 htb hns (X i) = 0 := by
  unfold satDeciderGaugeKeepFOBProjection
  rw [PiStarConcrete.piZero_X]
  exact if_neg (by simpa [PiStarConcrete.keepFOB] using hi)

/-- The first-of-block projection fixes the first flat Cook-Levin variable. -/
theorem satDeciderGaugeKeepFOBProjection_apply_firstVar
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    satDeciderGaugeKeepFOBProjection M n hn2 htb hns
        (X (satDeciderGaugeFirstVar M n hn2 htb hns)) =
      X (satDeciderGaugeFirstVar M n hn2 htb hns) := by
  apply satDeciderGaugeKeepFOBProjection_apply_var_of_dvd
  simp [satDeciderGaugeFirstVar]

/-- The first-of-block projection kills the second flat Cook-Levin variable. -/
theorem satDeciderGaugeKeepFOBProjection_apply_secondVar
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    satDeciderGaugeKeepFOBProjection M n hn2 htb hns
        (X (satDeciderGaugeSecondVar M n hn2 htb hns)) = 0 := by
  apply satDeciderGaugeKeepFOBProjection_apply_var_of_not_dvd
  norm_num [satDeciderGaugeSecondVar]

/-- The first-of-block projection is compatible with the stronger SPDP
subspace-image containment criterion. -/
theorem satDeciderGaugeKeepFOBProjection_spdpSubspaceImageContainment
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeSPDPSubspaceImageContainment M n hn2 htb hns
      (satDeciderGaugeKeepFOBProjection M n hn2 htb hns) :=
  piZero_spdpSubspaceImageContainment PiStarConcrete.keepFOB
    (cook_levin_compilation M n hn2 htb hns).partition

/-- Rank monotonicity follows from the SPDP image-containment criterion. -/
theorem satDeciderGaugeKeepFOBProjection_rankMonotonicity
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns
      (satDeciderGaugeKeepFOBProjection M n hn2 htb hns) :=
  satDeciderGaugeRankMonotonicity_of_spdpSubspaceImageContainment
    M n hn2 htb hns
    (satDeciderGaugeKeepFOBProjection M n hn2 htb hns)
    (satDeciderGaugeKeepFOBProjection_spdpSubspaceImageContainment
      M n hn2 htb hns)

/-- The first-of-block projection is not the zero linear map. -/
theorem satDeciderGaugeKeepFOBProjection_ne_zero
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    satDeciderGaugeKeepFOBProjection M n hn2 htb hns ≠
      (0 : SATDeciderGaugeMap M n hn2 htb hns) := by
  intro hzero
  have happ := congrArg
    (fun g : SATDeciderGaugeMap M n hn2 htb hns =>
      g (X (satDeciderGaugeFirstVar M n hn2 htb hns))) hzero
  dsimp at happ
  rw [satDeciderGaugeKeepFOBProjection_apply_firstVar] at happ
  exact (X_ne_zero (satDeciderGaugeFirstVar M n hn2 htb hns)) happ

/-- The first-of-block projection is not the identity linear map. -/
theorem satDeciderGaugeKeepFOBProjection_ne_id
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    satDeciderGaugeKeepFOBProjection M n hn2 htb hns ≠
      (LinearMap.id : SATDeciderGaugeMap M n hn2 htb hns) := by
  intro hid
  have happ := congrArg
    (fun g : SATDeciderGaugeMap M n hn2 htb hns =>
      g (X (satDeciderGaugeSecondVar M n hn2 htb hns))) hid
  dsimp at happ
  rw [satDeciderGaugeKeepFOBProjection_apply_secondVar] at happ
  exact (X_ne_zero (satDeciderGaugeSecondVar M n hn2 htb hns)) happ.symm

/-- The first-of-block projection is not the existing flat `piPhi` candidate,
because that candidate is definitionally the identity on the flat space. -/
theorem satDeciderGaugeKeepFOBProjection_ne_piPhi
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    satDeciderGaugeKeepFOBProjection M n hn2 htb hns ≠
      satDeciderGaugeMapPiPhi M n hn2 htb hns := by
  intro hpi
  exact satDeciderGaugeKeepFOBProjection_ne_id M n hn2 htb hns
    (by simpa [satDeciderGaugeMapPiPhi_eq_id M n hn2 htb hns] using hpi)

/-- For the concrete first-of-block projection, all candidate-core obligations
except moving `compiledPoly` are already discharged.  Thus the remaining
criterion is exactly non-fixing of the real compiled polynomial. -/
theorem satDeciderGaugeKeepFOBProjection_candidateCore_iff_moves_compiledPoly
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeCandidateCore M n hn2 htb hns
        (satDeciderGaugeKeepFOBProjection M n hn2 htb hns) ↔
      satDeciderGaugeKeepFOBProjection M n hn2 htb hns
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≠
        compiledPoly (cook_levin_compilation M n hn2 htb hns) := by
  constructor
  · intro hcore
    exact hcore.2.2.2.2
  · intro hmove
    exact
      ⟨satDeciderGaugeKeepFOBProjection_rankMonotonicity M n hn2 htb hns,
        satDeciderGaugeKeepFOBProjection_ne_zero M n hn2 htb hns,
        satDeciderGaugeKeepFOBProjection_ne_id M n hn2 htb hns,
        satDeciderGaugeKeepFOBProjection_ne_piPhi M n hn2 htb hns,
        hmove⟩

/-- Coefficient criterion specialized to the concrete first-of-block
projection. -/
theorem satDeciderGaugeKeepFOBProjection_candidateCore_iff_coeff
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeCandidateCore M n hn2 htb hns
        (satDeciderGaugeKeepFOBProjection M n hn2 htb hns) ↔
      ∃ α,
        coeff α
            (satDeciderGaugeKeepFOBProjection M n hn2 htb hns
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≠
          coeff α
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)) := by
  rw [satDeciderGaugeKeepFOBProjection_candidateCore_iff_moves_compiledPoly]
  exact mvPolynomial_ne_iff_exists_coeff_ne

/-! ## Axiom audit anchors -/

#print axioms satDeciderGaugeKeepFOBProjection_apply_var_of_dvd
#print axioms satDeciderGaugeKeepFOBProjection_apply_var_of_not_dvd
#print axioms satDeciderGaugeKeepFOBProjection_spdpSubspaceImageContainment
#print axioms satDeciderGaugeKeepFOBProjection_rankMonotonicity
#print axioms satDeciderGaugeKeepFOBProjection_ne_zero
#print axioms satDeciderGaugeKeepFOBProjection_ne_id
#print axioms satDeciderGaugeKeepFOBProjection_ne_piPhi
#print axioms satDeciderGaugeKeepFOBProjection_candidateCore_iff_moves_compiledPoly
#print axioms satDeciderGaugeKeepFOBProjection_candidateCore_iff_coeff

end PallLean.Paper93.DeepMath.PathB
