import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeRankMonotoneCriterion
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeMapPiPhi

/-!
# A nontrivial SAT-decider gauge-map candidate

This file records a concrete, kernel-checked attempt at a richer flat
`SATDeciderGaugeMap` for the real Cook-Levin object.  The map is the
`piZero` projection that keeps only the first Cook-Levin variable.  It is not
the identity, not the existing flat `piPhi` map, and not the zero map.  It also
satisfies the new `SATDeciderGaugeSPDPSubspaceImageContainment` criterion, so
rank monotonicity follows through the intended route.

What is *not* claimed here: no final `Π⋆` witness is built, and no P-side or
NP-side SAT-decider gauge package is asserted.  The remaining "moves the real
compiled polynomial" requirement is exposed as an exact coefficient criterion.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- The first variable of the real flat Cook-Levin space. -/
noncomputable def satDeciderGaugeFirstVar
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Fin (cook_levin_compilation M n hn2 htb hns).numVars :=
  ⟨0, by
    rw [cook_levin_numVars M n hn2 htb hns]
    omega⟩

/-- The second variable of the real flat Cook-Levin space. -/
noncomputable def satDeciderGaugeSecondVar
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Fin (cook_levin_compilation M n hn2 htb hns).numVars :=
  ⟨1, by
    rw [cook_levin_numVars M n hn2 htb hns]
    omega⟩

/-- Candidate gauge: keep only the first Cook-Levin variable and substitute
all other variables by zero. -/
noncomputable def satDeciderGaugeKeepFirstProjection
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeMap M n hn2 htb hns :=
  PiStarConcrete.piZero (PiStarConcrete.keepFirstK 1)

/-- The keep-first projection sends the first variable to itself. -/
theorem satDeciderGaugeKeepFirstProjection_apply_firstVar
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    satDeciderGaugeKeepFirstProjection M n hn2 htb hns
        (X (satDeciderGaugeFirstVar M n hn2 htb hns)) =
      X (satDeciderGaugeFirstVar M n hn2 htb hns) := by
  unfold satDeciderGaugeKeepFirstProjection
  rw [PiStarConcrete.piZero_X]
  rw [if_pos]
  simp [PiStarConcrete.keepFirstK, satDeciderGaugeFirstVar]

/-- The keep-first projection kills the second variable. -/
theorem satDeciderGaugeKeepFirstProjection_apply_secondVar
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    satDeciderGaugeKeepFirstProjection M n hn2 htb hns
        (X (satDeciderGaugeSecondVar M n hn2 htb hns)) = 0 := by
  unfold satDeciderGaugeKeepFirstProjection
  rw [PiStarConcrete.piZero_X]
  rw [if_neg]
  simp [PiStarConcrete.keepFirstK, satDeciderGaugeSecondVar]

/-- The keep-first projection is compatible with the stronger SPDP
subspace-image containment criterion. -/
theorem satDeciderGaugeKeepFirstProjection_spdpSubspaceImageContainment
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeSPDPSubspaceImageContainment M n hn2 htb hns
      (satDeciderGaugeKeepFirstProjection M n hn2 htb hns) :=
  piZero_spdpSubspaceImageContainment (PiStarConcrete.keepFirstK 1)
    (cook_levin_compilation M n hn2 htb hns).partition

/-- Rank monotonicity follows from the new containment criterion, not from a
bespoke rank argument. -/
theorem satDeciderGaugeKeepFirstProjection_rankMonotonicity
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns
      (satDeciderGaugeKeepFirstProjection M n hn2 htb hns) :=
  satDeciderGaugeRankMonotonicity_of_spdpSubspaceImageContainment
    M n hn2 htb hns
    (satDeciderGaugeKeepFirstProjection M n hn2 htb hns)
    (satDeciderGaugeKeepFirstProjection_spdpSubspaceImageContainment
      M n hn2 htb hns)

/-- The keep-first projection is not the zero linear map. -/
theorem satDeciderGaugeKeepFirstProjection_ne_zero
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    satDeciderGaugeKeepFirstProjection M n hn2 htb hns ≠
      (0 : SATDeciderGaugeMap M n hn2 htb hns) := by
  intro hzero
  have happ := congrArg
    (fun g : SATDeciderGaugeMap M n hn2 htb hns =>
      g (X (satDeciderGaugeFirstVar M n hn2 htb hns))) hzero
  dsimp at happ
  rw [satDeciderGaugeKeepFirstProjection_apply_firstVar] at happ
  exact (X_ne_zero (satDeciderGaugeFirstVar M n hn2 htb hns)) happ

/-- The keep-first projection is not the identity linear map. -/
theorem satDeciderGaugeKeepFirstProjection_ne_id
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    satDeciderGaugeKeepFirstProjection M n hn2 htb hns ≠
      (LinearMap.id : SATDeciderGaugeMap M n hn2 htb hns) := by
  intro hid
  have happ := congrArg
    (fun g : SATDeciderGaugeMap M n hn2 htb hns =>
      g (X (satDeciderGaugeSecondVar M n hn2 htb hns))) hid
  dsimp at happ
  rw [satDeciderGaugeKeepFirstProjection_apply_secondVar] at happ
  exact (X_ne_zero (satDeciderGaugeSecondVar M n hn2 htb hns)) happ.symm

/-- The keep-first projection is not the existing flat `piPhi` candidate,
because that candidate is definitionally the identity on the flat space. -/
theorem satDeciderGaugeKeepFirstProjection_ne_piPhi
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    satDeciderGaugeKeepFirstProjection M n hn2 htb hns ≠
      satDeciderGaugeMapPiPhi M n hn2 htb hns := by
  intro hpi
  exact satDeciderGaugeKeepFirstProjection_ne_id M n hn2 htb hns
    (by simpa [satDeciderGaugeMapPiPhi_eq_id M n hn2 htb hns] using hpi)

/-- A candidate core: rank monotone, not zero, not identity, not the flat
`piPhi`, and not fixing the real Cook-Levin compiled polynomial. -/
def SATDeciderGaugeCandidateCore
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns) : Prop :=
  SATDeciderGaugeRankMonotonicity M n hn2 htb hns gauge ∧
    gauge ≠ (0 : SATDeciderGaugeMap M n hn2 htb hns) ∧
      gauge ≠ (LinearMap.id : SATDeciderGaugeMap M n hn2 htb hns) ∧
        gauge ≠ satDeciderGaugeMapPiPhi M n hn2 htb hns ∧
          gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≠
            compiledPoly (cook_levin_compilation M n hn2 htb hns)

/-- Polynomial inequality is exactly coefficient inequality. -/
theorem mvPolynomial_ne_iff_exists_coeff_ne
    {N : Nat} {p q : MvPolynomial (Fin N) Rat} :
    p ≠ q ↔ ∃ α, coeff α p ≠ coeff α q := by
  constructor
  · intro hpq
    by_contra hcoeff
    push_neg at hcoeff
    exact hpq (MvPolynomial.ext p q hcoeff)
  · rintro ⟨α, hα⟩ hpq
    exact hα (congrArg (fun r => coeff α r) hpq)

/-- Sharp coefficient form of the candidate-core obligations for any proposed
flat SAT-decider gauge map. -/
theorem satDeciderGaugeCandidateCore_iff_rankMonotone_nontrivial_coeff
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns) :
    SATDeciderGaugeCandidateCore M n hn2 htb hns gauge ↔
      SATDeciderGaugeRankMonotonicity M n hn2 htb hns gauge ∧
        gauge ≠ (0 : SATDeciderGaugeMap M n hn2 htb hns) ∧
          gauge ≠ (LinearMap.id : SATDeciderGaugeMap M n hn2 htb hns) ∧
            gauge ≠ satDeciderGaugeMapPiPhi M n hn2 htb hns ∧
              ∃ α,
                coeff α
                    (gauge
                      (compiledPoly
                        (cook_levin_compilation M n hn2 htb hns))) ≠
                  coeff α
                    (compiledPoly
                      (cook_levin_compilation M n hn2 htb hns)) := by
  unfold SATDeciderGaugeCandidateCore
  rw [mvPolynomial_ne_iff_exists_coeff_ne]

/-- For the concrete keep-first projection, all candidate-core obligations
except moving `compiledPoly` are already discharged.  Thus the remaining
criterion is exactly non-fixing of the real compiled polynomial. -/
theorem satDeciderGaugeKeepFirstProjection_candidateCore_iff_moves_compiledPoly
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeCandidateCore M n hn2 htb hns
        (satDeciderGaugeKeepFirstProjection M n hn2 htb hns) ↔
      satDeciderGaugeKeepFirstProjection M n hn2 htb hns
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≠
        compiledPoly (cook_levin_compilation M n hn2 htb hns) := by
  constructor
  · intro hcore
    exact hcore.2.2.2.2
  · intro hmove
    exact
      ⟨satDeciderGaugeKeepFirstProjection_rankMonotonicity M n hn2 htb hns,
        satDeciderGaugeKeepFirstProjection_ne_zero M n hn2 htb hns,
        satDeciderGaugeKeepFirstProjection_ne_id M n hn2 htb hns,
        satDeciderGaugeKeepFirstProjection_ne_piPhi M n hn2 htb hns,
        hmove⟩

/-- Coefficient criterion specialized to the concrete keep-first projection. -/
theorem satDeciderGaugeKeepFirstProjection_candidateCore_iff_coeff
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeCandidateCore M n hn2 htb hns
        (satDeciderGaugeKeepFirstProjection M n hn2 htb hns) ↔
      ∃ α,
        coeff α
            (satDeciderGaugeKeepFirstProjection M n hn2 htb hns
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≠
          coeff α
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)) := by
  rw [satDeciderGaugeKeepFirstProjection_candidateCore_iff_moves_compiledPoly]
  exact mvPolynomial_ne_iff_exists_coeff_ne

/-! ## Axiom audit anchors -/

#print axioms satDeciderGaugeKeepFirstProjection_spdpSubspaceImageContainment
#print axioms satDeciderGaugeKeepFirstProjection_rankMonotonicity
#print axioms satDeciderGaugeKeepFirstProjection_ne_zero
#print axioms satDeciderGaugeKeepFirstProjection_ne_id
#print axioms satDeciderGaugeKeepFirstProjection_ne_piPhi
#print axioms satDeciderGaugeCandidateCore_iff_rankMonotone_nontrivial_coeff
#print axioms satDeciderGaugeKeepFirstProjection_candidateCore_iff_moves_compiledPoly
#print axioms satDeciderGaugeKeepFirstProjection_candidateCore_iff_coeff

end PallLean.Paper93.DeepMath.PathB
