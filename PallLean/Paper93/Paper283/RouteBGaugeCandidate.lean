import PallLean.Paper93.Paper283.RouteBToSATGaugeBridge
import PallLean.Paper93.NFrame.NonTrivialGaugeHypotheses
import PallLean.Paper93.NFrame.UnitPreservingAdmissible

/-!
# Route B candidate-gauge construction

This file owns only the NFrame-side candidate construction at the exact
Cook-Levin dimension.  It deliberately does not use the Route A/profile or
`keepFOB` surface as a source of truth.

The strongest existing unconditional NFrame candidate is the constants
projection `Substantive.nonTrivialGauge`: it is finite-rank, idempotent,
admissible, nonzero, and fixes the constant polynomial `1`.  The remaining
Route B content is not the existence of an NFrame `CandidateGauge`, but the
nontrivial SAT/SPDP functoriality fields packaged as `RouteBNFrameGaugeSubgoals`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open TuringMachine

/-- The existing constants-projection NFrame candidate, specialized to the
Route B Cook-Levin ambient dimension. -/
noncomputable def routeBConstantsCandidateGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns) :=
  PallLean.Paper93.Substantive.nonTrivialGauge
    (RouteBCookLevinDim M n hn2 htb hns)

/-- The Route B constants candidate is admissible in the current NFrame API. -/
theorem routeBConstantsCandidateGauge_admissible
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    PallLean.Paper93.NFrame.AdmissibleGauge
      (routeBConstantsCandidateGauge M n hn2 htb hns) := by
  unfold routeBConstantsCandidateGauge
  exact PallLean.Paper93.NFrame.nonTrivialGauge_admissible
    (RouteBCookLevinDim M n hn2 htb hns)

/-- The Route B constants candidate fixes the constant row `1`, the existing
unit-preserving strengthening of NFrame admissibility. -/
theorem routeBConstantsCandidateGauge_projection_one
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    (routeBConstantsCandidateGauge M n hn2 htb hns).projection
        (1 : MvPolynomial
          (Fin (RouteBCookLevinDim M n hn2 htb hns)) ℚ) =
      1 := by
  unfold routeBConstantsCandidateGauge
  exact PallLean.Paper93.NFrame.nonTrivialGauge_projection_one
    (RouteBCookLevinDim M n hn2 htb hns)

/-- The Route B constants candidate is unit-preserving admissible, hence it is
not the zero projection. -/
theorem routeBConstantsCandidateGauge_unitPreserving
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    PallLean.Paper93.NFrame.UnitPreservingAdmissibleGauge
      (routeBConstantsCandidateGauge M n hn2 htb hns) := by
  unfold routeBConstantsCandidateGauge
  exact PallLean.Paper93.NFrame.nonTrivialGauge_unitPreserving
    (RouteBCookLevinDim M n hn2 htb hns)

/-- The specialized Route B candidate has a nonzero projection. -/
theorem routeBConstantsCandidateGauge_projection_ne_zero
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    (routeBConstantsCandidateGauge M n hn2 htb hns).projection ≠ 0 :=
  PallLean.Paper93.NFrame.unitPreserving_projection_ne_zero
    (routeBConstantsCandidateGauge_unitPreserving M n hn2 htb hns)

/-- The honest remaining nontrivial Route B obligations for this candidate:
the constants projection must satisfy the SAT/SPDP rank, P-side, and NP-side
fields consumed downstream. -/
def RouteBConstantsCandidateRemainingObligations
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  RouteBNFrameGaugeSubgoals M n hn2 htb hns
    (routeBConstantsCandidateGauge M n hn2 htb hns)

/-- If the named nontrivial SAT/SPDP obligations are supplied, the constants
candidate gives the existing Route B NFrame gauge package. -/
theorem routeBNFrameGaugePackage_of_constantsCandidate_obligations
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hobligations :
      RouteBConstantsCandidateRemainingObligations M n hn2 htb hns) :
    RouteBNFrameGaugePackage M n hn2 htb hns := by
  exact ⟨routeBConstantsCandidateGauge M n hn2 htb hns,
    routeBConstantsCandidateGauge_admissible M n hn2 htb hns,
    hobligations⟩

/-- Unconditional package recording exactly what is constructed here, without
claiming the downstream SAT/SPDP fields. -/
def RouteBConstructedCandidatePackage
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns),
    PallLean.Paper93.NFrame.AdmissibleGauge Pi ∧
      PallLean.Paper93.NFrame.UnitPreservingAdmissibleGauge Pi ∧
        Pi.projection ≠ 0

/-- The Route B constants candidate is an unconditional nonzero,
unit-preserving admissible NFrame candidate at the Cook-Levin dimension. -/
theorem routeBConstructedCandidatePackage_constants
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBConstructedCandidatePackage M n hn2 htb hns := by
  exact ⟨routeBConstantsCandidateGauge M n hn2 htb hns,
    routeBConstantsCandidateGauge_admissible M n hn2 htb hns,
    routeBConstantsCandidateGauge_unitPreserving M n hn2 htb hns,
    routeBConstantsCandidateGauge_projection_ne_zero M n hn2 htb hns⟩

end PallLean.Paper93.Paper283
