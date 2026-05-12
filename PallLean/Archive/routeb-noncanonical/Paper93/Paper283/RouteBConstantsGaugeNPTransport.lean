import PallLean.Paper93.Paper283.RouteBConstantsGaugeCertificate
import PallLean.Paper93.Paper283.RouteBTransportNPIdentityMinor

/-!
# Route B constants-gauge NP transport

This file specializes the projected NP identity-minor transport field to the
currently selected constants NFrame gauge.  The constants gauge is the
`piStarConcrete` projection to the span of `1`, so at the Cook-Levin
rank-gap derivative order `κ = log₂ n ≥ 1` its projected SPDP rank is zero.

Consequently the Route B projected NP identity-minor lower-bound field for
this selected gauge is not discharged by the constants gauge: it reduces
sharply to the impossible-looking scalar inequality
`Nat.choose (n / 3) (Nat.log 2 n) ≤ 0`.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

private theorem one_le_log_two_of_two_le {n : Nat} (hn2 : n ≥ 2) :
    1 ≤ Nat.log 2 n := by
  exact Nat.le_log_of_pow_le (by norm_num : (1 : Nat) < 2) (by simpa using hn2)

/-- The selected constants Route B gauge is literally the substantive
`piStarConcrete` constants projection on the Cook-Levin ambient polynomial
space. -/
theorem routeBConstantsGauge_asSATGauge_eq_piStarConcrete
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    routeBNFrameCandidateAsSATGauge M n hn2 htb hns
        (routeBConstantsGauge M n hn2 htb hns) =
      PallLean.Paper93.Substantive.piStarConcrete
        (RouteBCookLevinDim M n hn2 htb hns) := by
  unfold routeBNFrameCandidateAsSATGauge routeBConstantsGauge
    routeBConstantsCandidateGauge
  exact PallLean.Paper93.NFrame.nonTrivialGauge_projection_eq_piStarConcrete
    (RouteBCookLevinDim M n hn2 htb hns)

/-- The constants gauge collapses the projected Cook-Levin compiled
polynomial to SPDP rank zero at the Route B identity-minor derivative order.

This is the exact constants-gauge obstruction: unlike a fixed embedded
identity-minor sheet, the constants projection only sees the scalar row. -/
theorem routeBConstantsGauge_projectedCompiled_rank_le_zero
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
            (routeBConstantsGauge M n hn2 htb hns))
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≤ 0 := by
  rw [routeBConstantsGauge_asSATGauge_eq_piStarConcrete]
  exact
    PallLean.Paper93.Substantive.piStar_rank_bounded
      (N := RouteBCookLevinDim M n hn2 htb hns)
      (B := (cook_levin_compilation M n hn2 htb hns).partition)
      (κ := Nat.log 2 n) (ℓ := Nat.log 2 n)
      (p := compiledPoly (cook_levin_compilation M n hn2 htb hns))
      (one_le_log_two_of_two_le hn2)

/-- If the constants gauge satisfied the Route B projected NP identity-minor
lower-bound field, then the binomial lower bound would have to be at most
zero.  This is the reduced blocker for the selected constants NFrame gauge,
with no keepFOB or profile-collapse premise. -/
theorem choose_le_zero_of_routeBConstantsGauge_projectedNPIdentityMinor
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hNP :
      RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBConstantsGauge M n hn2 htb hns))) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤ 0 :=
  le_trans hNP
    (routeBConstantsGauge_projectedCompiled_rank_le_zero
      M n hn2 htb hns)

/-- Equivalently, proving the projected NP identity-minor field for the
selected constants gauge is exactly proving the collapsed binomial inequality
against zero. -/
theorem routeBConstantsGauge_projectedNPIdentityMinor_iff_choose_le_zero
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBConstantsGauge M n hn2 htb hns)) ↔
      Nat.choose (n / 3) (Nat.log 2 n) ≤ 0 := by
  constructor
  · exact choose_le_zero_of_routeBConstantsGauge_projectedNPIdentityMinor
      M n hn2 htb hns
  · intro hzero
    unfold RouteBSATProjectedNPIdentityMinorLowerBound
    exact le_trans hzero (Nat.zero_le _)

/-- At the paper scale, the selected constants NFrame gauge cannot satisfy the
Route B projected NP identity-minor lower-bound field: the constants
projection gives rank zero, while the checked arithmetic gap makes the
binomial lower bound strictly positive. -/
theorem not_routeBConstantsGauge_projectedNPIdentityMinor
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ¬ RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBConstantsGauge M n hn2 htb hns)) := by
  intro hNP
  have hzero :
      Nat.choose (n / 3) (Nat.log 2 n) ≤ 0 :=
    choose_le_zero_of_routeBConstantsGauge_projectedNPIdentityMinor
      M n hn2 htb hns hNP
  have hgap :
      n ^ 200 < Nat.choose (n / 3) (Nat.log 2 n) :=
    PaperFaithfulCompilation.arithmetic_gap_2pow804 n hn
  have hpos :
      0 < Nat.choose (n / 3) (Nat.log 2 n) :=
    lt_of_le_of_lt (Nat.zero_le _) hgap
  exact (not_lt_of_ge hzero) hpos

/-! ## Axiom audit anchors -/

#print axioms routeBConstantsGauge_asSATGauge_eq_piStarConcrete
#print axioms routeBConstantsGauge_projectedCompiled_rank_le_zero
#print axioms choose_le_zero_of_routeBConstantsGauge_projectedNPIdentityMinor
#print axioms routeBConstantsGauge_projectedNPIdentityMinor_iff_choose_le_zero
#print axioms not_routeBConstantsGauge_projectedNPIdentityMinor

end PallLean.Paper93.Paper283
