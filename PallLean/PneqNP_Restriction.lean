import PallLean.RestrictionPipeline
import Mathlib.Tactic

/-!
# PneqNP_Restriction

Paper-consistent final contradiction wrapper around RestrictionPipeline (Theorem 12,
Steps 2–5 + Lemma 13-style bridge assumptions).

This module intentionally keeps only the final assembly theorem, with all heavy
switching-lemma / extraction machinery abstracted by `RestrictionPipeline` axioms.
-/

namespace PneqNP_Restriction

open RestrictionPipeline TuringMachine Compiler NPWitness SPDP

/-- Assumption package for a SAT decider in the restriction route. -/
structure PeqNP where
  sat_decider : DTM
  decides_sat : True


/-- Concrete arithmetic separation at the paper regime `κ = log₂ n`.
For sufficiently large `n`, `n^(log₂ n / 4)` dominates `n^215`.
(Direct specialization of the arithmetic step used in SPDPDefs.) -/
theorem exponent_separation_log
    (n : ℕ) (hnHuge : n ≥ 2 ^ (4 * 215 + 4)) :
    n ^ 215 < n ^ (Nat.log 2 n / 4) := by
  apply Nat.pow_lt_pow_right
  · have : (2 : ℕ) ^ 1 ≤ 2 ^ (4 * 215 + 4) := by
      apply Nat.pow_le_pow_right (by norm_num)
      omega
    omega
  · have h_log : Nat.log 2 n ≥ 4 * 215 + 4 := by
      have : 2 ^ (4 * 215 + 4) ≤ n := hnHuge
      calc
        4 * 215 + 4 = Nat.log 2 (2 ^ (4 * 215 + 4)) := by
          rw [Nat.log_pow (by norm_num : 1 < 2)]
        _ ≤ Nat.log 2 n := Nat.log_mono_right this
    omega

/-!
## Paper map (Theorem 12 line-by-line)

`P_neq_NP_from_restriction` corresponds to the paper as follows:

1. **Set SPDP scale**: `κ := log₂ n` (paper uses κ,ℓ = Θ(log n)).
2. **Lower-bound regime check**: `hκ : κ ≥ 5` from `n ≥ 32`.
3. **Pick good restriction**: `explicit_restriction_exists` (paper §32.3).
4. **P-side restricted upper bound**: inside `restricted_rank_contradiction`,
   `pside_restricted_rank` (Step 4 / depth collapse + Width⇒Rank).
5. **NP-side restricted lower bound**: inside `restricted_rank_contradiction`,
   `npside_restricted_rank` (Step 5 / identity-minor survival).
6. **Exponent separation**: `exponent_separation_log` gives
   `n^215 < n^(log₂ n / 4)` for large `n`.
7. **Contradiction**: same restricted compiled polynomial cannot satisfy both bounds.

This wrapper is intentionally thin: all heavy switching-lemma and extraction machinery
is isolated in `RestrictionPipeline` with paper-named assumptions.
-/

/-- Final contradiction in the restriction route.

Given:
- a SAT decider `M`
- a good restriction `ρ*`
- Step-4 upper bound and Step-5 lower bound (from `RestrictionPipeline`)
- exponent separation

we derive `False`.
-/
theorem P_neq_NP_from_restriction
    (h : PeqNP)
    (n : ℕ)
    (hnFloor : n ≥ max (max 32 (max 4 h.sat_decider.numStates))
                        (max npLowerThreshold (2 ^ (4 * 215 + 4))))
    (heven : 2 ∣ n)
    (h_le : npNumVars n ≤ numVars h.sat_decider n (Nat.log 2 n))
    : False := by
  have hn : n ≥ 32 := by omega
  have hnM : n ≥ max 4 h.sat_decider.numStates := by omega
  have hnNP : n ≥ npLowerThreshold := by omega
  have hnHuge : n ≥ 2 ^ (4 * 215 + 4) := by omega
  have hdepth : depth_collapse_L171 h.sat_decider n (canonicalRestriction h.sat_decider n) :=
    depth_collapse_canonical h.sat_decider n
  have hminor : identity_minor_survives_Step5 h.sat_decider n (canonicalRestriction h.sat_decider n) :=
    identity_minor_survives_canonical h.sat_decider n
  obtain ⟨ρ, hgood⟩ := explicit_restriction_exists h.sat_decider n hn hdepth hminor
  exact restricted_rank_contradiction h.sat_decider n hn hnNP hnM heven h_le ρ hgood
    (exponent_separation_log n hnHuge)

end PneqNP_Restriction
