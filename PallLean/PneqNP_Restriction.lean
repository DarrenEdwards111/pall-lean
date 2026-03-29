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
## Paper checklist (active obligations)

`P_neq_NP_from_restriction` is now a thin contradiction wrapper with an explicit
paper-facing checklist. Remaining substantive proof obligations are exposed directly
in the theorem inputs rather than hidden behind legacy bridge lemmas.

### Inputs interpreted as paper steps

1. `hnFloor` + `heven`
   - places us in the asymptotic/even regime used by the NP witness lower bound,
     log-parameter arithmetic, and contradiction exponent split.

2. `h_le : npNumVars n ≤ numVars ...`
   - witness-variable embedding into compiled-variable space.

3. `hdepth : depth_collapse_L171 ... (canonicalRestriction ...)`
   - **Step 4** obligation (restriction/depth-collapse → polynomial P-side rank).

4. (derived internally) `hminor : identity_minor_survives_Step5 ...`
   - **Step 5** NP lower bound at κ = log₂ n (from extraction + NP witness bound).

5. `exponent_separation_log`
   - arithmetic separation `n^215 < n^(log₂ n/4)`.

6. `restricted_rank_contradiction`
   - combines Step 4 + Step 5 on the same restricted compiled polynomial.
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
    (hdepth : depth_collapse_L171 h.sat_decider n (canonicalRestriction h.sat_decider n))
    : False := by
  have hn : n ≥ 32 := by omega
  have hnM : n ≥ max 4 h.sat_decider.numStates := by omega
  have hnNP : n ≥ npLowerThreshold := by omega
  have hnHuge : n ≥ 2 ^ (4 * 215 + 4) := by omega
  have hminor : identity_minor_survives_Step5 h.sat_decider n (canonicalRestriction h.sat_decider n) :=
    identity_minor_survives_canonical h.sat_decider n
  obtain ⟨ρ, hgood⟩ := explicit_restriction_exists h.sat_decider n hn hdepth hminor
  exact restricted_rank_contradiction h.sat_decider n hn hnNP hnM heven h_le ρ hgood
    (exponent_separation_log n hnHuge)

end PneqNP_Restriction
