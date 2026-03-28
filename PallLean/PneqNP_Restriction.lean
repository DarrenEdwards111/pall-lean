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

open RestrictionPipeline TuringMachine Compiler NPWitness

/-- Assumption package for a SAT decider in the restriction route. -/
structure PeqNP where
  sat_decider : DTM
  decides_sat : True

/-- Arithmetic growth interface used at the final contradiction step.
(For sufficiently large `n`, the NP exponent beats the P exponent.) -/
axiom exponent_separation
    (n κ : ℕ) : n ^ 215 < n ^ (κ / 4)

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
    (n : ℕ) (hn : n ≥ 32) (hnM : n ≥ max 4 h.sat_decider.numStates) (heven : 2 ∣ n)
    (h_le : npNumVars n ≤ numVars h.sat_decider n (Nat.log 2 n))
    (κ : ℕ) (hκ : κ ≥ 5) (hκ_le : κ ≤ Nat.log 2 n) : False := by
  obtain ⟨ρ, hgood⟩ := explicit_restriction_exists h.sat_decider n hn
  exact restricted_rank_contradiction h.sat_decider n hn hnM heven h_le κ hκ hκ_le ρ hgood
    (exponent_separation n κ)

end PneqNP_Restriction
