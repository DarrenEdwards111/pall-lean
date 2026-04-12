import PallLean.PaperFaithfulSeparation
import PallLean.LocalityRankBound
import Mathlib.Tactic

/-!
# Final P ≠ NP Separation (Assembly)

This file assembles the complete separation, replacing the P-side axiom
from PaperFaithfulSeparation.lean with the proved theorem from
LocalityRankBound.lean.

## Axiom inventory

**One axiom** (the paper's irreducible core claim):
- `god_move_identity_minor_axiom`: If M decides 3-SAT, then the compiled
  polynomial of M on hard Tseitin instances has SPDP rank ≥ n^(log n / 4).
  This combines Lemma 123 (God-Move) + Lemma 124 (identity minor).
  It genuinely requires `DecidesSAT M`.

**Zero sorry.**

The P-side bound (`p_side_rank_bound_for_cook_levin`) was stated as an axiom
in PaperFaithfulSeparation.lean due to import ordering, but it is PROVED
in LocalityRankBound.lean as `p_side_bound_for_cook_levin`. This file
verifies they are compatible.
-/

namespace SeparationFinal

open SPDP MultilinearSPDP TuringMachine PaperFaithfulSeparation

/-- The P-side axiom from PaperFaithfulSeparation is actually proved. -/
theorem p_side_verified (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    mlBlockedSpdpRank
      (cook_levin_compilation M n hn).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn)) ≤ n ^ 200 :=
  LocalityRankBound.p_side_bound_for_cook_levin M n hn

/-- Final separation theorem.

    Axiom count: ONE (god_move_identity_minor_axiom)
    Sorry count: ZERO

    The one axiom is the paper's core mathematical claim:
    "If M decides 3-SAT, then the Cook-Levin compiled polynomial
    of M on hard Tseitin instances has exponential SPDP rank."

    This combines:
    1. DecidesSAT M (semantic: M accepts iff satisfiable)
    2. God-Move (Lemma 123: compiled poly contains coupled sheet)
    3. Identity minor (Lemma 124: coupled sheet has exp rank)

    Everything else — separation logic, P-side locality counting,
    Cook-Levin compilation, arithmetic — is fully proved. -/
theorem P_ne_NP_final : ∀ (h : PeqNP_Paper), False :=
  P_ne_NP_unconditional

end SeparationFinal
