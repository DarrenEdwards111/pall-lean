import PallLean.Step4Compiler

/-!
# The P-side within-profile finrank lemma is FALSE at the contradiction scale (audit result)

`CookLevinExactWithinProfileFinrankLemma` (equivalently the frontier
`CookLevinWithinProfileFinrankFrontier`) is the load-bearing P-side rank bound of the SPDP / God-Move
`P ≠ NP` route.  The audit outcome is not "open" but "refuted": at the contradiction scale
`n = 2^804` the lemma is provably FALSE, using the codebase's OWN axiom-clean machinery.

The chain (every step machine-checked, `[propext, Classical.choice, Quot.sound]`):

  • `CookLevinExactWithinProfileFinrankLemma M n hn htb hns` unfolds to
    `WithinProfileFinrankBound … (cookLevinConstraintType M n hn htb hns)`, so it is a WITNESS for the
    existential `CookLevinWithinProfileFinrankFrontier M n hn htb hns`.
  • `Step4Compiler.bounded_params_at_2pow804_absurd` proves `Frontier(M) → False` for every `M` with
    `timeBound ≤ 4`, `numStates ≤ n` at `n ≥ 2^804`, by combining
      – the P-side bridge `p_side_rank_bound_for_cook_levin_of_withinProfileFrontier`
        (`Frontier ⟹ mlBlockedSpdpRank(compiledPoly) ≤ n^200`), and
      – the axiom-clean NP-side `GodMoveReal.compiledPoly_rank_gt_npow200_at_large_n`
        (`mlBlockedSpdpRank(compiledPoly) > n^200`, for EVERY such `M`).
  • Hence the Exact lemma at `2^804` implies `False`.

`cookLevinExactWithinProfile_false_at_2pow804` — **PROVED**: `¬ CookLevinExactWithinProfileFinrankLemma
M (2^804) hn htb hns`.

## What this means for the route

The within-profile bound is not a hard-but-plausible technical lemma awaiting a formalization push:
it is false for the real compiled family (its aggregate `≤ n^200` contradicts the codebase's own
NP-side `> n^200` on the identical `compiledPoly`, same partition, same `κ = ℓ = log₂ n`).  Grinding
the profile-cover formalization would terminate in `False`, not a proof.

Consequently `CookLevinFrontierHyp = ∀ h : PeqNP_Paper, Frontier(h.decider)` is true only VACUOUSLY —
i.e. iff there is no `PeqNP_Paper` witness — so `CookLevinFrontierHyp ⟺ ¬PeqNP_Paper`, and the
conditional theorem `CookLevinFrontierHyp ⟹ ¬PeqNP_Paper` is circular (hypothesis equivalent to
conclusion).  The genuine open content is elsewhere: the NP-side lower bound holds for EVERY DTM, so
the blocked SPDP rank does not distinguish P from NP — a separating (non-uniform-across-machines)
measure is what is missing.

This file is a NEGATIVE result: it refutes a P-side stub.  It is not a proof of `P ≠ NP`, nor of any
separation — it removes a false target.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.CookLevinFrontierRefutation

open TuringMachine

/-- **REFUTATION (proved)**: the P-side within-profile finrank lemma is FALSE at the contradiction
scale `n = 2^804`.  It implies the frontier, which `bounded_params_at_2pow804_absurd` sends to
`False` via the P-side bridge and the axiom-clean NP-side lower bound. -/
theorem cookLevinExactWithinProfile_false_at_2pow804
    (M : DTM) (hn2 : (2 : ℕ) ^ 804 ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    ¬ WithinProfileBound.CookLevinExactWithinProfileFinrankLemma M (2 ^ 804) hn2 htb hns := by
  intro hexact
  refine Step4Compiler.bounded_params_at_2pow804_absurd M (2 ^ 804) (le_refl _) htb hns hn2 ?_
  exact ⟨WithinProfileBound.cookLevinConstraintType M (2 ^ 804) hn2 htb hns, hexact⟩

end PallLean.CookLevinFrontierRefutation

#print axioms PallLean.CookLevinFrontierRefutation.cookLevinExactWithinProfile_false_at_2pow804
