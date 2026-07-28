import PallLean.Step4Compiler

/-!
# `bounded_params_at_2pow804_absurd` hides no false hypothesis — it fires on a concrete real machine

`bounded_params_at_2pow804_absurd` proves `CookLevinWithinProfileFinrankFrontier M n … → False` for a bounded
machine, and the SAT-decider "gauge proofs" invoke it via `False.elim`.  The worry: is that refutation
legitimate, or does it hide a false hypothesis — i.e. is one of its *non-frontier* hypotheses (`n ≥ 2^804`,
`timeBound ≤ 4`, `numStates ≤ n`, `n ≥ 2`) already unsatisfiable, so that it refutes a vacuous conjunction and
says nothing about the P-side?

Reading rules out the other forms:
* It is kernel-clean (`[propext, Classical.choice, Quot.sound]`), so it uses no false custom axiom.
* `CookLevinWithinProfileFinrankFrontier` is a genuine P-side statement — `∃ constraintType,
  WithinProfileFinrankBound …` — not a definitional falsehood, so refuting it is not a strawman.
* Its two lemmas bound the *same* `mlBlockedSpdpRank`, with the NP-side (`compiledPoly_rank_gt_npow200_at_large_n`)
  carrying no frontier hypothesis.

The remaining form — vacuity of the parameter hypotheses — is settled here by *firing the absurdity on a
concrete machine* with every non-frontier hypothesis discharged by a real proof (not assumed).  The witness is
`Step4Compiler.rejectAllDTM` (`numStates = 3`, `timeBound = 1`), a genuine `DTM`.

**`frontier_false_on_concrete_machine`** applies `bounded_params_at_2pow804_absurd` to `rejectAllDTM` at
`n = 2^804`, with `htb`, `hns`, `hn2`, `hn` all supplied as proved facts (`rejectAllDTM_timeBound_le`,
`rejectAllDTM_numStates_le`, `two_le_2pow804`).  It concludes `CookLevinWithinProfileFinrankFrontier
rejectAllDTM (2^804) … → False`.  Because every parameter hypothesis is genuinely satisfied by a real machine,
the contradiction comes from the frontier alone — the refutation is non-vacuous and hides no false hypothesis.

## What is proved

* **`rejectAllDTM_timeBound_le`** — `rejectAllDTM.timeBound ≤ 4` (it is `1`).
* **`rejectAllDTM_numStates_le`** — `rejectAllDTM.numStates ≤ 2^804` (it is `3`).
* **`two_le_2pow804`** — `2 ≤ 2^804`.
* **`frontier_false_on_concrete_machine`** — the frontier for `rejectAllDTM` at `2^804` entails `False`, with
  all parameter hypotheses discharged: the absurdity fires on a real machine.

## Honest verdict — the refutation is legitimate and non-vacuous

`bounded_params_at_2pow804_absurd` does not hide a false hypothesis.  It is kernel-clean (no false axiom); the
frontier it refutes is a real P-side rank claim, not a strawman; its NP-side lemma is unconditional; and its
parameter hypotheses are jointly satisfiable by a concrete `DTM` (`rejectAllDTM`), on which the absurdity
provably fires (`frontier_false_on_concrete_machine`).  So the frontier is genuinely false for a real bounded
machine, the contradiction arises from the frontier alone, and the downstream `False.elim` gauge "proofs" are
therefore vacuous *because the frontier is really false* — not because of a smuggled contradiction elsewhere.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.FrontierRefutationNonVacuous

/-- `rejectAllDTM.timeBound = 1 ≤ 4`. -/
theorem rejectAllDTM_timeBound_le : Step4Compiler.rejectAllDTM.timeBound ≤ 4 := by decide

/-- `2 ≤ 2^804`. -/
theorem two_le_2pow804 : (2 : ℕ) ≤ 2 ^ 804 := by
  calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by norm_num) (by norm_num)

/-- `rejectAllDTM.numStates = 3 ≤ 2^804`. -/
theorem rejectAllDTM_numStates_le : Step4Compiler.rejectAllDTM.numStates ≤ 2 ^ 804 := by
  have h : (4 : ℕ) ≤ 2 ^ 804 := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  show (3 : ℕ) ≤ 2 ^ 804
  omega

/-- **The absurdity fires on a concrete real machine (proved).**  For `rejectAllDTM` at `n = 2^804`, with every
parameter hypothesis discharged by a real proof, the within-profile frontier entails `False`.  So the
refutation of the P-side frontier is non-vacuous — the contradiction comes from the frontier alone, not from a
hidden-false parameter hypothesis. -/
theorem frontier_false_on_concrete_machine
    (hfront : WithinProfileBound.CookLevinWithinProfileFinrankFrontier
        Step4Compiler.rejectAllDTM (2 ^ 804)
        two_le_2pow804 rejectAllDTM_timeBound_le rejectAllDTM_numStates_le) :
    False :=
  Step4Compiler.bounded_params_at_2pow804_absurd
    Step4Compiler.rejectAllDTM (2 ^ 804) (le_refl _)
    rejectAllDTM_timeBound_le rejectAllDTM_numStates_le two_le_2pow804 hfront

end PallLean.FrontierRefutationNonVacuous

#print axioms PallLean.FrontierRefutationNonVacuous.rejectAllDTM_timeBound_le
#print axioms PallLean.FrontierRefutationNonVacuous.rejectAllDTM_numStates_le
#print axioms PallLean.FrontierRefutationNonVacuous.frontier_false_on_concrete_machine
