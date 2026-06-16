import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NTM

/-!
# Guess-and-verify, the time bound — two-phase time composition proved, phase budgets socketed

The remaining socket of guess-and-verify (`…ACC0GuessVerify`) was the *complexity* bound: the guess-and-verify decider
lies in `NTIME[2ⁿ/superpoly]`.  Its structure is **two phases** — guess a small circuit code, then verify it via the
`ACC⁰`-SAT speedup — and the time is **additive**: `guessTime + verifyTime`.  This file proves the time-budget
composition: a machine that reaches an intermediate configuration in `guessT` steps and then accepts within `verifyT`
steps accepts within `guessT + verifyT`, hence within any larger budget.  That reduces the complexity socket to the two
*phase* budgets (guess `poly`, verify `2ⁿ/superpoly`) plus a budget calibration — the composition itself is proved.

## What is proved (clean axioms, no `sorry`)

* **`acceptsFrom`** — acceptance from an arbitrary start configuration within a step budget.
* **`acceptsWithin_compose`** — two-phase composition: `reachIn M guessT (init x) mid` and `acceptsFrom M mid verifyT`
  give `acceptsWithin M x (guessT + verifyT)` (via `reachIn_add`).
* **`guess_verify_within`** — with `guessT + verifyT ≤ target`, the decider accepts within `target`: the guess-and-verify
  time bound, given the two phase budgets.

## Honest scope

The two-phase **time composition** (`guess + verify`, additive) and the budget-monotonicity are proved — the genuine
quantitative content reducing `gvDecider ∈ NTIME2nFast` to its two phase budgets.  The remaining sockets are the phase
budgets themselves: that guessing a *small* circuit reaches the intermediate configuration in `poly` steps, and that
verification via the `ACC⁰`-SAT speedup accepts within `2ⁿ/superpoly` steps (the latter is the actual fast-SAT content,
needing the read-off + the physical machine).  This **does not** prove the complexity bound outright.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0GuessVerifyTime

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (NTM reachIn acceptsWithin reachIn_add acceptsWithin_mono)

/-- **Acceptance from an arbitrary start configuration within a step budget.**  `acceptsWithin M x t` is
`acceptsFrom M (M.init x) t`. -/
def acceptsFrom (M : NTM) (start : M.Config) (t : ℕ) : Prop :=
  ∃ k ≤ t, ∃ c, reachIn M k start c ∧ M.accept c

/-- **Two-phase time composition (proved): `guessT` to reach `mid`, then accept within `verifyT`, accepts within
`guessT + verifyT`.**  The guess and verify phases compose additively in time (via `reachIn_add`). -/
theorem acceptsWithin_compose (M : NTM) (x : List Bool) (guessT verifyT : ℕ) (mid : M.Config)
    (hguess : reachIn M guessT (M.init x) mid)
    (hverify : acceptsFrom M mid verifyT) :
    acceptsWithin M x (guessT + verifyT) := by
  obtain ⟨k, hk, c, hr, ha⟩ := hverify
  exact ⟨guessT + k, by omega, c,
    (reachIn_add M guessT k (M.init x) c).mpr ⟨mid, hguess, hr⟩, ha⟩

/-- **The guess-and-verify time bound (proved).**  Guess phase (`guessT` to reach `mid`) plus verify phase (accept
within `verifyT`), with `guessT + verifyT ≤ target`, gives acceptance within `target` — so the guess-and-verify decider
fits the `NTIME[2ⁿ/superpoly]` budget once the two phase budgets do. -/
theorem guess_verify_within (M : NTM) (x : List Bool) (guessT verifyT target : ℕ) (mid : M.Config)
    (hguess : reachIn M guessT (M.init x) mid)
    (hverify : acceptsFrom M mid verifyT)
    (hbudget : guessT + verifyT ≤ target) :
    acceptsWithin M x target :=
  acceptsWithin_mono M x hbudget (acceptsWithin_compose M x guessT verifyT mid hguess hverify)

end PallLean.Paper93.DeepMath.PathB.ACC0GuessVerifyTime

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0GuessVerifyTime.acceptsWithin_compose
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0GuessVerifyTime.guess_verify_within
