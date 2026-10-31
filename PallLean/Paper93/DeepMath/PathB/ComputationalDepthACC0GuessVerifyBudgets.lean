import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0GuessVerifyTime

/-!
# Guess-and-verify budgets — the budget closure proved, the two phase machines socketed

The verify phase of guess-and-verify evaluates the circuit's sparse representation: by the composite-BT capstone
(`…ACC0CompositeBTCapstone.compositeBT_representation`) the cube count is a sum over `≤ (n+1)^D` features (`D` the
quasipolynomial degree `δ^{depth+1}`), so **verify time `≤` the feature count** — quasipolynomial, *not* `2^n`.  The
guess phase writes a small circuit code, costing `poly`.  This file proves the **budget closure**: once both phases fit
the feature-count bound and the quasipolynomial feature count fits the faster budget (`2·features ≤ target`), the
guess-and-verify decider accepts within `target`.

## What is proved (clean axioms, no `sorry`)

* **`budget_split`** — `guessT ≤ b → verifyT ≤ b → 2·b ≤ target → guessT + verifyT ≤ target`.
* **`guess_verify_fits`** — the closure: the two physical phases (guess reaches the intermediate config in `≤ b` steps,
  verify accepts in `≤ b` steps) with `2·b ≤ target` give `acceptsWithin M x target`.  Instantiating `b` with the
  composite-BT feature count `(n+1)^{δ^{depth+1}}` makes the budget the quasipolynomial-fits-sub-`2^n` condition.

## Honest scope

The budget arithmetic and the two-phase composition are proved — the verify time is reduced to the feature count
(quasipolynomial) and the closure is complete *given the two phase machines*.  The remaining sockets are exactly those
two physical achievements: that the guess machine reaches the intermediate configuration in `poly` steps, and that the
**verify machine enumerates the `≤ (n+1)^D` features in feature-count steps** — the latter *is* the fast-`ACC⁰`-SAT
algorithm (the sparse read-off realised as an actual machine).  This **does not** prove the verify machine.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0GuessVerifyBudgets

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (NTM reachIn acceptsWithin)
open PallLean.Paper93.DeepMath.PathB.ACC0GuessVerifyTime (acceptsFrom guess_verify_within)

/-- **Budget split (proved): two phases each within `b`, with `2·b ≤ target`, sum within `target`.** -/
theorem budget_split {guessT verifyT b target : ℕ}
    (hg : guessT ≤ b) (hv : verifyT ≤ b) (hcal : 2 * b ≤ target) :
    guessT + verifyT ≤ target := by
  omega

/-- **The guess-and-verify budget closure (proved).**  The guess phase (reaching `mid` in `≤ b` steps) and the verify
phase (accepting in `≤ b` steps), with the quasipolynomial bound fitting the faster budget (`2·b ≤ target`), give
`acceptsWithin M x target`.  Taking `b = (n+1)^{δ^{depth+1}}` (the composite-BT feature count), this is the
quasipolynomial-verify time bound; the two phase machines are the remaining sockets. -/
theorem guess_verify_fits (M : NTM) (x : List Bool) (guessT verifyT b target : ℕ) (mid : M.Config)
    (hguess : reachIn M guessT (M.init x) mid)
    (hverify : acceptsFrom M mid verifyT)
    (hg : guessT ≤ b) (hv : verifyT ≤ b) (hcal : 2 * b ≤ target) :
    acceptsWithin M x target :=
  guess_verify_within M x guessT verifyT target mid hguess hverify
    (budget_split hg hv hcal)

end PallLean.Paper93.DeepMath.PathB.ACC0GuessVerifyBudgets

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0GuessVerifyBudgets.budget_split
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0GuessVerifyBudgets.guess_verify_fits
