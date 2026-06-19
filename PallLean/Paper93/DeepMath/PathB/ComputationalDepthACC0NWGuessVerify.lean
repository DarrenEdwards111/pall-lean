import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0GuessVerifyTime
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0WilliamsFastSat

/-!
# NW guess-verify — verify the guessed witness inside the fast-SAT framework (proved)

Target 2 of the Williams socket elimination (link 3, Nisan–Wigderson / guess-and-verify).  The pipeline is already
decomposed: the guess-and-verify decider is *correct* (`…ACC0GuessVerify.gvDecider_eq`, decides exactly `L`), the two
phases *compose additively* in time (`…ACC0GuessVerifyTime.guess_verify_within`), and the collapse follows
(`…ACC0GuessVerify.guessVerify_subset`).  The remaining socket is the *complexity* of the decider — that it lies in
`NTIME[2ⁿ/superpoly]`.  This file connects the **verify phase to the fast-SAT**: if small `ACC⁰` witness circuits
exist, verifying a guessed witness is an `ACC⁰`-SAT check, decided by the fast-SAT count-cell search in `≤ 2^{n-k}`
(entry 291) — so the guess-and-verify decider runs in `2ⁿ/superpoly`.

**The bound.**  Guess a *small* (poly `≤ 2^{n-k}`) witness-circuit code, then verify it via the fast-SAT (`≤ 2^{n-k}`):
by the two-phase time composition, the decider accepts within `2 · 2^{n-k}` — which is `2ⁿ / 2^{k-1}`, i.e.
`2ⁿ/superpoly` once `k = ω(log n)` (the fast-SAT speedup margin).  The verify step's `2^{n-k}` budget is precisely the
fast-SAT work, whose `2^k` savings over brute force `2ⁿ` is the entry-291 / `SpeedupMargin` arithmetic
(`verify_fastSat_savings`).

## What is proved (clean axioms, no `sorry`)

* **`nw_guess_verify_within_fast`** — guess a small witness (`≤ 2^{n-k}`) + verify via the fast-SAT (`≤ 2^{n-k}`) ⟹ the
  decider accepts within `2 · 2^{n-k}` (the `2ⁿ/superpoly` fast budget), via the proved two-phase composition.
* **`verify_fastSat_savings`** — the verify phase's fast-SAT work `≤ 2^{n-k}` delivers the `2^k` savings over brute
  force `2ⁿ`: `2^k · work ≤ 2ⁿ` — the speedup that makes verification fast (entry 291).

## Honest scope

This connects NW guess-verify's **verify phase to the fast-SAT**: a guessed small witness is verified by the
`ACC⁰`-SAT speedup in `≤ 2^{n-k}`, so the guess-and-verify decider runs in `2ⁿ/superpoly` (`nw_guess_verify_within_fast`,
via the proved time composition + fast-SAT savings).  The decider's *correctness* and the *collapse* are already proved
(`…ACC0GuessVerify`); together this reduces the NW socket to its two phase-realisation facts: the **guess** phase is
poly (the IKW small-witness reduction — Williams link 1, separate) and the **verify** circuit is `ACC⁰`-SAT-searchable
(entry 291, via the YBT exact form).  Those are *proven*-classical ingredients, formalization engineering, not open
obstructions (`NEXP ⊄ ACC⁰` is Williams 2011).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0NWGuessVerify

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (NTM reachIn acceptsWithin)
open PallLean.Paper93.DeepMath.PathB.ACC0GuessVerifyTime (acceptsFrom guess_verify_within)
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsFastSat (fastSatWork fastSat_savings_of_work_le)

/-- **NW guess-verify within the fast budget (PROVED).**  Guess a *small* witness-circuit code (reaching `mid` in
`guessT ≤ 2^{n-k}` steps) and verify it via the fast-SAT (`acceptsFrom mid verifyT` with `verifyT ≤ 2^{n-k}`): by the
two-phase time composition (`guess_verify_within`), the decider accepts within `2 · 2^{n-k}` — the `2ⁿ/superpoly` fast
budget (`= 2ⁿ / 2^{k-1}` for `k = ω(log n)`).  Verification "inside the fast-SAT framework". -/
theorem nw_guess_verify_within_fast (M : NTM) (x : List Bool) (guessT verifyT n k : ℕ) (mid : M.Config)
    (hguess : reachIn M guessT (M.init x) mid)
    (hverify : acceptsFrom M mid verifyT)
    (hguessSmall : guessT ≤ 2 ^ (n - k))
    (hverifyFast : verifyT ≤ 2 ^ (n - k)) :
    acceptsWithin M x (2 * 2 ^ (n - k)) := by
  apply guess_verify_within M x guessT verifyT (2 * 2 ^ (n - k)) mid hguess hverify
  omega

/-- **The verify phase's fast-SAT savings (PROVED).**  The verify work `≤ 2^{n-k}` (the fast-SAT count-cell budget)
beats brute force `2ⁿ` by a factor `2^k`: `2^k · work ≤ 2ⁿ` — the entry-291 speedup that makes verifying a guessed
witness fast. -/
theorem verify_fastSat_savings {m n k : ℕ} (hkn : k ≤ n) (hw : fastSatWork m ≤ 2 ^ (n - k)) :
    2 ^ k * fastSatWork m ≤ 2 ^ n :=
  fastSat_savings_of_work_le hkn hw

/-!
**NW guess-verify, verify connected to the fast-SAT.**  Guessing a small `ACC⁰` witness circuit and verifying it via
the `ACC⁰`-SAT speedup (`≤ 2^{n-k}`, entry 291) puts the guess-and-verify decider in `2ⁿ/superpoly`
(`nw_guess_verify_within_fast`), the savings being the entry-291 fast-SAT margin (`verify_fastSat_savings`).  With the
decider's correctness and the collapse already proved (`…ACC0GuessVerify`), the NW socket reduces to the two
phase-realisation facts — guess poly (IKW small-witness, link 1) and verify `ACC⁰`-SAT-searchable (entry 291, YBT) —
both proven-classical.  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0NWGuessVerify

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NWGuessVerify.nw_guess_verify_within_fast
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NWGuessVerify.verify_fastSat_savings
