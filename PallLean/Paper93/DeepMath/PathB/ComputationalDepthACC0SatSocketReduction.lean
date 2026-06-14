import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameACC0Master

/-!
# Attacking the master socket from `exists_low_survival`

The master bridge (`…NFrameACC0Master`) left one socket: `NFrameGivesACC0SatSpeedupSocket supports` — a restriction
leaving few surviving gates (`∃ L, (n+1)^{survivingCount} < 2^n`).  This file **discharges it from the probabilistic
existence theorem** `exists_low_survival`, reducing it to a single clean expectation hypothesis.

The argument: by `exists_low_survival`, if the *expected* surviving‑gate count is `≤ r` then some restriction `L`
has `survivingCount L < r + 1`, i.e. `≤ r`; and `(n+1)^{survivingCount L} ≤ (n+1)^r < 2^n` when `(n+1)^r < 2^n`.  So
**expected survivors `≤ r` (with `(n+1)^r < 2^n`) ⇒ the socket**, hence the master speedup.

## What is proved (clean axioms, no `sorry`)

* `socket_of_expectation` — **the reduction**: `Exp p (survivingCount) ≤ r` and `(n+1)^r < 2^n` ⇒
  `NFrameGivesACC0SatSpeedupSocket supports`.
* `speedup_of_expectation` — chaining to the master: the same hypotheses give a restriction whose cell search beats
  brute force.

## Honest scope

This reduces the master socket to a single standard quantity — the **measure expectation of the surviving‑gate
count**, `Exp p (survivingCount) ≤ r`.  By the first moment (`survProb_le`, Bernoulli) this expectation is
`≤ k·s·p`, so the remaining piece is the routine identification `Exp p (survivingCount) = ∑_j Pr(S_j survives)`
(linearity of the discrete expectation over the support indicators) together with `Pr(S_j killed) = (1-p)^{|S_j|}`
(the per‑support marginal).  Those are standard probabilistic facts about the `p`‑biased measure — the only
remaining input.  Still the cell‑search cost model; proves nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SatSocketReduction

open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingChebyshev
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline
open PallLean.Paper93.DeepMath.PathB.ACC0SatRestrictionActive
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Master

variable {n k : ℕ}

/-- **The socket from the expectation bound (proved).**  If the expected surviving‑gate count is `≤ r` and
`(n+1)^r < 2^n`, then a restriction leaving few surviving gates exists — the master socket. -/
theorem socket_of_expectation (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (supports : Fin k → Finset (Fin n))
    (r : ℕ) (hreg : (n + 1) ^ r < 2 ^ n)
    (hE : Exp p (fun L => (survivingCount supports L : ℝ)) ≤ (r : ℝ)) :
    NFrameGivesACC0SatSpeedupSocket supports := by
  obtain ⟨L, _, hLsurv⟩ :=
    exists_low_survival p hp0 hp1 supports (r : ℝ) ((r : ℝ) + 1) (by positivity) hE (by linarith)
  refine ⟨L, ?_⟩
  have hle : survivingCount supports L ≤ r := by
    have h1 : (survivingCount supports L : ℝ) < ((r + 1 : ℕ) : ℝ) := by push_cast; linarith
    have h2 : survivingCount supports L < r + 1 := by exact_mod_cast h1
    omega
  calc (n + 1) ^ survivingCount supports L
      ≤ (n + 1) ^ r := Nat.pow_le_pow_right (by omega) hle
    _ < 2 ^ n := hreg

/-- **The speedup from the expectation bound (proved): chaining the socket to the master.**  Expected survivors
`≤ r` with `(n+1)^r < 2^n` gives a restriction whose cell search beats brute force. -/
theorem speedup_of_expectation (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (supports : Fin k → Finset (Fin n))
    (r : ℕ) (hreg : (n + 1) ^ r < 2 ^ n)
    (hE : Exp p (fun L => (survivingCount supports L : ℝ)) ≤ (r : ℝ)) :
    ∃ L : Finset (Fin n),
      (Finset.univ.image (weightVec (fun j => supports j ∩ L))).card < 2 ^ n :=
  speedup_of_socket supports (socket_of_expectation p hp0 hp1 supports r hreg hE)

end PallLean.Paper93.DeepMath.PathB.ACC0SatSocketReduction

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatSocketReduction.socket_of_expectation
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatSocketReduction.speedup_of_expectation
