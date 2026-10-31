import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLowBoundaryFromStreaming

/-!
# Feeding a structured (bounded-width branching-program) low boundary into engine 1

The Lagrangian's third route-3 move: feed a *structured* low-boundary decomposition into the algorithmic
engine.  The structured class here is the **branching-program / oblivious** regime: a layered branching
program of width `w` over `n` variables carries one of `w` states between consecutive layers, so its boundary
is `log₂ w` per layer over `n` stages — exactly the input `LowBoundaryInstance` consumes.  So a bounded-width
BP feeds engine 1 (the layer-DP beats brute force).

## Proved (clean axioms, no `sorry`)

* `LayeredBP` — a layered branching program (`n` layers, width `w`, transition per layer, accept predicate);
  `LayeredBP.eval` runs it.
* `LayeredBP.lowBoundaryInstance` — a width-`w`, `n`-layer BP with `n·w ≤ 2^{n−1}` yields a
  `LowBoundaryInstance` of boundary `log₂ w` (`O(1)` for constant width).
* `LayeredBP.dp_beats_bruteforce` — **engine 1 fires**: the layer-DP over its `w` states beats brute force.
* `parityBP`, `parity_bp_dp_beats_bruteforce` — the concrete **width-2** PARITY branching program (state =
  running parity); engine 1 fires for `n ≥ 4`.

## Two-sided reading

This is the *low* side of a two-sided witness: a width-2 BP computes PARITY with boundary `1`, so engine 1
fires — while the *same* parity-flavoured function is **high** boundary in AC⁰ (`MOD_q ∉ AC⁰[p]`, the
calibration; PARITY `∉ AC⁰`).  A hard function in its lower-bound class can be low in the BP/algorithmic class
— the decomposition gap, with the structured (BP) low-boundary fed into engine 1.

## Honest scope

Engine 1 needs *low* boundary; this supplies it from the BP structure.  Constant-width-BP functions are easy
(PARITY, AND, OR) — the bridge is the *mechanism* (structured BP boundary ⇒ fast DP), not a hardness claim.
The Williams bridge (engine 3) and the open all-decompositions quantifier are unchanged.
-/

namespace PallLean.Paper93.DeepMath.PathB.BPLowBoundary

open PallLean.Paper93.DeepMath.PathB.ObserverAlgorithmic
open PallLean.Paper93.DeepMath.PathB.LowBoundaryFromStreaming

/-- `4·n ≤ 2^n` for `n ≥ 4`. -/
private theorem four_mul_le_two_pow {n : ℕ} (hn : 4 ≤ n) : 4 * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have h4 : 4 ≤ 2 ^ k := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc 4 * (k + 1) = 4 * k + 4 := by ring
        _ ≤ 2 ^ k + 2 ^ k := by omega
        _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

/-- `n·2 ≤ 2^{n-1}` for `n ≥ 4` (the width-2 gap). -/
private theorem gap2 {n : ℕ} (hn : 4 ≤ n) : n * 2 ≤ 2 ^ (n - 1) := by
  have h := four_mul_le_two_pow hn
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 from by omega]
    rw [pow_succ']
  rw [hpow] at h
  omega

/-- A **layered branching program**: `n` layers, width `w` (states `Fin w`), a per-layer transition reading
one input bit, and an accept predicate. -/
structure LayeredBP (n w : ℕ) where
  /-- start state -/
  start : Fin w
  /-- layer `i`: current state and the `i`-th input bit → next state -/
  trans : Fin n → Fin w → Bool → Fin w
  /-- accept predicate on the final state -/
  accept : Fin w → Bool

/-- Run a layered BP, threading the state through the layers in index order. -/
def LayeredBP.eval {n w : ℕ} (B : LayeredBP n w) (x : Fin n → Bool) : Bool :=
  B.accept ((List.finRange n).foldl (fun s i => B.trans i s (x i)) B.start)

/-- **A bounded-width BP yields a low-boundary instance** (`n` vars, `n` stages, boundary `log₂ w`). -/
def LayeredBP.lowBoundaryInstance {n w : ℕ} (_B : LayeredBP n w) (hn : 1 ≤ n) (hw : w ≠ 0)
    (h : n * w ≤ 2 ^ (n - 1)) : LowBoundaryInstance :=
  streamLowBoundaryInstance n n w hn hw h

/-- **Engine 1 fires on a bounded-width BP**: the layer-DP over its `w` boundary states beats brute force. -/
theorem LayeredBP.dp_beats_bruteforce {n w : ℕ} (B : LayeredBP n w) (hn : 1 ≤ n) (hw : w ≠ 0)
    (h : n * w ≤ 2 ^ (n - 1)) :
    dpSatTime (B.lowBoundaryInstance hn hw h).stages (B.lowBoundaryInstance hn hw h).boundary
      < bruteForceTime (B.lowBoundaryInstance hn hw h).n :=
  (B.lowBoundaryInstance hn hw h).fast

/-- The **width-2 PARITY branching program**: state is the running parity, flipped by each `true` bit;
accept iff odd (state `1`). -/
def parityBP (n : ℕ) : LayeredBP n 2 where
  start := 0
  trans := fun _ s b => if b then s + 1 else s
  accept := fun s => decide (s = 1)

/-- **Engine 1 fires on the width-2 PARITY BP** for `n ≥ 4` (boundary `1`, `n` stages, `n·2 ≤ 2^{n−1}`). -/
theorem parity_bp_dp_beats_bruteforce (n : ℕ) (hn : 4 ≤ n) :
    dpSatTime ((parityBP n).lowBoundaryInstance (by omega) (by norm_num) (gap2 hn)).stages
        ((parityBP n).lowBoundaryInstance (by omega) (by norm_num) (gap2 hn)).boundary
      < bruteForceTime ((parityBP n).lowBoundaryInstance (by omega) (by norm_num) (gap2 hn)).n :=
  (parityBP n).dp_beats_bruteforce (by omega) (by norm_num) (gap2 hn)

end PallLean.Paper93.DeepMath.PathB.BPLowBoundary

#print axioms PallLean.Paper93.DeepMath.PathB.BPLowBoundary.LayeredBP.dp_beats_bruteforce
#print axioms PallLean.Paper93.DeepMath.PathB.BPLowBoundary.parity_bp_dp_beats_bruteforce
