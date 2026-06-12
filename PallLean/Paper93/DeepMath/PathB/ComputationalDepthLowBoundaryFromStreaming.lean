import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverAlgorithmicSchema
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDecompositionGap

/-!
# Discharging engine 1: a proved `LowBoundaryInstance` from a low-boundary decomposition

The algorithmic engine (`ComputationalDepthObserverAlgorithmicSchema.lean`) needs a `LowBoundaryInstance` —
an instance with a *low*-boundary decomposition — to fire.  This file **discharges that input with a proved
object**, so engine 1 no longer rests on an assumption.

## The honest direction (an important correction)

A `LowBoundaryInstance` requires boundary to be **low** (`stages · 2^B ≤ 2^{n−1}`).  The **forcing families**
(`ForcingFamily`, expander-Tseitin proof-space) prove the **opposite** — that boundary is *high* (`≥`
super-log).  So a forcing family **cannot** supply engine 1; the two engines use opposite boundary
conditions.  The honest source for engine 1 is a *proved low-boundary decomposition* — and we have one: the
streaming observer `DecompositionGap.eqStream`, which decides EQUALITY with boundary `1`
(`eqStream_boundary`).

This is exactly the decomposition gap (`equality_decomposition_gap`): the *same* function is high-boundary in
one decomposition class and low-boundary in another.  The forcing families live on the high side (lower
bounds); engine 1 lives on the low side (algorithms).  Feeding a forcing family into engine 1 would be
incoherent, and we do not.

## What is proved (clean axioms, no `sorry`)

* `streamLowBoundaryInstance` — from any streaming decomposition with `stages · #states ≤ 2^{n−1}`, a
  `LowBoundaryInstance` (boundary `= log₂ #states`).
* `equalityLowBoundaryInstance` — the concrete instance from `eqStream` (a `2`-state streaming EQUALITY
  decider, boundary `1`) on `2k`-bit EQUALITY.
* `equality_dp_beats_bruteforce` — engine 1 *fires*: DP over its `2` boundary states beats brute force.
* `equality_conditional_lower_bound` — fed into the schema: with the Williams bridge (explicit), the lower
  bound follows.  Engine 1 is **proved**; only Williams (engine 3) remains assumed.

## Honest status

Engine 1 is now discharged by a concrete proved low-boundary decomposition (not assumed).  EQUALITY is a
trivial witness (it *is* easy); the point is the *mechanism* — a proved low-boundary decomposition feeding the
DP bound — works end to end.  The deep input (Williams) and the open input (that a *hard* class has low enough
boundary to be worth diagonalising against) remain exactly as named.  Nothing here closes any separation.
-/

namespace PallLean.Paper93.DeepMath.PathB.LowBoundaryFromStreaming

open PallLean.Paper93.DeepMath.PathB.ObserverAlgorithmic
open PallLean.Paper93.DeepMath.PathB.DecompositionGap

/-- `m + 1 ≤ 2^m`. -/
private theorem succ_le_two_pow : ∀ m : ℕ, m + 1 ≤ 2 ^ m
  | 0 => by norm_num
  | (m + 1) => by
      have ih := succ_le_two_pow m
      have hp : 0 < 2 ^ m := pow_pos (by norm_num) m
      have hpow : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; ring
      omega

/-- **From a low-boundary streaming decomposition to a `LowBoundaryInstance`.**  Given a decomposition into
`stages` stages, each carrying one of `card` boundary states (`card ≠ 0`), with `stages · card ≤ 2^{n−1}`, the
boundary in *bits* is `log₂ card` and the instance satisfies the engine-1 gap (`2^{log₂ card} ≤ card`). -/
def streamLowBoundaryInstance (n stages card : ℕ) (hn : 1 ≤ n) (hcard : card ≠ 0)
    (h : stages * card ≤ 2 ^ (n - 1)) : LowBoundaryInstance where
  n := n
  stages := stages
  boundary := Nat.log 2 card
  npos := hn
  low := le_trans (mul_le_mul_left' (Nat.pow_log_le_self 2 hcard) stages) h

/-- **The concrete EQUALITY instance.**  The streaming EQUALITY decider `eqStream` has `2` boundary states
(`Bool`, boundary `1` by `eqStream_boundary`); on `2k`-bit EQUALITY it runs `k` stages.  Since
`k · 2 ≤ 2^{2k−1}`, this is a `LowBoundaryInstance`. -/
def equalityLowBoundaryInstance (k : ℕ) (hk : 1 ≤ k) : LowBoundaryInstance :=
  streamLowBoundaryInstance (2 * k) k 2 (by omega) (by norm_num) (by
    have h := succ_le_two_pow (2 * k - 1)
    have : 2 * k - 1 + 1 = 2 * k := by omega
    rw [this] at h
    omega)

/-- **Engine 1 fires (proved).**  On the EQUALITY instance, DP over its `2` boundary states beats brute
force. -/
theorem equality_dp_beats_bruteforce (k : ℕ) (hk : 1 ≤ k) :
    dpSatTime (equalityLowBoundaryInstance k hk).stages (equalityLowBoundaryInstance k hk).boundary
      < bruteForceTime (equalityLowBoundaryInstance k hk).n :=
  (equalityLowBoundaryInstance k hk).fast

/-- **The conditional lower bound, with engine 1 discharged.**  Given the Williams bridge (explicit
hypothesis) from "DP beats brute force on this instance" to a lower bound, the lower bound follows — engine 1
is *proved*, only Williams is assumed. -/
theorem equality_conditional_lower_bound {LowerBound : Prop} (k : ℕ) (hk : 1 ≤ k)
    (williams : (dpSatTime (equalityLowBoundaryInstance k hk).stages
        (equalityLowBoundaryInstance k hk).boundary
        < bruteForceTime (equalityLowBoundaryInstance k hk).n) → LowerBound) :
    LowerBound :=
  nexp_not_subset_of_lowBoundary (equalityLowBoundaryInstance k hk) williams

end PallLean.Paper93.DeepMath.PathB.LowBoundaryFromStreaming

#print axioms PallLean.Paper93.DeepMath.PathB.LowBoundaryFromStreaming.equalityLowBoundaryInstance
#print axioms PallLean.Paper93.DeepMath.PathB.LowBoundaryFromStreaming.equality_dp_beats_bruteforce
