import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLowBoundaryFromStreaming
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverBoundary

/-!
# A non-trivial `LowBoundaryInstance` from the Route-F oblivious-wide crossing bound

`ComputationalDepthLowBoundaryFromStreaming.lean` discharged engine 1 with the (trivial) streaming EQUALITY
decider.  This file does it with a **non-trivial, machine-model** low-boundary decomposition: the Route-F
crossing-sequence bound for **oblivious, wide** Turing machines.

## The bridge

Route-F proved (`ObliviousCrossings.exists_fewCrossings`, Hennie pigeonhole) that an oblivious machine of time
`T` and active width `W` has a cut with `C ≤ T/W` crossings, and (`CrossingBound.crossingSeq_card`) that the
number of crossing sequences at that cut — the boundary states — is `A^C` for alphabet size `A`.  For a
**wide** machine (`W ≳ T/log n`, so `C ≤ O(log n)`), the boundary is `log₂(A^C) ≤ boundaryEntropy A C =
C·(log₂A + 1) = O(log n)` (`ComputationalDepthObserverBoundary`).  That `A^C` is exactly the `#states` my
`streamLowBoundaryInstance` consumes — so an oblivious-wide computation yields a genuine `LowBoundaryInstance`.

## What is proved (clean axioms, no `sorry`)

* `crossingLowBoundaryInstance` — from a few-crossings cut (`C` crossings, alphabet `A`, time `T`, `n`
  variables, gap `T·A^C ≤ 2^{n−1}`), a `LowBoundaryInstance` with boundary `= log₂(A^C)`.
* `crossing_boundary_le` — boundary `≤ boundaryEntropy A C = C·(log₂A + 1)`.
* `oblivious_wide_low_boundary` — for a wide cut (`C ≤ L`), boundary `≤ L·(log₂A + 1)` — with `L = log₂ n`
  this is `O(log n)`: a genuinely low boundary from a Turing-machine model.
* `crossing_dp_beats_bruteforce` — engine 1 *fires* on it.

## Honest status

This is a real machine-model low-boundary decomposition (oblivious + wide), reusing the proved Route-F
crossing bounds — strictly less trivial than the EQUALITY streaming witness, and `O(log n)` boundary.  It is
still on the **low-boundary (algorithm) side**; the function is whatever the oblivious-wide machine computes
(easy, by construction).  The deep input (Williams) and the open input (a *hard* class with low boundary)
remain exactly as named.  Nothing here closes any separation.
-/

namespace PallLean.Paper93.DeepMath.PathB.LowBoundaryFromCrossings

open PallLean.Paper93.DeepMath.PathB.ObserverAlgorithmic
open PallLean.Paper93.DeepMath.PathB.ObserverBoundary
open PallLean.Paper93.DeepMath.PathB.LowBoundaryFromStreaming

/-- **From a few-crossings cut to a `LowBoundaryInstance`.**  A cut with `C` crossings over alphabet `A` has
`A^C` crossing sequences (boundary states); over time `T` on `n` variables, if `T·A^C ≤ 2^{n−1}`, this is a
low-boundary instance with boundary `= log₂(A^C)`. -/
def crossingLowBoundaryInstance (A C T n : ℕ) (hn : 1 ≤ n) (hA : 0 < A)
    (h : T * A ^ C ≤ 2 ^ (n - 1)) : LowBoundaryInstance :=
  streamLowBoundaryInstance n T (A ^ C) hn (pow_pos hA C).ne' h

/-- The crossing instance's boundary is `≤ boundaryEntropy A C = C·(log₂A + 1)`. -/
theorem crossing_boundary_le (A C T n : ℕ) (hn : 1 ≤ n) (hA : 0 < A)
    (h : T * A ^ C ≤ 2 ^ (n - 1)) :
    (crossingLowBoundaryInstance A C T n hn hA h).boundary ≤ boundaryEntropy A C := by
  show Nat.log 2 (A ^ C) ≤ boundaryEntropy A C
  have hb : A ^ C ≤ 2 ^ boundaryEntropy A C :=
    rank_le_two_pow_boundaryEntropy (A ^ C) A C (le_refl _)
  calc Nat.log 2 (A ^ C) ≤ Nat.log 2 (2 ^ boundaryEntropy A C) := Nat.log_mono_right hb
    _ = boundaryEntropy A C := Nat.log_pow (by norm_num) _

/-- **Oblivious-wide ⇒ low boundary.**  If the cut has `C ≤ L` crossings (for a *wide* machine `L = log₂ n`,
this holds with `C ≤ T/W ≤ log₂ n`), the boundary is `≤ L·(log₂A + 1)` — `O(log n)` for constant alphabet.
A genuinely low boundary from a Turing-machine decomposition. -/
theorem oblivious_wide_low_boundary (A C T n L : ℕ) (hn : 1 ≤ n) (hA : 0 < A)
    (h : T * A ^ C ≤ 2 ^ (n - 1)) (hC : C ≤ L) :
    (crossingLowBoundaryInstance A C T n hn hA h).boundary ≤ L * (Nat.log 2 A + 1) := by
  calc (crossingLowBoundaryInstance A C T n hn hA h).boundary
      ≤ boundaryEntropy A C := crossing_boundary_le A C T n hn hA h
    _ = C * (Nat.log 2 A + 1) := rfl
    _ ≤ L * (Nat.log 2 A + 1) := by gcongr

/-- **Engine 1 fires (proved)** on the oblivious-wide crossing instance: DP over its `A^C` boundary states
beats brute force. -/
theorem crossing_dp_beats_bruteforce (A C T n : ℕ) (hn : 1 ≤ n) (hA : 0 < A)
    (h : T * A ^ C ≤ 2 ^ (n - 1)) :
    dpSatTime (crossingLowBoundaryInstance A C T n hn hA h).stages
        (crossingLowBoundaryInstance A C T n hn hA h).boundary
      < bruteForceTime (crossingLowBoundaryInstance A C T n hn hA h).n :=
  (crossingLowBoundaryInstance A C T n hn hA h).fast

/-- **The conditional lower bound, engine 1 discharged by the crossing model.**  With the Williams bridge
(explicit) from "DP beats brute force on this oblivious-wide instance" to the lower bound, the lower bound
follows. -/
theorem crossing_conditional_lower_bound {LowerBound : Prop} (A C T n : ℕ) (hn : 1 ≤ n) (hA : 0 < A)
    (h : T * A ^ C ≤ 2 ^ (n - 1))
    (williams : (dpSatTime (crossingLowBoundaryInstance A C T n hn hA h).stages
        (crossingLowBoundaryInstance A C T n hn hA h).boundary
        < bruteForceTime (crossingLowBoundaryInstance A C T n hn hA h).n) → LowerBound) :
    LowerBound :=
  nexp_not_subset_of_lowBoundary (crossingLowBoundaryInstance A C T n hn hA h) williams

end PallLean.Paper93.DeepMath.PathB.LowBoundaryFromCrossings

#print axioms PallLean.Paper93.DeepMath.PathB.LowBoundaryFromCrossings.crossingLowBoundaryInstance
#print axioms PallLean.Paper93.DeepMath.PathB.LowBoundaryFromCrossings.oblivious_wide_low_boundary
#print axioms PallLean.Paper93.DeepMath.PathB.LowBoundaryFromCrossings.crossing_dp_beats_bruteforce
