import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingBound

/-!
# Observer boundary entropy — grounding the meta-complexity / thermodynamic-observer idea

A formal anchor for the "thermodynamic observer boundary" reframing (`SCOPE_OBSERVER_BOUNDARY_ENTROPY.md`):
the *observer boundary entropy* at a cut is the `log` of the interface information (the crossing-sequence
count) that a deterministic observer must retain across it.  This file makes that a definition and proves
its two basic laws, both consequences of the Route-F crossing-sequence bound (`rank ≤ A^C`):

* `rank_le_two_pow_boundaryEntropy` — `log₂ rank ≤ B`: an observer of boundary entropy `B` resolves at most
  `2^B` profiles.
* `lowBoundary_poly_rank` — a *low-boundary* (P-style) observer, `B = O(log n)`, sees only `poly(n)` rank.

So the observer language is **not metaphor here**: "boundary entropy" `= C·(log₂ A + 1)` is a real
quantity and these are theorems.  The *conjecture* that SAT forces super-logarithmic boundary on every
faithful deterministic observer is the open content (`= CookLevinFrontierHyp` / the `T/log n` space lower
bound); it is **not** proved — see the scope doc.
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverBoundary

open PallLean.Paper93.DeepMath.PathB

/-- **Observer boundary entropy** at a cut (`A` = state-alphabet size, `C` = number of crossings): an upper
estimate on the `log` of the crossing-sequence count `A^C`, namely `C·(log₂ A + 1)`.  This is the interface
information a deterministic observer must carry across the cut. -/
def boundaryEntropy (A C : ℕ) : ℕ := C * (Nat.log 2 A + 1)

/-- **`log₂ rank ≤ boundary entropy`.**  The space-cut rank is at most `2^B`: an observer of boundary
entropy `B` can resolve at most `2^B` distinct profiles.  (From the proved crossing bound `rank ≤ A^C`.) -/
theorem rank_le_two_pow_boundaryEntropy (rank A C : ℕ) (h : rank ≤ A ^ C) :
    rank ≤ 2 ^ boundaryEntropy A C := by
  calc rank ≤ A ^ C := h
    _ ≤ (2 ^ (Nat.log 2 A + 1)) ^ C :=
        Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self (by norm_num) A).le C
    _ = 2 ^ boundaryEntropy A C := by rw [← pow_mul, boundaryEntropy, Nat.mul_comm]

/-- A **low-boundary (P-style) observer** — boundary entropy `O(log n)` — sees only `poly(n)` rank. -/
theorem lowBoundary_poly_rank (rank A C c n : ℕ) (hn : 1 ≤ n)
    (h : rank ≤ A ^ C) (hlow : boundaryEntropy A C ≤ c * Nat.log 2 n) :
    rank ≤ n ^ c := by
  calc rank ≤ 2 ^ boundaryEntropy A C := rank_le_two_pow_boundaryEntropy rank A C h
    _ ≤ 2 ^ (c * Nat.log 2 n) := Nat.pow_le_pow_right (by norm_num) hlow
    _ = (2 ^ Nat.log 2 n) ^ c := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ n ^ c := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (by omega)) c

end PallLean.Paper93.DeepMath.PathB.ObserverBoundary

#print axioms PallLean.Paper93.DeepMath.PathB.ObserverBoundary.rank_le_two_pow_boundaryEntropy
