import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BoundedWidthDNFCover

/-!
# Good/bad switching cash-out: charge the failure set instead of discarding it

Random-restriction switching theorems usually say that most restrictions collapse to shallow
decision trees.  For SAT, the exceptional restrictions cannot be ignored: a satisfying assignment
may live only under a bad restriction.  This file gives the exact deterministic accounting.

Fix `q` variables of an `N`-active-variable problem.  Good leaves are solved in `2^d` work each;
bad leaves are brute-forced over the remaining `N-q` variables.  Thus

`work = goodCount * 2^d + badCount * 2^(N-q)`.

To obtain an `s`-bit total saving, each summand is given half the target budget:

* `q+d ≤ N-s-1` pays for all good leaves;
* `badCount ≤ 2^(q-s-1)` pays for the exceptional leaves.

Then total work is at most `2^(N-s)`.  This is the quantitative socket into which a switching-tail
bound must plug.  It is normalized to active variables and explicitly includes every failure leaf.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout

/-- Work of a complete good/bad restriction cover. -/
def goodBadWork (N q goodCount badCount residualDepth : ℕ) : ℕ :=
  goodCount * 2 ^ residualDepth + badCount * 2 ^ (N - q)

/-- Work after recursively replacing every good bucket leaf by a child cover, while every bad leaf
stops immediately and is brute-forced over the `K` remaining variables. -/
def recursiveSpliceWork (K goodCount badCount childWork : ℕ) : ℕ :=
  goodCount * childWork + badCount * 2 ^ K

/-- **Recursive splice recurrence.**  The good arm and exceptional arm each consume one half of
the target budget.  Thus a child saving `saving+1` bits and a current bad-count saving
`saving+1` bits combine into a parent saving of `saving` bits, with no discarded branch. -/
theorem recursiveSpliceWork_le (N q K goodCount badCount childWork saving : ℕ)
    (hN : q + K = N) (hsq : saving + 1 ≤ q) (hsK : saving + 1 ≤ K)
    (hgood : goodCount ≤ 2 ^ q)
    (hchild : childWork ≤ 2 ^ (K - saving - 1))
    (hbad : badCount ≤ 2 ^ (q - saving - 1)) :
    recursiveSpliceWork K goodCount badCount childWork ≤ 2 ^ (N - saving) := by
  unfold recursiveSpliceWork
  have hg : goodCount * childWork ≤ 2 ^ (N - saving - 1) := by
    calc
      goodCount * childWork ≤ 2 ^ q * 2 ^ (K - saving - 1) :=
        Nat.mul_le_mul hgood hchild
      _ = 2 ^ (q + (K - saving - 1)) := by rw [Nat.pow_add]
      _ = 2 ^ (N - saving - 1) := by congr 1 <;> omega
  have hb : badCount * 2 ^ K ≤ 2 ^ (N - saving - 1) := by
    calc
      badCount * 2 ^ K ≤ 2 ^ (q - saving - 1) * 2 ^ K :=
        Nat.mul_le_mul_right _ hbad
      _ = 2 ^ ((q - saving - 1) + K) := by rw [Nat.pow_add]
      _ = 2 ^ (N - saving - 1) := by congr 1 <;> omega
  calc
    goodCount * childWork + badCount * 2 ^ K
        ≤ 2 ^ (N - saving - 1) + 2 ^ (N - saving - 1) := Nat.add_le_add hg hb
    _ = 2 ^ (N - saving) := by
      have hpos : 0 < N - saving := by omega
      conv_rhs => rw [show N - saving = (N - saving - 1) + 1 by omega]
      rw [pow_succ]
      ring

/-- Good-leaf work fits in half the final target under the combined branch/depth budget. -/
theorem good_work_le_half_target (N q goodCount residualDepth saving : ℕ)
    (hleaves : goodCount ≤ 2 ^ q)
    (hbudget : q + residualDepth ≤ N - saving - 1) :
    goodCount * 2 ^ residualDepth ≤ 2 ^ (N - saving - 1) := by
  calc
    goodCount * 2 ^ residualDepth
        ≤ 2 ^ q * 2 ^ residualDepth := Nat.mul_le_mul_right _ hleaves
    _ = 2 ^ (q + residualDepth) := by rw [Nat.pow_add]
    _ ≤ 2 ^ (N - saving - 1) :=
      Nat.pow_le_pow_right (by norm_num) hbudget

/-- Bad-leaf brute force fits in half the target when the switching tail saves `saving+1` bits
among the `q` restriction choices. -/
theorem bad_work_le_half_target (N q badCount saving : ℕ)
    (hq : q ≤ N) (hsq : saving + 1 ≤ q)
    (hbad : badCount ≤ 2 ^ (q - saving - 1)) :
    badCount * 2 ^ (N - q) ≤ 2 ^ (N - saving - 1) := by
  calc
    badCount * 2 ^ (N - q)
        ≤ 2 ^ (q - saving - 1) * 2 ^ (N - q) := Nat.mul_le_mul_right _ hbad
    _ = 2 ^ ((q - saving - 1) + (N - q)) := by rw [Nat.pow_add]
    _ = 2 ^ (N - saving - 1) := by
      congr 1
      omega

/-- **Full good/bad switching cash-out.**  Every good leaf and every exceptional leaf is charged;
the total is at most `2^(N-saving)`. -/
theorem goodBadWork_le_active_gap (N q goodCount badCount residualDepth saving : ℕ)
    (hq : q ≤ N) (hs : saving + 1 ≤ N) (hsq : saving + 1 ≤ q)
    (hleaves : goodCount ≤ 2 ^ q)
    (hdepth : q + residualDepth ≤ N - saving - 1)
    (hbad : badCount ≤ 2 ^ (q - saving - 1)) :
    goodBadWork N q goodCount badCount residualDepth ≤ 2 ^ (N - saving) := by
  unfold goodBadWork
  have hg := good_work_le_half_target N q goodCount residualDepth saving hleaves hdepth
  have hb := bad_work_le_half_target N q badCount saving hq hsq hbad
  calc
    goodCount * 2 ^ residualDepth + badCount * 2 ^ (N - q)
        ≤ 2 ^ (N - saving - 1) + 2 ^ (N - saving - 1) := Nat.add_le_add hg hb
    _ = 2 ^ (N - saving) := by
      have hpos : 0 < N - saving := by omega
      conv_rhs => rw [show N - saving = (N - saving - 1) + 1 by omega]
      rw [pow_succ]
      ring

/-- Positive saving gives a strict improvement over active-variable brute force. -/
theorem goodBadWork_lt_bruteforce (N q goodCount badCount residualDepth saving : ℕ)
    (hpos : 0 < saving) (hq : q ≤ N) (hs : saving + 1 ≤ N)
    (hsq : saving + 1 ≤ q) (hleaves : goodCount ≤ 2 ^ q)
    (hdepth : q + residualDepth ≤ N - saving - 1)
    (hbad : badCount ≤ 2 ^ (q - saving - 1)) :
    goodBadWork N q goodCount badCount residualDepth < 2 ^ N := by
  apply lt_of_le_of_lt
    (goodBadWork_le_active_gap N q goodCount badCount residualDepth saving
      hq hs hsq hleaves hdepth hbad)
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- If every restriction is bad, the exceptional-leaf arm exactly recovers brute force. -/
theorem all_bad_zero_surplus (N q : ℕ) (hq : q ≤ N) :
    goodBadWork N q 0 (2 ^ q) 0 = 2 ^ N := by
  simp [goodBadWork, ← Nat.pow_add]
  omega

end PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout.good_work_le_half_target
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout.bad_work_le_half_target
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout.goodBadWork_le_active_gap
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout.recursiveSpliceWork_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout.goodBadWork_lt_bruteforce
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout.all_bad_zero_surplus
