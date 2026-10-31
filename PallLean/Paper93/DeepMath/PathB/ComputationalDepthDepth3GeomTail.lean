import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3StarTail
import Mathlib.Algebra.Field.GeomSum

/-!
# Tight switching, step 6: the geometric shell-sum tail (branch `razborov-recoverRho-wip`)

The analytic convergence behind the tight route's `F`-independence.  The bad event `{depth ≥ s}` splits
into depth-shells `{depth = K}` for `K ≥ s`; each shell's tight weight is `≤ (2p/(1-p))^K·(2w)^K = r^K`
with `r = 4pw/(1-p)`.  Summing the shells is a **finite geometric tail** `∑_{K=s}^{N} r^K ≤ r^s/(1-r)`,
*finite and `N`-independent* once `r < 1` — which forces the parameter regime `p ≈ 1/(4w)` (so
`r = 4pw/(1-p) < 1`), unlike the crude route's `p ≤ 1/3`.  Then the union-bound budget
`#gates · r^s/(1-r) < 1` is `s ≳ log #gates` — independent of the fuel `F`, exactly what removes the
depth-3 vacuity.

`geom_tail_le` (existing, brick 56: `∑_{i<N} r^i ≤ 1/(1-r)`) gives the uniform geometric bound; here we
shift it to a tail starting at `s`.

* `geom_shell_tail_le` — `∑_{K ∈ Icc s N} r^K ≤ r^s/(1-r)` (the shell tail).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

/-- **The geometric shell tail.**  For `0 ≤ r < 1`, the tail from `s` is below `r^s/(1-r)`, uniformly in
the upper limit `N` — the convergence that makes the tight switching budget `F`-independent. -/
theorem geom_shell_tail_le {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1) (s N : ℕ) :
    ∑ K ∈ Finset.Icc s N, r ^ K ≤ r ^ s / (1 - r) := by
  have hIco : Finset.Icc s N = Finset.Ico s (N + 1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIco, Finset.sum_Ico_eq_sum_range]
  simp only [pow_add]
  rw [← Finset.mul_sum]
  calc r ^ s * ∑ j ∈ Finset.range (N + 1 - s), r ^ j
      ≤ r ^ s * (1 / (1 - r)) :=
        mul_le_mul_of_nonneg_left (geom_tail_le hr0 hr1 _) (pow_nonneg hr0 s)
    _ = r ^ s / (1 - r) := by rw [mul_one_div]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.geom_shell_tail_le
