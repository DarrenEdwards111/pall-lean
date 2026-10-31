import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingBinomialRegime
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingBridge

/-!
# The base condition in shell/family form (branch only)

`base_term_lt` gives the binomial inequality `2·(4w)^T·C(n,K-T) < C(n,K)`.  Wrapped with the family
cardinality `card_stars_eq` (`|{stars = K}| = C(n,K)·2^(n-K)`), this is exactly the `hbase` hypothesis
of the family capstone `exists_shallow_in_of_count`:

  `2·(2^(n-K+T)·C(n,K-T)·(2w)^T) < |{stars = K}|`.

So the capstone's base condition is discharged from the doubled-slack regime and `T ≥ 2`.

Clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The capstone's base condition, discharged.**  In the doubled-slack regime `(8w)·K + K ≤ n+1`
with `T ≥ 2`, twice the threshold term is strictly below the `K`-star family size. -/
theorem hbase_shell {w K T : ℕ} (hw : 0 < w) (hT : 2 ≤ T) (hTK : T ≤ K) (hKn : K ≤ n)
    (hreg : (8 * w) * K + K ≤ n + 1) :
    2 * (2 ^ (n - K + T) * n.choose (K - T) * (2 * w) ^ T)
      < (Finset.univ.filter (fun ρ : SwitchingCounting.Restriction n =>
          SwitchingCounting.stars ρ = K)).card := by
  rw [SwitchingCounting.card_stars_eq K]
  have key : 2 * ((4 * w) ^ T * n.choose (K - T)) < n.choose K :=
    SwitchingCounting.base_term_lt hw hT hTK hKn hreg
  calc 2 * (2 ^ (n - K + T) * n.choose (K - T) * (2 * w) ^ T)
      = 2 ^ (n - K) * (2 * ((4 * w) ^ T * n.choose (K - T))) := by
        rw [pow_add, show (4 * w) ^ T = (2 * w) ^ T * 2 ^ T by rw [← mul_pow]; congr 1; ring]
        ring
    _ < 2 ^ (n - K) * n.choose K := by
        exact mul_lt_mul_of_pos_left key (pow_pos (by norm_num) (n - K))
    _ = n.choose K * 2 ^ (n - K) := Nat.mul_comm _ _

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.hbase_shell
