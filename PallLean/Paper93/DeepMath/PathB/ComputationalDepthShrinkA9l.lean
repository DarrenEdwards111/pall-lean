import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA9j

/-!
# Shrinkage brick A9l: the falling-factorial inequality

The last counting fact, `2k·perm r m ≤ perm (k·m) m`, proved unconditionally
from a clean parameter condition (`(2k−1)·r ≤ m·(n−r)`, met by free-set size
`n − r ≈ 2k²`):

* **`factor_ineq`** — `(r−m)·n ≤ (n−m)·r` for `m ≤ r ≤ n`;
* **`perm_prod_ineq`** — `perm r m · n^m ≤ perm n m · r^m` (each factor `≥ n/r`);
* **`two_term_binom`** — `(m+1)·r^m·K + r^(m+1) ≤ (r+K)^(m+1)`;
* **`pow_ratio`** — `2k·r^m ≤ (r+K)^m` from `(2k−1)·r ≤ m·K`;
* **`two_k_perm_le` (proved)** — `2k·perm r m ≤ perm n m`.

Combined with `andreev_shrinkage_of_perm` (A9k), this discharges the last fence
of the Andreev shrinkage.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

theorem factor_ineq (m r n : ℕ) (hmr : m ≤ r) (hrn : r ≤ n) :
    (r - m) * n ≤ (n - m) * r := by
  obtain ⟨a, rfl⟩ : ∃ a, r = m + a := ⟨r - m, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, n = (m + a) + b := ⟨n - (m + a), by omega⟩
  have h1 : (m + a) - m = a := by omega
  have h2 : (m + a + b) - m = a + b := by omega
  rw [h1, h2]
  have hkey : (a + b) * (m + a) = a * (m + a + b) + b * m := by ring
  omega

theorem perm_prod_ineq (n r : ℕ) (hrn : r ≤ n) :
    ∀ m, m ≤ r → perm r m * n ^ m ≤ perm n m * r ^ m := by
  intro m
  induction m with
  | zero => intro _; simp [perm]
  | succ m ih =>
    intro hmr
    have hm : m ≤ r := by omega
    have hih := ih hm
    have hfac := factor_ineq m r n hm hrn
    rw [perm_succ_right m r, perm_succ_right m n, pow_succ, pow_succ]
    calc (perm r m * (r - m)) * (n ^ m * n)
        = (perm r m * n ^ m) * ((r - m) * n) := by ring
      _ ≤ (perm n m * r ^ m) * ((n - m) * r) := Nat.mul_le_mul hih hfac
      _ = (perm n m * (n - m)) * (r ^ m * r) := by ring

theorem perm_ratio_bound (n r m k : ℕ) (hrn : r ≤ n) (hmr : m ≤ r) (hr : 0 < r)
    (hpow : 2 * k * r ^ m ≤ n ^ m) : 2 * k * perm r m ≤ perm n m := by
  have ha := perm_prod_ineq n r hrn m hmr
  have hb : perm r m * (2 * k * r ^ m) ≤ perm r m * n ^ m :=
    mul_le_mul_left' hpow _
  have hchain : 2 * k * perm r m * r ^ m ≤ perm n m * r ^ m := by
    calc 2 * k * perm r m * r ^ m = perm r m * (2 * k * r ^ m) := by ring
      _ ≤ perm r m * n ^ m := hb
      _ ≤ perm n m * r ^ m := ha
  exact Nat.le_of_mul_le_mul_right hchain (pow_pos hr m)

theorem two_term_binom (r K : ℕ) :
    ∀ m, (m + 1) * r ^ m * K + r ^ (m + 1) ≤ (r + K) ^ (m + 1) := by
  intro m
  induction m with
  | zero => simp only [pow_zero, Nat.zero_add, pow_one, one_mul, mul_one]; omega
  | succ m ih =>
    have hstep : (r + K) ^ (m + 1 + 1) = (r + K) * (r + K) ^ (m + 1) := by
      rw [pow_succ]; ring
    rw [hstep]
    have h1 : (r + K) * ((m + 1) * r ^ m * K + r ^ (m + 1))
        ≤ (r + K) * (r + K) ^ (m + 1) := mul_le_mul_left' ih _
    have hexp : (r + K) * ((m + 1) * r ^ m * K + r ^ (m + 1))
        = (m + 1 + 1) * r ^ (m + 1) * K + r ^ (m + 1 + 1) + (m + 1) * K ^ 2 * r ^ m := by
      ring
    rw [hexp] at h1
    omega

theorem pow_ratio (r K m' k : ℕ) (hr : 0 < r) (hk : 1 ≤ k)
    (hcond : (2 * k - 1) * r ≤ (m' + 1) * K) :
    2 * k * r ^ (m' + 1) ≤ (r + K) ^ (m' + 1) := by
  have hbin := two_term_binom r K m'
  have h1 : (2 * k - 1) * r ^ (m' + 1) ≤ (m' + 1) * r ^ m' * K := by
    calc (2 * k - 1) * r ^ (m' + 1) = (2 * k - 1) * r * r ^ m' := by rw [pow_succ]; ring
      _ ≤ (m' + 1) * K * r ^ m' := mul_le_mul_right' hcond _
      _ = (m' + 1) * r ^ m' * K := by ring
  have hkk : 1 + (2 * k - 1) = 2 * k := by omega
  calc 2 * k * r ^ (m' + 1) = (1 + (2 * k - 1)) * r ^ (m' + 1) := by rw [hkk]
    _ = r ^ (m' + 1) + (2 * k - 1) * r ^ (m' + 1) := by ring
    _ ≤ r ^ (m' + 1) + (m' + 1) * r ^ m' * K := by omega
    _ ≤ (r + K) ^ (m' + 1) := by omega

/-- **THE FALLING-FACTORIAL INEQUALITY (proved).** -/
theorem two_k_perm_le (k m r n : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (hmr : m ≤ r)
    (hrn : r ≤ n) (hcond : (2 * k - 1) * r ≤ m * (n - r)) :
    2 * k * perm r m ≤ perm n m := by
  have hr : 0 < r := by omega
  have hpow : 2 * k * r ^ m ≤ n ^ m := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨K, rfl⟩ : ∃ K, n = r + K := ⟨n - r, by omega⟩
    have hc' : (2 * k - 1) * r ≤ (m' + 1) * K := by
      have : (r + K) - r = K := by omega
      rw [this] at hcond
      exact hcond
    exact pow_ratio r K m' k hr hk hc'
  exact perm_ratio_bound n r m k hrn hmr hr hpow

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.two_k_perm_le
