import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA9m

/-!
# Shrinkage brick A9n: the `shrinkP/bigN` ratio and the squared Andreev bound

The shrinkage gain `(bigN/shrinkP)² ≥ (n/(n−r))³`, and the resulting squared
lower bound on Andreev formula size — all in `ℕ`, avoiding the fractional
`Γ = 3/2` exponent by squaring:

* **`shrink_factor`** — `(2n−3)²·n³ ≤ (2n)²·(n−1)³` (the per-step gain);
* **`shrink_bigN_ratio` (proved)** — `shrinkP n r²·n³ ≤ bigN n r²·(n−r)³`
  (telescoped);
* **`bigN_pos`** — `0 < bigN n r` for `r ≤ n`;
* **`andreev_squared` (proved)** — combining `andreev_shrinkage_final` with the
  ratio: `(dmsizeC f − 2r)²·(k·m)³ ≤ 4·dmsizeC(andreevStar f)²·(k·m − r)³`.

`andreev_squared` is the `n^{5/2}` content: it says
`dmsizeC(andreevStar f) ≥ (dmsizeC f − 2r)·(k·m)^{3/2} / (2·(k·m−r)^{3/2})`.
The remaining step is the parameter instantiation.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

open scoped Classical

/-- **The per-step shrinkage gain (proved).** -/
theorem shrink_factor (n : ℕ) : (2 * n - 3) ^ 2 * n ^ 3 ≤ (2 * n) ^ 2 * (n - 1) ^ 3 := by
  match n with
  | 0 => decide
  | 1 => decide
  | (m + 2) =>
    have h1 : 2 * (m + 2) - 3 = 2 * m + 1 := by omega
    have h2 : (m + 2) - 1 = m + 1 := by omega
    rw [h1, h2]
    have hid : (2 * (m + 2)) ^ 2 * (m + 1) ^ 3
        = (2 * m + 1) ^ 2 * (m + 2) ^ 3 + (m + 2) ^ 2 * (3 * m + 2) := by ring
    rw [hid]; omega

/-- **The telescoped ratio (proved)**: `shrinkP² n³ ≤ bigN² (n−r)³`. -/
theorem shrink_bigN_ratio : ∀ (r n : ℕ),
    shrinkP n r ^ 2 * n ^ 3 ≤ bigN n r ^ 2 * (n - r) ^ 3 := by
  intro r
  induction r with
  | zero => intro n; simp [shrinkP, bigN]
  | succ r ih =>
    intro n
    show ((2 * n - 3) * shrinkP (n - 1) r) ^ 2 * n ^ 3
      ≤ ((2 * n) * bigN (n - 1) r) ^ 2 * (n - (r + 1)) ^ 3
    have hih := ih (n - 1)
    have hfac := shrink_factor n
    have hnr : n - (r + 1) = (n - 1) - r := by omega
    rw [hnr]
    calc ((2 * n - 3) * shrinkP (n - 1) r) ^ 2 * n ^ 3
        = shrinkP (n - 1) r ^ 2 * ((2 * n - 3) ^ 2 * n ^ 3) := by ring
      _ ≤ shrinkP (n - 1) r ^ 2 * ((2 * n) ^ 2 * (n - 1) ^ 3) :=
          mul_le_mul_left' hfac _
      _ = (2 * n) ^ 2 * (shrinkP (n - 1) r ^ 2 * (n - 1) ^ 3) := by ring
      _ ≤ (2 * n) ^ 2 * (bigN (n - 1) r ^ 2 * ((n - 1) - r) ^ 3) :=
          mul_le_mul_left' hih _
      _ = ((2 * n) * bigN (n - 1) r) ^ 2 * ((n - 1) - r) ^ 3 := by ring

theorem bigN_pos : ∀ (r n : ℕ), r ≤ n → 0 < bigN n r := by
  intro r
  induction r with
  | zero => intro n _; exact Nat.one_pos
  | succ r ih =>
    intro n hn
    show 0 < 2 * n * bigN (n - 1) r
    have h1 : 0 < 2 * n := by omega
    have h2 : 0 < bigN (n - 1) r := ih (n - 1) (by omega)
    exact Nat.mul_pos h1 h2

/-- **THE SQUARED ANDREEV BOUND (proved)**: the `n^{5/2}` content in `ℕ`. -/
theorem andreev_squared {k m : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (f : (Fin k → Bool) → Bool) (r : ℕ) (hr : r + 2 ≤ k * m) (hmr : m ≤ r)
    (hcond : (2 * k - 1) * r ≤ m * (k * m - r)) :
    (dmsizeC f - 2 * r) ^ 2 * (k * m) ^ 3
      ≤ 4 * dmsizeC (andreevStar hm f) ^ 2 * (k * m - r) ^ 3 := by
  set df := dmsizeC f
  set L := dmsizeC (andreevStar hm f)
  set N := bigN (k * m) r
  set S := shrinkP (k * m) r
  have hand := andreev_shrinkage_final hm hk f r hr hmr hcond
  -- hand : N * df ≤ 2 * (S * L) + 2 * (r * N)
  have hd : N * (df - 2 * r) ≤ 2 * (S * L) := by
    by_cases hdf : 2 * r ≤ df
    · have key : N * (df - 2 * r) + 2 * (r * N) = N * df := by
        rw [show 2 * (r * N) = N * (2 * r) from by ring, ← Nat.mul_add]
        congr 1; omega
      have hle : N * (df - 2 * r) + 2 * (r * N) ≤ 2 * (S * L) + 2 * (r * N) := by
        rw [key]; exact hand
      omega
    · have hz : df - 2 * r = 0 := by omega
      rw [hz, Nat.mul_zero]
      exact Nat.zero_le _
  have hsq : N ^ 2 * (df - 2 * r) ^ 2 ≤ 4 * (S ^ 2 * L ^ 2) := by
    calc N ^ 2 * (df - 2 * r) ^ 2 = (N * (df - 2 * r)) ^ 2 := by ring
      _ ≤ (2 * (S * L)) ^ 2 := Nat.pow_le_pow_left hd 2
      _ = 4 * (S ^ 2 * L ^ 2) := by ring
  have hratio : S ^ 2 * (k * m) ^ 3 ≤ N ^ 2 * (k * m - r) ^ 3 :=
    shrink_bigN_ratio r (k * m)
  have hchain : N ^ 2 * ((df - 2 * r) ^ 2 * (k * m) ^ 3)
      ≤ N ^ 2 * (4 * L ^ 2 * (k * m - r) ^ 3) := by
    calc N ^ 2 * ((df - 2 * r) ^ 2 * (k * m) ^ 3)
        = (N ^ 2 * (df - 2 * r) ^ 2) * (k * m) ^ 3 := by ring
      _ ≤ (4 * (S ^ 2 * L ^ 2)) * (k * m) ^ 3 := Nat.mul_le_mul_right _ hsq
      _ = 4 * L ^ 2 * (S ^ 2 * (k * m) ^ 3) := by ring
      _ ≤ 4 * L ^ 2 * (N ^ 2 * (k * m - r) ^ 3) := mul_le_mul_left' hratio _
      _ = N ^ 2 * (4 * L ^ 2 * (k * m - r) ^ 3) := by ring
  have hpos : 0 < N ^ 2 := pow_pos (bigN_pos r (k * m) (by omega)) 2
  exact Nat.le_of_mul_le_mul_left hchain hpos

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.shrink_bigN_ratio
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.andreev_squared
