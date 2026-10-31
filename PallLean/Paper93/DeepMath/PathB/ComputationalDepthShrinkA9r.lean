import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA9p

/-!
# Shrinkage brick A9r: the full `n^{5/2}` Andreev bound

The tight Andreev bound `L ≥ N^{5/2}`, with `k ≈ log N` (i.e. exponential
hardness `B`).  The free-set is `K = 2k²`, so the `k⁶` from `(B−2r)²` cancels
the `k⁶` from `K³` and the bound is CLEAN `N⁵ ≤ L²` — no polylog loss:

* **`andreev_five_halves_full` (proved)** — for `k ≥ 4`, `m ≥ 4k`, and
  `24·m·k⁵ < 2ᵏ` (satisfiable: `m ∈ [4k, 2ᵏ/(24k⁵))`, nonempty for large `k`),
  taking `B = 6mk⁴`, there is a `k`-bit function `f` such that every DeMorgan
  formula computing `andreevStar f` (on `N = k·m` variables) has
  `N⁵ ≤ lsize²`, i.e. `lsize ≥ N^{5/2}`.

The hardness `B = 6mk⁴ ≈ 2ᵏ/poly` is exponential in `k` (via the counting
hypothesis `24mk⁵ < 2ᵏ`), and `k ≈ log N`.  This is the full Andreev 1987
`n^{5/2}` DeMorgan formula lower bound, machine-checked.  Its ceiling is
`P ≠ NC¹`, not `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

open scoped Classical

/-- **THE FULL `n^{5/2}` ANDREEV BOUND (proved)**: `N⁵ ≤ lsize²`. -/
theorem andreev_five_halves_full (k m : ℕ) (hk : 4 ≤ k) (hm4k : 4 * k ≤ m)
    (hmk : 24 * m * k ^ 5 < 2 ^ k) :
    ∃ f : (Fin k → Bool) → Bool,
      ∀ t : DMTree (k * m),
        (∀ x, t.eval x = andreevStar (show 0 < m from by omega) f x) →
        (k * m) ^ 5 ≤ t.lsize ^ 2 := by
  have hm : 1 ≤ m := by omega
  have hk1 : 1 ≤ k := by omega
  have hk3 : 8 ≤ k ^ 3 := by have h := Nat.pow_le_pow_left hk 3; omega
  have hk2p : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ (by omega)
  set r := k * m - 2 * k ^ 2 with hrdef
  set B := 6 * m * k ^ 4 with hBdef
  have h2k2 : 2 * k ^ 2 ≤ k * m := by
    have h := Nat.mul_le_mul hm4k (le_refl k); nlinarith [h]
  have hkmr : k * m - r = 2 * k ^ 2 := by rw [hrdef]; exact Nat.sub_sub_self h2k2
  have hr : r + 2 ≤ k * m := by rw [hrdef]; omega
  have hmr : m ≤ r := by
    rw [hrdef]
    have key : m + 2 * k ^ 2 ≤ k * m := by
      nlinarith [hm4k, hk, Nat.mul_le_mul hm4k (le_refl k), Nat.mul_le_mul hk (le_refl k)]
    omega
  have hcond : (2 * k - 1) * r ≤ m * (k * m - r) := by
    rw [hkmr]
    have h1 : (2 * k - 1) * r ≤ 2 * k * r := by
      apply Nat.mul_le_mul_right; omega
    have h2 : 2 * k * r ≤ m * (2 * k ^ 2) := by
      rw [hrdef]
      calc 2 * k * (k * m - 2 * k ^ 2)
          ≤ 2 * k * (k * m) := Nat.mul_le_mul (le_refl (2 * k)) (by omega)
        _ = m * (2 * k ^ 2) := by ring
    omega
  have hnum : (2 * B + 1) * (2 * k + 4) ^ (2 * B) < 2 ^ (2 ^ k) := by
    have hk2 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
    have h24 : 2 * k + 4 ≤ 2 ^ (k + 2) := by
      have hpw : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [pow_add]; ring
      omega
    have hp1 : (2 * k + 4) ^ (2 * B) ≤ (2 ^ (k + 2)) ^ (2 * B) := Nat.pow_le_pow_left h24 _
    have hp2 : (2 ^ (k + 2)) ^ (2 * B) = 2 ^ ((k + 2) * (2 * B)) := by rw [← pow_mul]
    have hp3 : 2 * B + 1 ≤ 2 ^ (2 * B) := by
      have := Nat.lt_two_pow_self (n := 2 * B); omega
    have hlt : 2 * B + (k + 2) * (2 * B) < 2 ^ k := by
      have hexp : 2 * B + (k + 2) * (2 * B) = 12 * m * k ^ 5 + 36 * m * k ^ 4 := by
        rw [hBdef]; ring
      have hb : 12 * m * k ^ 5 + 36 * m * k ^ 4 ≤ 24 * m * k ^ 5 := by
        have h1 : 3 * (m * k ^ 4) ≤ k * (m * k ^ 4) :=
          Nat.mul_le_mul_right _ (by omega : 3 ≤ k)
        nlinarith [h1]
      omega
    calc (2 * B + 1) * (2 * k + 4) ^ (2 * B)
        ≤ 2 ^ (2 * B) * (2 ^ (k + 2)) ^ (2 * B) := Nat.mul_le_mul hp3 hp1
      _ = 2 ^ (2 * B) * 2 ^ ((k + 2) * (2 * B)) := by rw [hp2]
      _ = 2 ^ (2 * B + (k + 2) * (2 * B)) := by rw [← pow_add]
      _ < 2 ^ (2 ^ k) := Nat.pow_lt_pow_right (by norm_num) hlt
  -- apply the formula lower bound
  obtain ⟨f, hf⟩ := andreev_formula_lb_final hm hk1 r B hr hmr hcond hnum
  refine ⟨f, fun t ht => ?_⟩
  have hbound := hf t ht
  set L := t.lsize
  rw [hkmr] at hbound
  have hRHS : 4 * L ^ 2 * (2 * k ^ 2) ^ 3 = 32 * k ^ 6 * L ^ 2 := by ring
  rw [hRHS] at hbound
  -- hbound : (B - 2r)^2 * (k*m)^3 ≤ 32 * k^6 * L^2
  -- lower-bound (B - 2r)
  have hDeq : 2 * k * m * (3 * k ^ 3 - 1) = 6 * m * k ^ 4 - 2 * k * m := by
    have hone : 1 ≤ 3 * k ^ 3 := by omega
    have hsum : 2 * k * m * (3 * k ^ 3 - 1) + 2 * k * m = 6 * m * k ^ 4 := by
      have hma : 2 * k * m * (3 * k ^ 3 - 1) + 2 * k * m * 1
          = 2 * k * m * ((3 * k ^ 3 - 1) + 1) := by rw [Nat.mul_add]
      rw [Nat.mul_one] at hma
      rw [hma, Nat.sub_add_cancel hone]
      ring
    omega
  have hD_ge : 2 * k * m * (3 * k ^ 3 - 1) ≤ B - 2 * r := by
    rw [hDeq, hBdef]
    have hrle : r ≤ k * m := by rw [hrdef]; omega
    have h2r : 2 * r ≤ 2 * k * m := by nlinarith [hrle]
    exact Nat.sub_le_sub_left h2r _
  have hcore : 8 * k ^ 6 ≤ (3 * k ^ 3 - 1) ^ 2 := by
    have hk6 : k ^ 6 = (k ^ 3) ^ 2 := by ring
    rw [hk6]
    set t := k ^ 3 with ht
    have htge : 8 ≤ t := hk3
    have h3t : 1 ≤ 3 * t := by omega
    obtain ⟨u, hu⟩ : ∃ u, 3 * t = u + 1 := ⟨3 * t - 1, by omega⟩
    have hsub : 3 * t - 1 = u := by omega
    rw [hsub]
    have huge : 23 ≤ u := by omega
    have h23 : 23 * u ≤ u ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul huge (le_refl u)
    have hu16 : 16 * u + 8 ≤ u ^ 2 := by omega
    have hsq9 : 9 * t ^ 2 = (u + 1) ^ 2 := by rw [← hu]; ring
    have hexp9 : (u + 1) ^ 2 = u ^ 2 + 2 * u + 1 := by ring
    have h72 : 72 * t ^ 2 = 8 * u ^ 2 + 16 * u + 8 := by
      have h8 : 72 * t ^ 2 = 8 * (9 * t ^ 2) := by ring
      rw [h8, hsq9, hexp9]; ring
    have h9u : 9 * (8 * t ^ 2) ≤ 9 * u ^ 2 := by
      have h9e : 9 * (8 * t ^ 2) = 72 * t ^ 2 := by ring
      rw [h9e, h72]; omega
    exact Nat.le_of_mul_le_mul_left h9u (by norm_num)
  have hsq : 32 * (k * m) ^ 2 * k ^ 6 ≤ (2 * k * m * (3 * k ^ 3 - 1)) ^ 2 := by
    have hfac : (2 * k * m * (3 * k ^ 3 - 1)) ^ 2
        = 4 * (k * m) ^ 2 * (3 * k ^ 3 - 1) ^ 2 := by ring
    rw [hfac]
    calc 32 * (k * m) ^ 2 * k ^ 6
        = 4 * (k * m) ^ 2 * (8 * k ^ 6) := by ring
      _ ≤ 4 * (k * m) ^ 2 * (3 * k ^ 3 - 1) ^ 2 := Nat.mul_le_mul (le_refl _) hcore
  have hsep : 32 * (k * m) ^ 2 * k ^ 6 ≤ (B - 2 * r) ^ 2 :=
    le_trans hsq (Nat.pow_le_pow_left hD_ge 2)
  -- combine: 32 k^6 (km)^5 ≤ 32 k^6 L^2
  have hchain : 32 * k ^ 6 * (k * m) ^ 5 ≤ 32 * k ^ 6 * L ^ 2 := by
    calc 32 * k ^ 6 * (k * m) ^ 5
        = (32 * (k * m) ^ 2 * k ^ 6) * (k * m) ^ 3 := by ring
      _ ≤ (B - 2 * r) ^ 2 * (k * m) ^ 3 := Nat.mul_le_mul_right _ hsep
      _ ≤ 32 * k ^ 6 * L ^ 2 := hbound
  have hpos : 0 < 32 * k ^ 6 := by positivity
  exact Nat.le_of_mul_le_mul_left hchain hpos

/-- `96·k⁶ ≤ 2ᵏ` for `k ≥ 255` (from `poly_bound`). -/
theorem log96 (k : ℕ) (hk : 255 ≤ k) : 96 * k ^ 6 ≤ 2 ^ k := by
  have hpb := poly_bound k hk
  have hk2 : 3 ≤ k ^ 2 := by
    have h := Nat.pow_le_pow_left (show 2 ≤ k by omega) 2; omega
  have h1 : 96 * k ^ 6 ≤ 32 * k ^ 8 := by
    calc 96 * k ^ 6 = 32 * k ^ 6 * 3 := by ring
      _ ≤ 32 * k ^ 6 * k ^ 2 := Nat.mul_le_mul (le_refl _) hk2
      _ = 32 * k ^ 8 := by ring
  omega

/-- The `k ≈ log N` block size `m = 2ᵏ/(24k⁵)` is positive for `k ≥ 255`. -/
theorem log_m_pos (k : ℕ) (hk : 255 ≤ k) : 0 < 2 ^ k / (24 * k ^ 5) := by
  have hpos : 0 < 24 * k ^ 5 := by positivity
  have h1 : 24 * k ^ 5 ≤ 96 * k ^ 6 := by
    have he : 96 * k ^ 6 = 24 * k ^ 5 * (4 * k) := by ring
    rw [he]; exact Nat.le_mul_of_pos_right _ (by positivity)
  have h24 : 24 * k ^ 5 ≤ 2 ^ k := le_trans h1 (log96 k hk)
  exact Nat.div_pos h24 hpos

/-- **THE `k ≈ log N` WITNESS (proved)**: with `m = 2ᵏ/(24k⁵)`, so that
`N = k·m ≈ 2ᵏ/(24k⁴)` and hence `k ≈ log N` — the hard function reads only
`k ≈ log N` input bits — every DeMorgan formula computing the Andreev function
on `N` variables has `N⁵ ≤ lsize²`, i.e. `lsize ≥ N^{5/2}`.  This exhibits the
full Andreev family in its canonical logarithmic-arity regime. -/
theorem andreev_five_halves_log (k : ℕ) (hk : 255 ≤ k) :
    ∃ f : (Fin k → Bool) → Bool,
      ∀ t : DMTree (k * (2 ^ k / (24 * k ^ 5))),
        (∀ x, t.eval x = andreevStar (log_m_pos k hk) f x) →
        (k * (2 ^ k / (24 * k ^ 5))) ^ 5 ≤ t.lsize ^ 2 := by
  set m := 2 ^ k / (24 * k ^ 5) with hmdef
  have hpos : 0 < 24 * k ^ 5 := by positivity
  have hm4k : 4 * k ≤ m := by
    rw [hmdef, Nat.le_div_iff_mul_le hpos]
    have h96 : 4 * k * (24 * k ^ 5) = 96 * k ^ 6 := by ring
    rw [h96]; exact log96 k hk
  have hmk : 24 * m * k ^ 5 < 2 ^ k := by
    have hd : ¬ (24 * k ^ 5 ∣ 2 ^ k) := by
      intro hdvd
      have h3 : (3 : ℕ) ∣ 24 * k ^ 5 := ⟨8 * k ^ 5, by ring⟩
      have h3' : (3 : ℕ) ∣ 2 ^ k := h3.trans hdvd
      have hb := Nat.prime_three.dvd_of_dvd_pow h3'
      norm_num at hb
    have hmod : 2 ^ k % (24 * k ^ 5) ≠ 0 := by
      rwa [Nat.dvd_iff_mod_eq_zero] at hd
    have hdm := Nat.div_add_mod (2 ^ k) (24 * k ^ 5)
    have hval : 24 * m * k ^ 5 = 24 * k ^ 5 * (2 ^ k / (24 * k ^ 5)) := by
      rw [hmdef]; ring
    rw [hval]; omega
  exact andreev_five_halves_full k m (by omega) hm4k hmk

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.andreev_five_halves_full
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.andreev_five_halves_log
