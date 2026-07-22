import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA9p

/-!
# Shrinkage brick A9q: a concrete superquadratic Andreev family

Instantiating `andreev_formula_lb_final` (A9o) at `m = k⁶`, `r = k⁷ − 2k²`,
`B = 3k⁷` gives an explicit infinite family of Boolean functions on `N = k⁷`
variables whose DeMorgan formula size provably exceeds `N²`:

* **`andreev_superquadratic` (proved)** — for every `k ≥ 255` there is a
  `k`-bit function `f` such that every DeMorgan formula computing
  `andreevStar f` (on `N = k·k⁶ = k⁷` variables) has size `> N²`.

This is a machine-checked DeMorgan formula lower bound STRICTLY beating the
`N²` Khrapchenko ceiling — the honest payoff of the shrinkage campaign.  (The
exponent here is `≈ N^{2.07}`; the full `N^{5/2}` needs `k ≈ log N`, i.e. an
exponential `B`, which pushes the counting condition into logarithmic
territory.)  It is a DeMorgan-formula result — its ceiling is `P ≠ NC¹`, not
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

open scoped Classical

theorem andreev_superquadratic (k : ℕ) (hk : 255 ≤ k) :
    ∃ f : (Fin k → Bool) → Bool,
      ∀ t : DMTree (k * k ^ 6),
        (∀ x, t.eval x = andreevStar (show 0 < k ^ 6 from pow_pos (show (0:ℕ) < k by omega) 6) f x) →
        (k * k ^ 6) ^ 2 < t.lsize := by
  have hk1 : 1 ≤ k := by omega
  have hm : 1 ≤ k ^ 6 := Nat.one_le_pow _ _ (by omega)
  set r := k ^ 7 - 2 * k ^ 2 with hrdef
  -- k * k^6 = k^7
  have hkm : k * k ^ 6 = k ^ 7 := by ring
  -- 2k² ≤ k^7
  have h2k2 : 2 * k ^ 2 ≤ k ^ 7 := by
    have : (2 : ℕ) * k ^ 2 ≤ k ^ 5 * k ^ 2 := by
      apply Nat.mul_le_mul_right
      calc (2 : ℕ) ≤ k := by omega
        _ ≤ k ^ 5 := Nat.le_self_pow (by omega) k
    calc 2 * k ^ 2 ≤ k ^ 5 * k ^ 2 := this
      _ = k ^ 7 := by ring
  have hkmr : k * k ^ 6 - r = 2 * k ^ 2 := by rw [hkm, hrdef]; exact Nat.sub_sub_self h2k2
  -- hypotheses of andreev_formula_lb_final
  have hk2p : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hr : r + 2 ≤ k * k ^ 6 := by rw [hkm, hrdef]; omega
  have hmr : k ^ 6 ≤ r := by
    rw [hrdef]
    have : k ^ 6 + 2 * k ^ 2 ≤ k ^ 7 := by
      have h1 : (2 : ℕ) * k ^ 2 ≤ k ^ 6 := by
        have : (2 : ℕ) * k ^ 2 ≤ k ^ 4 * k ^ 2 := by
          apply Nat.mul_le_mul_right
          calc (2 : ℕ) ≤ k := by omega
            _ ≤ k ^ 4 := Nat.le_self_pow (by omega) k
        calc 2 * k ^ 2 ≤ k ^ 4 * k ^ 2 := this
          _ = k ^ 6 := by ring
      have h2 : k ^ 6 + k ^ 6 ≤ k ^ 7 := by
        have : k ^ 6 + k ^ 6 = 2 * k ^ 6 := by ring
        rw [this]
        calc 2 * k ^ 6 ≤ k * k ^ 6 := by apply Nat.mul_le_mul_right; omega
          _ = k ^ 7 := by ring
      omega
    omega
  have hcond : (2 * k - 1) * r ≤ k ^ 6 * (k * k ^ 6 - r) := by
    rw [hkmr, hrdef]
    -- (2k-1)(k^7-2k²) ≤ k^6 * 2k² = 2k^8
    have hexp : k ^ 6 * (2 * k ^ 2) = 2 * k ^ 8 := by ring
    rw [hexp]
    have hle : (2 * k - 1) * (k ^ 7 - 2 * k ^ 2) ≤ (2 * k) * (k ^ 7) := by
      apply Nat.mul_le_mul <;> omega
    have hval : (2 * k) * (k ^ 7) = 2 * k ^ 8 := by ring
    omega
  have hnum : (2 * (3 * k ^ 7) + 1) * (2 * k + 4) ^ (2 * (3 * k ^ 7))
      < 2 ^ (2 ^ k) := by
    have h24 : 2 * k + 4 ≤ 2 ^ (k + 2) := by
      have hk2 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
      have hpw : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [pow_add]; ring
      omega
    have hp1 : (2 * k + 4) ^ (2 * (3 * k ^ 7))
        ≤ (2 ^ (k + 2)) ^ (2 * (3 * k ^ 7)) := Nat.pow_le_pow_left h24 _
    have hp2 : (2 ^ (k + 2)) ^ (2 * (3 * k ^ 7)) = 2 ^ ((k + 2) * (2 * (3 * k ^ 7))) := by
      rw [← pow_mul]
    have hp3 : 2 * (3 * k ^ 7) + 1 ≤ 2 ^ (2 * (3 * k ^ 7)) := by
      have := Nat.lt_two_pow_self (n := 2 * (3 * k ^ 7)); omega
    have hexp : 2 * (3 * k ^ 7) + (k + 2) * (2 * (3 * k ^ 7)) = 6 * k ^ 8 + 18 * k ^ 7 := by
      ring
    have hlt : 6 * k ^ 8 + 18 * k ^ 7 < 2 ^ k := by
      have hpb := poly_bound k hk
      have h18 : 18 * k ^ 7 ≤ 18 * k ^ 8 := by
        apply Nat.mul_le_mul_left
        calc k ^ 7 ≤ k * k ^ 7 := Nat.le_mul_of_pos_left _ (by omega)
          _ = k ^ 8 := by ring
      omega
    calc (2 * (3 * k ^ 7) + 1) * (2 * k + 4) ^ (2 * (3 * k ^ 7))
        ≤ 2 ^ (2 * (3 * k ^ 7)) * (2 ^ (k + 2)) ^ (2 * (3 * k ^ 7)) :=
          Nat.mul_le_mul hp3 hp1
      _ = 2 ^ (2 * (3 * k ^ 7)) * 2 ^ ((k + 2) * (2 * (3 * k ^ 7))) := by rw [hp2]
      _ = 2 ^ (2 * (3 * k ^ 7) + (k + 2) * (2 * (3 * k ^ 7))) := by rw [← pow_add]
      _ = 2 ^ (6 * k ^ 8 + 18 * k ^ 7) := by rw [hexp]
      _ < 2 ^ (2 ^ k) := Nat.pow_lt_pow_right (by norm_num) hlt
  -- apply the formula lower bound
  obtain ⟨f, hf⟩ := andreev_formula_lb_final hm hk1 r (3 * k ^ 7) hr hmr hcond hnum
  refine ⟨f, fun t ht => ?_⟩
  have hbound := hf t ht
  set L := t.lsize
  -- hbound : (3k^7 - 2r)^2 * (k*k^6)^3 ≤ 4 * L^2 * (k*k^6 - r)^3
  rw [hkmr, hkm] at hbound
  have hBr : 3 * k ^ 7 - 2 * r = k ^ 7 + 4 * k ^ 2 := by rw [hrdef]; omega
  rw [hBr] at hbound
  -- lower-bound LHS, simplify RHS
  have hLHS : k ^ 35 ≤ (k ^ 7 + 4 * k ^ 2) ^ 2 * (k ^ 7) ^ 3 := by
    have : (k ^ 7) ^ 2 * (k ^ 7) ^ 3 = k ^ 35 := by ring
    calc k ^ 35 = (k ^ 7) ^ 2 * (k ^ 7) ^ 3 := by ring
      _ ≤ (k ^ 7 + 4 * k ^ 2) ^ 2 * (k ^ 7) ^ 3 := by
          apply Nat.mul_le_mul_right
          apply Nat.pow_le_pow_left
          omega
  have hRHS : 4 * L ^ 2 * (2 * k ^ 2) ^ 3 = 32 * (k ^ 6 * L ^ 2) := by ring
  rw [hRHS] at hbound
  have hH : k ^ 35 ≤ 32 * (k ^ 6 * L ^ 2) := le_trans hLHS hbound
  -- goal: (k^7)^2 < L, i.e. k^14 < L.  Show k^28 < L^2 then conclude.
  have hk28 : k ^ 28 < L ^ 2 := by
    by_contra hc
    push_neg at hc  -- L^2 ≤ k^28
    have h1 : 32 * (k ^ 6 * L ^ 2) ≤ 32 * (k ^ 6 * k ^ 28) := by
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_left
      exact hc
    have h2 : 32 * (k ^ 6 * k ^ 28) = 32 * k ^ 34 := by ring
    have h3 : 32 * k ^ 34 < k ^ 35 := by
      have hx : (0 : ℕ) < k ^ 34 := pow_pos (by omega) 34
      have : 32 * k ^ 34 < k * k ^ 34 := (Nat.mul_lt_mul_right hx).mpr (by omega)
      calc 32 * k ^ 34 < k * k ^ 34 := this
        _ = k ^ 35 := by ring
    omega
  -- from k^28 < L^2 conclude (k^7)^2 = k^14 < L
  have hfin : (k ^ 7) ^ 2 < L := by
    by_contra hc
    push_neg at hc  -- L ≤ k^14
    have : L ^ 2 ≤ (k ^ 7) ^ 4 := by
      calc L ^ 2 ≤ ((k ^ 7) ^ 2) ^ 2 := Nat.pow_le_pow_left hc 2
        _ = (k ^ 7) ^ 4 := by ring
    have he : (k ^ 7) ^ 4 = k ^ 28 := by ring
    rw [he] at this
    omega
  rw [hkm]
  exact hfin

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.andreev_superquadratic
