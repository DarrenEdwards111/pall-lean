import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW5

/-!
# KRW brick 6: the concrete `2^k`-bit hard gadget

Instantiating `exists_deep` at arity `a = 2^k` with `s = 2^{k-1} - 1`,
`B = 2^s` discharges the counting condition, giving an UNCONDITIONAL
near-maximal depth lower bound (the depth analogue of `andreev_superquadratic`):

* **`add4_le_two_pow` (proved)** — `n + 4 ≤ 2^n` for `n ≥ 3`;
* **`hard_pow2_hnum` (proved)** — the counting condition holds at these
  parameters (the nested-exponential arithmetic: `(k+3)·2^{2^{k-1}} < 2^{2^k}`
  since `2^k = 2·2^{k-1}` and `k+3 < 2^{2^{k-1}}`);
* **`exists_deep_pow2` (proved)** — for `k ≥ 4` there is a function on `2^k` bits
  of DeMorgan formula depth `≥ 2^{k-1} - 1` (≈ half the maximum), UNCONDITIONAL;
* **`krw_iter_deep_pow2` (from the conjecture)** — its `d`-fold iterate on
  `(2^k)^{d+1}` bits has depth `≥ (d+1)·(2^{k-1}-1)`.

The concrete bound is unconditional (pure counting); only the iterated statement
uses `KRWConjectureDepth`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-- `n + 4 ≤ 2^n` for `n ≥ 3`. -/
theorem add4_le_two_pow (n : ℕ) (hn : 3 ≤ n) : n + 4 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; ring
    omega

/-- **The counting condition at `a = 2^k`, `B = 2^{2^{k-1}-1}` (proved).** -/
theorem hard_pow2_hnum (k : ℕ) (hk : 4 ≤ k) :
    (2 * 2 ^ (2 ^ (k - 1) - 1) + 1) * (2 * 2 ^ k + 4) ^ (2 * 2 ^ (2 ^ (k - 1) - 1))
      < 2 ^ (2 ^ (2 ^ k)) := by
  have hM8 : 8 ≤ 2 ^ (k - 1) :=
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hkM : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 from by omega]
    rw [pow_succ]; ring
  have h24 : 2 * 2 ^ k + 4 ≤ 2 ^ (k + 2) := by
    have e1 : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
    have e2 : (2 : ℕ) ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := by rw [pow_succ]; ring
    have h4 : (4 : ℕ) ≤ 2 ^ (k + 1) :=
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set E : ℕ := 2 * 2 ^ (2 ^ (k - 1) - 1) with hEdef
  have hE : E = 2 ^ (2 ^ (k - 1)) := by
    rw [hEdef]
    conv_rhs => rw [show 2 ^ (k - 1) = (2 ^ (k - 1) - 1) + 1 from by omega]
    rw [pow_succ]; ring
  have hp1 : (2 * 2 ^ k + 4) ^ E ≤ (2 ^ (k + 2)) ^ E := Nat.pow_le_pow_left h24 _
  have hp2 : (2 ^ (k + 2)) ^ E = 2 ^ ((k + 2) * E) := by rw [← pow_mul]
  have hp3 : E + 1 ≤ 2 ^ E := by have := Nat.lt_two_pow_self (n := E); omega
  have hk3 : k + 3 < 2 ^ (2 ^ (k - 1)) := by
    have hlin : 2 ^ (k - 1) + 4 ≤ 2 ^ (2 ^ (k - 1)) := add4_le_two_pow (2 ^ (k - 1)) (by omega)
    have hkle : k ≤ 2 ^ (k - 1) := by
      have := Nat.lt_two_pow_self (n := k - 1); omega
    omega
  have hExp : (k + 3) * E < 2 ^ (2 ^ k) := by
    rw [hE]
    have hsplit : (2 : ℕ) ^ (2 ^ k) = 2 ^ (2 ^ (k - 1)) * 2 ^ (2 ^ (k - 1)) := by
      conv_lhs => rw [hkM]
      rw [two_mul, pow_add]
    rw [hsplit]
    have hpos : 0 < 2 ^ (2 ^ (k - 1)) := pow_pos (by norm_num) _
    nlinarith [hk3, hpos]
  calc (E + 1) * (2 * 2 ^ k + 4) ^ E
      ≤ 2 ^ E * (2 ^ (k + 2)) ^ E := Nat.mul_le_mul hp3 hp1
    _ = 2 ^ E * 2 ^ ((k + 2) * E) := by rw [hp2]
    _ = 2 ^ (E + (k + 2) * E) := by rw [← pow_add]
    _ = 2 ^ ((k + 3) * E) := by rw [show E + (k + 2) * E = (k + 3) * E from by ring]
    _ < 2 ^ (2 ^ (2 ^ k)) := Nat.pow_lt_pow_right (by norm_num) hExp

/-- **THE CONCRETE `2^k`-BIT DEPTH LOWER BOUND (proved, unconditional)**: for
`k ≥ 4` some function on `2^k` bits needs DeMorgan formula depth `≥ 2^{k-1} - 1`. -/
theorem exists_deep_pow2 (k : ℕ) (hk : 4 ≤ k) :
    ∃ g : (Fin (2 ^ k) → Bool) → Bool, 2 ^ (k - 1) - 1 ≤ dmdepth g :=
  exists_deep (2 ^ k) (2 ^ (2 ^ (k - 1) - 1)) (2 ^ (k - 1) - 1)
    (pow_pos (by norm_num) k) (le_refl _) (hard_pow2_hnum k hk)

/-- **The iterated `2^k`-bit family under KRW (proved from the conjecture)**: the
`d`-fold iterate on `(2^k)^{d+1}` bits has depth `≥ (d+1)·(2^{k-1}-1)`. -/
theorem krw_iter_deep_pow2 (H : KRWConjectureDepth) (k : ℕ) (hk : 4 ≤ k) (d : ℕ) :
    ∃ g : (Fin (2 ^ k) → Bool) → Bool,
      (iterComp (pow_pos (by norm_num) k) g d).1 = (2 ^ k) ^ (d + 1)
      ∧ (d + 1) * (2 ^ (k - 1) - 1) ≤ dmdepth (iterComp (pow_pos (by norm_num) k) g d).2 := by
  have hs2 : 2 ≤ 2 ^ (k - 1) - 1 := by
    have h8 : 8 ≤ 2 ^ (k - 1) :=
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact krw_iter_deep H (2 ^ k) (2 ^ (2 ^ (k - 1) - 1)) (2 ^ (k - 1) - 1)
    (pow_pos (by norm_num) k) hs2 (le_refl _) (hard_pow2_hnum k hk) d

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.hard_pow2_hnum
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.exists_deep_pow2
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.krw_iter_deep_pow2
