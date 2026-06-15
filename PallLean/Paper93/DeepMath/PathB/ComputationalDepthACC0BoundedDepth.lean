import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RestrictedWilliamsSpeedup

/-!
# Bounded-depth `ACC⁰`: depth `d` ⇒ `≤ 2^d` leaves ⇒ polynomial exact `SYM∘AND` and a Williams speedup

The restricted-`YBT` fragments so far were controlled by **leaf count** (`…ACC0RestrictedYBT`) or **support
footprint** (`…ACC0BoundedOverlapMOD`).  This file controls them by **depth**: a circuit of (binary) depth `d` has at
most `2^d` leaves, so its exact `SYM∘AND` size is `≤ maxBase^{2^d}` — *polynomial* for constant depth and polynomial
base.  Combined with the count-cell search (`…ACC0RestrictedWilliamsSpeedup`), a bounded-depth circuit gets a Williams
speedup with savings `2^{n − 2^d·log(maxBase)}` — **super-polynomial** for constant depth.

The lever is again the multiplicative `psize` identity, now bounded through `leafCount ≤ 2^depth`.

## What is proved (clean axioms, no `sorry`)

* **`leafCount_le_two_pow_depth`** — `leafCount C ≤ 2 ^ depth C` (a depth-`d` binary circuit has `≤ 2^d` leaves).
* **`psize_le_of_depth`** — `depth C ≤ d`, `maxBase C ≤ B ⇒ psize C ≤ B^{2^d}` (polynomial for constant `d`, poly `B`).
* **`bounded_depth_exact`** — `B^{2^d} < 2^n ⇒ HasExactSymAndForm C`: bounded-depth, poly-base circuits have an exact
  `SYM∘AND` form.
* **`restricted_williams_speedup_of_psize`** — the `psize`-parametric speedup (`psize C ≤ 2^{n−k} ⇒` savings `2^k`).
* **`bounded_depth_williams_speedup`** — the headline: `depth C ≤ d`, `maxBase C ≤ B`, `B^{2^d} ≤ 2^{n−k} ⇒` SAT
  decided by `≤ 2^{n−k}` cells with Williams savings `≥ 2^k`.  For constant `d` and poly `B`, `B^{2^d} = 2^{O(log n)}`,
  so `k = n − O(log n)` — super-polynomial savings.

## Honest scope — *binary* depth

`depth` here is **binary** (`and`/`or` are 2-ary).  So "depth 2" means `≤ 4` leaves, "depth 3" `≤ 8` — small balanced
circuits.  The classic *unbounded-fan-in* depth-2 `ACC⁰` circuit (one `AND`/`OR` over poly-many `MOD`s) is a *deep*
binary chain, with large `2^depth` but only *linearly* many leaves; that regime is covered instead by the leaf-count
fragment (`restricted_acc0_quasipoly`, `O(log n)` leaves) and the footprint fragment (`…ACC0BoundedOverlapMOD`).  So
this is a genuine complementary fragment (balanced low-depth), not the full unbounded-fan-in model.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BoundedDepth

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.ACC0YBTSocket
open PallLean.Paper93.DeepMath.PathB.ACC0RestrictedYBT
open PallLean.Paper93.DeepMath.PathB.ACC0RestrictedWilliamsSpeedup
open PallLean.Paper93.DeepMath.PathB.SpeedupMargin

variable {n : ℕ}

/-- **A depth-`d` binary circuit has `≤ 2^d` leaves (proved).** -/
theorem leafCount_le_two_pow_depth (C : ACC0Circuit n) : leafCount C ≤ 2 ^ depth C := by
  induction C with
  | const _ => simp [leafCount, depth]
  | var _ => simp [leafCount, depth]
  | not c ih =>
      simp only [leafCount, depth]
      exact le_trans ih (Nat.pow_le_pow_right (by norm_num) (by omega))
  | and a b iha ihb =>
      simp only [leafCount, depth]
      have ha : leafCount a ≤ 2 ^ max (depth a) (depth b) :=
        le_trans iha (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hb : leafCount b ≤ 2 ^ max (depth a) (depth b) :=
        le_trans ihb (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc leafCount a + leafCount b
          ≤ 2 ^ max (depth a) (depth b) + 2 ^ max (depth a) (depth b) := Nat.add_le_add ha hb
        _ = 2 ^ (1 + max (depth a) (depth b)) := by rw [pow_add, pow_one]; ring
  | or a b iha ihb =>
      simp only [leafCount, depth]
      have ha : leafCount a ≤ 2 ^ max (depth a) (depth b) :=
        le_trans iha (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hb : leafCount b ≤ 2 ^ max (depth a) (depth b) :=
        le_trans ihb (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc leafCount a + leafCount b
          ≤ 2 ^ max (depth a) (depth b) + 2 ^ max (depth a) (depth b) := Nat.add_le_add ha hb
        _ = 2 ^ (1 + max (depth a) (depth b)) := by rw [pow_add, pow_one]; ring
  | mod _ _ _ => simp [leafCount, depth]

/-- **The exact size is polynomial at constant depth (proved): `psize C ≤ B^{2^d}`.** -/
theorem psize_le_of_depth (C : ACC0Circuit n) {d B : ℕ} (hd : depth C ≤ d) (hb : maxBase C ≤ B) :
    psize C ≤ B ^ (2 ^ d) := by
  calc psize C ≤ maxBase C ^ leafCount C := psize_le C
    _ ≤ B ^ leafCount C := Nat.pow_le_pow_left hb _
    _ ≤ B ^ (2 ^ d) := Nat.pow_le_pow_right (le_trans (one_le_maxBase C) hb)
        (le_trans (leafCount_le_two_pow_depth C) (Nat.pow_le_pow_right (by norm_num) hd))

/-- **Bounded-depth, poly-base circuits have an exact `SYM∘AND` form (proved).** -/
theorem bounded_depth_exact (C : ACC0Circuit n) {d B : ℕ}
    (hd : depth C ≤ d) (hb : maxBase C ≤ B) (hfit : B ^ (2 ^ d) < 2 ^ n) :
    HasExactSymAndForm C :=
  restricted_acc0_has_exact_symAnd C (lt_of_le_of_lt (psize_le_of_depth C hd hb) hfit)

/-- **The `psize`-parametric Williams speedup (proved): `psize C ≤ 2^{n−k} ⇒` savings `≥ 2^k`.** -/
theorem restricted_williams_speedup_of_psize (C : ACC0Circuit n) {k : ℕ} (hk : k ≤ n)
    (h : psize C ≤ 2 ^ (n - k)) :
    ∃ (cells : Finset ℕ) (dec : ℕ → Bool),
      (Satisfiable (eval C) ↔ ∃ c ∈ cells, dec c = true)
      ∧ cells.card ≤ 2 ^ (n - k) ∧ 2 ^ k * cells.card ≤ 2 ^ n := by
  obtain ⟨cells, dec, hsat, hcard⟩ := restricted_acc0_searchable C
  have hfit : cells.card ≤ 2 ^ (n - k) := le_trans hcard h
  exact ⟨cells, dec, hsat, hfit, savings_ge_of_work_le hk hfit⟩

/-- **The bounded-depth Williams speedup (proved).**  If `depth C ≤ d`, `maxBase C ≤ B`, and `B^{2^d} ≤ 2^{n−k}`,
then SAT of `eval C` is decided by `≤ 2^{n−k}` cells with Williams savings `≥ 2^k`.  For constant `d` and poly `B`,
`B^{2^d} = 2^{O(log n)}`, so `k = n − O(log n)` — super-polynomial savings. -/
theorem bounded_depth_williams_speedup (C : ACC0Circuit n) {d B k : ℕ}
    (hd : depth C ≤ d) (hb : maxBase C ≤ B) (hk : k ≤ n) (hfit : B ^ (2 ^ d) ≤ 2 ^ (n - k)) :
    ∃ (cells : Finset ℕ) (dec : ℕ → Bool),
      (Satisfiable (eval C) ↔ ∃ c ∈ cells, dec c = true)
      ∧ cells.card ≤ 2 ^ (n - k) ∧ 2 ^ k * cells.card ≤ 2 ^ n :=
  restricted_williams_speedup_of_psize C hk (le_trans (psize_le_of_depth C hd hb) hfit)

end PallLean.Paper93.DeepMath.PathB.ACC0BoundedDepth

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedDepth.leafCount_le_two_pow_depth
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedDepth.bounded_depth_exact
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedDepth.bounded_depth_williams_speedup
