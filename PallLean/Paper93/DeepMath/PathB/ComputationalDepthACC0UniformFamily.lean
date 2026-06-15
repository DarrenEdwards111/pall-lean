import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BoundedDepth

/-!
# Uniformity bookkeeping: the restricted constructions lift to uniform `ACC⁰` families

The realization split (`…ACC0WilliamsRealizationSplit`) parks "the per-`n` algorithms form a uniform family" in the
abstract `UniformitySocket`.  This file makes the *structural* half of that concrete: a **uniform `ACC⁰` family** is a
single Lean function `F : (n : ℕ) → ACC0Circuit n`, and the exact-`SYM∘AND` / count-cell constructions lift from a
single circuit to a whole family with a **single bound function** of `n` — no per-`n` cleverness, so the translation
is manifestly uniform.

The point: every restricted theorem (`…ACC0RestrictedYBT`, `…ACC0BoundedOverlapMOD`, `…ACC0BoundedDepth`,
`…ACC0RestrictedWilliamsSpeedup`) is applied *pointwise* at each `n` by one structural recursion, so a *uniformly*
bounded family (bound `b : ℕ → ℕ`) yields a *uniform* family of exact forms / speedups.

## What is proved (clean axioms, no `sorry`)

* `ACC0Family`, and the uniform-bound predicates `UniformFootprint` / `UniformLeaf` / `UniformBase` / `UniformDepth`.
* **`uniform_symAndSize_bound`** — the *uniform SYM∘AND translation*: `symAndSize (F n) + 1 ≤ 2^(b n)`, i.e. the exact
  form's size is bounded by a single function of `n`.
* **`uniform_exact_of_footprint`** / **`uniform_exact_of_depth`** — the *whole family* has exact `SYM∘AND` forms when
  the footprint (resp. depth+base) is uniformly bounded below `2^n`.
* **`uniform_williams_speedup`** / **`uniform_depth_williams_speedup`** — the *whole family* gets the count-cell
  Williams speedup with a uniform savings exponent `k : ℕ → ℕ`.

## Honest scope — structural uniformity, not TM-uniformity

A family here is a single total function `(n : ℕ) → ACC0Circuit n`, and every bound is a single function `ℕ → ℕ`, so
the construction is *structurally* uniform (one recursion, all `n`).  This discharges the structural half of
`UniformitySocket`.  It does **not** define Turing machines, so it does **not** establish full *machine* uniformity
(a single poly-time TM emitting the count cells) — that remains the socket's open content (`…ACC0WilliamsRealization
Split`, `EncodingSocket`/`CostBridgeSocket`).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniformFamily

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.ACC0YBTSocket
open PallLean.Paper93.DeepMath.PathB.ACC0YBTExactCompose
open PallLean.Paper93.DeepMath.PathB.ACC0RestrictedYBT
open PallLean.Paper93.DeepMath.PathB.ACC0BoundedOverlapMOD
open PallLean.Paper93.DeepMath.PathB.ACC0RestrictedWilliamsSpeedup
open PallLean.Paper93.DeepMath.PathB.ACC0BoundedDepth

/-- A **uniform `ACC⁰` family**: one circuit per input length, given by a single total function. -/
def ACC0Family : Type := (n : ℕ) → ACC0Circuit n

/-- The family's support footprint is bounded by a single function `b : ℕ → ℕ`. -/
def UniformFootprint (F : ACC0Family) (b : ℕ → ℕ) : Prop := ∀ n, baseSum (F n) ≤ b n

/-- The family's leaf count is bounded by `b`. -/
def UniformLeaf (F : ACC0Family) (b : ℕ → ℕ) : Prop := ∀ n, leafCount (F n) ≤ b n

/-- The family's leaf base size is bounded by `b`. -/
def UniformBase (F : ACC0Family) (b : ℕ → ℕ) : Prop := ∀ n, maxBase (F n) ≤ b n

/-- The family's (binary) depth is bounded by `b`. -/
def UniformDepth (F : ACC0Family) (b : ℕ → ℕ) : Prop := ∀ n, depth (F n) ≤ b n

/-- **The uniform `SYM∘AND` translation (proved): the exact-form size is bounded by a single function of `n`.**  If
the footprint is uniformly `≤ b n`, then `symAndSize (F n) + 1 ≤ 2^(b n)` for every `n`. -/
theorem uniform_symAndSize_bound (F : ACC0Family) (b : ℕ → ℕ) (hF : UniformFootprint F b) (n : ℕ) :
    symAndSize (F n) + 1 ≤ 2 ^ b n := by
  rw [symAndSize_succ_eq_psize]
  exact le_trans (psize_le_two_pow_baseSum (F n)) (Nat.pow_le_pow_right (by norm_num) (hF n))

/-- **Uniform exact form by footprint (proved): the whole family has exact `SYM∘AND` forms.**  If the footprint is
uniformly `< n`, every member `F n` has an exact `SYM∘AND` form. -/
theorem uniform_exact_of_footprint (F : ACC0Family) (b : ℕ → ℕ) (hF : UniformFootprint F b)
    (hb : ∀ n, b n < n) (n : ℕ) : HasExactSymAndForm (F n) :=
  acc0_exact_of_baseSum_lt (F n) (lt_of_le_of_lt (hF n) (hb n))

/-- **Uniform exact form by depth (proved).**  If the depth is uniformly `≤ d n`, the base uniformly `≤ B n`, and
`(B n)^{2^{d n}} < 2^n`, every member `F n` has an exact `SYM∘AND` form. -/
theorem uniform_exact_of_depth (F : ACC0Family) (d B : ℕ → ℕ)
    (hD : UniformDepth F d) (hB : UniformBase F B) (hfit : ∀ n, (B n) ^ (2 ^ d n) < 2 ^ n) (n : ℕ) :
    HasExactSymAndForm (F n) :=
  bounded_depth_exact (F n) (hD n) (hB n) (hfit n)

/-- **The uniform restricted Williams speedup by footprint (proved).**  If the footprint is uniformly `≤ b n` and
`b n + k n ≤ n`, then for *every* `n`, `F n`'s SAT is decided by a count-cell search of `≤ 2^(n − k n)` cells with
Williams savings `≥ 2^(k n)` — a single (uniform) speedup family with savings exponent `k : ℕ → ℕ`. -/
theorem uniform_williams_speedup (F : ACC0Family) (b k : ℕ → ℕ) (hF : UniformFootprint F b)
    (hk : ∀ n, k n ≤ n) (hfit : ∀ n, b n + k n ≤ n) (n : ℕ) :
    ∃ (cells : Finset ℕ) (dec : ℕ → Bool),
      (Satisfiable (eval (F n)) ↔ ∃ c ∈ cells, dec c = true)
      ∧ cells.card ≤ 2 ^ (n - k n) ∧ 2 ^ (k n) * cells.card ≤ 2 ^ n :=
  restricted_williams_speedup (F n) (hk n)
    (le_trans (Nat.add_le_add_right (hF n) (k n)) (hfit n))

/-- **The uniform restricted Williams speedup by depth (proved).**  Bounded depth + base uniformly, with
`(B n)^{2^{d n}} ≤ 2^(n − k n)`, gives the count-cell speedup with savings `≥ 2^(k n)` for every `n`. -/
theorem uniform_depth_williams_speedup (F : ACC0Family) (d B k : ℕ → ℕ)
    (hD : UniformDepth F d) (hB : UniformBase F B) (hk : ∀ n, k n ≤ n)
    (hfit : ∀ n, (B n) ^ (2 ^ d n) ≤ 2 ^ (n - k n)) (n : ℕ) :
    ∃ (cells : Finset ℕ) (dec : ℕ → Bool),
      (Satisfiable (eval (F n)) ↔ ∃ c ∈ cells, dec c = true)
      ∧ cells.card ≤ 2 ^ (n - k n) ∧ 2 ^ (k n) * cells.card ≤ 2 ^ n :=
  bounded_depth_williams_speedup (F n) (hD n) (hB n) (hk n) (hfit n)

end PallLean.Paper93.DeepMath.PathB.ACC0UniformFamily

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniformFamily.uniform_symAndSize_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniformFamily.uniform_exact_of_footprint
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniformFamily.uniform_williams_speedup
