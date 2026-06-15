import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0YBTExactCompose

/-!
# Restricted YBT: bounded-leaf `ACC⁰` fragments have an exact *quasipolynomial* `SYM∘AND` form

`…ACC0YBTExactCompose` proved every `ACC0Circuit` has an *exact* `SYM∘AND` form of size `symAndSize C`, with the
**size** the only remaining wall (`symAndSize` is multiplicative at `AND`/`OR`, hence exponential in general).  This
file proves the size is *quasipolynomial* — hence the socket `HasExactSymAndForm` genuinely fires — on the natural
**restricted** fragments: circuits with a bounded number of leaves and bounded `MOD`-support.

The engine is a clean structural identity: writing `psize C := symAndSize C + 1`,

```
psize (const) = 1     psize (var) = 2     psize (not c) = psize c
psize (and a b) = psize a · psize b       psize (or a b) = psize a · psize b
psize (mod q S t) = |S| + 1
```

so **`symAndSize C + 1` is exactly the product of the leaves' base sizes** (`symAndSize_succ_eq_psize`).  A product
of `leafCount C` factors each `≤ maxBase C` is `≤ maxBase C ^ leafCount C` (`psize_le`), which is *quasipolynomial*
once `leafCount = O(log n)` and `maxBase = poly(n)` — well below `2^n`.

## What is proved (clean axioms, no `sorry`)

* `psize`/`leafCount`/`maxBase` and **`symAndSize_succ_eq_psize`** — the multiplicative identity.
* **`psize_le`** — `psize C ≤ maxBase C ^ leafCount C` (product of `leafCount` factors `≤ maxBase`).
* **`restricted_acc0_has_exact_symAnd`** — `psize C < 2^n ⇒ HasExactSymAndForm C` (the socket fires when the exact
  size fits).
* **`restricted_acc0_quasipoly`** — the headline: `leafCount C ≤ ℓ`, `maxBase C ≤ B`, `B^ℓ < 2^n ⇒
  HasExactSymAndForm C`.  For `ℓ = O(log n)`, `B = poly(n)`, `B^ℓ = 2^{O(log²n)}` (quasipoly) `< 2^n`, so
  **bounded-leaf, poly-`MOD`-support `ACC⁰` has an exact quasipolynomial `SYM∘AND` form** — genuine restricted YBT.

## Honest scope

This is *restricted* YBT: the bound `maxBase^leafCount` is quasipolynomial only when the **leaf count is
logarithmic** (a depth-2 `AND`/`OR` of `O(log n)` `MOD`/literal gates, or any `O(log n)`-leaf circuit).  Full `ACC⁰`
(poly-many leaves) gives `B^{poly} = 2^{poly}` — exponential, the genuine wall, unchanged.  This proves a real
fragment, not the full theorem; it does not pretend to.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RestrictedYBT

open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.ACC0YBTSocket
open PallLean.Paper93.DeepMath.PathB.ACC0YBTExactCompose

variable {n : ℕ}

/-- `psize C := symAndSize C + 1` — the *multiplicative* size: the product of the leaves' base sizes. -/
def psize : ACC0Circuit n → ℕ
  | .const _ => 1
  | .var _ => 2
  | .not c => psize c
  | .and a b => psize a * psize b
  | .or a b => psize a * psize b
  | .mod _ S _ => S.card + 1

/-- The number of leaves (`const`/`var`/`mod`) of the circuit. -/
def leafCount : ACC0Circuit n → ℕ
  | .const _ => 1
  | .var _ => 1
  | .not c => leafCount c
  | .and a b => leafCount a + leafCount b
  | .or a b => leafCount a + leafCount b
  | .mod _ _ _ => 1

/-- The maximum leaf base size in the circuit. -/
def maxBase : ACC0Circuit n → ℕ
  | .const _ => 1
  | .var _ => 2
  | .not c => maxBase c
  | .and a b => max (maxBase a) (maxBase b)
  | .or a b => max (maxBase a) (maxBase b)
  | .mod _ S _ => S.card + 1

/-- **The multiplicative identity (proved): `symAndSize C + 1` is the product of leaf base sizes.** -/
theorem symAndSize_succ_eq_psize (C : ACC0Circuit n) : symAndSize C + 1 = psize C := by
  induction C with
  | const b => rfl
  | var i => rfl
  | not c ih => simpa only [symAndSize, psize] using ih
  | and a b iha ihb => simp only [symAndSize, psize]; rw [← iha, ← ihb]; ring
  | or a b iha ihb => simp only [symAndSize, psize]; rw [← iha, ← ihb]; ring
  | mod q S t => rfl

/-- **`1 ≤ maxBase C` (proved).** -/
theorem one_le_maxBase (C : ACC0Circuit n) : 1 ≤ maxBase C := by
  induction C with
  | const _ => exact le_refl 1
  | var _ => exact one_le_two
  | not c ih => exact ih
  | and a b iha _ => exact le_trans iha (le_max_left _ _)
  | or a b iha _ => exact le_trans iha (le_max_left _ _)
  | mod _ S _ => exact Nat.le_add_left 1 S.card

/-- **The exact size is bounded by a product (proved): `psize C ≤ maxBase C ^ leafCount C`.** -/
theorem psize_le (C : ACC0Circuit n) : psize C ≤ maxBase C ^ leafCount C := by
  induction C with
  | const _ => simp [psize, maxBase, leafCount]
  | var _ => simp [psize, maxBase, leafCount]
  | not c ih => simpa only [psize, maxBase, leafCount] using ih
  | and a b iha ihb =>
      simp only [psize, maxBase, leafCount]
      calc psize a * psize b
          ≤ maxBase a ^ leafCount a * maxBase b ^ leafCount b := Nat.mul_le_mul iha ihb
        _ ≤ max (maxBase a) (maxBase b) ^ leafCount a * max (maxBase a) (maxBase b) ^ leafCount b :=
            Nat.mul_le_mul (Nat.pow_le_pow_left (le_max_left _ _) _)
              (Nat.pow_le_pow_left (le_max_right _ _) _)
        _ = max (maxBase a) (maxBase b) ^ (leafCount a + leafCount b) := by rw [pow_add]
  | or a b iha ihb =>
      simp only [psize, maxBase, leafCount]
      calc psize a * psize b
          ≤ maxBase a ^ leafCount a * maxBase b ^ leafCount b := Nat.mul_le_mul iha ihb
        _ ≤ max (maxBase a) (maxBase b) ^ leafCount a * max (maxBase a) (maxBase b) ^ leafCount b :=
            Nat.mul_le_mul (Nat.pow_le_pow_left (le_max_left _ _) _)
              (Nat.pow_le_pow_left (le_max_right _ _) _)
        _ = max (maxBase a) (maxBase b) ^ (leafCount a + leafCount b) := by rw [pow_add]
  | mod _ S _ => simp [psize, maxBase, leafCount]

/-- **The socket fires when the exact size fits (proved): `psize C < 2^n ⇒ HasExactSymAndForm C`.** -/
theorem restricted_acc0_has_exact_symAnd (C : ACC0Circuit n) (h : psize C < 2 ^ n) :
    HasExactSymAndForm C :=
  acc0circuit_hasExactSymAndForm C (by rw [symAndSize_succ_eq_psize]; exact h)

/-- **Restricted YBT (proved): bounded-leaf, bounded-base `ACC⁰` has an exact (quasipolynomial) `SYM∘AND` form.**
If `leafCount C ≤ ℓ`, `maxBase C ≤ B`, and `B^ℓ < 2^n`, then `C` has an exact `SYM∘AND` form.  For `ℓ = O(log n)` and
`B = poly(n)` this is `B^ℓ = 2^{O(log²n)}` (quasipolynomial) `< 2^n` — the genuine restricted Beigel–Tarui. -/
theorem restricted_acc0_quasipoly (C : ACC0Circuit n) {ℓ B : ℕ}
    (hlc : leafCount C ≤ ℓ) (hb : maxBase C ≤ B) (hfit : B ^ ℓ < 2 ^ n) :
    HasExactSymAndForm C := by
  apply restricted_acc0_has_exact_symAnd
  calc psize C ≤ maxBase C ^ leafCount C := psize_le C
    _ ≤ B ^ leafCount C := Nat.pow_le_pow_left hb _
    _ ≤ B ^ ℓ := Nat.pow_le_pow_right (le_trans (one_le_maxBase C) hb) hlc
    _ < 2 ^ n := hfit

end PallLean.Paper93.DeepMath.PathB.ACC0RestrictedYBT

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RestrictedYBT.symAndSize_succ_eq_psize
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RestrictedYBT.psize_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RestrictedYBT.restricted_acc0_quasipoly
