import Mathlib

/-!
# The `MOD_p` gate is *exactly* degree `≤ |F|−1` over any finite field `F` (Fermat) — the prime-power-field form

`…ACC0ModPExact` proved `MOD_p` is exactly `1 − (∑ X_i)^{p−1}` over `F_p` (degree `p−1`), via Fermat's little
theorem.  Its docstring *asserts* that "prime-powers reduce to `F_{p^k}` by the same Fermat argument" but proves only
the `F_p` case.  This file proves that generalization: over **any** finite field `F` (order `q = p^k`), the
count-`≡ 0`-in-`F` indicator is exactly

```
[∑_{i∈S} x_i = 0  in F]  =  1 − (∑_{i∈S} x_i)^{q−1} ,        q = |F|,
```

since `a^{q−1} = 1` for `a ≠ 0` and `0^{q−1} = 0` in `F` (`FiniteField.pow_card_sub_one_eq_one`).  As the cell value
`∑ x_i` reduces mod the characteristic `p`, this computes `MOD_p` (count `≡ 0 mod p`) *exactly*, over the
prime-power field `F_{p^k}`, with degree `q − 1`.  This is the extension-field ingredient the `q`-ary Razborov–
Smolensky machinery uses (characters over `F_{p^ℓ}`); it is the genuine **prime-power-field** exact representation
the `F_p` file asserted.

## What is proved (clean axioms, no `sorry`)

* `modFieldPoly` / `modFieldBool` — the `F`-polynomial `1 − (∑ X_i)^{|F|−1}` and the gate.
* `modFieldPoly_totalDegree_le` — total degree `≤ |F| − 1`.
* `modField_exact_eval` — the polynomial computes the gate *exactly* (by the finite-field Fermat).

## Honest scope

This is the prime-power-**field** (`F_{p^k}`) exact form of the **`MOD_p`** gate — the non-barriered direction.  It
does **not** give `MOD_{p^e}` (prime-power **modulus**, count `≡ 0 mod p^e`), which is *not* exact-low-degree over
`F_p`, nor does it cross the composite-`MOD` barrier (no single field makes `MOD_{p·q}` low-degree).  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact

open MvPolynomial

variable {n : ℕ} {F : Type*} [Field F] [Fintype F]

/-- `{0,1} → F`. -/
def boolToF (b : Bool) : F := if b then 1 else 0

/-- The `F` **`MOD_p` polynomial** `1 − (∑_{i∈S} X_i)^{|F|−1}` over a finite field `F`. -/
noncomputable def modFieldPoly (S : Finset (Fin n)) : MvPolynomial (Fin n) F :=
  1 - (∑ i ∈ S, X i) ^ (Fintype.card F - 1)

/-- **Total degree `≤ |F| − 1` (proved).** -/
theorem modFieldPoly_totalDegree_le (S : Finset (Fin n)) :
    (modFieldPoly (F := F) S).totalDegree ≤ Fintype.card F - 1 := by
  unfold modFieldPoly
  refine le_trans (totalDegree_sub _ _) ?_
  rw [totalDegree_one]
  refine max_le (Nat.zero_le _) ?_
  refine le_trans (totalDegree_pow _ _) ?_
  have hlin : (∑ i ∈ S, (X i : MvPolynomial (Fin n) F)).totalDegree ≤ 1 := by
    apply totalDegree_finsetSum_le
    intro i _
    exact le_of_eq (totalDegree_X i)
  calc (Fintype.card F - 1) * (∑ i ∈ S, (X i : MvPolynomial (Fin n) F)).totalDegree
      ≤ (Fintype.card F - 1) * 1 := Nat.mul_le_mul_left _ hlin
    _ = Fintype.card F - 1 := mul_one _

variable [DecidableEq F]

/-- The gate: the support sum is `0` in `F` (i.e. the count is `≡ 0 mod char F = p`). -/
def modFieldBool (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide ((∑ i ∈ S, boolToF (x i) : F) = 0)

/-- **`MOD_p` computed *exactly* by the degree-`(|F|−1)` polynomial over `F` (proved), via the finite-field
Fermat `a^{|F|−1} = 1`.** -/
theorem modField_exact_eval (x : Fin n → Bool) (S : Finset (Fin n)) :
    eval (fun i => if x i then (1 : F) else 0) (modFieldPoly (F := F) S)
      = (boolToF (modFieldBool (F := F) S x) : F) := by
  unfold modFieldPoly modFieldBool boolToF
  rw [eval_sub, map_one, map_pow, eval_sum]
  simp only [eval_X]
  have hp1 : Fintype.card F - 1 ≠ 0 := by have := Fintype.one_lt_card (α := F); omega
  set s := ∑ i ∈ S, (if x i then (1 : F) else 0) with hsdef
  by_cases hs : s = 0
  · rw [hs, zero_pow hp1, sub_zero]
    simp
  · rw [FiniteField.pow_card_sub_one_eq_one s hs, sub_self]
    simp [hs]

end PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact.modField_exact_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact.modFieldPoly_totalDegree_le
