import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3DimensionCount

/-!
# Beigel–Tarui sparsity — the `SYM∘AND` monomial count is quasipolynomial

The counting socket's only remaining input is the Beigel–Tarui bound: an `ACC⁰` circuit has a `SYM∘AND` (low-degree)
representation with **quasipolynomially** many monomials.  That theorem has two halves:

1. a **degree** bound `D` (a degree-`D` representation exists), and
2. a **count** bound (the number of degree-`≤D` monomials is sub-`2ⁿ` / quasipolynomial).

This file proves the **count** half cleanly: the number of degree-`≤D` monomials is
`∑_{i≤D} C(n,i) ≤ (n+1)^D`, which is **quasipolynomial in `n`** when `D` is polylogarithmic.  Together with the
degree half it gives the `SYM∘AND` sparsity.

```
#monomials(degree ≤ D)  =  ∑_{i=0}^{D} C(n,i)  ≤  (n+1)^D .
```

## What is proved (clean axioms, no `sorry`)

* **`sum_choose_le_quasipoly`** — `∑_{i≤D} C(n,i) ≤ (n+1)^D` (via `Nat.choose_le_pow` and the binomial theorem).
* **`beigelTarui_monomial_count_le`** — the degree-`≤D` monomial set `lowDegMonomials n D` has `≤ (n+1)^D` elements:
  a degree-`≤D` `SYM∘AND` representation is `(n+1)^D`-sparse.

## Honest scope — the count half only; the degree half splits AC⁰[p] (done) vs composite ACC⁰ (deep open)

This is the **combinatorial sparsity** half — proved.  The **degree** half is:
* for `AC⁰[p]` (`p` prime): *proved* in the RS layer (`…Layer3DegreeComposition.toApprox_totalDegree_le`,
  `D = ((p-1)·t)^depth`), so `AC⁰[p]` circuits are `(n+1)^{((p-1)t)^depth}`-sparse — quasipolynomial for constant
  depth/`p` and `t = polylog`;
* for *general* (composite-modulus) `ACC⁰`: the **deep open** Yao / Beigel–Tarui construction (the symmetric
  representation over `ℤ`), which is **not** established here — it is the genuine `NEXP`-strength frontier (Williams'
  algorithmic method), per `ACC_ROADMAP.md`.

So this closes the *count* input to the counting socket and pins the *degree* input as the one remaining deep theorem.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BeigelTaruiSparsity

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.Layer3

/-- **The quasipolynomial monomial-count bound (proved): `∑_{i≤D} C(n,i) ≤ (n+1)^D`.** -/
theorem sum_choose_le_quasipoly (n D : ℕ) :
    ∑ i ∈ Finset.range (D + 1), n.choose i ≤ (n + 1) ^ D := by
  calc ∑ i ∈ Finset.range (D + 1), n.choose i
      ≤ ∑ i ∈ Finset.range (D + 1), n ^ i * D.choose i := by
        apply Finset.sum_le_sum
        intro i hi
        calc n.choose i ≤ n ^ i := Nat.choose_le_pow n i
          _ = n ^ i * 1 := (mul_one _).symm
          _ ≤ n ^ i * D.choose i := by
              gcongr
              exact Nat.choose_pos (Finset.mem_range_succ_iff.mp hi)
    _ = (n + 1) ^ D := by
        rw [add_pow]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp [one_pow, mul_one, Nat.cast_id]

/-- **Beigel–Tarui sparsity, count half (proved): the degree-`≤D` monomial set is `(n+1)^D`-sparse.**  A degree-`≤D`
`SYM∘AND` representation uses at most `(n+1)^D` monomial-`AND` gates — quasipolynomial for `D = polylog`. -/
theorem beigelTarui_monomial_count_le (n D : ℕ) :
    (lowDegMonomials n D).card ≤ (n + 1) ^ D := by
  rw [lowDegMonomials_card]
  exact sum_choose_le_quasipoly n D

end PallLean.Paper93.DeepMath.PathB.ACC0BeigelTaruiSparsity

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BeigelTaruiSparsity.sum_choose_le_quasipoly
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BeigelTaruiSparsity.beigelTarui_monomial_count_le
