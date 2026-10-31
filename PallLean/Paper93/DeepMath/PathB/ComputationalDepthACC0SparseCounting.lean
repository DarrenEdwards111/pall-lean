import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PolyToSymAnd

/-!
# The sparse-counting kernel — fast counting over a `SYM∘AND` representation

The Williams cash-out's open *counting* socket asks: given the sparse low-degree (`SYM∘AND`) representation of an
`ACC⁰` circuit, count satisfying assignments faster than `2ⁿ`.  This file proves the genuinely-provable algorithmic
kernel of that step: **a monomial-`AND` over support `S` is satisfied by exactly `2^{n−|S|}` inputs**, so the cube-sum
of any *sparse* `ZMod`/ring combination of monomial-`AND`s is a **closed form over its coefficients** — computable in
`#monomials` operations, with **no enumeration of the `2ⁿ` cube**.

```
∑_{x ∈ {0,1}ⁿ}  Σ_{S ∈ 𝒮} c_S · [∏_{i∈S} x_i]   =   Σ_{S ∈ 𝒮} c_S · 2^{n−|S|}.
```

This is exactly why the polynomial representation gives a counting speedup: when `|𝒮|` (the number of monomials) is
sub-`2ⁿ`, the right-hand side is computed without touching the cube.

## What is proved (clean axioms, no `sorry`)

* **`monoAND_cube_count`** — `|{x : monoAND S x}| = 2^{n−|S|}` (the subcube count).
* **`monoAND_cube_sum`** — the cube-sum of one monomial-`AND` indicator (over a comm. ring) is `2^{n−|S|}`.
* **`sparse_cube_sum`** — the cube-sum of a sparse combination `Σ_{S∈𝒮} c_S · [∏_{i∈S} x_i]` is `Σ_{S∈𝒮} c_S · 2^{n−|S|}`
  — the closed form computed from the coefficients alone.

## Honest scope — what this is and is not

This is the **counting primitive**, proved: a sparse polynomial's cube-sum is a coefficient-sum, not a `2ⁿ`-enumeration.
It is the kernel of Williams' fast `ACC⁰`-SAT counting.  It is **not** the full socket: turning the cube-*sum* into a
SAT *decision* needs the `SYM` (symmetric) top layer, and the bound `#monomials < 2ⁿ` needs the Beigel–Tarui
quasipolynomial `SYM∘AND` size for `ACC⁰` — both genuine algorithmic inputs left open.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SparseCounting

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd

variable {n : ℕ}

/-- **The subcube count (proved): a monomial-`AND` over `S` is satisfied by exactly `2^{n−|S|}` inputs.** -/
theorem monoAND_cube_count (S : Finset (Fin n)) :
    (Finset.univ.filter (fun x : Fin n → Bool => monoAND S x = true)).card = 2 ^ (n - S.card) := by
  have hset : (Finset.univ.filter (fun x : Fin n → Bool => monoAND S x = true))
      = Fintype.piFinset (fun i => if i ∈ S then ({true} : Finset Bool) else Finset.univ) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, monoAND,
      decide_eq_true_eq]
    constructor
    · intro h i
      by_cases hi : i ∈ S
      · simp [hi, h i hi]
      · simp [hi]
    · intro h i hi
      have hx := h i
      simp [hi] at hx
      exact hx
  rw [hset, Fintype.card_piFinset]
  have hprod : (∏ i : Fin n, (if i ∈ S then ({true} : Finset Bool) else Finset.univ).card)
      = ∏ i : Fin n, (if i ∈ S then 1 else 2) := by
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ S <;> simp [hi]
  rw [hprod, Finset.prod_ite (fun _ => (1 : ℕ)) (fun _ => (2 : ℕ)),
      Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  rw [show (Finset.univ.filter (fun i : Fin n => ¬ i ∈ S)) = Finset.univ \ S from by ext i; simp]
  rw [Finset.card_univ_diff, Fintype.card_fin]

/-- **The cube-sum of one monomial-`AND` indicator (proved): `∑_x [∏_{i∈S} x_i] = 2^{n−|S|}` (over any comm. ring).** -/
theorem monoAND_cube_sum {R : Type*} [CommRing R] (S : Finset (Fin n)) :
    (∑ x : Fin n → Bool, (if monoAND S x = true then (1 : R) else 0))
      = (2 : R) ^ (n - S.card) := by
  rw [Finset.sum_boole, monoAND_cube_count S]
  push_cast
  ring

/-- **The sparse-counting kernel (proved): the cube-sum of a sparse monomial-`AND` combination is a closed form over its
coefficients.**  `∑_x Σ_{S∈𝒮} c_S·[∏_{i∈S} x_i] = Σ_{S∈𝒮} c_S·2^{n−|S|}` — computable in `|𝒮|` operations, no
`2ⁿ`-enumeration. -/
theorem sparse_cube_sum {R : Type*} [CommRing R] (𝒮 : Finset (Finset (Fin n))) (c : Finset (Fin n) → R) :
    (∑ x : Fin n → Bool, ∑ S ∈ 𝒮, c S * (if monoAND S x = true then (1 : R) else 0))
      = ∑ S ∈ 𝒮, c S * (2 : R) ^ (n - S.card) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [← Finset.mul_sum, monoAND_cube_sum S]

end PallLean.Paper93.DeepMath.PathB.ACC0SparseCounting

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SparseCounting.monoAND_cube_count
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SparseCounting.monoAND_cube_sum
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SparseCounting.sparse_cube_sum
