import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBeigelTaruiBase

/-!
# Beigel–Tarui, rung 9: the `SYM∘AND` fold — a polynomial is a weighted sum of ANDs

The polynomial method (rungs 1–8) produces a *low-degree polynomial* over `F_p` that (approximately) computes an `ACC⁰`
circuit.  The Beigel–Tarui normal form turns that polynomial into a `SYM∘AND`.  This file proves the **`∘AND` half** of
that fold: on Boolean inputs, *any* polynomial equals a weighted sum of its monomials, and each monomial is an **AND**
of its variables — so a degree-`D` polynomial is a weighted sum of ANDs, one per monomial.

  `embed_pow` — **PROVED**: `(embed b)^m = embed b` for `m ≥ 1` (Boolean idempotence collapses monomial exponents).
  `prod_embed` — **PROVED**: `∏_{i∈S} embed(xᵢ)` is `1` if every `xᵢ` (`i∈S`) is `true`, else `0` — the monomial `∏_{i∈S}
        Xᵢ` on Boolean inputs is exactly the **AND** of `{xᵢ : i∈S}`.
  `eval_as_sum_of_ands` — **PROVED**: `eval (embed∘x) P = ∑_{d∈support} coeff(d) · ∏_{i∈d.support} embed(xᵢ)` — the
        polynomial's Boolean value is a weighted sum over its monomials.
  `eval_as_weighted_ands` — **PROVED, the `∘AND` fold**: `eval (embed∘x) P = ∑_{d∈support} coeff(d) · [AND over d's
        variables]` — a weighted sum of AND-gates, one per monomial (so `#ANDs = #support`).

## Honest scope

This is the `∘AND` half of the `SYM∘AND` fold: a polynomial on Boolean inputs *is* a weighted sum of ANDs, one per
monomial (bounded by the number of low-degree monomials `≤ (n+1)^D` — the repo's `beigelTarui_monomial_count_le`).  What
remains is the `SYM` top: that the whole weighted sum is a **symmetric** function of the *count* of satisfied ANDs.  For
`0/1` coefficients this is immediate (the value is the count); for general `F_p` coefficients it is Toda's symmetric
encoding — grouping monomials by coefficient and reading the counts mod `p` (the repo's symmetric count layer
`symEval`/`gateCount` is the target).  Discharging that symmetric fold, and instantiating on a concrete `ACC⁰` circuit
(via rungs 6–8's low-degree approximation), are the remaining Beigel–Tarui content.  This file supplies the `∘AND`
half.  Nothing here is the Beigel–Tarui reduction, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase

open MvPolynomial
open scoped Classical

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **Boolean idempotence under powers (proved)**: `(embed b)^m = embed b` for `m ≥ 1` — monomial exponents collapse on
Boolean inputs. -/
theorem embed_pow (b : Bool) (m : ℕ) (hm : 1 ≤ m) : (embed b : R) ^ m = embed b := by
  cases b <;> simp [embed, zero_pow (by omega : m ≠ 0)]

/-- **A monomial is an AND (proved)**: `∏_{i∈S} embed(xᵢ)` is `1` iff every `xᵢ` (`i∈S`) is `true` — the monomial
`∏_{i∈S} Xᵢ` on Boolean inputs is the AND of `{xᵢ : i∈S}`. -/
theorem prod_embed (S : Finset (Fin n)) (x : Fin n → Bool) :
    ∏ i ∈ S, (embed (x i) : R) = if (∀ i ∈ S, x i = true) then 1 else 0 := by
  by_cases h : ∀ i ∈ S, x i = true
  · rw [if_pos h]
    exact Finset.prod_eq_one (fun i hi => by rw [h i hi]; simp [embed])
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hi, hxi⟩ := h
    exact Finset.prod_eq_zero hi (by rw [embed, if_neg hxi])

/-- **The monomial expansion (proved)**: on Boolean inputs, a polynomial equals the weighted sum over its monomials of
`coeff · ∏ embed`. -/
theorem eval_as_sum_of_ands (P : MvPolynomial (Fin n) R) (x : Fin n → Bool) :
    (eval (fun i => embed (x i))) P
      = ∑ d ∈ P.support, P.coeff d * ∏ i ∈ d.support, (embed (x i) : R) := by
  rw [eval_eq]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  congr 1
  refine Finset.prod_congr rfl (fun i hi => ?_)
  exact embed_pow (x i) (d i) (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))

/-- **The `∘AND` fold (proved)**: on Boolean inputs, a polynomial is a weighted sum of ANDs — one AND per monomial, its
value the AND of that monomial's variables.  Hence a degree-`D` polynomial is a weighted sum of `#support` ANDs. -/
theorem eval_as_weighted_ands (P : MvPolynomial (Fin n) R) (x : Fin n → Bool) :
    (eval (fun i => embed (x i))) P
      = ∑ d ∈ P.support, P.coeff d * (if (∀ i ∈ d.support, x i = true) then 1 else 0) := by
  rw [eval_as_sum_of_ands]
  exact Finset.sum_congr rfl (fun d _ => by rw [prod_embed])

end PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase

#print axioms PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase.eval_as_sum_of_ands
#print axioms PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase.eval_as_weighted_ands
