import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBeigelTaruiSymAndFold

/-!
# Beigel–Tarui, rung 10: the `SYM` top — the AND-count is the symmetric statistic

Rung 9 folded a polynomial into a weighted sum of ANDs, one per monomial.  The `SYM∘AND` normal form's top gate is
**symmetric**: it reads only the *count* of satisfied ANDs.  This file proves that top for the base case — **unit
coefficients** — where the fold is exactly the count of satisfied ANDs, a manifestly symmetric statistic (`h(count)`,
the `symEval` shape of the repo's count layer).

  `andSat` — the satisfied AND-monomials of a polynomial at an input (a `Finset`, hence order-independent).
  `count_ands_eq` — **PROVED**: the unit-coefficient fold (over `ℕ`) is the number of satisfied ANDs.
  `uniform_fold_eq_symmetric` — **PROVED, the `SYM` top (base case)**: over any ring, the unit-coefficient fold equals
        `↑(#satisfied ANDs)` — a function `h(count)` of the count, the symmetric `SYM∘AND` shape.
  `andSat_card_le` — the number of satisfied ANDs is at most the number of monomials.

## Honest scope

This is the `SYM` top for **unit coefficients**: the fold *is* the count of satisfied ANDs, so it is `h(count)` with
`h = Nat.cast` — a symmetric function of the count, exactly the `SYM∘AND` form (feeding the repo's `symEval`/`gateCount`
count layer, which `…NFrameFastSAT.symAndModel` turns into a `FastSATModel` for the Williams route).  What remains is
the general case: for arbitrary `F_p` coefficients the fold is `∑_{satisfied d} coeff(d)`, which is *not* a function of
the bare count — Toda's symmetric encoding groups monomials by coefficient and reads the counts mod `p` to recover a
single symmetric top.  Discharging that general encoding, and instantiating the whole pipeline (rungs 1–10) on a concrete
`ACC⁰` circuit, are the remaining Beigel–Tarui content.  With this rung the polynomial-method pipeline is complete for
the unit-coefficient case: `ACC⁰`-shaped formula → low-degree polynomial → weighted sum of ANDs → symmetric function of
the AND-count.  Nothing here is the Beigel–Tarui reduction, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase

open MvPolynomial
open scoped Classical

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The satisfied AND-monomials of `P` at input `x` — a `Finset`, so the count below is order-independent. -/
def andSat (P : MvPolynomial (Fin n) R) (x : Fin n → Bool) : Finset (Fin n →₀ ℕ) :=
  P.support.filter (fun d => ∀ i ∈ d.support, x i = true)

/-- **The unit-coefficient fold is the AND-count (proved, over `ℕ`)**. -/
theorem count_ands_eq (P : MvPolynomial (Fin n) R) (x : Fin n → Bool) :
    ∑ d ∈ P.support, (if (∀ i ∈ d.support, x i = true) then (1 : ℕ) else 0) = (andSat P x).card := by
  rw [andSat, Finset.card_filter]

/-- **The `SYM` top, base case (proved)**: the unit-coefficient fold equals `↑(#satisfied ANDs)` — a function `h(count)`
of the count of satisfied ANDs, the symmetric `SYM∘AND` shape. -/
theorem uniform_fold_eq_symmetric (P : MvPolynomial (Fin n) R) (x : Fin n → Bool) :
    ∑ d ∈ P.support, (if (∀ i ∈ d.support, x i = true) then (1 : R) else 0)
      = ((andSat P x).card : R) := by
  rw [andSat, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  split_ifs <;> simp

/-- The number of satisfied ANDs is at most the number of monomials. -/
theorem andSat_card_le (P : MvPolynomial (Fin n) R) (x : Fin n → Bool) :
    (andSat P x).card ≤ P.support.card := Finset.card_filter_le _ _

end PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase

#print axioms PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase.count_ands_eq
#print axioms PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase.uniform_fold_eq_symmetric
