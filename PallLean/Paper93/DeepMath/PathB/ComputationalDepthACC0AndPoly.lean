import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PolyToSymAnd

/-!
# Brick (AND) — the `AND` gate as an exact polynomial `∏ Xᵢ` (proved)

The exact polynomial representation of an `AND` gate over any `CommSemiring`: `andPoly S = ∏_{i∈S} Xᵢ` evaluates to the `AND`
of the bits in `S` on Boolean inputs, with total degree `≤ |S|` (the fan-in).  This is the *exact* `AND`/`OR` representation
(`OR` via De Morgan): a single `AND`-term, faithful, but of degree = fan-in.

That degree is exactly the point: for a *single* gate, fan-in degree is fine (one `AND`-term).  But under **composition**
(an `AND` feeding into higher gates), the exact degree multiplies as `fan-in^depth`, which is *not* polylog — so general YBT
needs the **approximate** Razborov–Smolensky probabilistic polynomial for `AND`/`OR` (low degree with small error), a
genuinely different method.  This brick is the honest exact part; the approximate part is open and **not** faked.

## What is proved (clean axioms, no `sorry`)

* **`andPoly S`** — the `AND`-gate polynomial `∏_{i∈S} Xᵢ`.
* **`andPoly_eval`** (PROVED) — `eval (fun i => if x i then 1 else 0) (andPoly S) = if (∀ i ∈ S, x i = true) then 1 else 0`
  — exactly the `AND` of the bits in `S`.
* **`andPoly_totalDegree_le`** (PROVED) — `(andPoly S).totalDegree ≤ S.card` (degree at most the fan-in).

## Honest scope

This is the **exact** `AND` representation (degree = fan-in).  It does **not** build the *approximate* low-degree `AND`/`OR`
polynomial needed for composition, cross-prime nesting, prime-power composition, nor `composite_BT_degree`.  General YBT
remains open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0AndPoly

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)

variable {n : ℕ} {R : Type*} [CommSemiring R]

/-- **The `AND`-gate polynomial:** `∏_{i∈S} Xᵢ`. -/
noncomputable def andPoly (S : Finset (Fin n)) : MvPolynomial (Fin n) R := ∏ i ∈ S, X i

/-- **`andPoly` evaluates to the `AND` of the bits in `S` (PROVED).** -/
theorem andPoly_eval (S : Finset (Fin n)) (x : Fin n → Bool) :
    eval (fun i => if x i then (1 : R) else 0) (andPoly S) = if (∀ i ∈ S, x i = true) then 1 else 0 := by
  rw [andPoly, map_prod]
  simp only [eval_X]
  by_cases h : ∀ i ∈ S, x i = true
  · rw [if_pos h]
    exact Finset.prod_eq_one (fun i hi => if_pos (h i hi))
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hiS, hi⟩ := h
    exact Finset.prod_eq_zero hiS (if_neg hi)

/-- **`andPoly` has total degree at most the fan-in (PROVED).** -/
theorem andPoly_totalDegree_le [Nontrivial R] (S : Finset (Fin n)) :
    (andPoly S : MvPolynomial (Fin n) R).totalDegree ≤ S.card := by
  rw [andPoly]
  refine le_trans (MvPolynomial.totalDegree_finset_prod _ _) ?_
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum (fun i _ => le_of_eq (MvPolynomial.totalDegree_X i))

/-!
**The exact `AND` polynomial, proved.**  An `AND` gate is `∏ Xᵢ` (eval = `AND`, degree ≤ fan-in) — a single faithful
`AND`-term.  The exact degree being the fan-in is *why* composition needs the approximate RS polynomial; that approximate
method (and prime-power composition, circuit assembly) is the genuine open content — not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0AndPoly

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AndPoly.andPoly_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AndPoly.andPoly_totalDegree_le
