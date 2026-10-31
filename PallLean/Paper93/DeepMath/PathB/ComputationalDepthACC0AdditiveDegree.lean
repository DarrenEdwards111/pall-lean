import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3AC0pPoly

/-!
# Additive degree control: an `AND` gate's polynomial degree is the *sum* of its inputs' degrees

The depth-composition observer (`…ACC0DepthCompose`) gives a **product** boundary `∏ᵢ |Sᵢ|` — exponential in the
fan-in.  The polynomial method beats it because polynomial degree composes **additively**: the degree of an `AND`
(`= ∏` of the inputs' polynomials) is the **sum** of the inputs' degrees, not their product.  This file proves that
additivity for the `toPoly` representation.

```
totalDegree (toPoly (AND cs))  ≤  ∑_{c ∈ cs} totalDegree (toPoly c).
```

With bounded fan-in `≤ w` and per-input degree `≤ D`, an `AND`/`OR` layer multiplies the degree by `≤ w` (`≤ w·D`), so
across constant depth the degree stays `polylog` (the `((p-1)t)^{depth}` bound of `toAgree_totalDegree_le`) — and a
polylog-degree polynomial has only **quasipolynomially** many monomial-`AND`s.  This additive (not multiplicative-over-
fan-in) behaviour is exactly the gap between the observer's exponential product boundary and the polynomial method's
quasipolynomial one.

## What is proved (clean axioms, no `sorry`)

* `toPolyList_eq_map` — `toPolyList p cs = cs.map (toPoly p)`.
* `toPoly_andGate_totalDegree_le` — `AND`-gate degree `≤ ∑` of input degrees (additivity, via `totalDegree_list_prod`).
* `toPoly_andGate_totalDegree_le_of_bounded` — bounded fan-in `≤ w`, inputs `≤ D` ⇒ `AND`-gate degree `≤ w·D`
  (one layer multiplies the degree by at most the fan-in).

## Honest scope

This is the *additive* degree law for `AND` (the within-layer key).  The full polylog-degree-across-depth bound is
Layer3's `toAgree_totalDegree_le` (already proved, for the *approximant*).  This file isolates *why* the polynomial
method's count is quasipolynomial (additive degree) rather than the observer's exponential product.  The exact
quasipoly depth-composition (true YBT, not approximate) remains the open wall.  Still the cell/observer model; nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0AdditiveDegree

open scoped Classical
open MvPolynomial
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Layer3

variable {n : ℕ}

/-- **`toPolyList` is the pointwise map of `toPoly` (proved).** -/
theorem toPolyList_eq_map (p : ℕ) (cs : List (BoolCircuitSyntax n)) :
    toPolyList p cs = cs.map (toPoly p) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [toPolyList, ih]

/-- **Additive degree control for `AND` (proved): the gate's degree is at most the *sum* of its inputs' degrees.** -/
theorem toPoly_andGate_totalDegree_le (p : ℕ) (cs : List (BoolCircuitSyntax n)) :
    (toPoly p (BoolCircuitSyntax.andGate cs)).totalDegree
      ≤ (cs.map (fun c => (toPoly p c).totalDegree)).sum := by
  show ((toPolyList p cs).prod).totalDegree ≤ _
  rw [toPolyList_eq_map]
  have h := MvPolynomial.totalDegree_list_prod (cs.map (toPoly p))
  rwa [List.map_map] at h

/-- **Bounded-fan-in degree control (proved): one `AND` layer of fan-in `≤ w` with inputs of degree `≤ D` has degree
`≤ w·D`.**  So across constant depth the degree stays polylog (`((p-1)t)^{depth}`, `toAgree_totalDegree_le`). -/
theorem toPoly_andGate_totalDegree_le_of_bounded (p : ℕ) (cs : List (BoolCircuitSyntax n)) (w D : ℕ)
    (hw : cs.length ≤ w) (hD : ∀ c ∈ cs, (toPoly p c).totalDegree ≤ D) :
    (toPoly p (BoolCircuitSyntax.andGate cs)).totalDegree ≤ w * D := by
  refine le_trans (toPoly_andGate_totalDegree_le p cs) ?_
  refine le_trans (List.sum_le_card_nsmul _ D ?_) ?_
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    exact hD c hc
  · rw [List.length_map, smul_eq_mul]
    exact Nat.mul_le_mul_right _ hw

end PallLean.Paper93.DeepMath.PathB.ACC0AdditiveDegree

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AdditiveDegree.toPoly_andGate_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AdditiveDegree.toPoly_andGate_totalDegree_le_of_bounded
