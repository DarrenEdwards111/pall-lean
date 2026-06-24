import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneTarget

/-!
# Kleene interpreter project — the memoization table is polynomial-size (PROVED)

The efficient universal simulator must be **memoized**: naive `evaln` re-evaluates repeated subcodes (e.g.
`pair (comp f g) (comp f g)` evaluates `comp f g` twice), so the naive simulation tree is exponential in the
code size.  A memoized course-of-values simulator avoids this — each configuration is computed once — and is
polynomial **because the table of configurations is polynomial-size**.

This file proves exactly that quantitative foundation.  A configuration `(k, ec, n)` with `k, n ≤ s` and
`ec ≤ E` (the value bound from `config_encode_le`: fuel/input `≤ s`, code-encoding `≤ E`) lies in a table of
size at most `(s+1)(E+1)(s+1)`:

  `configTable s E` — the finite set of encoded configs within the value bounds.
  `configTable_card_le` — `|configTable s E| ≤ (s+1) * ((E+1) * (s+1))` (polynomial in `s, E`).

With per-cell work polynomial (the dispatch + table lookups) and a polynomial number of cells, a memoized
simulator runs in polynomial time — the content of `UniversalCodeRuntimePoly`.  For the diagonal
(`s = bound e`, `E = e`) the table is `poly(bound e, e)`.

## What is proved (clean axioms, no `sorry`)

* `configTable`, `configTable_card_le` — the table is polynomial-size.

## Honest scope

The quantitative foundation (poly-many configs ⇒ memoized simulation is poly).  Building the memoized
course-of-values simulator as an explicit `Code` (which *uses* this bound for its runtime) remains the core.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneTarget

/-- The finite set of encoded configurations within the value bounds `k, n ≤ s`, `ec ≤ E`. -/
noncomputable def configTable (s E : ℕ) : Finset ℕ :=
  (Finset.Iic s ×ˢ Finset.Iic E ×ˢ Finset.Iic s).image (fun p => encConfig p.1 p.2.1 p.2.2)

/-- **The memoization table is polynomial-size (proved).** -/
theorem configTable_card_le (s E : ℕ) :
    (configTable s E).card ≤ (s + 1) * ((E + 1) * (s + 1)) := by
  refine le_trans Finset.card_image_le ?_
  simp [Finset.card_product, Nat.card_Iic]

/-!
**Table-size bound proved.**  Only polynomially many configurations satisfy the value bound, so a memoized
simulator (each config computed once) runs in polynomial time.  The explicit memoized `Code` remains the
core.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneTarget

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneTarget.configTable_card_le
