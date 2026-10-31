import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer10Monotone

/-!
# Layer 10D — a right-shaped candidate: the Khrapchenko formal complexity measure

Following the spectral probe (which *failed* (A)), a **differently-shaped** candidate invariant: the
Khrapchenko measure, a *formal complexity measure* designed to be `≤ size` by construction (so it satisfies
(A) automatically) and to be large on hard functions.

`khrap f = |∂(f⁻¹0, f⁻¹1)|² / (|f⁻¹0|·|f⁻¹1|)`, where `∂` counts hypercube edges crossing the
`0/1`-boundary.  By **Khrapchenko's theorem** it lower-bounds *formula leaf-size* (cited, not formalized
here).

## Small-`n` results (`native_decide`)

* `khrap_parity_two/three`: `khrap (parityFn n) = n²` (`4, 9`) — large, the right shape.
* `khrap_dictator_two/three`: `khrap (x ↦ x₀) = 1` — small on the trivially-easy function (so it is
  consistent with (A), unlike `specMax` which gave `2ⁿ`).

So Khrapchenko **passes the small-`n` (A) sanity check** the spectral quantity failed, and gives a genuine
**superlinear** lower bound: PARITY needs formula-size `≥ n²`.

## ⚠ Two honest caveats (both material)

1. **This is a *formula* lower bound, and so is all of Layers 8–10.**  The `Circuit` model (Layers 8–10) is
   an *inductive tree*: `size (and c d) = size c + size d + 1` double-counts shared subterms, so it measures
   **formula size**, not DAG/circuit size.  Hence `SIZE`/`Ppoly` are *poly-size formulas* ≈ **nonuniform
   `NC¹`**, not `P/poly`.  See `SCOPE_MODEL_FORMULA_CORRECTION.md`.  Khrapchenko's `n²` is a correct formula
   bound here (a real beyond-linear result for this model); it says nothing about general (sharing) circuits.
2. **Formal complexity measures provably cap polynomially.**  Khrapchenko tops out at `n²`; the best known
   measure-based formula bounds are `~n³` (Håstad).  No formal complexity measure is known to break
   `n^{3+o(1)}` — so even this right-shaped candidate cannot reach super-polynomial.  Property (B) at the
   frontier scale is *not* attainable this way.

Net: the sandbox found a candidate that *passes* (A) and gives a real superlinear (formula) bound — but it
is bounded-by-construction at `n²`, and it lives in the formula model, not `P/poly`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer10

open Finset

/-- Flip bit `i` of `x`. -/
def flipBit {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool := Function.update x i (!x i)

/-- The number of (directed) sensitive hypercube edges of `f`. -/
def sensCount {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  (Finset.univ.filter (fun p : (Fin n → Bool) × Fin n => f p.1 ≠ f (flipBit p.1 p.2))).card

/-- `|f⁻¹(0)|`. -/
def zerosN {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ := (Finset.univ.filter (fun x => f x = false)).card
/-- `|f⁻¹(1)|`. -/
def onesN {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ := (Finset.univ.filter (fun x => f x = true)).card

/-- **Khrapchenko measure** — a formal complexity measure; by Khrapchenko's theorem a lower bound on formula
leaf-size.  (Directed sensitive-edge count is twice the undirected, hence the `4` in the denominator.) -/
def khrap {n : ℕ} (f : (Fin n → Bool) → Bool) : ℚ :=
  (sensCount f : ℚ) ^ 2 / (4 * zerosN f * onesN f)

/-! ### Small-`n` results -/

/-- PARITY has Khrapchenko measure `n²` (a superlinear formula lower bound). -/
theorem khrap_parity_two : khrap (parityFn 2) = 4 := by native_decide
theorem khrap_parity_three : khrap (parityFn 3) = 9 := by native_decide

/-- The dictator has Khrapchenko measure `1` — small on the easy function, so consistent with (A). -/
theorem khrap_dictator_two : khrap (fun x : Fin 2 → Bool => x 0) = 1 := by native_decide
theorem khrap_dictator_three : khrap (fun x : Fin 3 → Bool => x 0) = 1 := by native_decide

end PallLean.Paper93.DeepMath.PathB.Layer10

#print axioms PallLean.Paper93.DeepMath.PathB.Layer10.khrap_parity_three
