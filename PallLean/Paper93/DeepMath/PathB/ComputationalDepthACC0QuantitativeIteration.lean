import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0QuantitativeDepthBound

/-!
# The quantitative iteration — solving the size/depth/error recurrence in closed form (roadmap step 1)

Entry 273 gave the clean *per-layer* quantitative estimates (degree `↦ t·D`, gate error `2^t·Eg ≤ 2ⁿ`).  This file
solves the *iteration*: turning those per-layer/per-gate estimates into the full closed-form bound that the depth
induction produces — built on top of entry 273 (not modifying the committed circuit arc).

**The two closed forms.**
* *Degree* — `t·` applied at each of `d` layers gives `t^d · D₀` (`pow_depth_degree`, entry 273).
* *Error* — each of the `m` gates contributes `Eg i` with `2^t · Eg i ≤ 2ⁿ` (entry 273); the union bound
  (`E ≤ ∑ᵢ Eg i`, the committed `error_union_bound`) then gives **`2^t · E ≤ m · 2ⁿ`**: the total error is at most a
  `m·2^{-t}` fraction.  For a size-`s` circuit, `2^t · E ≤ s · 2ⁿ`.

Together these are the closed-form solution of the recurrence — the content turning the per-layer steps into
`depth_d_circuit_lowDegreeApprox`.  The remaining piece is the *structural recursion* over the committed `Circ`
datatype (apply the layer step at each node, collecting the `m = size` per-gate errors), which lives in the committed
arc.

## What is proved (clean axioms, no `sorry`)

* **`error_accumulation`** (PROVED) — the error closed form: if `E ≤ ∑ᵢ Eg i` (union bound) and each `2^t · Eg i ≤ 2ⁿ`
  (per-gate, entry 273), then `2^t · E ≤ m · 2ⁿ` (`Finset.mul_sum` + `Finset.sum_le_sum` + `Finset.sum_const`).
* **`error_accumulation_size`** (PROVED) — the size form: with `m ≤ s`, `2^t · E ≤ s · 2ⁿ`.
* **`quantitative_iteration_closed_form`** (PROVED) — the combined solver: given a polynomial whose degree satisfies the
  `d`-fold degree recurrence and an error satisfying the union bound with per-gate `2^{-t}` gates, its degree is
  `≤ t^d · D₀` and `2^t · E ≤ m · 2ⁿ`.

## The remaining socket

* **`CircuitStructuralRecursion`** — the structural induction over the committed `Circ` that produces, for a
  size-`s`, depth-`d` circuit, a polynomial of degree satisfying the `d`-fold recurrence and an error `≤ ∑` of `s`
  per-gate `2^{-t}` errors (the quantitative refinement of the committed `approximable_exists`).  Lives in the committed
  circuit arc.

## Honest scope

This solves the recurrence in closed form — the error accumulation `2^t·E ≤ size·2ⁿ` and (via entry 273) the degree
`t^d·D₀` — completing the *analytic* content of roadmap (A)'s iteration.  The remaining piece is the structural `Circ`
recursion (Codex's arc) that feeds these closed forms; supplying it discharges `QuantitativeDepthBound` (entry 272).
This is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0QuantitativeIteration

open PallLean.Paper93.DeepMath.PathB.ACC0QuantitativeDepthBound (pow_depth_degree)

/-- **The error closed form (PROVED).**  If the circuit error `E` is union-bounded by the sum of the `m` per-gate errors
(`E ≤ ∑ᵢ Eg i`, via the committed `error_union_bound`) and each gate's error is a `2^{-t}` fraction
(`2^t · Eg i ≤ 2ⁿ`, entry 273), then the total error is a `m·2^{-t}` fraction: `2^t · E ≤ m · 2ⁿ`. -/
theorem error_accumulation {m n t : ℕ} (Eg : Fin m → ℕ) (E : ℕ)
    (hE : E ≤ ∑ i, Eg i) (hgate : ∀ i, 2 ^ t * Eg i ≤ 2 ^ n) :
    2 ^ t * E ≤ m * 2 ^ n := by
  calc 2 ^ t * E
      ≤ 2 ^ t * ∑ i, Eg i := Nat.mul_le_mul (le_refl _) hE
    _ = ∑ i, 2 ^ t * Eg i := by rw [Finset.mul_sum]
    _ ≤ ∑ _i : Fin m, 2 ^ n := Finset.sum_le_sum (fun i _ => hgate i)
    _ = m * 2 ^ n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **The error closed form, size version (PROVED).**  With at most `s` gates (`m ≤ s`), the total error satisfies
`2^t · E ≤ s · 2ⁿ`. -/
theorem error_accumulation_size {m n t s : ℕ} (Eg : Fin m → ℕ) (E : ℕ) (hms : m ≤ s)
    (hE : E ≤ ∑ i, Eg i) (hgate : ∀ i, 2 ^ t * Eg i ≤ 2 ^ n) :
    2 ^ t * E ≤ s * 2 ^ n :=
  le_trans (error_accumulation Eg E hE hgate) (Nat.mul_le_mul_right _ hms)

/-- **The combined closed-form solver (PROVED).**  Given a polynomial whose degree satisfies the `d`-fold degree
recurrence `(·t)^[d] D₀` and an error `E` union-bounded by `m` per-gate `2^{-t}` errors, its degree is `≤ t^d · D₀`
(`pow_depth_degree`) and `2^t · E ≤ m · 2ⁿ` (`error_accumulation`).  This is the closed-form solution of the depth/error
recurrence — the iteration content turning the per-layer steps (entry 273) into the full quantitative bound. -/
theorem quantitative_iteration_closed_form {n m t d D₀ E : ℕ}
    (P : MvPolynomial (Fin n) (ZMod 2)) (Eg : Fin m → ℕ)
    (hdeg : P.totalDegree ≤ (fun D => t * D)^[d] D₀)
    (hE : E ≤ ∑ i, Eg i) (hgate : ∀ i, 2 ^ t * Eg i ≤ 2 ^ n) :
    P.totalDegree ≤ t ^ d * D₀ ∧ 2 ^ t * E ≤ m * 2 ^ n := by
  refine ⟨?_, error_accumulation Eg E hE hgate⟩
  rw [← pow_depth_degree t D₀ d]
  exact hdeg

/-- **The structural-recursion socket.**  The induction over the committed `Circ` datatype producing, for a size-`s`,
depth-`d` circuit, a polynomial whose degree satisfies the `d`-fold recurrence and an error union-bounded by `s`
per-gate `2^{-t}` errors — the quantitative refinement of the committed `approximable_exists`.  Lives in the committed
circuit arc; feeding it to `quantitative_iteration_closed_form` discharges `QuantitativeDepthBound` (entry 272). -/
def CircuitStructuralRecursion (PerGateDecomposition : Prop) : Prop :=
  PerGateDecomposition

/-!
**The rung.**  The recurrence is solved in closed form: the error accumulation `2^t·E ≤ size·2ⁿ`
(`error_accumulation`/`error_accumulation_size`) and the degree `t^d·D₀` (`pow_depth_degree`, entry 273), packaged as
`quantitative_iteration_closed_form`.  These are the *analytic* content of roadmap (A)'s iteration — the per-gate
`2^{-t}` errors (entry 273) sum, via the committed union bound, to a `size·2^{-t}` total.  The one remaining piece is
the structural `Circ` recursion (`CircuitStructuralRecursion`, the committed arc's quantitative `approximable_exists`)
that produces the per-gate decomposition; supplying it discharges `QuantitativeDepthBound`, after which the only open
theorem is the Smolensky wall (`SmolenskyNonNativeLowerBound`).  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0QuantitativeIteration

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0QuantitativeIteration.error_accumulation
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0QuantitativeIteration.error_accumulation_size
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0QuantitativeIteration.quantitative_iteration_closed_form
