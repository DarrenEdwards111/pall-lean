import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# A local accumulator construction for the coupled product

The paper's coupled verifier expression is a product of factors
`1 - z_C * V_C^2`.  This file constructs an accumulator realization of that
product, for arbitrary evaluated real factors, using `m + 1` accumulator
values and the local equations `w_0 = 1`, `w_(i+1) = w_i * f_i`.
The canonical prefix products satisfy every equation, and any satisfying
assignment has the required final product.  A sum of squares enforces exactly
these equations over the reals.  No division or nonzero-factor assumption is
used, so zero factors are included.

This is a constructive local constraint encoding.  The sum-of-squares
constraint energy is not identified with the product polynomial.  Projecting
the zero set onto the final accumulator coordinate gives the product's graph;
this existential semantic fact is not rank-preserving polynomial extraction.
No small CEW, polynomial SPDP rank, or SAT separation is asserted.  Those
properties would require separate theorems for this accumulator construction
and the same extraction/gauge used for the NP-side lower bound.
-/

namespace GodMoveProductAccumulator

open scoped BigOperators

/-- The initial condition and one multiplication equation for each factor. -/
structure AccumulatorConstraints {m : ℕ} (f : Fin m → ℝ)
    (w : Fin (m + 1) → ℝ) : Prop where
  initial : w 0 = 1
  step : ∀ i : Fin m, w i.succ = w i.castSucc * f i

/-- The explicit accumulator is the sequence of prefix products. -/
noncomputable def canonicalAccumulator {m : ℕ} (f : Fin m → ℝ) :
    Fin (m + 1) → ℝ := Fin.partialProd f

theorem canonical_satisfies {m : ℕ} (f : Fin m → ℝ) :
    AccumulatorConstraints f (canonicalAccumulator f) where
  initial := Fin.partialProd_zero f
  step := Fin.partialProd_succ f

/-- The local recurrence determines every accumulator value uniquely. -/
theorem accumulator_unique {m : ℕ} (f : Fin m → ℝ)
    (w : Fin (m + 1) → ℝ) (hw : AccumulatorConstraints f w) :
    w = canonicalAccumulator f := by
  funext t
  refine Fin.inductionOn t ?_ ?_
  · simpa [canonicalAccumulator] using hw.initial
  · intro i hi
    change w i.succ = Fin.partialProd f i.succ
    rw [hw.step i, Fin.partialProd_succ]
    exact congrArg (fun a : ℝ => a * f i) hi

theorem canonical_final {m : ℕ} (f : Fin m → ℝ) :
    canonicalAccumulator f (Fin.last m) = ∏ i, f i := by
  change (List.take m (List.ofFn f)).prod = ∏ i, f i
  rw [List.take_of_length_le (by simp), Fin.prod_ofFn]

theorem satisfying_final {m : ℕ} (f : Fin m → ℝ)
    (w : Fin (m + 1) → ℝ) (hw : AccumulatorConstraints f w) :
    w (Fin.last m) = ∏ i, f i := by
  rw [accumulator_unique f w hw]
  exact canonical_final f

/-- A local sum-of-squares constraint energy for the accumulator recurrence. -/
noncomputable def constraintEnergy {m : ℕ} (f : Fin m → ℝ)
    (w : Fin (m + 1) → ℝ) : ℝ :=
  (w 0 - 1)^2 + ∑ i : Fin m, (w i.succ - w i.castSucc * f i)^2

theorem constraintEnergy_nonneg {m : ℕ} (f : Fin m → ℝ)
    (w : Fin (m + 1) → ℝ) : 0 ≤ constraintEnergy f w := by
  exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- Over the reals, zero energy is exactly satisfaction of all local equations. -/
theorem constraintEnergy_zero_iff {m : ℕ} (f : Fin m → ℝ)
    (w : Fin (m + 1) → ℝ) :
    constraintEnergy f w = 0 ↔ AccumulatorConstraints f w := by
  have hsum : 0 ≤ ∑ i : Fin m, (w i.succ - w i.castSucc * f i)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  constructor
  · intro h
    have hz := (add_eq_zero_iff_of_nonneg (sq_nonneg (w 0 - 1)) hsum).mp h
    refine ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp hz.1), ?_⟩
    intro i
    have hi : (w i.succ - w i.castSucc * f i)^2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hz.2
        i (Finset.mem_univ i)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
  · intro hw
    simp [constraintEnergy, hw.initial, hw.step]

theorem canonical_energy_zero {m : ℕ} (f : Fin m → ℝ) :
    constraintEnergy f (canonicalAccumulator f) = 0 :=
  (constraintEnergy_zero_iff f _).mpr (canonical_satisfies f)

/-- Existentially eliminating the accumulator equations recovers the graph
of the product as a relation on real values. -/
theorem zero_energy_output_iff {m : ℕ} (f : Fin m → ℝ) (y : ℝ) :
    (∃ w : Fin (m + 1) → ℝ,
      constraintEnergy f w = 0 ∧ w (Fin.last m) = y) ↔
      y = ∏ i, f i := by
  constructor
  · rintro ⟨w, hzero, hy⟩
    rw [← hy]
    exact satisfying_final f w ((constraintEnergy_zero_iff f w).mp hzero)
  · intro hy
    refine ⟨canonicalAccumulator f, canonical_energy_zero f, ?_⟩
    exact (canonical_final f).trans hy.symm

/-- The paper's evaluated local factors, with its sign and square unchanged. -/
noncomputable def clauseFactors {m : ℕ} (z V : Fin m → ℝ) : Fin m → ℝ :=
  fun i => 1 - z i * (V i)^2

theorem coupled_clause_product_realization {m : ℕ} (z V : Fin m → ℝ) :
    ∃ w : Fin (m + 1) → ℝ,
      constraintEnergy (clauseFactors z V) w = 0 ∧
      w (Fin.last m) = ∏ i, (1 - z i * (V i)^2) := by
  refine ⟨canonicalAccumulator (clauseFactors z V), canonical_energy_zero _, ?_⟩
  exact canonical_final (clauseFactors z V)

end GodMoveProductAccumulator

#print axioms GodMoveProductAccumulator.accumulator_unique
#print axioms GodMoveProductAccumulator.constraintEnergy_zero_iff
#print axioms GodMoveProductAccumulator.zero_energy_output_iff
#print axioms GodMoveProductAccumulator.coupled_clause_product_realization
