import GodMoveRationalPrecisionArithmetic
import GodMoveTrackedOrthogonalizationCost

/-!
# Precision of the executed zero-seeded dot-product loop

`DotPrecision` records bounds for the actual rational operands, products, and
every prefix accumulator of `sumProductsOn`. Its step theorem also covers the
result of the next executed addition, identified with the following prefix.
No arithmetic implementation cost or Turing-machine runtime is asserted.
-/

namespace GodMoveDotLoopPrecision

open GodMoveRationalPrecisionArithmetic
open GodMoveTrackedOrthogonalizationCost

theorem sumProductsOn_append {ι : Type*} (v w : ι → ℚ) (xs ys : List ι)
    (acc : Counted ℚ) :
    sumProductsOn v w (xs ++ ys) acc =
      sumProductsOn v w ys (sumProductsOn v w xs acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons i xs ih => simp only [List.cons_append, sumProductsOn, ih]

/-- Running a prefix and resuming the suffix is the very same execution,
including the arithmetic counter. -/
theorem sumProductsOn_resume_prefix {ι : Type*} (v w : ι → ℚ) (xs : List ι)
    (k : ℕ) (acc : Counted ℚ) :
    sumProductsOn v w xs acc =
      sumProductsOn v w (xs.drop k) (sumProductsOn v w (xs.take k) acc) := by
  rw [← sumProductsOn_append, List.take_append_drop]

theorem sumProductsOn_take_bitBound {ι : Type*} (xs : List ι) (v w : ι → ℚ)
    (b c k : ℕ) (hv : ∀ i ∈ xs, BitBound (v i) b)
    (hw : ∀ i ∈ xs, BitBound (w i) c) :
    BitBound (sumProductsOn v w (xs.take k) ⟨0, 0⟩).value
      ((b + c + 1) * min k xs.length) := by
  simpa only [sumProductsOn_value, zero_add] using
    list_partialDot_bitBound xs v w b c k hv hw

theorem sumProductsOn_prefix_bitBound {n : ℕ} (v w : Fin n → ℚ)
    (b c k : ℕ) (hv : ∀ i, BitBound (v i) b) (hw : ∀ i, BitBound (w i) c) :
    BitBound (sumProductsOn v w ((List.finRange n).take k) ⟨0, 0⟩).value
      ((b + c + 1) * min k n) := by
  simpa only [List.length_finRange] using
    sumProductsOn_take_bitBound (List.finRange n) v w b c k
      (fun i _ => hv i) (fun i _ => hw i)

structure DotPrecision {n : ℕ} (v w : Fin n → ℚ) (b : ℕ) : Prop where
  left : ∀ i, BitBound (v i) b
  right : ∀ i, BitBound (w i) b
  products : ∀ i, BitBound (v i * w i) b
  prefixes : ∀ k,
    BitBound (sumProductsOn v w ((List.finRange n).take k) ⟨0, 0⟩).value b

theorem DotPrecision.mono {n : ℕ} {v w : Fin n → ℚ} {b c : ℕ}
    (h : DotPrecision v w b) (hbc : b ≤ c) : DotPrecision v w c where
  left i := (h.left i).mono hbc
  right i := (h.right i).mono hbc
  products i := (h.products i).mono hbc
  prefixes k := (h.prefixes k).mono hbc

/-- An explicit enclosing exponent also handles the empty dot product. -/
theorem dotPrecision_of_bounds {n : ℕ} (v w : Fin n → ℚ) (b c B : ℕ)
    (hv : ∀ i, BitBound (v i) b) (hw : ∀ i, BitBound (w i) c)
    (hb : b ≤ B) (hc : c ≤ B) (hp : b + c ≤ B)
    (hs : (b + c + 1) * n ≤ B) : DotPrecision v w B where
  left i := (hv i).mono hb
  right i := (hw i).mono hc
  products i := ((hv i).mul (hw i)).mono hp
  prefixes k := (sumProductsOn_prefix_bitBound v w b c k hv hw).mono
    ((Nat.mul_le_mul_left _ (Nat.min_le_right k n)).trans hs)

/-- The next executed multiplication and addition produce the next prefix. -/
theorem prefix_next_eq {n : ℕ} (v w : Fin n → ℚ) (i : Fin n) :
    (qadd
      (sumProductsOn v w ((List.finRange n).take i.val) ⟨0, 0⟩).value
      (qmul (v i) (w i)).value).value =
    (sumProductsOn v w ((List.finRange n).take (i.val + 1)) ⟨0, 0⟩).value := by
  have hi : i.val < (List.finRange n).length := by simp
  rw [List.take_succ_eq_append_getElem hi]
  simp [sumProductsOn_value, qadd, qmul]

theorem DotPrecision.step {n : ℕ} {v w : Fin n → ℚ} {b : ℕ}
    (h : DotPrecision v w b) (i : Fin n) :
    BitBound (v i) b ∧ BitBound (w i) b ∧
      BitBound (qmul (v i) (w i)).value b ∧
      BitBound (sumProductsOn v w ((List.finRange n).take i.val) ⟨0, 0⟩).value b ∧
      BitBound (qadd
        (sumProductsOn v w ((List.finRange n).take i.val) ⟨0, 0⟩).value
        (qmul (v i) (w i)).value).value b := by
  refine ⟨h.left i, h.right i, h.products i, h.prefixes i.val, ?_⟩
  rw [prefix_next_eq]
  exact h.prefixes (i.val + 1)

theorem DotPrecision.result {n : ℕ} {v w : Fin n → ℚ} {b : ℕ}
    (h : DotPrecision v w b) : BitBound (sumProducts v w).value b := by
  have ht : (List.finRange n).take n = List.finRange n := by
    simpa only [List.length_finRange] using (List.take_length (l := List.finRange n))
  simpa only [ht, sumProducts] using h.prefixes n

end GodMoveDotLoopPrecision

#print axioms GodMoveDotLoopPrecision.sumProductsOn_take_bitBound
#print axioms GodMoveDotLoopPrecision.sumProductsOn_resume_prefix
#print axioms GodMoveDotLoopPrecision.sumProductsOn_prefix_bitBound
#print axioms GodMoveDotLoopPrecision.dotPrecision_of_bounds
#print axioms GodMoveDotLoopPrecision.prefix_next_eq
#print axioms GodMoveDotLoopPrecision.DotPrecision.step
#print axioms GodMoveDotLoopPrecision.DotPrecision.result
