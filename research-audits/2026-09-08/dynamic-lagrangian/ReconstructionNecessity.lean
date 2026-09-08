import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
What correctness actually forces at a boundary: preservation of distinguishable
continuation answers. This does not assume or prove full bulk reconstruction.
The factorization premise must itself be justified for the chosen machine cut;
in particular, later access to the original input cannot be silently omitted.
-/
namespace ReconstructionNecessity

theorem boundary_separates_continuations
    {Input Boundary Query Answer : Type*}
    (encode : Input → Boundary) (answer : Input → Query → Answer)
    (resume : Boundary → Query → Answer)
    (correct : ∀ x q, resume (encode x) q = answer x q)
    {x y : Input} (distinguish : ∃ q, answer x q ≠ answer y q) :
    encode x ≠ encode y := by
  intro same
  obtain ⟨q, hq⟩ := distinguish
  apply hq
  rw [← correct x q, ← correct y q, same]

theorem distinguishable_family_injective
    {Input Boundary Query Answer I : Type*}
    (encode : Input → Boundary) (answer : Input → Query → Answer)
    (resume : Boundary → Query → Answer)
    (correct : ∀ x q, resume (encode x) q = answer x q)
    (family : I → Input)
    (separated : ∀ i j, i ≠ j → ∃ q, answer (family i) q ≠ answer (family j) q) :
    Function.Injective (encode ∘ family) := by
  intro i j same
  by_contra ne
  exact boundary_separates_continuations encode answer resume correct
    (separated i j ne) same

/-- b bits allow 2^b distinguishable codes, not merely b codes. -/
theorem distinguishable_family_bit_bound
    {Input Query Answer I : Type*} [Fintype I] (bits : ℕ)
    (encode : Input → (Fin bits → Bool)) (answer : Input → Query → Answer)
    (resume : (Fin bits → Bool) → Query → Answer)
    (correct : ∀ x q, resume (encode x) q = answer x q)
    (family : I → Input)
    (separated : ∀ i j, i ≠ j → ∃ q, answer (family i) q ≠ answer (family j) q) :
    Fintype.card I ≤ 2 ^ bits := by
  have h := Fintype.card_le_of_injective _
    (distinguishable_family_injective encode answer resume correct family separated)
  simpa using h

/-- A runtime bound on represented bits only yields an exponential code bound.
The machine-specific bit/runtime bound is explicitly a premise. -/
theorem distinguishable_family_runtime_capacity
    {Input Query Answer I : Type*} [Fintype I] (bits initial rate time : ℕ)
    (encode : Input → (Fin bits → Bool)) (answer : Input → Query → Answer)
    (resume : (Fin bits → Bool) → Query → Answer)
    (correct : ∀ x q, resume (encode x) q = answer x q)
    (family : I → Input)
    (separated : ∀ i j, i ≠ j → ∃ q, answer (family i) q ≠ answer (family j) q)
    (space_time : bits ≤ initial + rate * time) :
    Fintype.card I ≤ 2 ^ (initial + rate * time) := by
  exact (distinguishable_family_bit_bound bits encode answer resume correct
    family separated).trans (Nat.pow_le_pow_right (by omega) space_time)

/-- Even an exact decision map need not retain the underlying object.
This is a logical counterexample, NOT a general-SAT algorithm. -/
theorem correct_decision_without_reconstruction :
    ∃ (encode : Bool → Unit) (resume : Unit → Bool),
      (∀ x, resume (encode x) = true) ∧
      ¬ ∃ reconstruct : Unit → Bool, ∀ x, reconstruct (encode x) = x := by
  refine ⟨fun _ => (), fun _ => true, by simp, ?_⟩
  rintro ⟨reconstruct, h⟩
  have hf := h false
  have ht := h true
  simp only at hf ht
  exact Bool.false_ne_true (hf.symm.trans ht)

end ReconstructionNecessity

#print axioms ReconstructionNecessity.distinguishable_family_runtime_capacity
#print axioms ReconstructionNecessity.correct_decision_without_reconstruction
