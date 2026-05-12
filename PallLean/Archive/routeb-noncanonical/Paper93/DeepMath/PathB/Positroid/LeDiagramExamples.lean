import PallLean.Paper93.DeepMath.PathB.Positroid.LeDiagramDef

/-!
# Concrete Le-diagram examples and basic structural theorems

This file provides concrete Le-diagram examples and basic structural theorems
about the Le condition in small dimensions.

Le diagrams of small dimensions can be enumerated.  For a `1 × n` diagram,
the Le condition is automatic (no NW-NE-SW pattern is possible with only
one row, since `i₁ < i₂` cannot hold with `i₁ i₂ : Fin 1`).  For an
`n × 0` diagram, the Le condition is automatic (no column indices exist).
For a `2 × 2` diagram, both the all-true and all-false fillings satisfy
the Le condition trivially.

The file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- For a 1×n Le diagram (only one row), the Le condition is automatic. -/
theorem LeDiagram_one_row_trivial (n : ℕ) (f : Fin 1 → Fin n → Bool) :
    ∀ (i₁ i₂ : Fin 1) (j₁ j₂ : Fin n),
      i₁ < i₂ → j₁ < j₂ → f i₁ j₂ = true → f i₂ j₁ = true → f i₂ j₂ = true := by
  intros i₁ i₂ j₁ j₂ h_ord _ _ _
  -- For Fin 1, all elements are equal, so i₁ < i₂ is impossible.
  have h_eq : i₁ = i₂ := Subsingleton.elim _ _
  exact absurd (h_eq ▸ h_ord) (lt_irrefl _)

/-- For an n×0 Le diagram (no columns), the Le condition is automatic. -/
theorem LeDiagram_zero_cols_trivial (n : ℕ) (f : Fin n → Fin 0 → Bool) :
    ∀ (i₁ i₂ : Fin n) (j₁ j₂ : Fin 0),
      i₁ < i₂ → j₁ < j₂ → f i₁ j₂ = true → f i₂ j₁ = true → f i₂ j₂ = true := by
  intros i₁ i₂ j₁ _ _ _ _ _
  exact j₁.elim0

/-- All-true 2×2 Le diagram is valid: the Le condition is automatic. -/
theorem LeDiagram_2x2_all_true_valid :
    ∀ (i₁ i₂ : Fin 2) (j₁ j₂ : Fin 2),
      i₁ < i₂ → j₁ < j₂ →
      (fun (_ : Fin 2) (_ : Fin 2) => true) i₁ j₂ = true →
      (fun (_ : Fin 2) (_ : Fin 2) => true) i₂ j₁ = true →
      (fun (_ : Fin 2) (_ : Fin 2) => true) i₂ j₂ = true := fun _ _ _ _ _ _ _ _ => rfl

/-- All-false 2×2 Le diagram is valid: the hypothesis "f i₁ j₂ = true" fails. -/
theorem LeDiagram_2x2_all_false_valid :
    ∀ (i₁ i₂ : Fin 2) (j₁ j₂ : Fin 2),
      i₁ < i₂ → j₁ < j₂ →
      (fun (_ : Fin 2) (_ : Fin 2) => false) i₁ j₂ = true →
      (fun (_ : Fin 2) (_ : Fin 2) => false) i₂ j₁ = true →
      (fun (_ : Fin 2) (_ : Fin 2) => false) i₂ j₂ = true := by
  intros i₁ i₂ j₁ j₂ _ _ h _
  exact absurd h Bool.false_ne_true

end PallLean.Paper93.DeepMath.PathB.Positroid
