import PallLean.Paper93.DeepMath.PathB.Positroid.BoundedAffinePerm
import PallLean.Paper93.DeepMath.PathB.Positroid.DecoratedPermutation
import PallLean.Paper93.DeepMath.PathB.Positroid.LeDiagramDef
import PallLean.Paper93.DeepMath.PathB.Positroid.LeDiagramExamples

/-!
# R70: small honest positroid-index correspondence

This file proves a restricted, nontrivial correspondence between the three
positroid index structures in the `n = 1` case.

For a `1 × 1` Le diagram, the single cell is the whole support.  We send an
empty cell to the positive fixed point and a filled cell to the negative fixed
point.  This is an actual equivalence
`LeDiagram 1 1 ≃ DecoratedPermutation 1`: every permutation of `Fin 1` is the
identity, and the single decoration carries exactly the same information as
the single Le cell.

On the bounded-affine side, the two decorations are represented by the two
canonical bounded affine maps of order `1`: `i ↦ i` and `i ↦ i + 1`.

The file is kernel-only and introduces no placeholder proofs or custom
primitives beyond Lean's ordinary kernel assumptions.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- Convert the one-cell Le support bit to the decoration at the unique fixed point. -/
def Decoration.ofFilledCell : Bool → Decoration
  | false => Decoration.positive
  | true => Decoration.negative

/-- Convert the unique fixed-point decoration back to the one-cell Le support bit. -/
def Decoration.toFilledCell : Decoration → Bool
  | Decoration.positive => false
  | Decoration.negative => true

@[simp]
theorem Decoration.toFilledCell_ofFilledCell (b : Bool) :
    (Decoration.ofFilledCell b).toFilledCell = b := by
  cases b <;> rfl

@[simp]
theorem Decoration.ofFilledCell_toFilledCell (d : Decoration) :
    Decoration.ofFilledCell d.toFilledCell = d := by
  cases d <;> rfl

/-- Le diagrams are equal when their fillings are pointwise equal. -/
theorem LeDiagram.ext_filling {k n : ℕ} {D E : LeDiagram k n}
    (h : ∀ i j, D.filling i j = E.filling i j) : D = E := by
  cases D with
  | mk f hf =>
    cases E with
    | mk g hg =>
      have hfg : f = g := by
        funext i j
        exact h i j
      cases hfg
      rfl

/-- Decorated permutations are equal when both the permutation and decoration agree. -/
theorem DecoratedPermutation.ext_structure {n : ℕ} {σ τ : DecoratedPermutation n}
    (hperm : σ.perm = τ.perm)
    (hdecoration : ∀ i, σ.decoration i = τ.decoration i) : σ = τ := by
  cases σ with
  | mk p d =>
    cases τ with
    | mk q e =>
      have hde : d = e := by
        funext i
        exact hdecoration i
      cases hperm
      cases hde
      rfl

/-- The decoration carried by a `1 × 1` Le diagram. -/
def LeDiagram.n1Decoration (D : LeDiagram 1 1) : Decoration :=
  Decoration.ofFilledCell (D.filling 0 0)

/-- The `1 × 1` Le-diagram-to-decorated-permutation map. -/
def LeDiagram.toDecoratedN1 (D : LeDiagram 1 1) : DecoratedPermutation 1 where
  perm := Equiv.refl (Fin 1)
  decoration := fun _ => D.n1Decoration

/-- The decorated-permutation-to-`1 × 1`-Le-diagram map. -/
def DecoratedPermutation.toLeDiagramN1 (σ : DecoratedPermutation 1) : LeDiagram 1 1 where
  filling := fun _ _ => (σ.decoration 0).toFilledCell
  le_condition := LeDiagram_one_row_trivial 1 _

/-- Converting a `1 × 1` Le diagram to a decorated permutation and back is the identity. -/
theorem LeDiagram.toDecoratedN1_toLeDiagramN1 (D : LeDiagram 1 1) :
    D.toDecoratedN1.toLeDiagramN1 = D := by
  apply LeDiagram.ext_filling
  intro i j
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  cases hi
  cases hj
  simp [DecoratedPermutation.toLeDiagramN1, LeDiagram.toDecoratedN1,
    LeDiagram.n1Decoration]

/-- Converting a decorated permutation of `Fin 1` to a Le diagram and back is the identity. -/
theorem DecoratedPermutation.toLeDiagramN1_toDecoratedN1 (σ : DecoratedPermutation 1) :
    σ.toLeDiagramN1.toDecoratedN1 = σ := by
  apply DecoratedPermutation.ext_structure
  · apply Equiv.ext
    intro i
    exact Subsingleton.elim _ _
  · intro i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    cases hi
    simp [DecoratedPermutation.toLeDiagramN1, LeDiagram.toDecoratedN1,
      LeDiagram.n1Decoration]

/-- The actual `n = 1` bijection between one-cell Le diagrams and decorated permutations. -/
def leDiagramDecoratedEquivN1 : LeDiagram 1 1 ≃ DecoratedPermutation 1 where
  toFun := LeDiagram.toDecoratedN1
  invFun := DecoratedPermutation.toLeDiagramN1
  left_inv := LeDiagram.toDecoratedN1_toLeDiagramN1
  right_inv := DecoratedPermutation.toLeDiagramN1_toDecoratedN1

/-- The single Le cell is filled exactly when the corresponding decoration is negative. -/
theorem leDiagramDecoratedEquivN1_support (D : LeDiagram 1 1) :
    (leDiagramDecoratedEquivN1 D).decoration 0 = Decoration.negative ↔
      D.filling 0 0 = true := by
  cases h : D.filling 0 0 <;>
    simp [leDiagramDecoratedEquivN1, LeDiagram.toDecoratedN1,
      LeDiagram.n1Decoration, h, Decoration.ofFilledCell]

/-- The order-1 bounded affine shift `i ↦ i + 1`. -/
def boundedAffineN1Shift : BoundedAffinePerm 1 where
  toFun :=
    { toFun := fun i : ℤ => i + 1
      invFun := fun i : ℤ => i - 1
      left_inv := by
        intro i
        show i + 1 - 1 = i
        omega
      right_inv := by
        intro i
        show i - 1 + 1 = i
        omega }
  shift_property := by
    intro i
    rfl
  lower_bound := by
    intro i
    show i ≤ i + 1
    omega
  upper_bound := by
    intro i
    rfl

@[simp]
theorem boundedAffineN1Shift_apply (i : ℤ) :
    boundedAffineN1Shift.toFun i = i + 1 := rfl

/-- The bounded-affine representative of the two `n = 1` decorations. -/
def Decoration.toBoundedAffineN1 : Decoration → BoundedAffinePerm 1
  | Decoration.positive => BoundedAffinePerm.id 1
  | Decoration.negative => boundedAffineN1Shift

/-- The bounded-affine representative attached to a one-cell Le diagram. -/
def LeDiagram.toBoundedAffineN1 (D : LeDiagram 1 1) : BoundedAffinePerm 1 :=
  D.n1Decoration.toBoundedAffineN1

/-- Empty cell, positive fixed point, and bounded-affine identity correspond at `n = 1`. -/
theorem n1_empty_cell_identity_correspondence :
    (LeDiagram.zero 1 1).toDecoratedN1 = DecoratedPermutation.id 1 ∧
      (LeDiagram.zero 1 1).toBoundedAffineN1 = BoundedAffinePerm.id 1 := by
  exact ⟨rfl, rfl⟩

/-- Filled cell, negative fixed point, and the shift `i ↦ i + 1` correspond at `n = 1`. -/
theorem n1_filled_cell_shift_correspondence :
    (LeDiagram.one 1 1).toDecoratedN1 = DecoratedPermutation.neg_id 1 ∧
      (LeDiagram.one 1 1).toBoundedAffineN1 = boundedAffineN1Shift := by
  exact ⟨rfl, rfl⟩

/-- The bounded-affine side preserves the one-cell support bit at `0`. -/
theorem leDiagramBoundedAffineN1_support (D : LeDiagram 1 1) :
    D.toBoundedAffineN1.toFun 0 = 1 ↔ D.filling 0 0 = true := by
  cases h : D.filling 0 0 <;>
    simp [LeDiagram.toBoundedAffineN1, LeDiagram.n1Decoration,
      Decoration.toBoundedAffineN1, Decoration.ofFilledCell, BoundedAffinePerm.id, h]

/-- The three restricted indices carry the same support bit in the `n = 1` correspondence. -/
theorem n1_triple_support_preservation (D : LeDiagram 1 1) :
    ((leDiagramDecoratedEquivN1 D).decoration 0 = Decoration.negative ↔
        D.filling 0 0 = true) ∧
      (D.toBoundedAffineN1.toFun 0 = 1 ↔ D.filling 0 0 = true) := by
  exact ⟨leDiagramDecoratedEquivN1_support D, leDiagramBoundedAffineN1_support D⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
