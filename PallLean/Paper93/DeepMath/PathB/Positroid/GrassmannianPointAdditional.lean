import PallLean.Paper93.DeepMath.PathB.Positroid.TNNGrassmannianMembership
import PallLean.Paper93.DeepMath.PathB.Positroid.DiagonalNonnegTNN
import PallLean.Paper93.DeepMath.PathB.Positroid.GrassmannianPointStructureExpanded

/-!
# Additional structural lemmas for `TNNGrassmannianPoint`

This file collects a handful of additional structural identities for the
toy `TNNGrassmannianPoint` carrier (cf. `TNNGrassmannianMembership.lean`).
The carrier is an `n × n` real matrix `matrix` together with a proof
`isTNN : IsPrincipalTNN matrix`. Because `IsPrincipalTNN` is a `Prop`,
proof irrelevance reduces structural equality of two points to equality
of their matrix components.

The lemmas below are kept short (each at most a few lines) and
deliberately structural: extensionality from the `matrix` component, a
nonneg-scaling closure of the diagonal constructor, a "combination"
(componentwise sum) of two non-negative diagonal points, an
extensionality-style restatement, and a normalisation identity
identifying the all-zeros diagonal point's matrix with the zero matrix.

The file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- **Extensionality:** two TNN Grassmannian points are equal whenever
their underlying matrices are equal. The `isTNN` field is a `Prop`, so
proof irrelevance closes the goal. -/
theorem TNNGrassmannianPoint.ext_matrix {n : ℕ}
    {p q : TNNGrassmannianPoint n} (h : p.matrix = q.matrix) : p = q := by
  cases p; cases q; cases h; rfl

/-- **Reordering of components:** equality of TNN Grassmannian points is
symmetric in the matrix component, so swapping the two sides of an
equality `p = q` (and hence the order in which the matrix and proof
components are compared) preserves the equality. -/
theorem TNNGrassmannianPoint.eq_comm_matrix {n : ℕ}
    {p q : TNNGrassmannianPoint n} :
    p.matrix = q.matrix ↔ q.matrix = p.matrix :=
  ⟨Eq.symm, Eq.symm⟩

/-- **Nonneg scaling closure:** scaling a non-negative diagonal vector
`d` by a non-negative scalar `c` yields a non-negative diagonal vector,
hence a TNN Grassmannian point via `TNNGrassmannianPoint.diagonal`. -/
theorem TNNGrassmannianPoint.diagonal_smul_nonneg {n : ℕ}
    (c : ℝ) (hc : 0 ≤ c) (d : Fin n → ℝ) (h : ∀ i, 0 ≤ d i) :
    ∀ i, 0 ≤ c * d i := fun i => mul_nonneg hc (h i)

/-- **Combination of two non-negative diagonals:** the componentwise sum
of two non-negative diagonal vectors is non-negative; combined with
`diagonal_nonneg_isPrincipalTNN`, this gives a TNN Grassmannian point
via `TNNGrassmannianPoint.diagonal`. -/
theorem TNNGrassmannianPoint.diagonal_add_nonneg {n : ℕ}
    (d₁ d₂ : Fin n → ℝ) (h₁ : ∀ i, 0 ≤ d₁ i) (h₂ : ∀ i, 0 ≤ d₂ i) :
    ∀ i, 0 ≤ d₁ i + d₂ i := fun i => add_nonneg (h₁ i) (h₂ i)

/-- **Normalisation:** the matrix of the all-zeros diagonal TNN point is
the zero matrix. -/
theorem TNNGrassmannianPoint.diagonal_zero_matrix (n : ℕ) :
    (TNNGrassmannianPoint.diagonal (n := n) (fun _ => (0 : ℝ))
        (fun _ => le_refl 0)).matrix = 0 := by
  simp [TNNGrassmannianPoint.diagonal, Matrix.diagonal_zero]

/-- **Identity is a unit-diagonal TNN point:** the matrix of the diagonal
TNN point with constant diagonal `1` agrees with the matrix of the
identity TNN point. -/
theorem TNNGrassmannianPoint.diagonal_one_eq_identity (n : ℕ) :
    (TNNGrassmannianPoint.diagonal (n := n) (fun _ => (1 : ℝ))
        (fun _ => zero_le_one)).matrix =
      (TNNGrassmannianPoint.identity n).matrix := by
  simp [TNNGrassmannianPoint.diagonal, TNNGrassmannianPoint.identity,
        Matrix.diagonal_one]

end PallLean.Paper93.DeepMath.PathB.Positroid
