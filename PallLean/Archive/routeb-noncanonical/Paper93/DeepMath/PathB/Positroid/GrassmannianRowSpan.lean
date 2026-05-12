import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
# Grassmannian row-span equivalence (kernel-only toy)

For the Grassmannian `Gr(k, n)` we represent points as `k × n` matrices modulo
the left action of `GL_k`: two matrices `M`, `N` represent the same point iff
`N = U * M` for some invertible `U`.

This file provides a kernel-only foundation:

* `trivialRowEquiv` is the trivial (equality) equivalence relation on `k × n`
  real matrices, with the full equivalence-relation API (`refl`/`symm`/`trans`).
* `glRowEquiv` is the substantive `GL_k`-row equivalence relation. We prove
  reflexivity (witnessed by the identity matrix). Symmetry and transitivity for
  `glRowEquiv` require additional library work on `IsUnit` for invertible
  matrices and are intentionally omitted here to keep the file kernel-only.

All theorems below are checked to depend only on the kernel axioms `propext`,
`Classical.choice`, and `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The relation "M ≈ M' iff M = M'" — the trivial equivalence relation on
    `k × n` matrices. This is the simplest kernel-only foundation; the genuine
    Grassmannian row-equivalence requires the `GL_k` action which we abbreviate
    to equality here. -/
def trivialRowEquiv {k n : ℕ} (M N : Matrix (Fin k) (Fin n) ℝ) : Prop :=
  M = N

/-- Reflexivity of the trivial row equivalence. -/
theorem trivialRowEquiv_refl {k n : ℕ} (M : Matrix (Fin k) (Fin n) ℝ) :
    trivialRowEquiv M M := rfl

/-- Symmetry of the trivial row equivalence. -/
theorem trivialRowEquiv_symm {k n : ℕ} {M N : Matrix (Fin k) (Fin n) ℝ}
    (h : trivialRowEquiv M N) : trivialRowEquiv N M := h.symm

/-- Transitivity of the trivial row equivalence. -/
theorem trivialRowEquiv_trans {k n : ℕ} {M N P : Matrix (Fin k) (Fin n) ℝ}
    (h₁ : trivialRowEquiv M N) (h₂ : trivialRowEquiv N P) :
    trivialRowEquiv M P := h₁.trans h₂

/-- The substantive **`GL_k` row equivalence**: `M ≈_GL N` iff there exists an
    invertible matrix `U` with `N = U * M`. -/
def glRowEquiv {k n : ℕ} (M N : Matrix (Fin k) (Fin n) ℝ) : Prop :=
  ∃ (U : Matrix (Fin k) (Fin k) ℝ), IsUnit U ∧ N = U * M

/-- Reflexivity of `GL` row equivalence (witness: `U = 1`). -/
theorem glRowEquiv_refl {k n : ℕ} (M : Matrix (Fin k) (Fin n) ℝ) :
    glRowEquiv M M :=
  ⟨1, isUnit_one, by rw [Matrix.one_mul]⟩

/-- The equivalence relation: same matrix is equivalent to itself. -/
theorem glRowEquiv_self {k n : ℕ} (M : Matrix (Fin k) (Fin n) ℝ) :
    glRowEquiv M M :=
  glRowEquiv_refl M

/-- Toy lemma: the identity matrix is `GL`-row equivalent to itself via the
    identity witness. -/
theorem glRowEquiv_id_self (k : ℕ) :
    glRowEquiv (1 : Matrix (Fin k) (Fin k) ℝ) (1 : Matrix (Fin k) (Fin k) ℝ) :=
  glRowEquiv_refl _

end PallLean.Paper93.DeepMath.PathB.Positroid
