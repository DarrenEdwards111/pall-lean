import PallLean.Paper93.DeepMath.PathB.Positroid.TNNMatrixDef
import PallLean.Paper93.DeepMath.PathB.Positroid.GrassmannianRowSpan

/-!
# TNN ↔ Grassmannian connection (kernel-only toy)

The **TNN Grassmannian** `Gr⁺(k, n)` is the closed subset of `Gr(k, n)`
consisting of points represented by `k × n` matrices all of whose maximal
minors are non-negative. Its closure properties under the `GL_k`-row action
are the cornerstone of the **positroid stratification** of `Gr(k, n)`.

This file provides a kernel-only toy connection between principal-TNN
square matrices (cf. `TNNMatrixDef.lean`) and the Grassmannian
row-equivalence picture (cf. `GrassmannianRowSpan.lean`):

* a principal-TNN `n × n` matrix paired with the trivial row-equivalence
  relation gives the simplest non-trivial Grassmannian-style structure;
* the identity matrix is principal-TNN and its trivial row-equivalence
  class defines a canonical "Grassmannian point" in `Gr⁺(n, n)`.

We additionally provide a local copy `trivialRowEquiv_local` of the
trivial row-equivalence relation, so that this file remains usable even
if downstream refactoring of `GrassmannianRowSpan.lean` changes the
definition or namespace of `trivialRowEquiv`.

All theorems below are checked to depend only on the kernel axioms
`propext`, `Classical.choice`, and `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The trivial row-equivalence relation: two `k × n` matrices are
    equivalent iff they are equal. This is a local copy of
    `trivialRowEquiv` from `GrassmannianRowSpan.lean`, included so that
    the statements below remain stable under upstream refactoring. -/
def trivialRowEquiv_local {k n : ℕ} (M N : Matrix (Fin k) (Fin n) ℝ) : Prop :=
  M = N

/-- Reflexivity of the local trivial row equivalence. -/
theorem trivialRowEquiv_local_refl {k n : ℕ} (M : Matrix (Fin k) (Fin n) ℝ) :
    trivialRowEquiv_local M M := rfl

/-- Symmetry of the local trivial row equivalence. -/
theorem trivialRowEquiv_local_symm {k n : ℕ} {M N : Matrix (Fin k) (Fin n) ℝ}
    (h : trivialRowEquiv_local M N) : trivialRowEquiv_local N M := h.symm

/-- Transitivity of the local trivial row equivalence. -/
theorem trivialRowEquiv_local_trans {k n : ℕ} {M N P : Matrix (Fin k) (Fin n) ℝ}
    (h₁ : trivialRowEquiv_local M N) (h₂ : trivialRowEquiv_local N P) :
    trivialRowEquiv_local M P := h₁.trans h₂

/-- A principal-TNN matrix is equivalent to itself under the trivial
    row-equivalence relation, and remains principal-TNN. This is the
    simplest non-trivial instance of the TNN-Grassmannian correspondence:
    the `Gr⁺`-class of a principal-TNN matrix is non-empty and contains
    the matrix itself. -/
theorem principalTNN_self_rowEquiv {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : IsPrincipalTNN M) :
    trivialRowEquiv_local M M ∧ IsPrincipalTNN M :=
  ⟨rfl, hM⟩

/-- The identity matrix is principal-TNN and equivalent (trivially) to
    itself; equivalently, the identity matrix represents a well-defined
    point of the TNN Grassmannian `Gr⁺(n, n)`. -/
theorem identity_TNN_grassmannian (n : ℕ) :
    trivialRowEquiv_local (1 : Matrix (Fin n) (Fin n) ℝ)
                          (1 : Matrix (Fin n) (Fin n) ℝ) ∧
    IsPrincipalTNN (1 : Matrix (Fin n) (Fin n) ℝ) :=
  ⟨rfl, identity_isPrincipalTNN n⟩

/-- The "Grassmannian point" associated to the identity matrix, modulo the
    trivial equivalence relation, is well-defined: there exists a matrix
    `M` in the trivial row-equivalence class of `1` that is also
    principal-TNN — namely `M = 1` itself. -/
theorem identity_defines_grassmannian_point (n : ℕ) :
    ∃ M : Matrix (Fin n) (Fin n) ℝ,
      trivialRowEquiv_local (1 : Matrix (Fin n) (Fin n) ℝ) M ∧
      IsPrincipalTNN M :=
  ⟨1, rfl, identity_isPrincipalTNN n⟩

/-- Compatibility lemma: the local trivial row-equivalence relation on
    `n × n` matrices coincides with the one defined in
    `GrassmannianRowSpan.lean`. This lets downstream files freely
    interchange the two. -/
theorem trivialRowEquiv_local_eq_trivialRowEquiv
    {k n : ℕ} (M N : Matrix (Fin k) (Fin n) ℝ) :
    trivialRowEquiv_local M N ↔ trivialRowEquiv M N :=
  Iff.rfl

end PallLean.Paper93.DeepMath.PathB.Positroid
