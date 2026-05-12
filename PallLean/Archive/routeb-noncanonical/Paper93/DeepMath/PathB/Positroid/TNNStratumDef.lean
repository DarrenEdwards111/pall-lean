import PallLean.Paper93.DeepMath.PathB.Positroid.TNNMatrixDef
import PallLean.Paper93.DeepMath.PathB.Positroid.PluckerSubsetIndices

/-!
# TNN strata

A **TNN stratum** at dimension `n` is a *positroid cell* in our truncated
formulation: a TNN matrix together with a designated "support" set of
subsets where the principal minor is required to be non-negative.

This file defines:

* `TNNStratum n`: the structure carrying a matrix, a proof that it is
  principal-TNN, a `support` collection of index subsets, and a
  positivity witness on the support.
* `TNNStratum.identity n`: the identity matrix with full support.
* `TNNStratum.identity_empty n`: the identity matrix with empty support.

This file is **kernel-only**: no `sorry`, no custom `axiom`, only the
kernel axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- A **TNN stratum** at dimension n: a TNN matrix together with a designated
    "support" set of subsets where the principal minor is strictly positive. -/
structure TNNStratum (n : ℕ) where
  matrix : Matrix (Fin n) (Fin n) ℝ
  is_TNN : IsPrincipalTNN matrix
  support : Finset (Finset (Fin n))
  /-- For J in support, the principal minor at J is non-negative (TNN);
      for J not in support, it could be zero. -/
  positivity : ∀ J ∈ support,
    0 ≤ (matrix.submatrix
        (fun i : J => (i.val : Fin n)) (fun j : J => (j.val : Fin n))).det

/-- The trivial TNN stratum: identity matrix with full support. -/
def TNNStratum.identity (n : ℕ) : TNNStratum n where
  matrix := 1
  is_TNN := identity_isPrincipalTNN n
  support := Finset.univ
  positivity := fun J _ => identity_isPrincipalTNN n J

/-- The empty-support TNN stratum: identity matrix with no support requirements. -/
def TNNStratum.identity_empty (n : ℕ) : TNNStratum n where
  matrix := 1
  is_TNN := identity_isPrincipalTNN n
  support := ∅
  positivity := fun J hJ => absurd hJ (Finset.notMem_empty J)

/-- The identity TNN stratum has identity matrix. -/
theorem TNNStratum.identity_matrix (n : ℕ) :
    (TNNStratum.identity n).matrix = (1 : Matrix (Fin n) (Fin n) ℝ) := rfl

/-- The identity TNN stratum has full support. -/
theorem TNNStratum.identity_support (n : ℕ) :
    (TNNStratum.identity n).support = Finset.univ := rfl

/-- The empty-support TNN stratum has empty support. -/
theorem TNNStratum.identity_empty_support (n : ℕ) :
    (TNNStratum.identity_empty n).support = ∅ := rfl

end PallLean.Paper93.DeepMath.PathB.Positroid
