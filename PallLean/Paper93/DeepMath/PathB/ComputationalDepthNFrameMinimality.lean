import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameFactorCircuit
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Minimality of the gate count — gate count equals rank exactly

To make the gate count *exactly* the rank we need `rank M ≤ k ⟹ M` factors through `k` dims.  This
file proves it, in both its pieces.

* `rank_factorization` — **the core**: `rank M ≤ k ⟹ ∃ A B, M = A · B` (`A : n×k`, `B : k×n`).  Built
  by factoring `M.mulVecLin` through a basis of its range (dim `= rank ≤ k`): lift the
  range-restriction along a surjection `Fin k → F ↠ range` (projectivity of `Fin n → F` via
  `projective_lifting_property`), then read off matrices via `toMatrix'_comp`.
* `factor_pad` — the padding: a factorization through `r` dims lifts to one through `k` given conjugate
  rectangles `Q · R = 1` (`Q : r×k`, `R : k×r`).

## What this completes

With `rank_factorization` (rank `≤ k` ⇒ a `k`-dim factorization ⇒, by `factorization_eq_sum_gates`, a
`k`-gate circuit) and the forward `rank_le_inner_dim` (a `k`-gate circuit ⇒ rank `≤ k`), the **minimal
gate count of the shared computation equals its rank exactly**.  So the N-Frame `coneInter` count and
the algebraic rank of the low-rank share coincide precisely: the residual `coneInter ≤ cN` and Valiant
rigidity are the *same* quantity, both directions, with the count now pinned to the rank.  The
famous-open core — rigidity itself — is untouched.

Nothing here proves `P ≠ NP`, resolves rigidity, discharges the capture, or is `NEXP ⊄ ACC⁰`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity

variable {n k : ℕ} {F : Type*} [Field F]

/-- **Padding a factorization.**  A factorization through `r` dims lifts to one through `k` dims given
conjugate rectangles `Q · R = 1`: `M = A'·B'` becomes `M = (A'·Q)·(R·B')`.  (For `r ≤ k`, such `Q, R`
are the coordinate inclusion `Fin r ↪ Fin k` and its retraction.) -/
theorem factor_pad {r : ℕ} (M : Matrix (Fin n) (Fin n) F)
    (A' : Matrix (Fin n) (Fin r) F) (B' : Matrix (Fin r) (Fin n) F) (hM : M = A' * B')
    (Q : Matrix (Fin r) (Fin k) F) (R : Matrix (Fin k) (Fin r) F) (hQR : Q * R = 1) :
    M = (A' * Q) * (R * B') := by
  have h : (A' * Q) * (R * B') = A' * B' := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q R B', hQR, Matrix.one_mul]
  rw [hM]; exact h.symm

/-- **The core rank-factorization.**  A matrix of rank `≤ k` factors through `k` dimensions:
`M = A · B` with `A : n×k`, `B : k×n`.  Built by factoring `M.mulVecLin` through a basis of its range
(dim `= rank ≤ k`): lift the range-restriction along a surjection `Fin k → F ↠ range` (projectivity of
`Fin n → F`), then read off matrices via `toMatrix'`. -/
theorem rank_factorization {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (h : M.rank ≤ k) :
    ∃ (A : Matrix (Fin n) (Fin k) F) (B : Matrix (Fin k) (Fin n) F), M = A * B := by
  classical
  let f : (Fin n → F) →ₗ[F] (Fin n → F) := M.mulVecLin
  let R : Submodule F (Fin n → F) := LinearMap.range f
  have hle : Module.finrank F R ≤ k := h
  let b := Module.finBasis F R
  let proj : (Fin k → F) →ₗ[F] (Fin (Module.finrank F R) → F) :=
    LinearMap.funLeft F F (Fin.castLE hle)
  have hproj : Function.Surjective proj := by
    intro u
    exact ⟨Function.extend (Fin.castLE hle) u 0, by
      ext i
      simp only [proj, LinearMap.funLeft_apply]
      exact (Fin.castLE_injective hle).extend_apply u 0 i⟩
  let s : (Fin k → F) →ₗ[F] R := b.equivFun.symm.toLinearMap.comp proj
  have hs : Function.Surjective s := b.equivFun.symm.surjective.comp hproj
  obtain ⟨B', hB'⟩ := Module.projective_lifting_property s f.rangeRestrict hs
  refine ⟨LinearMap.toMatrix' (R.subtype.comp s), LinearMap.toMatrix' B', ?_⟩
  rw [← LinearMap.toMatrix'_comp]
  have hcomp : (R.subtype.comp s).comp B' = f := by
    rw [LinearMap.comp_assoc, hB']
    ext x; rfl
  rw [hcomp, show f = Matrix.toLin' M from (Matrix.toLin'_apply' M).symm,
    LinearMap.toMatrix'_toLin']

end PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity
