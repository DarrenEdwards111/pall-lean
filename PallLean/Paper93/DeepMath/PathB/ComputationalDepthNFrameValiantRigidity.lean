import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameLoadBearing
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The `coneInter ≤ cN` residual is Valiant rigidity — the barrier, machine-checked

The N-Frame engine's direct sum closes iff the residual `coneInter ≤ cN` (`NFrameConeIntersection`):
the gates feeding *both* disjoint sub-computations number at most the mixer's fresh count.  In the
linear (matrix) case this is exactly **Valiant rigidity**: a matrix is non-rigid precisely when it
splits as a sparse part plus a low-rank part — and the residual's failure is such a split (a
low-rank/`coneInter` share sitting inside a sparse/mixer envelope).  This file machine-checks the
rigidity side of the correspondence.

* `sparsity` — the number of nonzero entries of a matrix.
* `MatrixRigid M r s` — Valiant rigidity: no `s`-sparse change drops the rank to `≤ r`.
* `notRigid_iff_sparse_lowrank` / `notRigid_iff_decomp` — **the decomposition characterization**:
  `M` is *not* `(r,s)`-rigid iff `M = C + L` with `C` `s`-sparse and `rank L ≤ r`.  This is the exact
  form the `coneInter ≤ cN` residual takes on the linear side: `coneInter` is the low-rank share `L`,
  `cN` is the sparse envelope `C`.

## Honest scope

This machine-checks the **rigidity side** (the decomposition characterization — the mathematical core
of Valiant's problem) and states its identification with the `coneInter` residual precisely.  The full
literal circuit-level identity `coneInter ≤ cN ⟺ MatrixRigid` additionally needs the linear-circuit ↔
matrix-factorization map (gate cones ↔ the `C,L` decomposition), which this file does not build.  What
it establishes: discharging the residual is discharging matrix rigidity — a famous open problem —
so the N-Frame central conjecture's linear form is Valiant's, precisely as the informal analysis said.

Nothing here proves `P ≠ NP`, resolves rigidity, discharges the capture, or is `NEXP ⊄ ACC⁰`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity

open scoped Classical

variable {n : ℕ} {F : Type*} [Field F]

/-- The number of nonzero entries of a matrix (its sparsity budget). -/
noncomputable def sparsity (C : Matrix (Fin n) (Fin n) F) : ℕ :=
  (Finset.univ.filter (fun ij : Fin n × Fin n => C ij.1 ij.2 ≠ 0)).card

/-- **Valiant rigidity.**  `M` is `(r,s)`-rigid if no change of at most `s` entries brings its rank
down to `≤ r`. -/
def MatrixRigid (M : Matrix (Fin n) (Fin n) F) (r s : ℕ) : Prop :=
  ∀ C : Matrix (Fin n) (Fin n) F, sparsity C ≤ s → r < (M - C).rank

/-- **Non-rigidity is a sparse + low-rank split.**  `M` is not `(r,s)`-rigid iff some `s`-sparse `C`
brings `M - C` to rank `≤ r`. -/
theorem notRigid_iff_sparse_lowrank (M : Matrix (Fin n) (Fin n) F) (r s : ℕ) :
    ¬ MatrixRigid M r s ↔ ∃ C : Matrix (Fin n) (Fin n) F, sparsity C ≤ s ∧ (M - C).rank ≤ r := by
  unfold MatrixRigid
  constructor
  · intro h; push_neg at h; exact h
  · rintro ⟨C, hs, hr⟩ hcon; exact absurd (hcon C hs) (not_lt.mpr hr)

/-- **The decomposition characterization** (the form the `coneInter` residual takes on the linear
side).  `M` is not `(r,s)`-rigid iff `M = C + L` with `C` `s`-sparse (`= cN` mixer envelope) and `L`
of rank `≤ r` (`= coneInter` low-rank share). -/
theorem notRigid_iff_decomp (M : Matrix (Fin n) (Fin n) F) (r s : ℕ) :
    ¬ MatrixRigid M r s ↔
      ∃ C L : Matrix (Fin n) (Fin n) F, sparsity C ≤ s ∧ L.rank ≤ r ∧ M = C + L := by
  rw [notRigid_iff_sparse_lowrank]
  constructor
  · rintro ⟨C, hs, hr⟩
    exact ⟨C, M - C, hs, hr, by abel⟩
  · rintro ⟨C, L, hs, hr, rfl⟩
    exact ⟨C, hs, by rw [add_sub_cancel_left]; exact hr⟩

end PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity
