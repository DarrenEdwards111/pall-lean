import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameFactorCircuit

/-!
# Minimality of the gate count — the padding half, and the honest core gap

To make the gate count *exactly* the rank we need `rank M ≤ k ⟹ M` factors through `k` dims.  That
splits into a **core** (factor through `rank M` dims) and **padding** (extend `rank M → k` for
`rank M ≤ k`).  This file delivers the padding cleanly.

* `factor_pad` — a factorization `M = A' · B'` through `r` dims lifts to one through `k` dims whenever
  there are conjugate rectangles `Q · R = 1` (`Q : r×k`, `R : k×r`): `M = (A'·Q) · (R·B')`.  For
  `r ≤ k` such `Q, R` exist (the coordinate inclusion and its retraction), so a factorization through
  `r ≤ k` dims *is* a factorization through `k` dims.

## Honest scope — the core is a real construction, not built here

The **core**, `rank M ≤ k ⟹ ∃` a factorization through `rank M` dims, is genuine linear algebra that
Mathlib does not provide directly: `Matrix.rank M := finrank (range M.mulVecLin)`, and turning that
finrank bound into a concrete `M = A · B` requires factoring `M.mulVecLin` through a basis of its
range (`Module.finBasis` on `range`, a section of the coordinate projection, then `toMatrix'_comp`).
That is a multi-lemma development, and I am **not** claiming it here.  What is complete: the *padding*
half above, plus the interchange from the previous files (any factorization ⇒ `k` gates ⇒ rank `≤ k`).
Together with the core, the gate count would equal the rank exactly; without it, the barrier identity
(the residual `≡` rigidity, both directions) already stands — this file only refines the *count*.

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

end PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity
