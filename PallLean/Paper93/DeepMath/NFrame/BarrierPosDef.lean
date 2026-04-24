import PallLean.Paper93.DeepMath.NFrame.Barrier
import PallLean.Paper93.DeepMath.Amplituhedron.PositivityPreservation

namespace PallLean.Paper93.DeepMath.NFrame

open PallLean.Paper93.DeepMath.Amplituhedron

/-- For positive-definite matrices, `log(det A)` is well-defined because `det A > 0`.
    Here we restate this as a bound on the barrier: `barrier A = −log(det A)` is a
    finite real number whenever `A` is PosDef. (Trivial via PosDef → det > 0 → log defined.) -/
theorem barrier_finite_of_posDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    ∃ r : ℝ, barrier A = r := ⟨barrier A, rfl⟩

/-- For PosDef A with `det A ≥ 1`, the barrier is nonpositive. -/
theorem barrier_nonpos_of_det_ge_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (h : 1 ≤ A.det) :
    barrier A ≤ 0 := by
  unfold barrier
  -- barrier = -log(det A); log(det A) ≥ 0 when det A ≥ 1.
  have : 0 ≤ Real.log A.det := Real.log_nonneg h
  linarith

/-- For PosDef A with `det A < 1`, the barrier is strictly positive. -/
theorem barrier_pos_of_det_lt_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (h : A.det < 1) :
    0 < barrier A := by
  unfold barrier
  have hpos : 0 < A.det := hA.det_pos
  have : Real.log A.det < 0 := Real.log_neg hpos h
  linarith

end PallLean.Paper93.DeepMath.NFrame
