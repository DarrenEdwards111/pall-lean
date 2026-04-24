import PallLean.Paper93.DeepMath.NFrame.Barrier

namespace PallLean.Paper93.DeepMath.NFrame

/-- For PosDef A and B with `A.det ≤ B.det`, `barrier A ≥ barrier B`.
    (Since `barrier = -log det` and `-log` is anti-monotone on positives.) -/
theorem barrier_antitone_det {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : 0 < A.det) (hle : A.det ≤ B.det) :
    barrier B ≤ barrier A := by
  unfold barrier
  have hB : 0 < B.det := lt_of_lt_of_le hA hle
  have hlog : Real.log A.det ≤ Real.log B.det := Real.log_le_log hA hle
  linarith

end PallLean.Paper93.DeepMath.NFrame
