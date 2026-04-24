import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace PallLean.Paper93.DeepMath.NFrame

/-- For `x > 0`, `log x ≤ 0 ↔ x ≤ 1`. -/
theorem log_nonpos_iff_le_one {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 0 ↔ x ≤ 1 := by
  constructor
  · intro h
    by_contra hgt
    push_neg at hgt
    have : 0 < Real.log x := Real.log_pos hgt
    linarith
  · intro h
    exact Real.log_nonpos hx.le h

/-- For `x > 0`, `log x ≥ 0 ↔ x ≥ 1`. -/
theorem log_nonneg_iff_ge_one {x : ℝ} (hx : 0 < x) :
    0 ≤ Real.log x ↔ 1 ≤ x := by
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    have : Real.log x < 0 := Real.log_neg hx hlt
    linarith
  · intro h
    exact Real.log_nonneg h

end PallLean.Paper93.DeepMath.NFrame
