import PallLean.Paper93.DeepMath.NFrame.ParityPenaltyBounded

namespace PallLean.Paper93.DeepMath.NFrame

/-- `parityTerm chi_v ·` is bounded below by 0 and above by 2 (for `|chi_v| ≤ 1`). -/
theorem parityTerm_bounded (chi_v phi_v : ℝ) (hchi : |chi_v| ≤ 1) :
    0 ≤ parityTerm chi_v phi_v ∧ parityTerm chi_v phi_v ≤ 2 :=
  ⟨parityTerm_nonneg chi_v phi_v, parityTerm_le_two chi_v phi_v hchi⟩

/-- For all valid (|chi_i| ≤ 1) vectors, `parityPenalty ≤ 2·n`. -/
theorem parityPenalty_upper_bound {n : ℕ} (chi phi : Fin n → ℝ)
    (hchi : ∀ i, |chi i| ≤ 1) :
    parityPenalty chi phi ≤ 2 * n := by
  unfold parityPenalty
  calc ∑ v, parityTerm (chi v) (phi v)
      ≤ ∑ v : Fin n, (2 : ℝ) := Finset.sum_le_sum (fun v _ => parityTerm_le_two _ _ (hchi v))
    _ = 2 * n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp [nsmul_eq_mul]
        ring

end PallLean.Paper93.DeepMath.NFrame
