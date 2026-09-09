import PallLean.Paper93.Paper283.BridgeALocalEnergy
import Mathlib.Tactic

namespace InducedParityActivity
open PallLean.Paper93.Paper283 PallLean.Paper93.Concrete

/-- The product compatibility is derived, not postulated, for a cyclic
incidence pattern (indeed any permutation of signed edges). -/
theorem induced_product {N : ℕ} (sigma : Equiv.Perm (Fin N)) (x : Fin N → ℝ)
    (hx : ∀ v, x v = -1 ∨ x v = 1) :
    (∏ v, x v * x (sigma v)) = 1 := by
  rw [Finset.prod_mul_distrib, Equiv.prod_comp sigma]
  rw [← Finset.prod_mul_distrib]
  have hsq : ∀ v, x v * x v = 1 := by
    intro v
    rcases hx v with h | h <;> rw [h] <;> norm_num
  simp_rw [hsq]
  simp

/-- Global incidence compatibility forces a violated site for negative total charge. -/
theorem exists_violation {N : ℕ} (chi : TseitinCharge N) (Phi : Fin N → ℝ)
    (hs : ∀ v, Phi v = -1 ∨ Phi v = 1)
    (hp : ∏ v, Phi v = 1)
    (hc : (∏ v, ((chi v).val : ℝ)) = -1) :
    ∃ v, parityViolation chi Phi v = 2 := by
  have hm : ∃ v, ((chi v).val : ℝ) ≠ Phi v := by
    by_contra h
    push_neg at h
    have he : (∏ v, ((chi v).val : ℝ)) = ∏ v, Phi v := by
      apply Finset.prod_congr rfl
      intro v _
      exact h v
    rw [hc, hp] at he
    norm_num at he
  obtain ⟨v, hv⟩ := hm
  refine ⟨v, ?_⟩
  have hcv := (chi v).property
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcv
  rcases hcv with hcv | hcv <;> rcases hs v with hphi | hphi
  all_goals norm_num [hcv, hphi] at hv
  all_goals norm_num [parityViolation, hcv, hphi,
    PallLean.Paper93.Paper283.sgn, PallLean.Paper93.Paper283.posPart]

/-- Positive gradient energy cannot remove the forced local penalty. -/
theorem exists_local_energy {N d : ℕ} (G : RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N → ℝ) (alpha beta : ℝ)
    (ha : 0 ≤ alpha)
    (hs : ∀ v, Phi v = -1 ∨ Phi v = 1)
    (hp : ∏ v, Phi v = 1)
    (hc : (∏ v, ((chi v).val : ℝ)) = -1) :
    ∃ v, 2 * beta ≤ localEnergy alpha beta G chi Phi v := by
  obtain ⟨v, hv⟩ := exists_violation chi Phi hs hp hc
  refine ⟨v, ?_⟩
  unfold localEnergy
  rw [hv]
  have hgrad : 0 ≤ alpha * (∑ e ∈ G.edges.filter (fun e => e.1 = v ∨ e.2 = v),
      (Phi e.1 - Phi e.2)^2) :=
    mul_nonneg ha (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  linarith

/-- Concrete edge-induced local activity on permutation cycles of every size. -/
theorem induced_local_energy {N d : ℕ} (G : RegularGraphFixed N d)
    (sigma : Equiv.Perm (Fin N)) (x : Fin N → ℝ) (chi : TseitinCharge N)
    (alpha beta : ℝ) (ha : 0 ≤ alpha)
    (hx : ∀ v, x v = -1 ∨ x v = 1)
    (hc : (∏ v, ((chi v).val : ℝ)) = -1) :
    ∃ v, 2 * beta ≤ localEnergy alpha beta G chi (fun v => x v * x (sigma v)) v := by
  apply exists_local_energy G chi _ alpha beta ha
  · intro v
    rcases hx v with h | h <;> rcases hx (sigma v) with h' | h'
    all_goals simp [h, h']
  · exact induced_product sigma x hx
  · exact hc

end InducedParityActivity
#print axioms InducedParityActivity.exists_violation
#print axioms InducedParityActivity.exists_local_energy
#print axioms InducedParityActivity.induced_local_energy
