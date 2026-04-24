import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetSumZero
import PallLean.Paper93.DeepMath.GadgetRank.NonzeroFromQuad
import PallLean.Paper93.DeepMath.GadgetRank.IdentityQuad
import Mathlib.Tactic.Linarith

namespace PallLean.Paper93.DeepMath.GadgetRank

/-- For `n ≥ 2`, the sum-zero subspace is nontrivial: `(1, -1, 0, 0, ..., 0)` is nonzero
    and has zero coordinate-sum. -/
theorem exists_nonzero_sumZero (n : ℕ) (hn : 2 ≤ n) :
    ∃ v : Fin n → ℝ, v ≠ 0 ∧ ∑ i, v i = 0 := by
  have h0_lt_n : 0 < n := by omega
  have h1_lt_n : 1 < n := by omega
  let i0 : Fin n := ⟨0, h0_lt_n⟩
  let i1 : Fin n := ⟨1, h1_lt_n⟩
  have hne : i0 ≠ i1 := by
    intro h
    have : (0 : ℕ) = 1 := by
      have := congrArg Fin.val h
      simpa using this
    exact absurd this (by decide)
  refine ⟨fun i => if i = i0 then (1 : ℝ) else if i = i1 then -1 else 0, ?_, ?_⟩
  · -- nonzero: at i0 value is 1
    intro h
    have h0 : (fun i : Fin n => if i = i0 then (1 : ℝ) else if i = i1 then -1 else 0) i0
              = (0 : Fin n → ℝ) i0 := by rw [h]
    simp at h0
  · -- sum = 0: split by i0, i1, others
    have h_i0_mem : i0 ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
    have h_i1_mem : i1 ∈ ((Finset.univ : Finset (Fin n)).erase i0) :=
      Finset.mem_erase.mpr ⟨fun h => hne h.symm, Finset.mem_univ _⟩
    rw [Finset.sum_erase_add _ _ h_i0_mem |>.symm]
    rw [Finset.sum_erase_add _ _ h_i1_mem |>.symm]
    have h_rest : ∀ i ∈ ((Finset.univ : Finset (Fin n)).erase i0).erase i1,
        (if i = i0 then (1 : ℝ) else if i = i1 then -1 else 0) = 0 := by
      intro i hi
      rw [Finset.mem_erase, Finset.mem_erase] at hi
      obtain ⟨hi1, hi0, _⟩ := hi
      simp [hi0, hi1]
    rw [Finset.sum_congr rfl h_rest]
    simp [hne, hne.symm]

/-- For `n ≥ 2` and `α > 0`, the compiled gadget is a nonzero matrix. -/
theorem compiledGadget_ne_zero (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    compiledGadget α n ≠ 0 := by
  rcases exists_nonzero_sumZero n hn with ⟨v, hv_ne, hv_sum⟩
  apply ne_zero_of_quad_pos (compiledGadget α n) v
  rw [compiledGadget_quadForm_sumZero α n v hv_sum]
  -- goal: 0 < (α + n) * ∑ v_i * v_i
  have h_sum_pos := sum_sq_pos_of_ne_zero v hv_ne
  have h_coef_pos : (0 : ℝ) < α + n := by
    have hn_cast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  exact mul_pos h_coef_pos h_sum_pos

end PallLean.Paper93.DeepMath.GadgetRank
