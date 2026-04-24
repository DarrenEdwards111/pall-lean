import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace PallLean.Paper93.DeepMath.NFrame

/-- For `n ≥ 2`, the sum-zero subspace of `Fin n → ℝ` contains a nonzero vector. -/
theorem exists_nonzero_sum_zero (n : ℕ) (hn : 2 ≤ n) :
    ∃ phi : Fin n → ℝ, phi ≠ 0 ∧ ∑ i, phi i = 0 := by
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  let i0 : Fin n := ⟨0, h0⟩
  let i1 : Fin n := ⟨1, h1⟩
  have hne : i0 ≠ i1 := by
    intro h
    have hv : (0 : ℕ) = 1 := congrArg Fin.val h
    exact absurd hv (by norm_num)
  refine ⟨fun i => if i = i0 then (1 : ℝ) else if i = i1 then -1 else 0, ?_, ?_⟩
  · -- nonzero: value at i0 is 1 ≠ 0
    intro h
    have heval :
        (fun i : Fin n => if i = i0 then (1:ℝ) else if i = i1 then -1 else 0) i0 =
          (0 : Fin n → ℝ) i0 := by
      rw [h]
    simp at heval
  · -- sum = 0: split the `if` into two indicators and use `sum_ite_eq'`.
    have hfun :
        (fun i : Fin n => if i = i0 then (1:ℝ) else if i = i1 then -1 else 0) =
        (fun i : Fin n =>
          (if i = i0 then (1:ℝ) else 0) + (if i = i1 then (-1:ℝ) else 0)) := by
      funext i
      by_cases hi0 : i = i0
      · rw [hi0]
        have hi1' : i0 ≠ i1 := hne
        simp [hi1']
      · by_cases hi1 : i = i1
        · rw [hi1]
          have hi0' : i1 ≠ i0 := fun h => hne h.symm
          simp [hi0']
        · simp [hi0, hi1]
    -- Now rewrite the sum using hfun and distribute.
    calc ∑ i, (fun j : Fin n =>
              if j = i0 then (1:ℝ) else if j = i1 then -1 else 0) i
        = ∑ i, ((if i = i0 then (1:ℝ) else 0) + (if i = i1 then (-1:ℝ) else 0)) := by
              rw [hfun]
      _ = (∑ i, (if i = i0 then (1:ℝ) else 0)) +
          (∑ i, (if i = i1 then (-1:ℝ) else 0)) := by
              rw [Finset.sum_add_distrib]
      _ = 1 + (-1) := by
              congr 1
              · rw [Finset.sum_ite_eq' Finset.univ i0 (fun _ => (1:ℝ))]
                simp
              · rw [Finset.sum_ite_eq' Finset.univ i1 (fun _ => (-1:ℝ))]
                simp
      _ = 0 := by ring

end PallLean.Paper93.DeepMath.NFrame
