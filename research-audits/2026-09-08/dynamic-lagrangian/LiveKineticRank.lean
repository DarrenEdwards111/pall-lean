import PallLean.Paper93.DeepMath.PathB.CompiledGadgetIsHessian
import PallLean.TuringMachine
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
A concrete candidate, NOT a definition of the full intended invariant.
We use the repository's kineticTermHessian and restrict it to coordinates
whose CURRENT tape bit is true. This mask is an explicit modelling choice.
The kinetic operator's matrix rank is derived, not an observer-supplied Nat.
Neither the parity nor barrier terms are included. No SAT hardness is assumed.
-/
namespace LiveKineticAudit
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

noncomputable def tapeMask (M : DTM) (n : ℕ)
    (cfg : Configuration M (tapeSize M n)) :
    Matrix (Fin (tapeSize M n)) (Fin (tapeSize M n)) ℝ :=
  Matrix.diagonal (fun i => if cfg.tape i then 1 else 0)

noncomputable def liveOperator (M : DTM) (n : ℕ)
    (cfg : Configuration M (tapeSize M n)) :
    Matrix (Fin (tapeSize M n)) (Fin (tapeSize M n)) ℝ :=
  tapeMask M n cfg * kineticTermHessian 1 (tapeSize M n) * tapeMask M n cfg

noncomputable def liveRank (M : DTM) (n : ℕ) (hn : 1 ≤ n)
    (input : Fin n → Bool) (t : ℕ) : ℕ :=
  (liveOperator M n (run M n t (initialConfig M n hn input))).rank

theorem liveRank_le_tapeSize (M : DTM) (n : ℕ) (hn : 1 ≤ n)
    (input : Fin n → Bool) (t : ℕ) :
    liveRank M n hn input t ≤ tapeSize M n := by
  exact Matrix.rank_le_width _

noncomputable def peakRank (M : DTM) (n : ℕ) (hn : 1 ≤ n)
    (input : Fin n → Bool) (T : ℕ) : ℕ :=
  (Finset.range (T + 1)).sup (liveRank M n hn input)

theorem peakRank_le_polynomial_clock (M : DTM) (n : ℕ) (hn : 1 ≤ n)
    (input : Fin n → Bool) (T : ℕ) :
    peakRank M n hn input T ≤ n ^ M.timeBound + 1 := by
  apply Finset.sup_le
  intro t _
  exact liveRank_le_tapeSize M n hn input t

theorem cumulativeRank_le_time_mul_space (M : DTM) (n : ℕ) (hn : 1 ≤ n)
    (input : Fin n → Bool) (T : ℕ) :
    (∑ t ∈ Finset.range (T + 1), liveRank M n hn input t) ≤
      (T + 1) * (n ^ M.timeBound + 1) := by
  calc
    _ ≤ ∑ _t ∈ Finset.range (T + 1), (n ^ M.timeBound + 1) := by
      apply Finset.sum_le_sum
      intro t _
      exact liveRank_le_tapeSize M n hn input t
    _ = _ := by simp

/-- The same dimension ceiling applies to ANY square live operator on these
coordinates, including a full-action Hessian if one is independently defined.
This does not bound operators on larger implicit spaces. -/
theorem any_live_matrix_rank_le_clock (M : DTM) (n : ℕ)
    (A : ℕ → Matrix (Fin (tapeSize M n)) (Fin (tapeSize M n)) ℝ) (t : ℕ) :
    (A t).rank ≤ n ^ M.timeBound + 1 := by
  exact Matrix.rank_le_width _

end LiveKineticAudit

#print axioms LiveKineticAudit.liveRank_le_tapeSize
#print axioms LiveKineticAudit.peakRank_le_polynomial_clock
#print axioms LiveKineticAudit.cumulativeRank_le_time_mul_space
#print axioms LiveKineticAudit.any_live_matrix_rank_le_clock
