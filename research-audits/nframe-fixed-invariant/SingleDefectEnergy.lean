import PallLean.Paper93.Paper283.BridgeALocalEnergy
import Mathlib.Tactic

namespace SingleDefectEnergy
open PallLean.Paper93.Paper283 PallLean.Paper93.Concrete

def negativeCharge (N : ℕ) : TseitinCharge N := fun _ => ⟨-1, by simp⟩
def defectField {N : ℕ} (r v : Fin N) : ℝ := if v = r then 1 else -1

theorem edge_square {N : ℕ} (r a b : Fin N) :
    (defectField r a - defectField r b)^2 =
      if (a = r ∧ b ≠ r) ∨ (b = r ∧ a ≠ r) then 4 else 0 := by
  by_cases ha : a = r <;> by_cases hb : b = r <;> norm_num [defectField, ha, hb]

theorem penalty {N : ℕ} (r v : Fin N) :
    parityViolation (negativeCharge N) (defectField r) v =
      if v = r then 2 else 0 := by
  by_cases h : v = r
  all_goals norm_num [parityViolation, negativeCharge, defectField, h,
    PallLean.Paper93.Paper283.sgn, PallLean.Paper93.Paper283.posPart]

/-- Exact local cost of the one-defect field, for the existing graph convention. -/
theorem local_cost {N d : ℕ} (G : RegularGraphFixed N d) (r v : Fin N)
    (alpha beta : ℝ) :
    localEnergy alpha beta G (negativeCharge N) (defectField r) v =
      alpha * (4 * ((G.edges.filter (fun e =>
        (e.1 = v ∨ e.2 = v) ∧
        ((e.1 = r ∧ e.2 ≠ r) ∨ (e.2 = r ∧ e.1 ≠ r)))).card : ℝ)) +
      beta * (if v = r then 2 else 0) := by
  classical
  unfold localEnergy
  rw [penalty]
  simp_rw [edge_square]
  congr 1
  congr 1
  simp [Finset.sum_ite, Finset.filter_filter, mul_comm]

end SingleDefectEnergy
#print axioms SingleDefectEnergy.local_cost
