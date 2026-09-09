import PallLean.Paper93.Paper283.BridgeALocalEnergy
import Mathlib.Tactic

namespace LocalEnergyParityGap
open PallLean.Paper93.Paper283 PallLean.Paper93.Concrete

def minusCharge (N : ℕ) : TseitinCharge N := fun _ => ⟨-1, by simp⟩

/-- The actual local-energy formula vanishes at the constant negative field,
for the constant negative charge, on every graph. -/
theorem local_energy_zero {N d : ℕ} (G : RegularGraphFixed N d)
    (alpha beta : ℝ) (v : Fin N) :
    localEnergy alpha beta G (minusCharge N) (fun _ => -1) v = 0 := by
  norm_num [localEnergy, parityViolation, minusCharge, PallLean.Paper93.Paper283.sgn, PallLean.Paper93.Paper283.posPart]

/-- Hence no vertex meets a positive activity threshold in this field. -/
theorem no_active_vertex {N d : ℕ} (G : RegularGraphFixed N d)
    (alpha beta threshold : ℝ) (ht : 0 < threshold) :
    ¬ ∃ v, threshold ≤ localEnergy alpha beta G (minusCharge N) (fun _ => -1) v := by
  simp only [local_energy_zero]
  exact fun ⟨_, h⟩ => (not_le_of_gt ht) h

/-- The triangle's three negative vertex-product constraints are inconsistent,
even allowing arbitrary real edge labels, hence also for signed Boolean labels. -/
theorem triangle_constraints_inconsistent :
    ¬ ∃ x y z : ℝ, x*y = -1 ∧ y*z = -1 ∧ z*x = -1 := by
  rintro ⟨x, y, z, hxy, hyz, hzx⟩
  have h : (x*y*z)^2 = -1 := by
    calc
      (x*y*z)^2 = (x*y)*(y*z)*(z*x) := by ring
      _ = -1 := by rw [hxy, hyz, hzx]; norm_num
  nlinarith [sq_nonneg (x*y*z)]

/-- Concrete zero-energy field on the triangle; this is not an edge assignment. -/
theorem triangle_zero_energy (alpha beta : ℝ) :
    ∀ v : Fin 3, localEnergy alpha beta (cycleGraphFixed 3)
      (minusCharge 3) (fun _ => -1) v = 0 :=
  local_energy_zero (cycleGraphFixed 3) alpha beta

/-- With the explicit edge-to-vertex incidence map, the same violation
function does detect the triangle contradiction. This is a restricted,
concrete coupling result, not a universal machine semantics theorem. -/
theorem induced_triangle_violation (x y z : ℝ)
    (hx : x = -1 ∨ x = 1) (hy : y = -1 ∨ y = 1) (hz : z = -1 ∨ z = 1) :
    2 ≤ ∑ v : Fin 3, parityViolation (minusCharge 3) ![x*y, y*z, z*x] v := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz
  all_goals subst x; subst y; subst z
  all_goals norm_num [Fin.sum_univ_succ, parityViolation, minusCharge, PallLean.Paper93.Paper283.sgn, PallLean.Paper93.Paper283.posPart]

end LocalEnergyParityGap

#print axioms LocalEnergyParityGap.triangle_constraints_inconsistent
#print axioms LocalEnergyParityGap.triangle_zero_energy
#print axioms LocalEnergyParityGap.no_active_vertex
#print axioms LocalEnergyParityGap.induced_triangle_violation
