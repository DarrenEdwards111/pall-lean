import PallLean.Paper93.NFrame.UnitPreservingAdmissible
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic

/-!
# Unit-preserving N-frame value set

This file repeats the S2 value-set/minimizer construction with the
strengthened predicate `UnitPreservingAdmissibleGauge`.  Unlike the raw
`AdmissibleGauge` surface, the unit-preserving surface excludes the zero
projection, so its attained natural minimum is positive.
-/

namespace PallLean
namespace Paper93
namespace NFrame

open MvPolynomial

/-! ## Explicit unit-preserving inhabitant -/

/-- The concrete constants projection, viewed as the preferred
unit-preserving candidate gauge. -/
noncomputable def unitPreservingConstantsGauge (N : ℕ) : CandidateGauge N :=
  PallLean.Paper93.Substantive.nonTrivialGauge N

/-- The preferred witness is literally the projection onto constants. -/
theorem unitPreservingConstantsGauge_projection (N : ℕ) :
    (unitPreservingConstantsGauge N).projection =
      PallLean.Paper93.Substantive.toConstantsProjection N := by
  rfl

/-- The concrete constants projection is unit-preserving admissible. -/
theorem unitPreservingConstantsGauge_admissible (N : ℕ) :
    UnitPreservingAdmissibleGauge (unitPreservingConstantsGauge N) := by
  exact nonTrivialGauge_unitPreserving N

/-! ## Value set -/

/-- Natural Lagrangian values attained by unit-preserving admissible gauges. -/
def unitPreservingLagrangianNatValues (N : ℕ) : Set ℕ :=
  {v : ℕ | ∃ gauge : CandidateGauge N,
    UnitPreservingAdmissibleGauge gauge ∧ lagrangianNat gauge = v}

/-- The constants projection contributes an explicit value to the value set. -/
theorem unitPreservingConstantsGauge_mem_values (N : ℕ) :
    lagrangianNat (unitPreservingConstantsGauge N)
      ∈ unitPreservingLagrangianNatValues N := by
  exact ⟨unitPreservingConstantsGauge N,
    unitPreservingConstantsGauge_admissible N, rfl⟩

/-- The unit-preserving value set is nonempty. -/
theorem unitPreservingLagrangianNatValues_nonempty (N : ℕ) :
    (unitPreservingLagrangianNatValues N).Nonempty := by
  exact ⟨lagrangianNat (unitPreservingConstantsGauge N),
    unitPreservingConstantsGauge_mem_values N⟩

/-- Every unit-preserving admissible gauge has positive natural rank value. -/
theorem unitPreservingGauge_lagrangianNat_pos
    {N : ℕ} {gauge : CandidateGauge N}
    (h : UnitPreservingAdmissibleGauge gauge) :
    0 < lagrangianNat gauge := by
  have hposR : 0 < (lagrangianNat gauge : ℝ) := unitPreserving_lagrangianNat_pos h
  exact Nat.cast_pos.mp hposR

/-- Every attained unit-preserving value is positive. -/
theorem unitPreservingLagrangianNatValues_pos
    {N v : ℕ} (hv : v ∈ unitPreservingLagrangianNatValues N) :
    0 < v := by
  obtain ⟨gauge, hUnit, hval⟩ := hv
  simpa [hval] using unitPreservingGauge_lagrangianNat_pos hUnit

/-- Zero is not attained by any unit-preserving admissible gauge. -/
theorem zero_not_mem_unitPreservingLagrangianNatValues (N : ℕ) :
    (0 : ℕ) ∉ unitPreservingLagrangianNatValues N := by
  intro hzero
  exact (Nat.lt_irrefl 0) (unitPreservingLagrangianNatValues_pos hzero)

/-! ## Attained minimum and minimizer surface -/

/-- The minimum natural Lagrangian value over unit-preserving gauges. -/
noncomputable def unitPreservingLagrangianNatMin (N : ℕ) : ℕ :=
  sInf (unitPreservingLagrangianNatValues N)

/-- The unit-preserving natural minimum is attained. -/
theorem unitPreservingLagrangianNatMin_mem (N : ℕ) :
    unitPreservingLagrangianNatMin N
      ∈ unitPreservingLagrangianNatValues N :=
  Nat.sInf_mem (unitPreservingLagrangianNatValues_nonempty N)

/-- The unit-preserving minimum bounds every unit-preserving value. -/
theorem unitPreservingLagrangianNatMin_le
    {N : ℕ} {gauge : CandidateGauge N}
    (h : UnitPreservingAdmissibleGauge gauge) :
    unitPreservingLagrangianNatMin N ≤ lagrangianNat gauge :=
  Nat.sInf_le ⟨gauge, h, rfl⟩

/-- A unit-preserving natural-Lagrangian minimizer exists. -/
theorem unitPreservingLagrangianNat_minimizer_exists (N : ℕ) :
    ∃ gauge : CandidateGauge N,
      UnitPreservingAdmissibleGauge gauge ∧
        lagrangianNat gauge = unitPreservingLagrangianNatMin N :=
  unitPreservingLagrangianNatMin_mem N

/-- The unit-preserving natural minimum is positive. -/
theorem unitPreservingLagrangianNatMin_pos (N : ℕ) :
    0 < unitPreservingLagrangianNatMin N :=
  unitPreservingLagrangianNatValues_pos
    (unitPreservingLagrangianNatMin_mem N)

/-- In particular, the unit-preserving minimum is not zero. -/
theorem unitPreservingLagrangianNatMin_ne_zero (N : ℕ) :
    unitPreservingLagrangianNatMin N ≠ 0 :=
  Nat.pos_iff_ne_zero.mp (unitPreservingLagrangianNatMin_pos N)

/-- The constants projection gives an explicit upper bound for the
unit-preserving minimum. -/
theorem unitPreservingLagrangianNatMin_le_constants (N : ℕ) :
    unitPreservingLagrangianNatMin N ≤
      lagrangianNat (unitPreservingConstantsGauge N) :=
  unitPreservingLagrangianNatMin_le
    (unitPreservingConstantsGauge_admissible N)

/-- The real N-frame Lagrangian attains its minimum on the
unit-preserving admissible surface. -/
theorem unitPreserving_minimizer_exists {N : ℕ}
    (family : ℕ → MvPolynomial (Fin N) ℚ) :
    ∃ Pi : CandidateGauge N, UnitPreservingAdmissibleGauge Pi ∧
      ∀ Pi' : CandidateGauge N, UnitPreservingAdmissibleGauge Pi' →
        nframeLagrangian family Pi ≤ nframeLagrangian family Pi' := by
  obtain ⟨PiStar, hUnit, hval⟩ := unitPreservingLagrangianNatMin_mem N
  refine ⟨PiStar, hUnit, ?_⟩
  intro Pi' hUnit'
  rw [nframeLagrangian_eq_proxy family PiStar,
      nframeLagrangian_eq_proxy family Pi']
  have hleNat : unitPreservingLagrangianNatMin N ≤ lagrangianNat Pi' :=
    unitPreservingLagrangianNatMin_le hUnit'
  have hStarNat : lagrangianNat PiStar = unitPreservingLagrangianNatMin N := hval
  have hleRank : (lagrangianNat PiStar : ℝ) ≤ (lagrangianNat Pi' : ℝ) := by
    rw [hStarNat]
    exact_mod_cast hleNat
  let a : ℝ := (lagrangianNat PiStar : ℝ)
  let b : ℝ := (lagrangianNat Pi' : ℝ)
  have ha : 0 ≤ a := by
    dsimp [a]
    exact Nat.cast_nonneg _
  have hba : 0 ≤ b - a := by
    dsimp [a, b]
    linarith
  have hmono : 2 * a + 1 / (1 + a) ≤ 2 * b + 1 / (1 + b) := by
    have hb : 0 ≤ b := by
      dsimp [b]
      exact Nat.cast_nonneg _
    have hden : 0 < (1 + a) * (1 + b) := by positivity
    have hden_ge_one : 1 ≤ (1 + a) * (1 + b) := by nlinarith [ha, hb]
    have hinv_le_one : 1 / ((1 + a) * (1 + b)) ≤ 1 := by
      simpa [one_div] using inv_le_one_of_one_le₀ hden_ge_one
    have hfacNonneg : 0 ≤ 2 - 1 / ((1 + a) * (1 + b)) := by linarith
    have hmulNonneg : 0 ≤ (b - a) * (2 - 1 / ((1 + a) * (1 + b))) :=
      mul_nonneg hba hfacNonneg
    have hdiff :
        (2 * b + 1 / (1 + b)) - (2 * a + 1 / (1 + a)) =
          (b - a) * (2 - 1 / ((1 + a) * (1 + b))) := by
      field_simp [hden.ne']
      ring_nf
    have : 0 ≤ (2 * b + 1 / (1 + b)) - (2 * a + 1 / (1 + a)) := by
      rw [hdiff]
      exact hmulNonneg
    linarith
  simpa [a, b] using hmono

end NFrame
end Paper93
end PallLean
