import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen

/-!
# Information-theory foundations 1: discrete Shannon entropy

The first foundation toward information complexity (for an eventual faithful GMWW
round-elimination proof — the socket `RoundElimStep` of KRW19).  Mathlib has
`Real.negMulLog` (`x ↦ -x log x`, concave, nonneg on `[0,1]`) and binary entropy,
but not the discrete Shannon entropy of a finite distribution — built here.

* **`IsProbDist p`** — `p : α → ℝ` is a finite probability distribution;
* **`entropy p := ∑ i, negMulLog (p i)`** — Shannon entropy;
* **`prob_le_one` / `entropy_nonneg` (proved)** — `p i ≤ 1`; `H(p) ≥ 0`;
* **`entropy_le_log_card` (proved)** — `H(p) ≤ log |α|` (maximum entropy, via
  Jensen on the concave `negMulLog` with uniform weights);
* **`entropy_dirac` (proved)** — a point mass has entropy `0`.

This is real analysis (logs, concavity), not `P ≠ NP`.  It is the substrate the
information-cost / round-elimination arguments will need.
-/

namespace PallLean.Paper93.DeepMath.PathB.InfoTheory

open Real Finset

/-- `p` is a finite probability distribution: nonnegative and summing to `1`. -/
def IsProbDist {α : Type*} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- Shannon entropy `H(p) = ∑ -p_i log p_i`. -/
noncomputable def entropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

/-- Every probability is at most `1`. -/
theorem prob_le_one {α : Type*} [Fintype α] {p : α → ℝ} (hp : IsProbDist p) (i : α) :
    p i ≤ 1 := by
  calc p i ≤ ∑ j, p j := Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)
    _ = 1 := hp.2

/-- **Entropy is nonnegative (proved)**. -/
theorem entropy_nonneg {α : Type*} [Fintype α] {p : α → ℝ} (hp : IsProbDist p) :
    0 ≤ entropy p := by
  apply Finset.sum_nonneg
  intro i _
  exact Real.negMulLog_nonneg (hp.1 i) (prob_le_one hp i)

/-- **Maximum entropy (proved)**: `H(p) ≤ log |α|`, by Jensen on `negMulLog`. -/
theorem entropy_le_log_card {α : Type*} [Fintype α] [Nonempty α] {p : α → ℝ}
    (hp : IsProbDist p) : entropy p ≤ Real.log (Fintype.card α) := by
  have hnpos : 0 < Fintype.card α := Fintype.card_pos
  have hnR : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast hnpos
  have hw0 : ∀ i ∈ (Finset.univ : Finset α), (0 : ℝ) ≤ (Fintype.card α : ℝ)⁻¹ :=
    fun _ _ => by positivity
  have hw1 : ∑ _i : α, (Fintype.card α : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ (ne_of_gt hnR)]
  have hmem : ∀ i ∈ (Finset.univ : Finset α), p i ∈ Set.Ici (0 : ℝ) :=
    fun i _ => Set.mem_Ici.mpr (hp.1 i)
  have hjen := concaveOn_negMulLog.le_map_sum hw0 hw1 hmem
  simp only [smul_eq_mul] at hjen
  rw [← Finset.mul_sum, ← Finset.mul_sum, hp.2, mul_one] at hjen
  have hval : Real.negMulLog ((Fintype.card α : ℝ)⁻¹)
      = (Fintype.card α : ℝ)⁻¹ * Real.log (Fintype.card α) := by
    rw [Real.negMulLog, Real.log_inv]; ring
  rw [hval] at hjen
  have hc : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt hnR
  have hmul := mul_le_mul_of_nonneg_left hjen (le_of_lt hnR)
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hc, one_mul, one_mul] at hmul
  exact hmul

/-- **A point mass has entropy `0` (proved)**. -/
theorem entropy_dirac {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    entropy (fun i => if i = a then (1 : ℝ) else 0) = 0 := by
  rw [entropy, Finset.sum_eq_single a]
  · simp
  · intro b _ hba; simp [hba]
  · intro h; exact absurd (Finset.mem_univ a) h

end PallLean.Paper93.DeepMath.PathB.InfoTheory

#print axioms PallLean.Paper93.DeepMath.PathB.InfoTheory.entropy_le_log_card
#print axioms PallLean.Paper93.DeepMath.PathB.InfoTheory.entropy_dirac
