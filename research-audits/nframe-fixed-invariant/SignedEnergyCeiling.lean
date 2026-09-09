import PallLean.Paper93.Paper283.BridgeALocalEnergy
import Mathlib.Tactic

namespace SignedEnergyCeiling
open PallLean.Paper93.Paper283 PallLean.Paper93.Concrete

theorem penalty_le_two {N : ℕ} (chi : TseitinCharge N) (Phi : Fin N → ℝ)
    (hs : ∀ v, Phi v = -1 ∨ Phi v = 1) (v : Fin N) :
    parityViolation chi Phi v ≤ 2 := by
  have hc := (chi v).property
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  rcases hc with hc | hc <;> rcases hs v with h | h
  all_goals norm_num [parityViolation, hc, h,
    PallLean.Paper93.Paper283.sgn, PallLean.Paper93.Paper283.posPart]

/-- A deliberately loose but uniform bound using the actual stored edge count. -/
theorem local_upper {N d : ℕ} (G : RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N → ℝ) (alpha beta : ℝ)
    (ha : 0 ≤ alpha) (hb : 0 ≤ beta)
    (hs : ∀ v, Phi v = -1 ∨ Phi v = 1) (v : Fin N) :
    localEnergy alpha beta G chi Phi v ≤ 4 * alpha * G.edges.card + 2 * beta := by
  classical
  have hsq : ∀ a b, (Phi a - Phi b)^2 ≤ 4 := by
    intro a b
    rcases hs a with h | h <;> rcases hs b with h' | h'
    all_goals norm_num [h, h']
  have hsum : (∑ e ∈ G.edges.filter (fun e => e.1 = v ∨ e.2 = v),
      (Phi e.1 - Phi e.2)^2) ≤ (G.edges.card : ℝ) * 4 := by
    calc
      _ ≤ ∑ e ∈ G.edges, (Phi e.1 - Phi e.2)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
      _ ≤ ∑ _e ∈ G.edges, (4 : ℝ) := Finset.sum_le_sum (fun _ _ => hsq _ _)
      _ = _ := by simp
  have hp := mul_le_mul_of_nonneg_left (penalty_le_two chi Phi hs v) hb
  have hg := mul_le_mul_of_nonneg_left hsum ha
  unfold localEnergy
  nlinarith

theorem total_upper {N d : ℕ} (G : RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N → ℝ) (alpha beta : ℝ)
    (ha : 0 ≤ alpha) (hb : 0 ≤ beta)
    (hs : ∀ v, Phi v = -1 ∨ Phi v = 1) :
    (∑ v, localEnergy alpha beta G chi Phi v) ≤
      (N : ℝ) * (4 * alpha * G.edges.card + 2 * beta) := by
  simpa [mul_add] using Finset.sum_le_sum (s := Finset.univ)
    (fun v _ => local_upper G chi Phi alpha beta ha hb hs v)

end SignedEnergyCeiling
#print axioms SignedEnergyCeiling.total_upper
