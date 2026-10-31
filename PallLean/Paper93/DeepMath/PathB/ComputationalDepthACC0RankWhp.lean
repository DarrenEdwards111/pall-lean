import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RankBridge

/-!
# The rank whp route — the two-event intersection with the *rank* tail (strictly weaker feasibility)

`ACCSwitchingPipeline.bounded_overlap_predictor_fails_whp` already intersects two tail events — "too many survivors"
(`survivingCount ≥ a`) and "too few live" (`|L| ≤ b`) — to produce a restriction with `2^{survivingCount} < |L|`,
hence low correlation, *whenever* the feasibility `Pr[survivingCount ≥ a] + Pr[|L| ≤ b] < 1` holds (with `2^a ≤ b`).

This file gives the **rank** version of that whp argument, keyed on the cell-rank tail `Pr[cellRank ≥ a]`.  Because
`cellRank ≤ survivingCount` pointwise, the rank tail is **never larger** than the survivor tail, so the rank
feasibility condition is **strictly weaker** — the rank whp route succeeds in *more* cases (whenever the survivor one
does, and also when only the rank tail is small).

## What is proved (clean axioms, no `sorry`)

* `Pr_mono` — monotonicity of the `p`-biased measure (`E ⊆ F ⇒ Pr E ≤ Pr F`).
* **`rank_predictor_fails_whp`** — `2^a ≤ b` and `Pr[cellRank ≥ a] + Pr[|L| ≤ b] < 1` ⇒ low holonomy correlation
  (two-event intersection `+` the sharp rank bridge).
* **`rank_feasibility_le_survivor`** — `Pr[cellRank ≥ a] + Pr[|L| ≤ b] ≤ Pr[survivingCount ≥ a] + Pr[|L| ≤ b]`:
  the rank feasibility is at most the survivor feasibility.
* **`rank_whp_of_survivor_feasible`** — hence the rank whp route fires whenever the *survivor* feasibility holds: it
  **subsumes** `bounded_overlap_predictor_fails_whp`.

## Honest scope — the feasibility is still the open balance

This is the sharpest whp formulation: the joint feasibility `Pr[cellRank ≥ a] + Pr[|L| ≤ b] < 1` with `2^a ≤ b` now
uses the *rank* tail.  But that feasibility is exactly the open quantitative balance — a restriction that is
*simultaneously* low-rank (`cellRank < a`) and large (`|L| > b ≥ 2^a`).  The rank tail makes the "low-rank" half
easier, but bounding `Pr[cellRank ≥ a]` for *general* poly-many overlapping `ACC⁰` supports under a restriction needs
the structural rank-of-`MOD`-incidence input — the open rank-flavoured switching lemma (`NP ⊄ ACC⁰`-strength).  This
file supplies the strongest reduction; it does not close that balance.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RankWhp

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingChebyshev
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge

variable {k n : ℕ}

/-- **Monotonicity of the `p`-biased measure (proved): `E ⊆ F ⇒ Pr E ≤ Pr F`.** -/
theorem Pr_mono (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E F : Finset (Fin n) → Prop)
    (hEF : ∀ L, E L → F L) : Pr p E ≤ Pr p F := by
  unfold Pr
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro L hL
    rw [Finset.mem_filter] at hL ⊢
    exact ⟨hL.1, hEF L hL.2⟩
  · intro L _ _
    exact weight_nonneg p hp0 hp1 L

/-- **The rank whp route (proved): the two-event intersection with the rank tail.**  If `2^a ≤ b` and the rank tail
plus the small-live tail sum to `< 1`, some restriction is low-rank (`cellRank < a`) and large (`|L| > b ≥ 2^a`), so
`2^{cellRank} < |L|` and the sharp rank bridge gives low correlation. -/
theorem rank_predictor_fails_whp (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool) (a b : ℕ) (hab : 2 ^ a ≤ b)
    (hfeas : Pr p (fun L => a ≤ cellRank supports L)
        + Pr p (fun L : Finset (Fin n) => L.card ≤ b) < 1) :
    LowHolonomyCorrelation supports g := by
  obtain ⟨L, _, hnot1, hnot2⟩ := exists_both_of_pr_add_lt_one p hp0 hp1
    (fun L : Finset (Fin n) => a ≤ cellRank supports L)
    (fun L : Finset (Fin n) => L.card ≤ b) hfeas
  push_neg at hnot1 hnot2
  have hkey : 2 ^ cellRank supports L < L.card :=
    calc 2 ^ cellRank supports L < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) hnot1
      _ ≤ b := hab
      _ < L.card := hnot2
  exact rank_collapse_low_correlation supports g L hkey

/-- **The rank feasibility is at most the survivor feasibility (proved).**  Since `cellRank ≤ survivingCount`, the
rank tail `Pr[cellRank ≥ a]` is at most the survivor tail `Pr[survivingCount ≥ a]`. -/
theorem rank_feasibility_le_survivor (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (a b : ℕ) :
    Pr p (fun L => a ≤ cellRank supports L) + Pr p (fun L : Finset (Fin n) => L.card ≤ b)
      ≤ Pr p (fun L => a ≤ survivingCount supports L)
        + Pr p (fun L : Finset (Fin n) => L.card ≤ b) := by
  gcongr
  apply Pr_mono p hp0 hp1
  intro L hL
  exact le_trans hL (cellRank_le_survivingCount supports L)

/-- **The rank whp route subsumes the survivor one (proved).**  Whenever the *survivor* feasibility holds, the rank
feasibility holds too (it is no larger), so the rank route fires — strictly more general than
`bounded_overlap_predictor_fails_whp`. -/
theorem rank_whp_of_survivor_feasible (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool) (a b : ℕ) (hab : 2 ^ a ≤ b)
    (hfeas : Pr p (fun L => a ≤ survivingCount supports L)
        + Pr p (fun L : Finset (Fin n) => L.card ≤ b) < 1) :
    LowHolonomyCorrelation supports g :=
  rank_predictor_fails_whp p hp0 hp1 supports g a b hab
    (lt_of_le_of_lt (rank_feasibility_le_survivor p hp0 hp1 supports a b) hfeas)

end PallLean.Paper93.DeepMath.PathB.ACC0RankWhp

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RankWhp.rank_predictor_fails_whp
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RankWhp.rank_feasibility_le_survivor
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RankWhp.rank_whp_of_survivor_feasible
