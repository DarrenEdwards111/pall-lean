import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RankBridge

/-!
# Random restriction toward low cell rank — the probabilistic stepping stones

Pushing on the open target `acc0_restriction_forces_low_cellRank` (`∃ L, 2^{cellRank} < |L|`), the route is to make
the *rank* small under a random restriction.  Because `cellRank ≤ survivingCount` *pointwise*
(`…ACC0RankBridge.cellRank_le_survivingCount`), the entire `p`-biased concentration machinery built for survivor
counts transfers to cell rank *for free*:

* the **expected** cell rank is at most the expected survivor count, and
* the proved low-survival restriction existence (`exists_low_survival`) immediately yields a **low-cell-rank**
  live set.

## What is proved (clean axioms, no `sorry`)

* **`expected_cellRank_le_expected_survivors`** — `Exp p (cellRank) ≤ Exp p (survivingCount)` (monotone expectation
  of a pointwise inequality).
* **`randomRestriction_forces_low_cellRank`** — from an expected-survivor bound `Exp ≤ B < a`, there is a live set
  `L` with `cellRank supports L < a` (the probabilistic low-rank restriction; via `exists_low_survival` +
  `cellRank_le_survivingCount`).

## Honest scope — a stepping stone, not the lemma

These transfer the survivor concentration to rank, so a structured/bounded-overlap support system whose expected
survivor count is small (supplied by the existing variance/Chebyshev machinery, `…ACCSwitchingChebyshev`) also has a
small *expected cell rank* and a low-rank live set.  But `randomRestriction_forces_low_cellRank` gives `cellRank < a`
(a *real* threshold), whereas the socket needs the integer collapse `2^{cellRank} < |L|`, i.e. `cellRank < log₂|L|`
with `|L|` large *simultaneously* — the quantitative balance is exactly the open rank-flavoured switching lemma
(`NP ⊄ ACC⁰`-strength).  This file supplies the probabilistic inputs; it does not close that balance.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictionRank

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingChebyshev
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge

variable {k n : ℕ}

/-- **Expected cell rank `≤` expected survivor count (proved).**  Monotone expectation of the pointwise inequality
`cellRank ≤ survivingCount`. -/
theorem expected_cellRank_le_expected_survivors (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) :
    Exp p (fun L => (cellRank supports L : ℝ))
      ≤ Exp p (fun L => (survivingCount supports L : ℝ)) := by
  unfold Exp
  apply Finset.sum_le_sum
  intro L _
  have hle : (cellRank supports L : ℝ) ≤ (survivingCount supports L : ℝ) := by
    exact_mod_cast cellRank_le_survivingCount supports L
  exact mul_le_mul_of_nonneg_left hle (weight_nonneg p hp0 hp1 L)

/-- **A random restriction forces low cell rank (proved).**  If the expected survivor count is `≤ B < a`, some live
set `L` has `cellRank supports L < a` — the probabilistic low-rank restriction, transferred from the proved
low-survival existence via `cellRank ≤ survivingCount`. -/
theorem randomRestriction_forces_low_cellRank (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (B a : ℝ) (ha : 0 < a)
    (hE : Exp p (fun L => (survivingCount supports L : ℝ)) ≤ B) (hBa : B < a) :
    ∃ L ∈ (Finset.univ : Finset (Fin n)).powerset, (cellRank supports L : ℝ) < a := by
  obtain ⟨L, hL, hLsurv⟩ := exists_low_survival p hp0 hp1 supports B a ha hE hBa
  refine ⟨L, hL, lt_of_le_of_lt ?_ hLsurv⟩
  exact_mod_cast cellRank_le_survivingCount supports L

end PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictionRank

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictionRank.expected_cellRank_le_expected_survivors
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictionRank.randomRestriction_forces_low_cellRank
