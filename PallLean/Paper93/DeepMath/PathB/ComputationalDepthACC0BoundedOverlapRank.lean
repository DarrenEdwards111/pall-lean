import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RandomRestrictionRank
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SatFirstMoment

/-!
# Bounded-fan-in instantiation: a low-cell-rank live set, and the exact remaining balance

This instantiates the probabilistic rank machinery with the corpus's *proved* first-moment bound
(`ACC0SatFirstMoment.exp_survivingCount_le`: `Exp p (survivingCount) ≤ k·s·p` for fan-in `≤ s`).  Plugged into
`randomRestriction_forces_low_cellRank`, it gives, for a bounded-fan-in support system, a `p`-biased restriction
whose live set has **cell rank below any threshold `a > k·s·p`**.

## What is proved (clean axioms, no `sorry`)

* **`boundedFanin_forces_low_cellRank`** — fan-in `≤ s`, `k·s·p < a` ⇒ `∃ L, cellRank supports L < a`.
* **`heavy_restriction_forces_rank_zero`** — the extreme regime: `k·s·p < 1` ⇒ `∃ L, cellRank supports L = 0` (the
  surviving supports are linearly trivial under a heavy restriction).

## Honest scope — the instantiation is real; the `|L|`-balance is the open crux

This supplies the **low-rank** half of the socket unconditionally for bounded fan-in: a live set with
`cellRank < a` (real threshold).  It does **not** close the socket `2^{cellRank} < |L|`, and the gap is precise and
genuine: the live set produced (from Markov on the survivor count) is **not guaranteed large** — indeed the empty set
`L = ∅` has `survivingCount = 0`, `cellRank = 0`, yet `|L| = 0`, so `2^{0} = 1 > 0 = |L|` and the socket *fails*
there.  The collapse needs a live set that is **simultaneously** low-rank *and* large (`|L| > 2^{cellRank}`).

That balance is the tension at the heart of the wall: a *heavy* restriction (small `p`) kills supports — few
survivors, low rank — but also leaves *few* live variables (small `|L|`); a *light* restriction keeps `|L|` large but
lets many supports survive.  Closing it needs a **two-sided** concentration argument — low cell rank *and* `|L| ≈ pn`
both with high probability, then intersect — which requires a lower-tail bound on `|L|` not yet in the corpus, and
ultimately the structural (rank-of-MOD-incidence) input for *general* `ACC⁰`.  That is the open rank-flavoured
switching lemma (`NP ⊄ ACC⁰`-strength).  This file pins exactly that gap.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BoundedOverlapRank

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictionRank
open PallLean.Paper93.DeepMath.PathB.ACC0SatFirstMoment

variable {k n : ℕ}

/-- **Bounded fan-in forces a low-cell-rank live set (proved).**  If every gate has fan-in `≤ s` and `k·s·p < a`,
some `p`-biased live set `L` has `cellRank supports L < a` — the expected survivor count `≤ k·s·p` bounds the
expected cell rank, and Markov produces such an `L`. -/
theorem boundedFanin_forces_low_cellRank (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (s : ℕ) (hfan : ∀ j, (supports j).card ≤ s)
    (a : ℝ) (ha : (k : ℝ) * s * p < a) :
    ∃ L ∈ (Finset.univ : Finset (Fin n)).powerset, (cellRank supports L : ℝ) < a := by
  have hpos : (0 : ℝ) ≤ (k : ℝ) * s * p :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg s)) hp0
  exact randomRestriction_forces_low_cellRank p hp0 hp1 supports ((k : ℝ) * s * p) a
    (by linarith) (exp_survivingCount_le p hp0 hp1 supports s hfan) ha

/-- **A heavy restriction forces cell rank `0` (proved).**  If `k·s·p < 1`, some live set has `cellRank = 0`: the
surviving supports span the trivial space.  (Even so, that `L` may be tiny — see the scope note; this gives low rank,
not the size needed for the socket.) -/
theorem heavy_restriction_forces_rank_zero (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (s : ℕ) (hfan : ∀ j, (supports j).card ≤ s)
    (hksp : (k : ℝ) * s * p < 1) :
    ∃ L ∈ (Finset.univ : Finset (Fin n)).powerset, cellRank supports L = 0 := by
  obtain ⟨L, hL, hLrank⟩ := boundedFanin_forces_low_cellRank p hp0 hp1 supports s hfan 1 hksp
  refine ⟨L, hL, ?_⟩
  -- (cellRank : ℝ) < 1 ⇒ cellRank = 0
  have : cellRank supports L < 1 := by exact_mod_cast hLrank
  omega

end PallLean.Paper93.DeepMath.PathB.ACC0BoundedOverlapRank

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedOverlapRank.boundedFanin_forces_low_cellRank
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedOverlapRank.heavy_restriction_forces_rank_zero
