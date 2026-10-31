import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0LowRankFragment

/-!
# A structured case of `ACC0ForcesLowCellRank`: bounded number of distinct supports

The open target is `ACC0ForcesLowCellRank : ∃ L, 2^{cellRank} < |L|`.  This file discharges it for a structured class
that the *survivor* route cannot touch: support systems with a **bounded number of distinct supports**.

If `supports : Fin k → Finset (Fin n)` takes at most `d` distinct values, then `cellRank ≤ d` — **independent of the
gate count `k`**.  The reason: each cell pattern `cellPatternVec v = (v ∈ supports j)_j` is constant on each
*support-class* (the gates sharing a support), so it is a combination of the `≤ d` class-indicator vectors; the
patterns span a space of dimension `≤ d`.  This generalizes the equal-supports case (`d = 1`,
`…ACC0LowRankFragment`).  With `2^d < n`, the live set `univ` witnesses the socket and the predictor fails — even
though `survivingCount = k` (all gates survive), so the survivor collapse `2^k < |L|` is hopeless.

## What is proved (clean axioms, no `sorry`)

* `classVec` / `cellPatternVec_mem_classSpan` — the cell pattern lies in the span of the `≤ d` support-class
  indicators.
* **`cellRank_le_distinct`** — `cellRank supports L ≤ |image supports|` (the number of distinct supports).
* **`bounded_distinct_forces_low_cellRank`** — `|image supports| ≤ d`, `2^d < n` ⇒ `ACC0ForcesLowCellRank`.
* **`bounded_distinct_low_correlation`** — hence the predictor fails to correlate with the holonomy parity,
  *unconditionally*, for any gate count `k`.

## Honest scope

A genuine new structured case (`d` distinct supports, any `k`, `2^d < n`) where the survivor route is powerless and
the rank route wins.  Still a fragment: a *general* `ACC⁰` system has polynomially many *distinct* wide supports
(`d` large), so `2^d > n` and this does not apply.  Forcing low cell rank for general `ACC⁰` under a restriction
remains the open rank-flavoured switching lemma (`NP ⊄ ACC⁰`-strength).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BoundedDistinctRank

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0LowRankFragment

variable {k n : ℕ}

/-- The `F₂` indicator of the **support-class** of `T`: the gates whose support equals `T`. -/
def classVec (supports : Fin k → Finset (Fin n)) (T : Finset (Fin n)) : Fin k → ZMod 2 :=
  fun j => if supports j = T then 1 else 0

/-- **A cell pattern lies in the span of the support-class indicators (proved).**  `cellPatternVec v` is constant on
each support-class, so it is `∑_T (v ∈ T) · classVec T` over the distinct supports `T`. -/
theorem cellPatternVec_mem_classSpan (supports : Fin k → Finset (Fin n)) (v : Fin n) :
    cellPatternVec supports v ∈ Submodule.span (ZMod 2)
      (↑((Finset.univ.image supports).image (fun T => classVec supports T)) :
        Set (Fin k → ZMod 2)) := by
  have hexp : cellPatternVec supports v
      = ∑ T ∈ Finset.univ.image supports,
          (if v ∈ T then (1 : ZMod 2) else 0) • classVec supports T := by
    funext j
    simp only [cellPatternVec, Finset.sum_apply, Pi.smul_apply, classVec, smul_eq_mul]
    rw [Finset.sum_eq_single_of_mem (supports j)
          (Finset.mem_image_of_mem supports (Finset.mem_univ j))
          (fun T _ hTne => by
            have hne : supports j ≠ T := fun h => hTne h.symm
            rw [if_neg hne, mul_zero])]
    rw [if_pos rfl, mul_one]
  rw [hexp]
  apply Submodule.sum_mem
  intro T hT
  apply Submodule.smul_mem
  apply Submodule.subset_span
  rw [Finset.mem_coe, Finset.mem_image]
  exact ⟨T, hT, rfl⟩

/-- **Cell rank is at most the number of distinct supports (proved).** -/
theorem cellRank_le_distinct (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) :
    cellRank supports L ≤ (Finset.univ.image supports).card := by
  have hle : cellSpan supports L ≤ Submodule.span (ZMod 2)
      (↑((Finset.univ.image supports).image (fun T => classVec supports T)) :
        Set (Fin k → ZMod 2)) := by
    rw [cellSpan, Submodule.span_le]
    intro p hp
    rw [Finset.mem_coe, Finset.mem_image] at hp
    obtain ⟨v, _, rfl⟩ := hp
    exact cellPatternVec_mem_classSpan supports v
  calc cellRank supports L
      ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
          (↑((Finset.univ.image supports).image (fun T => classVec supports T)) :
            Set (Fin k → ZMod 2))) := Submodule.finrank_mono hle
    _ ≤ ((Finset.univ.image supports).image (fun T => classVec supports T)).card :=
        finrank_span_finset_le_card _
    _ ≤ (Finset.univ.image supports).card := Finset.card_image_le

/-- **Bounded distinct supports force low cell rank (proved): `|image| ≤ d`, `2^d < n`.**  The survivor route fails
(`survivingCount = k`), but the cell rank is `≤ d`, so `2^{cellRank} ≤ 2^d < n = |univ|`. -/
theorem bounded_distinct_forces_low_cellRank (supports : Fin k → Finset (Fin n)) (d : ℕ)
    (hd : (Finset.univ.image supports).card ≤ d) (hdn : 2 ^ d < n) :
    ACC0ForcesLowCellRank supports := by
  apply bounded_cellRank_univ_forces
  calc 2 ^ cellRank supports Finset.univ
      ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num)
        (le_trans (cellRank_le_distinct supports Finset.univ) hd)
    _ < n := hdn

/-- **Unconditional low correlation for bounded distinct supports (proved).**  Any gate count `k`; the predictor
cannot correlate with the holonomy parity. -/
theorem bounded_distinct_low_correlation (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool)
    (d : ℕ) (hd : (Finset.univ.image supports).card ≤ d) (hdn : 2 ^ d < n) :
    LowHolonomyCorrelation supports g :=
  low_cellRank_low_correlation supports g (bounded_distinct_forces_low_cellRank supports d hd hdn)

end PallLean.Paper93.DeepMath.PathB.ACC0BoundedDistinctRank

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedDistinctRank.cellRank_le_distinct
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedDistinctRank.bounded_distinct_forces_low_cellRank
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedDistinctRank.bounded_distinct_low_correlation
