import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BoundedDistinctRank

/-!
# Low-dimensional support-span ⇒ low cell rank — the natural next N-Frame theorem

This generalizes the bounded-distinct-supports case (`…ACC0BoundedDistinctRank`).  Instead of counting *distinct*
supports, we bound the **F₂-dimension of the support indicators**: if every support indicator
`(i ∈ supports j)_i` is an `F₂`-linear combination of `r` fixed vectors `B₁,…,B_r`, then the cell rank is `≤ r`
— regardless of the gate count `k` *and* the number of distinct supports.

The mechanism: with `(i ∈ supports j) = ∑_m c_{j,m} B_m(i)`, each cell pattern is
`cellPatternVec v = ∑_m B_m(v) · (c_{·,m})`, a combination of the `r` coefficient vectors `c_{·,m} ∈ F₂^k`.  So the
patterns span a space of dimension `≤ r`, giving `cellRank ≤ r`.  This is the column-rank `≤` row-rank bound made
constructive (via the explicit coefficients), avoiding any abstract row-rank = column-rank appeal.

## What is proved (clean axioms, no `sorry`)

* `SupportsInRankSpan supports r` — the support indicators are `F₂`-combinations of `r` fixed vectors.
* **`cellRank_le_of_span`** — `SupportsInRankSpan supports r ⇒ cellRank supports L ≤ r`.
* **`supportSpan_forces_low_cellRank`** — `SupportsInRankSpan supports r`, `2^r < n` ⇒ `ACC0ForcesLowCellRank`.
* **`supportSpan_low_correlation`** — hence the predictor fails to correlate, *unconditionally*, for any `k`.

## Honest scope

This is the sharpest structured rank fragment so far: it caps cell rank by the *dimension* of the support family,
subsuming bounded-distinct (`r ≤ #distinct`) and equal supports (`r = 1`).  The survivor route is powerless whenever
`k` is large.  Still a fragment: a general `ACC⁰` system's support indicators span a *high*-dimensional space
(`r ~ poly`, so `2^r > n`).  Bounding the support-span dimension for general `ACC⁰` under a restriction is the open
rank-flavoured switching lemma (`NP ⊄ ACC⁰`-strength).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SupportSpanRank

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0LowRankFragment

variable {k n : ℕ}

/-- **The support indicators lie in a rank-`r` `F₂`-span**: each `(i ∈ supports j)` is `∑_m c_{j,m} B_m(i)`. -/
def SupportsInRankSpan (supports : Fin k → Finset (Fin n)) (r : ℕ) : Prop :=
  ∃ (B : Fin r → (Fin n → ZMod 2)) (c : Fin k → Fin r → ZMod 2),
    ∀ j i, (if i ∈ supports j then (1 : ZMod 2) else 0) = ∑ m, c j m * B m i

/-- **Low-dimensional support-span ⇒ low cell rank (proved): `cellRank ≤ r`.** -/
theorem cellRank_le_of_span (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) (r : ℕ)
    (h : SupportsInRankSpan supports r) : cellRank supports L ≤ r := by
  obtain ⟨B, c, hBc⟩ := h
  have hexp : ∀ v, cellPatternVec supports v = ∑ m : Fin r, B m v • (fun j => c j m) := by
    intro v
    funext j
    simp only [cellPatternVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hBc j v]
    exact Finset.sum_congr rfl (fun m _ => mul_comm _ _)
  have hle : cellSpan supports L ≤ Submodule.span (ZMod 2)
      (↑(Finset.univ.image (fun m : Fin r => (fun j => c j m : Fin k → ZMod 2))) :
        Set (Fin k → ZMod 2)) := by
    rw [cellSpan, Submodule.span_le]
    intro p hp
    rw [Finset.mem_coe, Finset.mem_image] at hp
    obtain ⟨v, _, rfl⟩ := hp
    rw [hexp v]
    apply Submodule.sum_mem
    intro m _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    rw [Finset.mem_coe, Finset.mem_image]
    exact ⟨m, Finset.mem_univ m, rfl⟩
  calc cellRank supports L
      ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
          (↑(Finset.univ.image (fun m : Fin r => (fun j => c j m : Fin k → ZMod 2))) :
            Set (Fin k → ZMod 2))) := Submodule.finrank_mono hle
    _ ≤ (Finset.univ.image (fun m : Fin r => (fun j => c j m : Fin k → ZMod 2))).card :=
        finrank_span_finset_le_card _
    _ ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_image_le
    _ = r := by rw [Finset.card_univ, Fintype.card_fin]

/-- **Low-dimensional support-span forces low cell rank (proved): `2^r < n`.** -/
theorem supportSpan_forces_low_cellRank (supports : Fin k → Finset (Fin n)) (r : ℕ)
    (h : SupportsInRankSpan supports r) (hrn : 2 ^ r < n) :
    ACC0ForcesLowCellRank supports := by
  apply bounded_cellRank_univ_forces
  calc 2 ^ cellRank supports Finset.univ
      ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (cellRank_le_of_span supports Finset.univ r h)
    _ < n := hrn

/-- **Unconditional low correlation for low-dimensional support-span (proved), any gate count `k`.** -/
theorem supportSpan_low_correlation (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool)
    (r : ℕ) (h : SupportsInRankSpan supports r) (hrn : 2 ^ r < n) :
    LowHolonomyCorrelation supports g :=
  low_cellRank_low_correlation supports g (supportSpan_forces_low_cellRank supports r h hrn)

end PallLean.Paper93.DeepMath.PathB.ACC0SupportSpanRank

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SupportSpanRank.cellRank_le_of_span
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SupportSpanRank.supportSpan_forces_low_cellRank
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SupportSpanRank.supportSpan_low_correlation
