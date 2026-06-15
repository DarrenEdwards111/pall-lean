import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RankBridge

/-!
# A low-rank fragment of `acc0_restriction_forces_low_cellRank` — where rank wins and survivors lose

The N-Frame open target is now the **rank** switching lemma `ACC0ForcesLowCellRank : ∃ L, 2^{cellRank} < |L|`.
This file discharges it for a structured fragment the *survivor* route provably cannot touch: **low-rank support
systems**.  The headline instance is **equal supports** — every gate has the same support `S`.  Then *all* `k` gates
survive any live set (`survivingCount = k`, arbitrarily large), so the survivor collapse `2^k < |L|` fails outright —
yet the incidence has **rank ≤ 1** (every cell pattern is a multiple of the all-ones vector), so the *rank* collapse
holds and the predictor still fails to correlate.

This is exactly the win the rank route was built for: many overlapping gates, few cells.

## What is proved (clean axioms, no `sorry`)

* `ACC0ForcesLowCellRank supports := ∃ L, 2^{cellRank supports L} < |L|` — the rank socket, and
  **`low_cellRank_low_correlation`** — it implies low holonomy correlation (socket ▸ the proved rank bridge).
* **`bounded_cellRank_univ_forces`** — `2^{cellRank supports univ} < n ⇒ ACC0ForcesLowCellRank` (live set `univ`).
* **`equal_supports_cellRank_le_one`** — equal supports have `cellRank ≤ 1` (patterns ∈ span of the all-ones vector),
  *independent of the gate count `k`*.
* **`equal_supports_forces_low_cellRank`** / **`equal_supports_low_correlation`** — equal supports (any `k`) with
  `n ≥ 3` force low cell rank, hence the predictor cannot correlate with the holonomy parity — **unconditionally**.

## Honest scope — a fragment, and why it matters

`equal_supports_low_correlation` is an *unconditional* lower bound where the **survivor route is powerless**
(`survivingCount = k`): proof that the rank reformulation is a genuine strengthening, not cosmetic.  It is still a
*fragment* (rank `≤ 1`, or more generally bounded `cellRank` with `2^{cellRank} < n`); forcing low `cellRank` for a
*general* `ACC⁰` support system under a restriction remains the open rank-flavoured switching lemma
(`NP ⊄ ACC⁰`-strength).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0LowRankFragment

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge

variable {k n : ℕ}

/-- **The rank socket**: some live set has cell rank below `log₂|L|` (`2^{cellRank} < |L|`). -/
def ACC0ForcesLowCellRank (supports : Fin k → Finset (Fin n)) : Prop :=
  ∃ L : Finset (Fin n), 2 ^ cellRank supports L < L.card

/-- **The rank socket implies low holonomy correlation (proved): socket ▸ the proved sharp rank bridge.** -/
theorem low_cellRank_low_correlation (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool)
    (h : ACC0ForcesLowCellRank supports) : LowHolonomyCorrelation supports g := by
  obtain ⟨L, hL⟩ := h
  exact rank_collapse_low_correlation supports g L hL

/-- **Bounded cell rank on the full cube forces the socket (proved): `2^{cellRank supports univ} < n`.** -/
theorem bounded_cellRank_univ_forces (supports : Fin k → Finset (Fin n))
    (h : 2 ^ cellRank supports Finset.univ < n) : ACC0ForcesLowCellRank supports :=
  ⟨Finset.univ, by rw [Finset.card_univ, Fintype.card_fin]; exact h⟩

/-- **Equal supports have cell rank `≤ 1` (proved), independent of the gate count.**  If every gate has support `S`,
each cell pattern is `(v ∈ S) · 𝟙`, a multiple of the all-ones vector, so the span has dimension `≤ 1`. -/
theorem equal_supports_cellRank_le_one (supports : Fin k → Finset (Fin n)) (S : Finset (Fin n))
    (hS : ∀ j, supports j = S) (L : Finset (Fin n)) : cellRank supports L ≤ 1 := by
  have hle : cellSpan supports L ≤
      Submodule.span (ZMod 2) ({(fun _ => 1 : Fin k → ZMod 2)} : Set (Fin k → ZMod 2)) := by
    rw [cellSpan, Submodule.span_le]
    intro p hp
    rw [Finset.mem_coe, Finset.mem_image] at hp
    obtain ⟨v, _, rfl⟩ := hp
    have hpat : cellPatternVec supports v
        = (if v ∈ S then (1 : ZMod 2) else 0) • (fun _ => 1 : Fin k → ZMod 2) := by
      funext j
      simp only [cellPatternVec, hS j, Pi.smul_apply, smul_eq_mul, mul_one]
    rw [hpat]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  calc cellRank supports L
      ≤ Module.finrank (ZMod 2)
          (Submodule.span (ZMod 2) ({(fun _ => 1 : Fin k → ZMod 2)} : Set (Fin k → ZMod 2))) :=
        Submodule.finrank_mono hle
    _ ≤ 1 := by simpa using finrank_span_le_card ({(fun _ => 1 : Fin k → ZMod 2)} : Set (Fin k → ZMod 2))

/-- **Equal supports force low cell rank (proved): any number of gates, `n ≥ 3`.**  The survivor route fails here
(`survivingCount = k`), but `cellRank ≤ 1` so `2^{cellRank} ≤ 2 < n`. -/
theorem equal_supports_forces_low_cellRank (supports : Fin k → Finset (Fin n)) (S : Finset (Fin n))
    (hS : ∀ j, supports j = S) (hn : 3 ≤ n) : ACC0ForcesLowCellRank supports := by
  apply bounded_cellRank_univ_forces
  calc 2 ^ cellRank supports Finset.univ
      ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num)
        (equal_supports_cellRank_le_one supports S hS Finset.univ)
    _ < n := by omega

/-- **Unconditional low correlation for equal supports (proved) — where the survivor route is powerless.**  All `k`
gates survive every live set, yet the predictor cannot correlate with the holonomy parity. -/
theorem equal_supports_low_correlation (supports : Fin k → Finset (Fin n)) (S : Finset (Fin n))
    (g : (Fin k → ℕ) → Bool) (hS : ∀ j, supports j = S) (hn : 3 ≤ n) :
    LowHolonomyCorrelation supports g :=
  low_cellRank_low_correlation supports g (equal_supports_forces_low_cellRank supports S hS hn)

end PallLean.Paper93.DeepMath.PathB.ACC0LowRankFragment

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LowRankFragment.equal_supports_cellRank_le_one
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LowRankFragment.equal_supports_forces_low_cellRank
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LowRankFragment.equal_supports_low_correlation
