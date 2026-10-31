import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RandomRestrictionRank
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RankWhp
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0LaminarCellCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BlockProductCellCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BoundedDistinctRank

/-!
# Random restriction in the cell-count language — first moments, Markov, and the precise wall

This is the cell-count analogue of the rank random-restriction / whp files (`…ACC0RandomRestrictionRank`,
`…ACC0RankWhp`), pushing on the *sharpest* open target `ACC0ForcesLowCellCount` (`∃ L, cellPatternCount < |L|`).

The cell count is the sharpest observer invariant, and it compares to `|L|` *directly* (no exponential gap): the whp
balance needs only `a ≤ b`, where the rank version needed `2^a ≤ b`.  So the cell-count whp route **subsumes** the
rank (hence survivor) whp route.

## What is proved (clean axioms, no `sorry`)

* **`cellPatternCount_le_two_pow_cellRank`** / **`cellPatternCount_le_two_pow_survivingCount`** — the monotone bounds.
* **`expected_cellPatternCount_le_expected_pow_survivors`** — `Exp[cellPatternCount] ≤ Exp[2^{survivingCount}]`
  (monotone expectation of the pointwise bound).
* **`Pr_cellPatternCount_ge_le_markov`** — Markov: `Pr[cellPatternCount ≥ a] ≤ Exp[cellPatternCount] / a`.
* **`Pr_cellPatternCount_ge_le_pow_survivor`** — the usable proxy: `Pr[cellPatternCount ≥ a] ≤ Exp[2^{surv}] / a`.
* **`randomRestriction_forces_low_cellCount`** — `Exp[cellPatternCount] ≤ B < a` ⇒ a live set with `cellPatternCount < a`.
* **`cellCount_predictor_fails_whp`** — the two-event balance with `a ≤ b` (sharper than rank): `Pr[cellPatternCount ≥ a]
  + Pr[|L| ≤ b] < 1` ⇒ low holonomy correlation.
* **`cellCount_whp_subsumes_rank`** — the cell-count whp fires whenever the rank feasibility (with `2^a ≤ b`) holds, so
  it subsumes the rank (hence survivor) whp route.
* Structured discharges of the first-moment bound: **`expected_cellPatternCount_le_of_bound`** (any deterministic
  bound), **`laminar_expected_cellPatternCount_le`** (`≤ k+1`), **`block_product_expected_cellPatternCount_le`** (`≤ cᵐ`).

## Honest stopping point — where the wall is, in cell-count language

The first moment controls the cell count **only for restricted structures**: a *deterministic* per-`L` bound
(laminar, bounded-distinct, uniform block products) gives `Exp[cellPatternCount] ≤ C` for free, closing the route.
For *general* polynomially-many wide overlapping `MOD` supports there is **no** such deterministic bound, and the only
first-moment handle is the naive `Exp[cellPatternCount] ≤ Exp[2^{survivingCount}]` — which is *exponentially large*
when survivors are abundant (exactly the overlapping regime).  Closing the gap between `cellPatternCount` and
`2^{survivingCount}` — i.e. bounding `Exp[cellPatternCount]` *without* the exponential survivor bound — needs
structural concentration on the *distinct-pattern* count, which is the open rank/cell switching lemma
(`NP ⊄ ACC⁰`-strength).  This file makes that wall precise; it does not climb it.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictionCellCount

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingChebyshev
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountRoute
open PallLean.Paper93.DeepMath.PathB.ACC0RankWhp
open PallLean.Paper93.DeepMath.PathB.ACC0LaminarCellCount
open PallLean.Paper93.DeepMath.PathB.ACC0BlockProductCellCount
open PallLean.Paper93.DeepMath.PathB.ACC0BoundedDistinctRank

variable {k n : ℕ}

/-! ## Monotone bounds (target 2) -/

/-- **`cellPatternCount ≤ 2^{cellRank}` (proved).**  Re-export of the rank-bridge bound. -/
theorem cellPatternCount_le_two_pow_cellRank (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) :
    cellPatternCount supports L ≤ 2 ^ cellRank supports L :=
  cellPattern_image_card_le supports L

/-- **`cellPatternCount ≤ 2^{survivingCount}` (proved).**  Compose with `cellRank ≤ survivingCount`. -/
theorem cellPatternCount_le_two_pow_survivingCount (supports : Fin k → Finset (Fin n))
    (L : Finset (Fin n)) : cellPatternCount supports L ≤ 2 ^ survivingCount supports L :=
  le_trans (cellPatternCount_le_two_pow_cellRank supports L)
    (Nat.pow_le_pow_right (by norm_num) (cellRank_le_survivingCount supports L))

/-! ## First-moment / Markov route (target 3) -/

/-- **Expected cell count `≤` expected `2^{survivingCount}` (proved).**  Monotone expectation of the pointwise bound. -/
theorem expected_cellPatternCount_le_expected_pow_survivors (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) :
    Exp p (fun L => (cellPatternCount supports L : ℝ))
      ≤ Exp p (fun L => ((2 ^ survivingCount supports L : ℕ) : ℝ)) := by
  unfold Exp
  apply Finset.sum_le_sum
  intro L _
  have hle : (cellPatternCount supports L : ℝ) ≤ ((2 ^ survivingCount supports L : ℕ) : ℝ) := by
    exact_mod_cast cellPatternCount_le_two_pow_survivingCount supports L
  exact mul_le_mul_of_nonneg_left hle (weight_nonneg p hp0 hp1 L)

/-- **Markov on the cell count (proved): `Pr[cellPatternCount ≥ a] ≤ Exp[cellPatternCount] / a`.** -/
theorem Pr_cellPatternCount_ge_le_markov (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (a : ℝ) (ha : 0 < a) :
    Pr p (fun L => a ≤ (cellPatternCount supports L : ℝ))
      ≤ Exp p (fun L => (cellPatternCount supports L : ℝ)) / a := by
  have hm := markov p hp0 hp1 (fun L => (cellPatternCount supports L : ℝ))
    (fun L => Nat.cast_nonneg _) a
  rw [le_div_iff₀ ha, mul_comm]
  exact hm

/-- **The usable proxy (proved): `Pr[cellPatternCount ≥ a] ≤ Exp[2^{survivingCount}] / a`.**  Markov composed with the
naive survivor bound — the only general first-moment handle (and exponentially weak when survivors are abundant). -/
theorem Pr_cellPatternCount_ge_le_pow_survivor (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (a : ℝ) (ha : 0 < a) :
    Pr p (fun L => a ≤ (cellPatternCount supports L : ℝ))
      ≤ Exp p (fun L => ((2 ^ survivingCount supports L : ℕ) : ℝ)) / a := by
  refine le_trans (Pr_cellPatternCount_ge_le_markov p hp0 hp1 supports a ha) ?_
  gcongr
  exact expected_cellPatternCount_le_expected_pow_survivors p hp0 hp1 supports

/-- **A random restriction forces low cell count (proved).**  If `Exp[cellPatternCount] ≤ B < a`, some live set has
`cellPatternCount < a` — Markov plus the probabilistic method (mirrors `exists_low_survival`). -/
theorem randomRestriction_forces_low_cellCount (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (B a : ℝ) (ha : 0 < a)
    (hE : Exp p (fun L => (cellPatternCount supports L : ℝ)) ≤ B) (hBa : B < a) :
    ∃ L ∈ (Finset.univ : Finset (Fin n)).powerset, (cellPatternCount supports L : ℝ) < a := by
  have hm := markov p hp0 hp1 (fun L => (cellPatternCount supports L : ℝ))
    (fun L => Nat.cast_nonneg _) a
  have hpr : Pr p (fun L => a ≤ (cellPatternCount supports L : ℝ)) < 1 := by
    by_contra hge
    push_neg at hge
    have hkey : a ≤ a * Pr p (fun L => a ≤ (cellPatternCount supports L : ℝ)) := by
      have := mul_le_mul_of_nonneg_left hge ha.le
      rwa [mul_one] at this
    linarith
  obtain ⟨L, hL, hLnot⟩ := exists_of_pr_lt_one p _ hpr
  push_neg at hLnot
  exact ⟨L, hL, hLnot⟩

/-! ## The cell-count whp route (sharper than rank: `a ≤ b`, no `2^a ≤ b`) -/

/-- **The cell-count whp route (proved): the two-event balance with `a ≤ b`.**  If `Pr[cellPatternCount ≥ a] +
Pr[|L| ≤ b] < 1` with `a ≤ b`, some restriction is low-cell (`cellPatternCount < a`) and large (`|L| > b ≥ a`), so
`cellPatternCount < |L|` and the cell-count bridge gives low correlation.  No exponential gap, unlike the rank whp. -/
theorem cellCount_predictor_fails_whp (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool) (a b : ℕ) (hab : a ≤ b)
    (hfeas : Pr p (fun L => a ≤ cellPatternCount supports L)
        + Pr p (fun L : Finset (Fin n) => L.card ≤ b) < 1) :
    LowHolonomyCorrelation supports g := by
  obtain ⟨L, _, hnot1, hnot2⟩ := exists_both_of_pr_add_lt_one p hp0 hp1
    (fun L : Finset (Fin n) => a ≤ cellPatternCount supports L)
    (fun L : Finset (Fin n) => L.card ≤ b) hfeas
  push_neg at hnot1 hnot2
  have hkey : cellPatternCount supports L < L.card :=
    calc cellPatternCount supports L < a := hnot1
      _ ≤ b := hab
      _ < L.card := hnot2
  exact cellCountCollapse_implies_low_correlation supports g L hkey

/-- **The cell-count whp subsumes the rank whp (proved).**  Since `cellPatternCount ≤ 2^{cellRank}`, the event
`cellPatternCount ≥ 2^a` is contained in `cellRank ≥ a`; so the rank feasibility (with `2^a ≤ b`) implies the
cell-count feasibility, and the cell-count route fires — broader than the rank (hence survivor) whp. -/
theorem cellCount_whp_subsumes_rank (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool) (a b : ℕ) (hab : 2 ^ a ≤ b)
    (hfeas : Pr p (fun L => a ≤ cellRank supports L)
        + Pr p (fun L : Finset (Fin n) => L.card ≤ b) < 1) :
    LowHolonomyCorrelation supports g := by
  apply cellCount_predictor_fails_whp p hp0 hp1 supports g (2 ^ a) b hab
  refine lt_of_le_of_lt ?_ hfeas
  gcongr
  apply Pr_mono p hp0 hp1
  intro L hL
  have hpow : (2 : ℕ) ^ a ≤ 2 ^ cellRank supports L :=
    le_trans hL (cellPatternCount_le_two_pow_cellRank supports L)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hpow

/-! ## Structured discharges of the first-moment bound (target 4) -/

/-- **Any deterministic cell-count bound gives the expectation bound (proved).** -/
theorem expected_cellPatternCount_le_of_bound (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (C : ℝ) (hC : ∀ L, (cellPatternCount supports L : ℝ) ≤ C) :
    Exp p (fun L => (cellPatternCount supports L : ℝ)) ≤ C := by
  unfold Exp
  calc ∑ L ∈ (Finset.univ : Finset (Fin n)).powerset, weight p L * (cellPatternCount supports L : ℝ)
      ≤ ∑ L ∈ (Finset.univ : Finset (Fin n)).powerset, weight p L * C := by
        apply Finset.sum_le_sum
        intro L _
        exact mul_le_mul_of_nonneg_left (hC L) (weight_nonneg p hp0 hp1 L)
    _ = (∑ L ∈ (Finset.univ : Finset (Fin n)).powerset, weight p L) * C := by rw [Finset.sum_mul]
    _ = C := by rw [total]; ring

/-- **Laminar discharge (proved): `Exp[cellPatternCount] ≤ k + 1`.**  The deterministic `≤ k+1` cell bound for laminar
supports gives the first-moment bound for free — the route closes with no concentration needed. -/
theorem laminar_expected_cellPatternCount_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (hlam : LaminarSupports supports) :
    Exp p (fun L => (cellPatternCount supports L : ℝ)) ≤ ((k + 1 : ℕ) : ℝ) :=
  expected_cellPatternCount_le_of_bound p hp0 hp1 supports ((k + 1 : ℕ) : ℝ)
    (fun L => by exact_mod_cast laminar_cellPatternCount_le supports hlam L)

/-- **Bounded-distinct discharge (proved): `≤ d` distinct supports ⇒ `Exp[cellPatternCount] ≤ 2ᵈ`.**  The cell rank is
`≤ d` independent of the gate count `k`, so `cellPatternCount ≤ 2^{cellRank} ≤ 2ᵈ` deterministically — the first
moment closes for free, no concentration needed. -/
theorem bounded_distinct_expected_cellPatternCount_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (d : ℕ) (hd : (Finset.univ.image supports).card ≤ d) :
    Exp p (fun L => (cellPatternCount supports L : ℝ)) ≤ ((2 ^ d : ℕ) : ℝ) := by
  apply expected_cellPatternCount_le_of_bound p hp0 hp1 supports ((2 ^ d : ℕ) : ℝ)
  intro L
  have hle : cellPatternCount supports L ≤ 2 ^ d := by
    calc cellPatternCount supports L
        ≤ 2 ^ cellRank supports L := cellPatternCount_le_two_pow_cellRank supports L
      _ ≤ 2 ^ d :=
          Nat.pow_le_pow_right (by norm_num) (le_trans (cellRank_le_distinct supports L) hd)
  exact_mod_cast hle

/-- **Block-product discharge (proved): uniformly `≤ c` cells per block ⇒ `Exp[cellPatternCount] ≤ cᵐ`.** -/
theorem block_product_expected_cellPatternCount_le {m b : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin m → Fin b → Finset (Fin n)) (c : ℕ)
    (hbound : ∀ L i, cellPatternCount (supports i) L ≤ c) :
    Exp p (fun L => (cellPatternCount (flatSupports supports) L : ℝ)) ≤ ((c ^ m : ℕ) : ℝ) := by
  apply expected_cellPatternCount_le_of_bound p hp0 hp1 (flatSupports supports) ((c ^ m : ℕ) : ℝ)
  intro L
  have hle : cellPatternCount (flatSupports supports) L ≤ c ^ m := by
    rw [cellPatternCount_flat_eq]
    exact blockCellCount_le_pow supports L c (fun i => hbound L i)
  exact_mod_cast hle

end PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictionCellCount

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictionCellCount.expected_cellPatternCount_le_expected_pow_survivors
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictionCellCount.Pr_cellPatternCount_ge_le_markov
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictionCellCount.randomRestriction_forces_low_cellCount
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictionCellCount.cellCount_predictor_fails_whp
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictionCellCount.cellCount_whp_subsumes_rank
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictionCellCount.laminar_expected_cellPatternCount_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictionCellCount.bounded_distinct_expected_cellPatternCount_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictionCellCount.block_product_expected_cellPatternCount_le
