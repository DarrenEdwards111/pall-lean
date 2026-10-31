import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGodelFeatureCount

/-!
# Applying the dynamic / Gödel‑SPDP framework to ACC⁰ — a diagnostic calibration

This is **calibration, not a lower bound**: ACC⁰ sits between the proved restricted cases and the Williams
frontier, and the dynamic‑SPDP projection lets us see *where* the modular structure stays tame and where mixed
moduli break it — sharpening the map, with no claim of `NP ⊄ ACC⁰`.

The handle: a modular‑counting gate computes a function of a few **weight statistics** of the input.  A symmetric
(single‑modulus) gate `MOD_m` is a function of one statistic — the total Hamming weight.  A mixed‑moduli object
(`MOD_{m₁}` on one block, `MOD_{m₂}` on another, …) is a function of `k` independent block‑weight statistics.  The
realized‑feature count under the Gödel‑SPDP projection is governed by *how many statistics* must be resolved.

## What is proved (clean axioms, no `sorry`)

* `statRow_realized_le` — **the core diagnostic.**  If every row of a class is `h ∘ stat` for a fixed statistic
  `stat : input → σ`, and the reachable statistics on the weight‑`≤ d` ball lie in a finite set `R`, then the
  realized low‑degree features of the class number `≤ 2^{|R|}`.  (The feature is determined by `h` on the
  reachable statistics.)
* `symmetric_realized_le` — **single modulus is tame**: symmetric rows (`r = g ∘ hw`, one statistic) have
  `≤ 2^{d+1}` realized features at order `d`.
* `godel_symmetric_realized_poly` — at the Gödel level this is `≤ 2n` — **polynomial**.  The framework cleanly
  explains a single modular gate (the AC⁰[p] success, rendered as poly realized features).
* `kStat_realized_le` — **mixed moduli, quantified**: a function of `k` block‑weight statistics has `≤ 2^{(d+1)^k}`
  realized features.  At the Gödel level `d = log₂ n`: `k = 1` gives `2^{O(log n)}` = poly; `k = 2` gives
  `2^{O(log² n)}` = **quasi‑poly**; growing `k` gives **super‑poly**.  This is the joint‑modular barrier as a
  feature‑budget blow‑up: each additional independent modulus multiplies the statistic space, and the realized
  feature count is exponential in `(d+1)^k`.

## The live strengthening, named

* `ACC0LowRealizedGodelSPDP` — the A1‑analogue for the **full** ACC⁰ class: every ACC⁰ circuit's realized
  Gödel‑level pcrank is polynomial.  This file *proves* it for the single‑symmetric‑gate sub‑case
  (`godel_symmetric_realized_poly`) and *bounds* the `k`‑statistic case (`kStat_realized_le`), but the full class
  computes **non‑symmetric functions via mixed‑modulus composition**, where `k` is not constant — exactly where
  the budget leaves poly.  Proving `ACC0LowRealizedGodelSPDP` for the full class is the open analogue of the
  `ScalingSPDPBridge`, and would be `NP ⊄ ACC⁰`‑strength.

## Verdict — a sharper map, no overclaim

The dynamic‑SPDP framework **explains AC⁰[p]/single‑modulus cleanly** (poly realized features) and **localizes the
ACC⁰ difficulty precisely**: it is the growth of the statistic count `k` under mixed‑modulus composition, which
pushes the realized‑feature budget `2^{(d+1)^k}` from polynomial (`k=1`) through quasi‑polynomial (`k=2`) to
super‑polynomial.  The barrier is not the projection's locality (single gates are visible and tame) but the
*number of independent moduli* the projection must jointly resolve — the joint‑modular barrier, now a quantitative
feature‑count statement.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0DynamicSPDPCalibration

open PallLean.Paper93.DeepMath.PathB.RankContextualWidth
open PallLean.Paper93.DeepMath.PathB.ProjectedContextualRank
open PallLean.Paper93.DeepMath.PathB.LowDegreeProjection
open PallLean.Paper93.DeepMath.PathB.SPDPFeatureProjection
open PallLean.Paper93.DeepMath.PathB.GodelHierarchySPDPScaling

variable {a : ℕ}

/-- A row that is a function `h` of a fixed **statistic** `stat` of the input (e.g. a modular gate of the Hamming
weight). -/
def statRow {σ : Type*} (stat : (Fin a → Bool) → σ) (h : σ → Bool) : (Fin a → Bool) → Bool :=
  fun v => h (stat v)

/-- **The core diagnostic (proved).**  If the reachable statistics on the weight‑`≤ d` ball lie in a finite set
`R`, then a class of statistic‑rows has `≤ 2^{|R|}` realized low‑degree features: the feature is determined by `h`
on `R`. -/
theorem statRow_realized_le {σ : Type*} [DecidableEq σ] (stat : (Fin a → Bool) → σ) (R : Finset σ) (d : ℕ)
    (hR : ∀ v, hw v ≤ d → stat v ∈ R) (H : Finset (σ → Bool)) :
    (H.image (fun h => lowDegProj a d (statRow stat h))).card ≤ 2 ^ R.card := by
  classical
  have hsub : H.image (fun h => lowDegProj a d (statRow stat h))
      ⊆ Finset.univ.image
          (fun (gp : ↥R → Bool) => (fun (y : LowWt a d) => gp ⟨stat y.val, hR y.val y.property⟩)) := by
    intro feat hfeat
    rw [Finset.mem_image] at hfeat
    obtain ⟨h, _, rfl⟩ := hfeat
    rw [Finset.mem_image]
    refine ⟨fun s => h s.val, Finset.mem_univ _, ?_⟩
    funext y
    rfl
  calc (H.image (fun h => lowDegProj a d (statRow stat h))).card
      ≤ (Finset.univ.image
          (fun (gp : ↥R → Bool) =>
            (fun (y : LowWt a d) => gp ⟨stat y.val, hR y.val y.property⟩))).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (↥R → Bool)).card := Finset.card_image_le
    _ = 2 ^ R.card := by
        rw [Finset.card_univ]
        simp [Fintype.card_bool]

/-- A symmetric (single‑modulus) row: a function of the total Hamming weight. -/
def symRow (g : ℕ → Bool) : (Fin a → Bool) → Bool := statRow hw g

/-- **Single modulus is tame (proved): `≤ 2^{d+1}` realized features.** -/
theorem symmetric_realized_le (d : ℕ) (G : Finset (ℕ → Bool)) :
    (G.image (fun g => lowDegProj a d (symRow g))).card ≤ 2 ^ (d + 1) := by
  have h := statRow_realized_le (a := a) hw (Finset.range (d + 1)) d
    (fun v hv => Finset.mem_range.mpr (by omega)) G
  rwa [Finset.card_range] at h

/-- **A single modular gate has polynomial realized features at the Gödel level (proved): `≤ 2n`.**  The framework
cleanly explains AC⁰[p]/single‑modulus structure. -/
theorem godel_symmetric_realized_poly (n : ℕ) (hn : 1 ≤ n) (G : Finset (ℕ → Bool)) :
    (G.image (fun g => lowDegProj a (godelLevel n).d (symRow g))).card ≤ 2 * n := by
  have h := symmetric_realized_le (a := a) (godelLevel n).d G
  have hlog : 2 ^ (Nat.log 2 n + 1) ≤ 2 * n := by
    rw [pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul (le_refl 2) (Nat.pow_log_le_self 2 (by omega))
  exact le_trans h hlog

/-- **Mixed moduli, quantified (proved): a function of `k` block‑weight statistics has `≤ 2^{(d+1)^k}` realized
features.**  At the Gödel level `d = log₂ n`: `k=1` poly, `k=2` quasi‑poly, growing `k` super‑poly — the
joint‑modular barrier as a feature‑budget blow‑up. -/
theorem kStat_realized_le {k : ℕ} (stat : (Fin a → Bool) → (Fin k → ℕ)) (d : ℕ)
    (hbound : ∀ v j, hw v ≤ d → stat v j ≤ d) (H : Finset ((Fin k → ℕ) → Bool)) :
    (H.image (fun h => lowDegProj a d (statRow stat h))).card ≤ 2 ^ ((d + 1) ^ k) := by
  have hpi := statRow_realized_le (a := a) stat
    (Fintype.piFinset (fun _ : Fin k => Finset.range (d + 1))) d
    (fun v hv => Fintype.mem_piFinset.mpr (fun j => Finset.mem_range.mpr (by have := hbound v j hv; omega))) H
  rwa [show (Fintype.piFinset (fun _ : Fin k => Finset.range (d + 1))).card = (d + 1) ^ k by
    rw [Fintype.card_piFinset]; simp [Finset.card_range]] at hpi

/-- **(A1 for ACC⁰, named — open for the full class):** every ACC⁰ circuit's realized Gödel‑level pcrank is
polynomial.  Proved here for single symmetric gates; the full class (mixed‑modulus composition, non‑constant `k`)
is the open `NP ⊄ ACC⁰`‑strength analogue of the `ScalingSPDPBridge`. -/
def ACC0LowRealizedGodelSPDP (acc0RealizedCount : ℕ → ℕ) (C : ℕ) : Prop :=
  ∀ n, acc0RealizedCount n ≤ n ^ C

end PallLean.Paper93.DeepMath.PathB.ACC0DynamicSPDPCalibration

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DynamicSPDPCalibration.statRow_realized_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DynamicSPDPCalibration.symmetric_realized_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DynamicSPDPCalibration.godel_symmetric_realized_poly
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DynamicSPDPCalibration.kStat_realized_le
