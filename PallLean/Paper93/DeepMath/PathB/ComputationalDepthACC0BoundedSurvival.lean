import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CellCollapseRoute

/-!
# Quantitative survival bound for bounded fragments — the N-Frame route closed *unconditionally*

`…ACC0CellCollapseRoute` left `FullACC0ForcesCellCollapse` (the restriction lemma) as the hard open socket.  This
file **discharges that socket for two bounded fragments**, by exhibiting an explicit live set with provably few
surviving supports — so the whole N-Frame route (collapse ⇒ low holonomy correlation) becomes an *unconditional*
theorem on those fragments.

Two regimes where the survival bound is real:

* **Bounded gate count.**  At most `k` supports can survive *any* live set (`survivingCount ≤ k`), so on the full
  cube `L = univ` (size `n`), `2^{#survivors} ≤ 2^k < n` whenever `k < log₂ n`.  Collapse holds.
* **Small support footprint.**  Take `L =` the *complement* of the supports' union; *no* support meets it
  (`survivingCount = 0`), and `|L| = n − |⋃ supports| ≥ 2`, so `2^0 = 1 < |L|`.  Collapse holds.

## What is proved (clean axioms, no `sorry`)

* `survivingCount_le_card` — at most `k` supports survive (`survivingCount supports L ≤ k`).
* **`bounded_gate_forces_cell_collapse`** — `2^k < n ⇒ FullACC0ForcesCellCollapse` (live set `univ`).
* `survivingCount_eq_zero_of_disjoint` / **`small_footprint_forces_cell_collapse`** — footprint `+ 2 ≤ n ⇒
  FullACC0ForcesCellCollapse` (live set = complement of the union).
* **`bounded_gate_low_holonomy_correlation`** / **`small_footprint_low_holonomy_correlation`** — composing with the
  proved bridge (`nframe_route`): the predictor **does not correlate** with the holonomy parity — *unconditionally*,
  on these fragments (no socket).

## Honest scope — bounded fragments only; the wall is full `ACC⁰`

These discharge the cell-collapse socket only for `k < log₂ n` gates (bounded gate count) or footprint `≤ n − 2`
(bounded total support) — the same controllable regimes as the size-wall fragments.  A *full* `ACC⁰` predictor has
polynomially many wide supports, so `survivingCount` on *any* large live set is large and the collapse fails — that
is the genuine wall, unchanged.  So this is a real, unconditional low-correlation lower bound *for the fragments*, not
for full `ACC⁰`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BoundedSurvival

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute

variable {n k : ℕ}

/-- **At most `k` supports survive any live set (proved): `survivingCount supports L ≤ k`.** -/
theorem survivingCount_le_card (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) :
    survivingCount supports L ≤ k := by
  unfold survivingCount
  calc (Finset.univ.filter (fun j => ¬ Disjoint (supports j) L)).card
      ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_filter_le _ _
    _ = k := by rw [Finset.card_univ, Fintype.card_fin]

/-- **Bounded gate count forces cell collapse (proved): `2^k < n ⇒ FullACC0ForcesCellCollapse`.**  The full cube
`L = univ` works: at most `k` of the `k` supports survive, and `2^k < n = |univ|`. -/
theorem bounded_gate_forces_cell_collapse (supports : Fin k → Finset (Fin n)) (h : 2 ^ k < n) :
    FullACC0ForcesCellCollapse supports := by
  refine ⟨Finset.univ, ?_⟩
  show 2 ^ survivingCount supports Finset.univ < (Finset.univ : Finset (Fin n)).card
  rw [Finset.card_univ, Fintype.card_fin]
  exact lt_of_le_of_lt
    (Nat.pow_le_pow_right (by norm_num) (survivingCount_le_card supports Finset.univ)) h

/-- **A live set disjoint from every support has zero survivors (proved).** -/
theorem survivingCount_eq_zero_of_disjoint (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n))
    (hdisj : ∀ j, Disjoint (supports j) L) : survivingCount supports L = 0 := by
  unfold survivingCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j _
  exact not_not.mpr (hdisj j)

/-- **Small footprint forces cell collapse (proved): `|⋃ supports| + 2 ≤ n ⇒ FullACC0ForcesCellCollapse`.**  The
complement `L = univ \ ⋃ supports` meets no support (`0` survivors) and has size `n − |⋃| ≥ 2 > 1`. -/
theorem small_footprint_forces_cell_collapse (supports : Fin k → Finset (Fin n))
    (h : (Finset.univ.biUnion supports).card + 2 ≤ n) :
    FullACC0ForcesCellCollapse supports := by
  set B := Finset.univ.biUnion supports with hB
  refine ⟨Finset.univ \ B, ?_⟩
  have hdisj : ∀ j, Disjoint (supports j) (Finset.univ \ B) := by
    intro j
    rw [Finset.disjoint_left]
    intro a ha ha2
    have haB : a ∈ B := Finset.subset_biUnion_of_mem supports (Finset.mem_univ j) ha
    exact (Finset.mem_sdiff.mp ha2).2 haB
  show 2 ^ survivingCount supports (Finset.univ \ B) < (Finset.univ \ B).card
  rw [survivingCount_eq_zero_of_disjoint supports _ hdisj, pow_zero,
    ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]
  omega

/-- **Unconditional low holonomy correlation for bounded gate count (proved).**  A `k`-gate predictor with `2^k < n`
does not correlate with the holonomy parity — the full N-Frame route, no socket. -/
theorem bounded_gate_low_holonomy_correlation (supports : Fin k → Finset (Fin n))
    (g : (Fin k → ℕ) → Bool) (h : 2 ^ k < n) : LowHolonomyCorrelation supports g :=
  nframe_route supports g (bounded_gate_forces_cell_collapse supports h)

/-- **Unconditional low holonomy correlation for small footprint (proved).**  A predictor whose supports cover
`≤ n − 2` variables does not correlate with the holonomy parity — the full N-Frame route, no socket. -/
theorem small_footprint_low_holonomy_correlation (supports : Fin k → Finset (Fin n))
    (g : (Fin k → ℕ) → Bool) (h : (Finset.univ.biUnion supports).card + 2 ≤ n) :
    LowHolonomyCorrelation supports g :=
  nframe_route supports g (small_footprint_forces_cell_collapse supports h)

end PallLean.Paper93.DeepMath.PathB.ACC0BoundedSurvival

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedSurvival.bounded_gate_forces_cell_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedSurvival.small_footprint_forces_cell_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedSurvival.bounded_gate_low_holonomy_correlation
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundedSurvival.small_footprint_low_holonomy_correlation
