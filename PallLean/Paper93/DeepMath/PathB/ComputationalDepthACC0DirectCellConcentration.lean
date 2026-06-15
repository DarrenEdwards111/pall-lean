import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RandomRestrictionCellCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CellCountSwitching

/-!
# Direct cell-count concentration — not via `2^{survivors}`

The previous random-restriction file routed `Exp[cellPatternCount]` through the exponential
`Exp[2^{survivingCount}]`.  This file gives **direct** handles that never invoke `2^{survivors}`, exploiting a
structural fact: `cellPatternVec supports v` ranges over *all* gates and is **independent of the live set `L`**.  So
the only randomness in `cellPatternCount supports L` is *which coordinates survive*, and the cell count is just the
number of distinct (fixed) coordinate-patterns among the live coordinates — monotone in `L` and bounded by the
restriction-independent **global pattern count** `globalCellCount := cellPatternCount supports univ`.

```
cellPatternCount supports L  ≤  min( |L| ,  globalCellCount supports )  ≤  min( |L|, 2^k ).
```

## What is proved (clean axioms, no `sorry`)

* **`cellPatternCount_le_card`** — `cellPatternCount supports L ≤ |L|` (image card).
* **`cellPatternCount_mono`** — `L ⊆ L' ⇒ cellPatternCount supports L ≤ cellPatternCount supports L'`.
* **`cellPatternCount_le_global`** / **`globalCellCount_le_two_pow_gates`** — `≤ globalCellCount ≤ 2^k`.
* **`Pr_cellPatternCount_ge_le_size_tail`** — direct tail: `Pr[cellPatternCount ≥ a] ≤ Pr[|L| ≥ a]` (no `2^{surv}`).
* **`Pr_cellPatternCount_ge_eq_zero_of_global_lt`** — `globalCellCount < a ⇒ Pr[cellPatternCount ≥ a] = 0`.
* **`expected_cellPatternCount_le_global`** — `Exp[cellPatternCount] ≤ globalCellCount` (direct first moment).
* **`low_global_cellCount_collapse`** / **`low_global_forces_lowCellCount`** / **`few_gates_forces_lowCellCount`** —
  the deterministic reframing: `globalCellCount < |L|` (resp. `< n`, resp. `2^k < n`) forces the collapse with **no
  probability at all**.

## Honest stopping point — where the direct route stalls

The global pattern count `globalCellCount` is restriction-independent and, for polynomially many gates with `k ≫ log n`,
is *generically equal to `n`* (every coordinate gets a distinct membership pattern).  So the deterministic reframing
fires only in the low-resolution regime (`2^k < n`, or heavy structural collisions).  The genuine power of a
restriction is that it *merges* patterns among the surviving gates — `cellPatternCount L` can be far below
`globalCellCount` because non-surviving gates do not separate live coordinates.  Bounding that merged count directly —
below *both* `2^{survivors}` and the trivial `|L|`/`globalCellCount` — is the open structural-concentration content
(`NP ⊄ ACC⁰`-strength).  This file supplies the direct, non-exponential handles and pins exactly what they miss.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0DirectCellConcentration

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingChebyshev
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountRoute
open PallLean.Paper93.DeepMath.PathB.ACC0RankWhp
open PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictionCellCount
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountSwitching

variable {k n : ℕ}

/-- The **global pattern count**: distinct coordinate-patterns over all of `Fin n` — restriction-independent. -/
def globalCellCount (supports : Fin k → Finset (Fin n)) : ℕ :=
  cellPatternCount supports Finset.univ

/-! ## Deterministic structural bounds -/

/-- **`cellPatternCount ≤ |L|` (proved).** -/
theorem cellPatternCount_le_card (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) :
    cellPatternCount supports L ≤ L.card := by
  unfold cellPatternCount cellPatternImage
  exact Finset.card_image_le

/-- **Cell count is monotone in the live set (proved).** -/
theorem cellPatternCount_mono (supports : Fin k → Finset (Fin n)) {L L' : Finset (Fin n)}
    (h : L ⊆ L') : cellPatternCount supports L ≤ cellPatternCount supports L' := by
  unfold cellPatternCount cellPatternImage
  exact Finset.card_le_card (Finset.image_subset_image h)

/-- **Cell count is at most the global pattern count (proved): restriction-independent ceiling.** -/
theorem cellPatternCount_le_global (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) :
    cellPatternCount supports L ≤ globalCellCount supports :=
  cellPatternCount_mono supports (Finset.subset_univ L)

/-- **The global pattern count is at most `2^k` (proved): patterns live in `Fin k → ZMod 2`.** -/
theorem globalCellCount_le_two_pow_gates (supports : Fin k → Finset (Fin n)) :
    globalCellCount supports ≤ 2 ^ k := by
  have hcard : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by
    rw [Fintype.card_pi]
    simp only [ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold globalCellCount cellPatternCount cellPatternImage
  calc (Finset.univ.image (cellPatternVec supports)).card
      ≤ Fintype.card (Fin k → ZMod 2) := Finset.card_le_univ _
    _ = 2 ^ k := hcard

/-! ## Direct concentration (no `2^{survivors}`) -/

/-- **Direct tail (proved): `Pr[cellPatternCount ≥ a] ≤ Pr[|L| ≥ a]`.**  Since `cellPatternCount ≤ |L|` pointwise — no
`2^{survivors}` anywhere. -/
theorem Pr_cellPatternCount_ge_le_size_tail (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (a : ℕ) :
    Pr p (fun L => a ≤ cellPatternCount supports L)
      ≤ Pr p (fun L : Finset (Fin n) => a ≤ L.card) := by
  apply Pr_mono p hp0 hp1
  intro L hL
  exact le_trans hL (cellPatternCount_le_card supports L)

/-- **The tail vanishes above the global count (proved): `globalCellCount < a ⇒ Pr[cellPatternCount ≥ a] = 0`.** -/
theorem Pr_cellPatternCount_ge_eq_zero_of_global_lt (p : ℝ) (supports : Fin k → Finset (Fin n))
    (a : ℕ) (h : globalCellCount supports < a) :
    Pr p (fun L => a ≤ cellPatternCount supports L) = 0 := by
  have hfalse : (fun L : Finset (Fin n) => a ≤ cellPatternCount supports L) = (fun _ => False) := by
    funext L
    simp only [eq_iff_iff, iff_false, not_le]
    exact lt_of_le_of_lt (cellPatternCount_le_global supports L) h
  rw [hfalse]
  unfold Pr
  simp

/-- **Direct first moment (proved): `Exp[cellPatternCount] ≤ globalCellCount`.**  The restriction-independent ceiling,
not the exponential survivor bound. -/
theorem expected_cellPatternCount_le_global (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) :
    Exp p (fun L => (cellPatternCount supports L : ℝ)) ≤ ((globalCellCount supports : ℕ) : ℝ) :=
  expected_cellPatternCount_le_of_bound p hp0 hp1 supports ((globalCellCount supports : ℕ) : ℝ)
    (fun L => by exact_mod_cast cellPatternCount_le_global supports L)

/-! ## The deterministic collapse reframing -/

/-- **Low global count forces collapse on any large live set (proved): `globalCellCount < |L|`.** -/
theorem low_global_cellCount_collapse (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n))
    (h : globalCellCount supports < L.card) : CellCountCollapse supports L :=
  lt_of_le_of_lt (cellPatternCount_le_global supports L) h

/-- **Low global count discharges the open socket on the full cube (proved): `globalCellCount < n`.** -/
theorem low_global_forces_lowCellCount (supports : Fin k → Finset (Fin n))
    (h : globalCellCount supports < n) : FullACC0ForcesLowCellCount supports := by
  refine ⟨Finset.univ, ?_⟩
  show cellPatternCount supports Finset.univ < (Finset.univ : Finset (Fin n)).card
  simpa [globalCellCount] using h

/-- **Few gates discharge the open socket (proved): `2^k < n`.**  The low-resolution regime — no probability. -/
theorem few_gates_forces_lowCellCount (supports : Fin k → Finset (Fin n)) (h : 2 ^ k < n) :
    FullACC0ForcesLowCellCount supports :=
  low_global_forces_lowCellCount supports
    (lt_of_le_of_lt (globalCellCount_le_two_pow_gates supports) h)

end PallLean.Paper93.DeepMath.PathB.ACC0DirectCellConcentration

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DirectCellConcentration.cellPatternCount_le_global
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DirectCellConcentration.globalCellCount_le_two_pow_gates
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DirectCellConcentration.Pr_cellPatternCount_ge_le_size_tail
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DirectCellConcentration.Pr_cellPatternCount_ge_eq_zero_of_global_lt
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DirectCellConcentration.expected_cellPatternCount_le_global
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DirectCellConcentration.low_global_forces_lowCellCount
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DirectCellConcentration.few_gates_forces_lowCellCount
