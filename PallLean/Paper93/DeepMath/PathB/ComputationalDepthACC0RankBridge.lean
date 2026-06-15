import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RankCollapseRoute

/-!
# The sharp rank bridge: `2^{rank} < |L|` ⇒ low holonomy correlation

The survivor bridge (`…ACC0CellCollapseRoute`) needs `2^{#survivors} < |L|`.  This file proves the **sharp** bridge:
`2^{cellRank} < |L| ⇒ low correlation`, where `cellRank` is the `F₂`-dimension of the span of the **cell-pattern
vectors** (the columns of the support-incidence matrix).  This is strictly sharper because — for overlapping supports
— the cell patterns live in a *low-dimensional* span even when many gates survive.

The mechanism, all proved here:

```
cell pattern of a coordinate v :  cellPatternVec v = (v ∈ supports j)_j  ∈  F₂^k
   SameCell v w  ⟺  cellPatternVec v = cellPatternVec w                         (sameCell_iff_pattern)
   the patterns over L lie in their span (dim = cellRank), of size 2^{cellRank} (cellPattern_image_card_le)
   so  2^{cellRank} < |L|  ⇒  two coordinates share a cell                       (exists_sameCell_pair_of_rank)
   ⇒  a CellWitness  ⇒  the predictor cannot correlate with the holonomy parity  (rank_collapse_low_correlation)
```

The `2^{cellRank}` cell count is exactly the parity-cell count of `…ACC0ParityRankCardinality`
(`parity_reachable_card = 2^{finrank}`): rank, not survivor count, governs the cells.

## What is proved (clean axioms, no `sorry`)

* `cellPatternVec` / `sameCell_iff_pattern` — the cell of a coordinate as an `F₂` vector; `SameCell` is equality of
  these vectors.
* `cellSpan` / `cellRank` and **`cellPattern_image_card_le`** — the distinct cell patterns over `L` number at most
  `2^{cellRank}` (they lie in a span of dimension `cellRank`; `Module.card_eq_pow_finrank` + `ZMod.card`).
* **`exists_sameCell_pair_of_rank`** — `2^{cellRank} < |L|` ⇒ two distinct live coordinates share a cell (pigeonhole).
* **`rank_collapse_low_correlation`** — the sharp bridge: `2^{cellRank} < |L| ⇒ LowHolonomyCorrelation` (via
  `CellWitness` + the proved `cellWitness_gives_low_correlation`).

## Honest scope

This is the sharp bridge for the **rank** collapse condition — a *genuine* theorem, no socket: once `2^{cellRank} <
|L|`, the predictor provably fails to correlate.  It is strictly more general than the survivor bridge (`cellRank`,
the column rank, is `≤ survivingCount`, the row count — for overlapping supports it can be far smaller).  What remains
open is *forcing* `cellRank < log₂|L|` for a *real* `ACC⁰` support system under a restriction — the rank-flavoured
switching lemma (`NP ⊄ ACC⁰`-strength).  This file does the bridge, not that forcing.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RankBridge

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute

variable {k n : ℕ}

/-- The **cell pattern** of a coordinate `v`: the `F₂` vector of its membership in each support (a column of the
support-incidence matrix). -/
def cellPatternVec (supports : Fin k → Finset (Fin n)) (v : Fin n) : Fin k → ZMod 2 :=
  fun j => if v ∈ supports j then 1 else 0

/-- **`SameCell` is equality of cell patterns (proved).** -/
theorem sameCell_iff_pattern (supports : Fin k → Finset (Fin n)) (v w : Fin n) :
    SameCell supports v w ↔ cellPatternVec supports v = cellPatternVec supports w := by
  unfold SameCell
  rw [funext_iff]
  refine forall_congr' (fun j => ?_)
  simp only [cellPatternVec]
  constructor
  · intro h
    by_cases hv : v ∈ supports j
    · rw [if_pos hv, if_pos (h.mp hv)]
    · rw [if_neg hv, if_neg (fun hw => hv (h.mpr hw))]
  · intro h
    constructor
    · intro hv
      by_contra hw
      rw [if_pos hv, if_neg hw] at h
      exact absurd h (by decide)
    · intro hw
      by_contra hv
      rw [if_neg hv, if_pos hw] at h
      exact absurd h (by decide)

/-- The `F₂`-span of the cell patterns realized by the live coordinates `L`. -/
noncomputable def cellSpan (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) :
    Submodule (ZMod 2) (Fin k → ZMod 2) :=
  Submodule.span (ZMod 2) (↑(L.image (cellPatternVec supports)) : Set (Fin k → ZMod 2))

/-- The **cell rank**: the dimension of the span of the cell patterns — the true governor of the cell count. -/
noncomputable def cellRank (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) : ℕ :=
  Module.finrank (ZMod 2) (cellSpan supports L)

/-- **At most `2^{cellRank}` distinct cell patterns over `L` (proved).**  The patterns lie in their span, which has
exactly `2^{cellRank}` elements over `F₂`. -/
theorem cellPattern_image_card_le (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) :
    (L.image (cellPatternVec supports)).card ≤ 2 ^ cellRank supports L := by
  haveI : Fintype ↥(cellSpan supports L) := Fintype.ofFinite _
  have hcard : Fintype.card ↥(cellSpan supports L) = 2 ^ cellRank supports L := by
    rw [cellRank, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have hsub : L.image (cellPatternVec supports) ⊆
      (↑(cellSpan supports L) : Set (Fin k → ZMod 2)).toFinset := by
    intro p hp
    rw [Set.mem_toFinset]
    rw [Finset.mem_image] at hp
    obtain ⟨v, hv, rfl⟩ := hp
    exact Submodule.subset_span (by rw [Finset.mem_coe, Finset.mem_image]; exact ⟨v, hv, rfl⟩)
  calc (L.image (cellPatternVec supports)).card
      ≤ ((↑(cellSpan supports L) : Set (Fin k → ZMod 2)).toFinset).card := Finset.card_le_card hsub
    _ = Fintype.card ↥(cellSpan supports L) := by rw [Set.toFinset_card]; simp [SetLike.coe_sort_coe]
    _ = 2 ^ cellRank supports L := hcard

/-- **The sharp pigeonhole (proved): `2^{cellRank} < |L|` ⇒ two distinct live coordinates share a cell.** -/
theorem exists_sameCell_pair_of_rank (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n))
    (h : 2 ^ cellRank supports L < L.card) :
    ∃ v ∈ L, ∃ w ∈ L, v ≠ w ∧ SameCell supports v w := by
  have himg : (L.image (cellPatternVec supports)).card < L.card :=
    lt_of_le_of_lt (cellPattern_image_card_le supports L) h
  obtain ⟨v, hv, w, hw, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to himg
      (fun v hv => Finset.mem_image_of_mem _ hv)
  exact ⟨v, hv, w, hw, hne, (sameCell_iff_pattern supports v w).mpr heq⟩

/-- **A witness from low rank (proved): `2^{cellRank} < |L|` ⇒ `∃ D, CellWitness`.** -/
theorem exists_cellWitness_of_rank (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n))
    (h : 2 ^ cellRank supports L < L.card) : ∃ D : Finset (Fin n), CellWitness supports D := by
  obtain ⟨v, _, w, _, hne, hcell⟩ := exists_sameCell_pair_of_rank supports L h
  exact ⟨{v}, v, w, hne, Finset.mem_singleton_self v,
    fun hmem => hne (Finset.mem_singleton.mp hmem).symm, hcell⟩

/-- **The sharp rank bridge (proved): `2^{cellRank} < |L|` ⇒ low holonomy correlation.**  Strictly sharper than the
survivor bridge — the cell count is `2^{rank}`, not `2^{#survivors}`. -/
theorem rank_collapse_low_correlation (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool)
    (L : Finset (Fin n)) (h : 2 ^ cellRank supports L < L.card) :
    LowHolonomyCorrelation supports g := by
  obtain ⟨D, hwit⟩ := exists_cellWitness_of_rank supports L h
  obtain ⟨v, w, hvw, hb⟩ := cellWitness_gives_low_correlation supports D g hwit
  exact ⟨D, v, w, hvw, hb⟩

/-- **A cell pattern lies in the span of the surviving coordinate vectors (proved).**  For `v ∈ L`, the pattern
`cellPatternVec v` vanishes off the surviving indices, so it is a combination of `{Pi.single j 1 : j surviving}`. -/
theorem cellPatternVec_mem_survivorSpan (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n))
    {v : Fin n} (hv : v ∈ L) :
    cellPatternVec supports v ∈ Submodule.span (ZMod 2)
      (↑((Finset.univ.filter (fun j => ¬ Disjoint (supports j) L)).image
        (fun j => Pi.single j (1 : ZMod 2))) : Set (Fin k → ZMod 2)) := by
  set K := Finset.univ.filter (fun j => ¬ Disjoint (supports j) L) with hK
  have heq : cellPatternVec supports v
      = ∑ j ∈ K, cellPatternVec supports v j • Pi.single j (1 : ZMod 2) := by
    funext j'
    rw [Finset.sum_apply]
    by_cases hj' : j' ∈ K
    · rw [Finset.sum_eq_single_of_mem j' hj' (fun j _ hjne => by
          rw [Pi.smul_apply, Pi.single_apply, if_neg (fun h => hjne h.symm), smul_zero])]
      rw [Pi.smul_apply, Pi.single_apply, if_pos rfl, smul_eq_mul, mul_one]
    · rw [Finset.sum_eq_zero (fun j hj => by
          rw [Pi.smul_apply, Pi.single_apply, if_neg (by rintro rfl; exact hj' hj), smul_zero])]
      have hvj' : v ∉ supports j' := fun hmem => hj' (by
        rw [hK, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, Finset.not_disjoint_iff.mpr ⟨v, hmem, hv⟩⟩)
      simp only [cellPatternVec, if_neg hvj']
  rw [heq]
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  apply Submodule.subset_span
  rw [Finset.mem_coe, Finset.mem_image]
  exact ⟨j, hj, rfl⟩

/-- **`cellRank ≤ survivingCount` (proved): the column rank is at most the row count.**  So the rank bridge strictly
subsumes the survivor bridge. -/
theorem cellRank_le_survivingCount (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) :
    cellRank supports L ≤ survivingCount supports L := by
  have hle : cellSpan supports L ≤ Submodule.span (ZMod 2)
      (↑((Finset.univ.filter (fun j => ¬ Disjoint (supports j) L)).image
        (fun j => Pi.single j (1 : ZMod 2))) : Set (Fin k → ZMod 2)) := by
    rw [cellSpan, Submodule.span_le]
    intro p hp
    rw [Finset.mem_coe, Finset.mem_image] at hp
    obtain ⟨v, hv, rfl⟩ := hp
    exact cellPatternVec_mem_survivorSpan supports L hv
  calc cellRank supports L
      ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
          (↑((Finset.univ.filter (fun j => ¬ Disjoint (supports j) L)).image
            (fun j => Pi.single j (1 : ZMod 2))) : Set (Fin k → ZMod 2))) :=
        Submodule.finrank_mono hle
    _ ≤ ((Finset.univ.filter (fun j => ¬ Disjoint (supports j) L)).image
          (fun j => Pi.single j (1 : ZMod 2))).card := finrank_span_finset_le_card _
    _ ≤ (Finset.univ.filter (fun j => ¬ Disjoint (supports j) L)).card := Finset.card_image_le
    _ = survivingCount supports L := rfl

/-- **The survivor collapse implies the rank collapse (proved): the rank bridge subsumes the survivor bridge.** -/
theorem survivor_collapse_implies_rank_collapse (supports : Fin k → Finset (Fin n))
    (L : Finset (Fin n)) (h : 2 ^ survivingCount supports L < L.card) :
    2 ^ cellRank supports L < L.card :=
  lt_of_le_of_lt
    (Nat.pow_le_pow_right (by norm_num) (cellRank_le_survivingCount supports L)) h

end PallLean.Paper93.DeepMath.PathB.ACC0RankBridge

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RankBridge.cellRank_le_survivingCount
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RankBridge.survivor_collapse_implies_rank_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RankBridge.cellPattern_image_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RankBridge.exists_sameCell_pair_of_rank
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RankBridge.rank_collapse_low_correlation
