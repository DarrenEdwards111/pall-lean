import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverBlockDecompositionMin

/-!
# The address-block min-realized class, enlarged to unions of blocks

`ComputationalDepthObserverBlockDecompositionMin` proves the min over the `m` *singleton* address blocks of
`hardF` is `≥ 2^b − 1`.  This file **enlarges the decomposition class** — from the `m` single blocks to every
address-only superset of a single block, in particular every nonempty **union** of address blocks (`2^m − 1`
decompositions) — and shows the minimum boundary stays `≥ 2^b − 1`.

## Why the bound survives (and why address-only)

The single-block bound comes from the data-table fooling family (`card_blockResiduals_hardF_ge`): distinct data
tables `t` (with the reserved cell `c0` set to `false`) give distinct residuals on `blockS k`, witnessed by
driving block `k`'s address to the differing cell (`hardF_merge`).

For a superset `S ⊇ blockS k` in which **every variable is an address bit** (`∀ i ∈ S, i.val < m·b`), the same
family works: the data cells are all *outside* `S`, so the family still sets them; and the fooling witness
`fun i => if i ∈ blockS k then wit k c i else false` (drive block `k` to `c`, every other block to the reserved
cell) makes the full assignment `if i ∈ S then witness else mkt t` **coincide** with the single-block assignment
`if i ∈ blockS k then wit k c i else mkt t` — because on `S \ blockS k` the witness is `false` and `mkt t` is also
`false` there (those are address bits).  So `hardF_merge` transfers verbatim (`hardF_merge_superset`).

The address-only hypothesis is essential: if `S` contained a data cell, the family could no longer set it and the
argument breaks — matching `BlockDecompositionMinGap`, where a cheap cut lives outside the address structure.

## Honest scope

A genuine (still restricted) enlargement of the address-block min-realized rung: the min over the union class is
super-logarithmic.  The class is still structured (address-only supersets of blocks), not *every* decomposition —
the general min stays `= CookLevinFrontierHyp`.  No separation, no new complexity-class bound.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BlockDecompositionMinUnion

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.NecHard
open PallLean.Paper93.DeepMath.PathB.ObserverNeciporuk
open scoped BigOperators

variable {b m : ℕ}

/-! ## The generalized merge lemma -/

/-- **The value lemma for an address-only superset.**  With block `k` driven to cell `c` and everything else at
the reserved cell, the assignment restricted to any address-only `S ⊇ blockS k` returns `t c` — because it
coincides with the single-block assignment of `hardF_merge`. -/
theorem hardF_merge_superset (k : Fin m) (S : Finset (Fin (nn b m))) (hkS : blockS k ⊆ S)
    (hSaddr : ∀ i ∈ S, (i : Fin (nn b m)).val < m * b) (c : Fin (Dsize b))
    (t : Fin (Dsize b) → Bool) (hc0 : t c0 = false) :
    hardF (fun i => if i ∈ S then (if i ∈ blockS k then wit k c i else false) else mkt t i) = t c := by
  have heq : (fun i => if i ∈ S then (if i ∈ blockS k then wit k c i else false) else mkt t i)
      = (fun i => if i ∈ blockS k then wit k c i else mkt t i) := by
    funext i
    by_cases hik : i ∈ blockS k
    · have hiS : i ∈ S := hkS hik
      simp only [if_pos hiS, if_pos hik]
    · by_cases hiS : i ∈ S
      · have hmt : mkt t i = false := by
          unfold mkt; rw [dif_neg (Nat.not_le.mpr (hSaddr i hiS))]
        simp only [if_pos hiS, if_neg hik, hmt]
      · simp only [if_neg hiS, if_neg hik]
  rw [heq]
  exact hardF_merge k c t hc0

/-! ## The per-block bound on an address-only superset -/

/-- **The subfunction lower bound on an address-only superset.**  Every address-only `S ⊇ blockS k` has at least
`2^{2^b − 1}` distinct residuals — the data-table fooling family injects, separated by `hardF_merge_superset`. -/
theorem card_blockResiduals_hardF_ge_superset (k : Fin m) (S : Finset (Fin (nn b m)))
    (hkS : blockS k ⊆ S) (hSaddr : ∀ i ∈ S, (i : Fin (nn b m)).val < m * b)
    (F : BFormula (nn b m)) (hF : ∀ x, BFormula.eval F x = hardF x) :
    (Finset.univ.filter (fun t : Fin (Dsize b) → Bool => t c0 = false)).card
      ≤ (blockResiduals S F).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun t => (fun x => BFormula.eval F (fun i => if i ∈ S then x i else mkt t i)))
    ?_ ?_
  · intro t _
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨mkt t, Finset.mem_univ _, rfl⟩)
  · intro t ht t' ht' hgt
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
    funext c
    have hc : BFormula.eval F
          (fun i => if i ∈ S then (if i ∈ blockS k then wit k c i else false) else mkt t i)
        = BFormula.eval F
          (fun i => if i ∈ S then (if i ∈ blockS k then wit k c i else false) else mkt t' i) :=
      congrFun hgt (fun i => if i ∈ blockS k then wit k c i else false)
    rw [hF, hF, hardF_merge_superset k S hkS hSaddr c t ht,
      hardF_merge_superset k S hkS hSaddr c t' ht'] at hc
    exact hc

/-- **`hardF` forces boundary `≥ 2^b − 1` on every address-only superset of a block.** -/
theorem hardF_blockBoundary_ge_superset (k : Fin m) (S : Finset (Fin (nn b m)))
    (hkS : blockS k ⊆ S) (hSaddr : ∀ i ∈ S, (i : Fin (nn b m)).val < m * b)
    (F : BFormula (nn b m)) (hF : ∀ x, BFormula.eval F x = hardF x) :
    Dsize b - 1 ≤ formulaBlockBoundary S F := by
  have h1 : 2 ^ (Dsize b - 1) ≤ (blockResiduals S F).card := by
    rw [← filter_c0_false_card]
    exact card_blockResiduals_hardF_ge_superset k S hkS hSaddr F hF
  unfold formulaBlockBoundary
  calc Dsize b - 1 = Nat.log 2 (2 ^ (Dsize b - 1)) := (Nat.log_pow (by norm_num) _).symm
    _ ≤ Nat.log 2 ((blockResiduals S F).card) := Nat.log_mono_right h1

/-! ## Unions of address blocks -/

/-- Every address-bit variable of any block lies in the address region `[0, m·b)`. -/
theorem blockS_val_lt {k' : Fin m} {i : Fin (nn b m)} (hi : i ∈ blockS k') : i.val < m * b := by
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
  have hk : k'.val < m := k'.isLt
  have e1 : (k'.val + 1) * b ≤ m * b := by gcongr; omega
  have e2 : (k'.val + 1) * b = k'.val * b + b := by ring
  have e3 : j.val < b := j.isLt
  show k'.val * b + j.val < m * b
  omega

/-- **Every nonempty union of address blocks forces boundary `≥ 2^b − 1`.**  So the minimum over the union class
(all `2^m − 1` nonempty unions) is `≥ 2^b − 1` — a strict enlargement of the `m` singleton blocks. -/
theorem hardF_union_blockBoundary_ge (K : Finset (Fin m)) (hK : K.Nonempty)
    (F : BFormula (nn b m)) (hF : ∀ x, BFormula.eval F x = hardF x) :
    Dsize b - 1 ≤ formulaBlockBoundary (K.biUnion blockS) F := by
  obtain ⟨k, hk⟩ := hK
  refine hardF_blockBoundary_ge_superset k (K.biUnion blockS)
    (Finset.subset_biUnion_of_mem blockS hk) ?_ F hF
  intro i hi
  obtain ⟨k', -, hik'⟩ := Finset.mem_biUnion.mp hi
  exact blockS_val_lt hik'

/-! ## The min over the enlarged (union) class -/

/-- **The minimum boundary over the nonempty-union decomposition class.** -/
noncomputable def minUnionBlockBoundary (hm : 0 < m) (F : BFormula (nn b m)) : ℕ :=
  (((Finset.univ : Finset (Fin m)).powerset.filter (fun K => K.Nonempty)).inf'
    ⟨{⟨0, hm⟩}, by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.subset_univ _, Finset.singleton_nonempty _⟩⟩
    (fun K => formulaBlockBoundary (K.biUnion blockS) F))

/-- **The min over the union class is `≥ 2^b − 1`.**  Every nonempty union of address blocks is expensive; the
enlargement from `m` singletons to `2^m − 1` unions keeps the minimum super-logarithmic. -/
theorem hardF_minUnionBlockBoundary_ge (hm : 0 < m) (F : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = hardF x) :
    Dsize b - 1 ≤ minUnionBlockBoundary hm F := by
  unfold minUnionBlockBoundary
  apply Finset.le_inf'
  intro K hK
  rw [Finset.mem_filter] at hK
  exact hardF_union_blockBoundary_ge K hK.2 F hF

end PallLean.Paper93.DeepMath.PathB.BlockDecompositionMinUnion

#print axioms PallLean.Paper93.DeepMath.PathB.BlockDecompositionMinUnion.hardF_blockBoundary_ge_superset
#print axioms PallLean.Paper93.DeepMath.PathB.BlockDecompositionMinUnion.hardF_union_blockBoundary_ge
#print axioms PallLean.Paper93.DeepMath.PathB.BlockDecompositionMinUnion.hardF_minUnionBlockBoundary_ge
