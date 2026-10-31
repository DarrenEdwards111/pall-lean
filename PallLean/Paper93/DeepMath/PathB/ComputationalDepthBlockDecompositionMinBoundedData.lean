import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverBlockDecompositionMin

/-!
# Graceful degradation: address blocks plus a bounded number of data cells

`ComputationalDepthBlockDecompositionMinUnion` enlarges the address-block min-realized class to *address-only*
supersets of a block (unions of blocks), keeping the boundary `≥ 2^b − 1`.  `BlockDecompositionMinGap` shows a
cut *entirely* outside the address structure (a single data variable) is cheap (`≤ 2`).  This file interpolates:
mixing a **bounded number of data cells** into the free block degrades the bound **gracefully** — by at most one
per added cell — rather than collapsing.

## The mechanism (fully general, no `hardF` re-derivation)

`blockResiduals_card_le_two_mul_insert`: adding one variable `v` to the free block at most **halves** the
residual count — every residual on `S` is a residual on `insert v S` restricted at `v`, so it factors through
`blockResiduals (insert v S) F × Bool`.  Hence `formulaBlockBoundary_le_insert_succ`: the boundary drops by at
most `1`.  Iterating (`formulaBlockBoundary_le_union_add_card`) over a data set `D` gives, with the address-only
base bound:

* `hardF_union_data_blockBoundary_ge`: `formulaBlockBoundary (blockS k ∪ D) F ≥ 2^b − 1 − |D|`.
* `hardF_union_data_superlog`: for `|D| ≤ 2^{b−1}` the boundary is still `≥ 2^{b−1} − 1` — super-logarithmic.

So the min-realized bound survives mixing in `o(2^b)` data cells; only a cut that is *mostly* data (as in
`BlockDecompositionMinGap`) collapses it.  The first three lemmas are general observer-boundary facts, reusable
beyond `hardF`.

## Honest scope

A quantitative robustness result for the address-block min-realized rung.  Still a restricted class (address block
plus few data cells, not *every* decomposition); the general min stays `= CookLevinFrontierHyp`.  No separation,
no new complexity-class bound.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BlockDecompositionMinBoundedData

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.NecHard
open PallLean.Paper93.DeepMath.PathB.ObserverNeciporuk
open scoped BigOperators

/-! ## General: one extra free variable at most halves the residual count -/

/-- **Adding a variable to the free block at most halves the residual count.**  Every residual on `S` equals a
residual on `insert v S` with `v` fixed, so the map factors through `blockResiduals (insert v S) F × Bool`. -/
theorem blockResiduals_card_le_two_mul_insert {n : ℕ} (v : Fin n) (S : Finset (Fin n)) (F : BFormula n) :
    (blockResiduals S F).card ≤ 2 * (blockResiduals (insert v S) F).card := by
  classical
  by_cases hv : v ∈ S
  · rw [Finset.insert_eq_self.mpr hv]; omega
  · have hsub : blockResiduals S F ⊆
        (blockResiduals (insert v S) F ×ˢ (Finset.univ : Finset Bool)).image
          (fun p => (fun x : Fin n → Bool => p.1 (Function.update x v p.2))) := by
      intro g hg
      simp only [blockResiduals, Finset.mem_image, Finset.mem_univ, true_and] at hg
      obtain ⟨α, rfl⟩ := hg
      refine Finset.mem_image.mpr
        ⟨(fun x => BFormula.eval F (fun i => if i ∈ insert v S then x i else α i), α v), ?_, ?_⟩
      · rw [Finset.mem_product]
        exact ⟨Finset.mem_image.mpr ⟨α, Finset.mem_univ _, rfl⟩, Finset.mem_univ _⟩
      · funext x
        show BFormula.eval F (fun i => if i ∈ insert v S then (Function.update x v (α v)) i else α i)
           = BFormula.eval F (fun i => if i ∈ S then x i else α i)
        congr 1
        funext i
        by_cases hiv : i = v
        · subst hiv
          rw [if_pos (Finset.mem_insert_self i S), Function.update_self, if_neg hv]
        · rw [Function.update_of_ne hiv]
          by_cases hiS : i ∈ S
          · rw [if_pos (Finset.mem_insert_of_mem hiS), if_pos hiS]
          · rw [if_neg (fun h => (Finset.mem_insert.mp h).elim hiv hiS), if_neg hiS]
    calc (blockResiduals S F).card
        ≤ ((blockResiduals (insert v S) F ×ˢ (Finset.univ : Finset Bool)).image
            (fun p => (fun x : Fin n → Bool => p.1 (Function.update x v p.2)))).card :=
          Finset.card_le_card hsub
      _ ≤ (blockResiduals (insert v S) F ×ˢ (Finset.univ : Finset Bool)).card := Finset.card_image_le
      _ = 2 * (blockResiduals (insert v S) F).card := by
          rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]; ring

/-- **Adding a variable drops the observer boundary by at most `1`.** -/
theorem formulaBlockBoundary_le_insert_succ {n : ℕ} (v : Fin n) (S : Finset (Fin n)) (F : BFormula n) :
    formulaBlockBoundary S F ≤ formulaBlockBoundary (insert v S) F + 1 := by
  classical
  have hcard := blockResiduals_card_le_two_mul_insert v S F
  have hne : (blockResiduals (insert v S) F).Nonempty := by
    simp only [blockResiduals]
    exact Finset.univ_nonempty.image _
  unfold formulaBlockBoundary
  calc Nat.log 2 ((blockResiduals S F).card)
      ≤ Nat.log 2 (2 * (blockResiduals (insert v S) F).card) := Nat.log_mono_right hcard
    _ = Nat.log 2 ((blockResiduals (insert v S) F).card) + 1 := by
        rw [Nat.mul_comm, Nat.log_mul_base (by norm_num) (Finset.card_ne_zero.mpr hne)]

/-- **Iterating: adding a whole set `D` to the free block drops the boundary by at most `|D|`.** -/
theorem formulaBlockBoundary_le_union_add_card {n : ℕ} (S D : Finset (Fin n)) (F : BFormula n) :
    formulaBlockBoundary S F ≤ formulaBlockBoundary (S ∪ D) F + D.card := by
  classical
  induction D using Finset.induction with
  | empty => simp
  | @insert v D hv ih =>
      rw [Finset.union_insert, Finset.card_insert_of_notMem hv]
      have hstep := formulaBlockBoundary_le_insert_succ v (S ∪ D) F
      omega

/-! ## `hardF`: graceful degradation with a bounded number of data cells -/

variable {b m : ℕ}

/-- **Graceful degradation.**  Mixing a data set `D` into the free block of address block `k` keeps the boundary
`≥ 2^b − 1 − |D|` — at most one lost per data cell, no collapse. -/
theorem hardF_union_data_blockBoundary_ge (k : Fin m) (D : Finset (Fin (nn b m)))
    (F : BFormula (nn b m)) (hF : ∀ x, BFormula.eval F x = hardF x) :
    Dsize b - 1 - D.card ≤ formulaBlockBoundary (blockS k ∪ D) F := by
  have hbase := hardF_blockBoundary_ge k F hF
  have hstep := formulaBlockBoundary_le_union_add_card (blockS k) D F
  omega

/-- **Still super-logarithmic for `|D| ≤ 2^{b−1}`.**  Up to half a block's worth of data cells, the boundary
stays `≥ 2^{b−1} − 1`. -/
theorem hardF_union_data_superlog (hb : 1 ≤ b) (k : Fin m) (D : Finset (Fin (nn b m)))
    (hD : D.card ≤ 2 ^ (b - 1)) (F : BFormula (nn b m)) (hF : ∀ x, BFormula.eval F x = hardF x) :
    2 ^ (b - 1) - 1 ≤ formulaBlockBoundary (blockS k ∪ D) F := by
  have hmain := hardF_union_data_blockBoundary_ge k D F hF
  have hd : Dsize b = 2 ^ b := dsize_eq
  have hsplit : 2 ^ b = 2 ^ (b - 1) + 2 ^ (b - 1) := by
    conv_lhs => rw [show b = (b - 1) + 1 from by omega]
    rw [pow_succ]; ring
  omega

end PallLean.Paper93.DeepMath.PathB.BlockDecompositionMinBoundedData

#print axioms PallLean.Paper93.DeepMath.PathB.BlockDecompositionMinBoundedData.formulaBlockBoundary_le_insert_succ
#print axioms PallLean.Paper93.DeepMath.PathB.BlockDecompositionMinBoundedData.hardF_union_data_blockBoundary_ge
#print axioms PallLean.Paper93.DeepMath.PathB.BlockDecompositionMinBoundedData.hardF_union_data_superlog
