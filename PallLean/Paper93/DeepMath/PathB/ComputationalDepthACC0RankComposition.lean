import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0LowRankFragment

/-!
# Rank growth through a layer — `cellRank` is subadditive under `append`

The depth direction of the rank-observer route: when two support families are stacked (`Fin.append`), how does the
**observer rank** grow?  Unlike the survivor count (which is *additive*, `survivingCount_append`), the cell rank is
**subadditive**:

```
cellRank (append supp₁ supp₂) L  ≤  cellRank supp₁ L  +  cellRank supp₂ L
```

The append's cell pattern is the concatenation of the two patterns — `cellPatternVec (append) v =
embedFst (cellPatternVec supp₁ v) + embedSnd (cellPatternVec supp₂ v)` — so the combined cell space lies in the sum
of the two embedded cell spaces, and `finrank(A ⊔ B) ≤ finrank A + finrank B`.

This turns depth composition into **rank-budget accounting**: a layer that adds only `r₂` observer degrees of freedom
keeps the composite rank within `r₁ + r₂` — much closer to the full N-Frame observer strategy than survivor-budget
accounting.

## What is proved (clean axioms, no `sorry`)

* `embedFst` / `embedSnd` — the `F₂`-linear inclusions extending a `Fin k₁` (resp. `Fin k₂`) vector by zero into
  `Fin (k₁+k₂)`; `cellPatternVec_append_eq` — the append pattern decomposes as their sum.
* **`cellRank_append_le`** — `cellRank (append supp₁ supp₂) L ≤ cellRank supp₁ L + cellRank supp₂ L`.
* **`rank_collapse_lifts_of_rank_budget`** — `2^{r₁+r₂} < |L|`, `cellRank supp₁ L ≤ r₁`, `cellRank supp₂ L ≤ r₂` ⇒
  `2^{cellRank (append …)} < |L|` (the composite rank collapse, by budget).

## Honest scope

This is the *rank* composition law: collapse lifts through a layer under a **rank** budget (`r₁ + r₂`), the sharpened
analogue of the survivor-budget `collapse_lifts_through_layer`.  Whether a real `ACC⁰` layer adds only a small rank
budget is the structural question — the open rank-flavoured switching lemma.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RankComposition

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge

variable {k₁ k₂ n : ℕ}

/-- The `F₂`-linear inclusion `Fin k₁ → ZMod 2 ↪ Fin (k₁+k₂) → ZMod 2`, extending by zero on the second block. -/
def embedFst (k₁ k₂ : ℕ) : (Fin k₁ → ZMod 2) →ₗ[ZMod 2] (Fin (k₁ + k₂) → ZMod 2) where
  toFun f := Fin.append f 0
  map_add' f g := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [Fin.append_left]
    · simp [Fin.append_right]
  map_smul' c f := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [Fin.append_left]
    · simp [Fin.append_right]

/-- The `F₂`-linear inclusion `Fin k₂ → ZMod 2 ↪ Fin (k₁+k₂) → ZMod 2`, extending by zero on the first block. -/
def embedSnd (k₁ k₂ : ℕ) : (Fin k₂ → ZMod 2) →ₗ[ZMod 2] (Fin (k₁ + k₂) → ZMod 2) where
  toFun f := Fin.append 0 f
  map_add' f g := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [Fin.append_left]
    · simp [Fin.append_right]
  map_smul' c f := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [Fin.append_left]
    · simp [Fin.append_right]

/-- **The append cell pattern decomposes (proved): `cellPatternVec (append) v = embedFst p₁ + embedSnd p₂`.** -/
theorem cellPatternVec_append_eq (supp₁ : Fin k₁ → Finset (Fin n)) (supp₂ : Fin k₂ → Finset (Fin n))
    (v : Fin n) :
    cellPatternVec (Fin.append supp₁ supp₂) v
      = embedFst k₁ k₂ (cellPatternVec supp₁ v) + embedSnd k₁ k₂ (cellPatternVec supp₂ v) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [cellPatternVec, embedFst, embedSnd, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply,
      Fin.append_left, Pi.zero_apply, add_zero]
  · simp only [cellPatternVec, embedFst, embedSnd, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply,
      Fin.append_right, Pi.zero_apply, zero_add]

/-- **`cellRank` is subadditive under `append` (proved).** -/
theorem cellRank_append_le (supp₁ : Fin k₁ → Finset (Fin n)) (supp₂ : Fin k₂ → Finset (Fin n))
    (L : Finset (Fin n)) :
    cellRank (Fin.append supp₁ supp₂) L ≤ cellRank supp₁ L + cellRank supp₂ L := by
  -- the combined cell space lies in the sum of the two embedded cell spaces
  have hle : cellSpan (Fin.append supp₁ supp₂) L ≤
      (cellSpan supp₁ L).map (embedFst k₁ k₂) ⊔ (cellSpan supp₂ L).map (embedSnd k₁ k₂) := by
    rw [cellSpan, Submodule.span_le]
    intro p hp
    rw [Finset.mem_coe, Finset.mem_image] at hp
    obtain ⟨v, hv, rfl⟩ := hp
    rw [cellPatternVec_append_eq]
    apply Submodule.add_mem_sup
    · exact Submodule.mem_map_of_mem (Submodule.subset_span (by
        rw [Finset.mem_coe, Finset.mem_image]; exact ⟨v, hv, rfl⟩))
    · exact Submodule.mem_map_of_mem (Submodule.subset_span (by
        rw [Finset.mem_coe, Finset.mem_image]; exact ⟨v, hv, rfl⟩))
  calc cellRank (Fin.append supp₁ supp₂) L
      ≤ Module.finrank (ZMod 2)
          (((cellSpan supp₁ L).map (embedFst k₁ k₂) ⊔ (cellSpan supp₂ L).map (embedSnd k₁ k₂)) :
            Submodule (ZMod 2) (Fin (k₁ + k₂) → ZMod 2)) :=
        Submodule.finrank_mono hle
    _ ≤ Module.finrank (ZMod 2) ((cellSpan supp₁ L).map (embedFst k₁ k₂))
          + Module.finrank (ZMod 2) ((cellSpan supp₂ L).map (embedSnd k₁ k₂)) := by
        have := Submodule.finrank_sup_add_finrank_inf_eq
          ((cellSpan supp₁ L).map (embedFst k₁ k₂)) ((cellSpan supp₂ L).map (embedSnd k₁ k₂))
        omega
    _ ≤ cellRank supp₁ L + cellRank supp₂ L :=
        Nat.add_le_add (Submodule.finrank_map_le _ _) (Submodule.finrank_map_le _ _)

/-- **The composite rank collapse, by rank budget (proved).**  If `2^{r₁+r₂} < |L|` and each layer's cell rank is
`≤ rᵢ`, the appended system has `2^{cellRank} < |L|` — rank-budget accounting for depth composition. -/
theorem rank_collapse_lifts_of_rank_budget (supp₁ : Fin k₁ → Finset (Fin n))
    (supp₂ : Fin k₂ → Finset (Fin n)) (L : Finset (Fin n)) (r₁ r₂ : ℕ)
    (hbudget : 2 ^ (r₁ + r₂) < L.card) (h₁ : cellRank supp₁ L ≤ r₁) (h₂ : cellRank supp₂ L ≤ r₂) :
    2 ^ cellRank (Fin.append supp₁ supp₂) L < L.card := by
  refine lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) ?_) hbudget
  exact le_trans (cellRank_append_le supp₁ supp₂ L) (Nat.add_le_add h₁ h₂)

end PallLean.Paper93.DeepMath.PathB.ACC0RankComposition

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RankComposition.cellRank_append_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RankComposition.rank_collapse_lifts_of_rank_budget
