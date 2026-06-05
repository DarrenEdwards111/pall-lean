import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukCountingLemma

/-!
# Nečiporuk lower-bound tool: many distinct subfunctions ⇒ large block-residual count

`neciporuk_formula_lower_bound` lower-bounds formula size by `∑ᵢ log₂ (#blockResiduals (Sᵢ) F)`.
`blockResiduals_card_le` is the *upper* bound (the counting capacity).  To turn the method on a
**concrete** hard function we need the *lower* direction: a function with many distinct subfunctions
on each block.  This file supplies the reusable bridge.

`blockResiduals (S) F = univ.image (α ↦ (x ↦ eval F (merge S x α)))` — the residual for parameters `α`
is the subfunction of `eval F` on block `S`.  So if a finite family `P` of parameter settings maps
**injectively** to subfunctions (distinct `α ∈ P` give pointwise-different restrictions to `S`), then
`#blockResiduals (S) F ≥ |P|`.

* `card_blockResiduals_ge` — the lower bound from an injective parameter family.
* `card_blockResiduals_ge_of_pairwise` — convenience form: a pairwise-separated family
  (`∀ α ≠ β ∈ P, ∃ x, eval F (merge S x α) ≠ eval F (merge S x β)`) gives `|P| ≤ #blockResiduals`.

These feed `neciporuk_formula_lower_bound` to produce explicit formula-size lower bounds once a
concrete function with provably-many block subfunctions is supplied.
-/

namespace PallLean.Paper93.DeepMath.PathB

variable {n : ℕ}

/-- **Subfunction lower bound (injective family).**  If the parameter-to-subfunction map is injective
on a finite set `P` of parameter settings, then the block-residual count is at least `|P|`. -/
theorem card_blockResiduals_ge (S : Finset (Fin n)) (F : BFormula n)
    {P : Finset (Fin n → Bool)}
    (hinj : Set.InjOn
      (fun α : Fin n → Bool =>
        (fun (x : Fin n → Bool) => BFormula.eval F (fun i => if i ∈ S then x i else α i)))
      (P : Set (Fin n → Bool))) :
    P.card ≤ (blockResiduals S F).card := by
  unfold blockResiduals
  rw [← Finset.card_image_of_injOn hinj]
  exact Finset.card_le_card (Finset.image_subset_image (Finset.subset_univ P))

/-- **Subfunction lower bound (pairwise-separated family).**  If distinct parameter settings in `P`
yield restrictions that differ at some input, the block-residual count is at least `|P|`. -/
theorem card_blockResiduals_ge_of_pairwise (S : Finset (Fin n)) (F : BFormula n)
    {P : Finset (Fin n → Bool)}
    (hsep : ∀ α ∈ P, ∀ β ∈ P, α ≠ β →
      ∃ x : Fin n → Bool, BFormula.eval F (fun i => if i ∈ S then x i else α i)
         ≠ BFormula.eval F (fun i => if i ∈ S then x i else β i)) :
    P.card ≤ (blockResiduals S F).card := by
  refine card_blockResiduals_ge S F ?_
  intro α hα β hβ hαβ
  by_contra hne
  obtain ⟨x, hx⟩ := hsep α hα β hβ hne
  exact hx (congrFun hαβ x)

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.card_blockResiduals_ge
#print axioms PallLean.Paper93.DeepMath.PathB.card_blockResiduals_ge_of_pairwise
