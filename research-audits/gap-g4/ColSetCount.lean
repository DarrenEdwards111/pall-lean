import Def12Measure

/-!
# G4.4 item 3: exact column count of the Def. 12 matrix

`colSet N D = {β : Fin N →₀ ℕ | β multilinear ∧ |β| ≤ D}` has exactly `Σ_{j ≤ D} C(N, j)` elements.
Hence `def12Rank_le_columns` reads `Γ ≤ Σ_{j ≤ deg p + ℓ − κ} C(N, j)`, the classical column bound.
-/

set_option autoImplicit false

open MvPolynomial

namespace Def12Measure

variable {N : ℕ}

/-- The 0/1 exponent vector of a set of variables. -/
noncomputable def indVec (s : Finset (Fin N)) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => if i ∈ s then 1 else 0)

@[simp] theorem indVec_apply (s : Finset (Fin N)) (i : Fin N) :
    indVec s i = if i ∈ s then 1 else 0 := by
  simp [indVec]

theorem indVec_support (s : Finset (Fin N)) : (indVec s).support = s := by
  ext i; by_cases h : i ∈ s <;> simp [h]

theorem weight_eq_card_support {β : Fin N →₀ ℕ} (h : Finsupp.IsMultilinear β) :
    weight β = β.support.card := by
  unfold weight Finsupp.sum
  rw [Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have h1 := h i
  have h2 : β i ≠ 0 := Finsupp.mem_support_iff.mp hi
  show β i = 1
  omega

theorem indVec_support_of_multilinear {β : Fin N →₀ ℕ} (h : Finsupp.IsMultilinear β) :
    indVec β.support = β := by
  ext i
  have h1 := h i
  by_cases h0 : β i = 0
  · simp [h0]
  · have : β i = 1 := by omega
    simp [this]

theorem indVec_multilinear (s : Finset (Fin N)) : Finsupp.IsMultilinear (indVec s) := by
  intro i; by_cases h : i ∈ s <;> simp [h]

/-- **Exact column count.** `#colSet N D = Σ_{j ≤ D} C(N, j)`. -/
theorem card_colSet (D : ℕ) :
    (colSet_finite (N := N) D).toFinset.card = ∑ j ∈ Finset.range (D + 1), N.choose j := by
  classical
  have hbij : (colSet_finite (N := N) D).toFinset.card =
      ((Finset.univ : Finset (Finset (Fin N))).filter (fun s => s.card ≤ D)).card := by
    refine Finset.card_nbij' (fun β => β.support) indVec ?_ ?_ ?_ ?_
    · intro β hβ
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      have hβ' : β ∈ colSet N D := by simpa using hβ
      rw [← weight_eq_card_support hβ'.1]; exact hβ'.2
    · intro s hs
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hs
      simp only [Set.Finite.coe_toFinset]
      refine ⟨indVec_multilinear s, ?_⟩
      rw [weight_eq_card_support (indVec_multilinear s), indVec_support]; exact hs
    · intro β hβ
      have hβ' : β ∈ colSet N D := by simpa using hβ
      exact indVec_support_of_multilinear hβ'.1
    · intro s _; exact indVec_support s
  rw [hbij]
  have hU : ((Finset.univ : Finset (Finset (Fin N))).filter (fun s => s.card ≤ D)) =
      (Finset.range (D + 1)).biUnion (fun j => Finset.powersetCard j Finset.univ) := by
    ext s
    simp [Finset.mem_powersetCard]
  rw [hU, Finset.card_biUnion]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  · intro i _ j _ hij
    exact Finset.disjoint_left.mpr (fun s hi hj =>
      hij ((Finset.mem_powersetCard.mp hi).2.symm.trans (Finset.mem_powersetCard.mp hj).2))

/-- `def12Rank_le_columns`, restated with the exact binomial count. -/
theorem def12Rank_le_binomialSum {F : Type*} [Field F] (c : Conv) (B : BlockPartition N) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin N) F) :
    def12Rank c B κ ℓ p ≤ ∑ j ∈ Finset.range (p.totalDegree + ℓ - κ + 1), N.choose j := by
  rw [← card_colSet]; exact def12Rank_le_columns c B κ ℓ p

end Def12Measure

#print axioms Def12Measure.card_colSet
#print axioms Def12Measure.def12Rank_le_binomialSum
