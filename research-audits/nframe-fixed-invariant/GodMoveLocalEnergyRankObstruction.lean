import PallLean.MultilinearSPDP

/-!
# The local accumulator energy does not supply the strict-rank bridge

This file tests the actual sum-of-squares polynomial of a five-step local
product accumulator, not just an isolated output wire.  Variables 0,...,5
are accumulator wires and variables 6,...,10 are selectors.  The factors
are `1 - z_i`, the paper factors with their clause-square values fixed to one.

The energy is `(w_0 - 1)^2 + sum_i (w_{i+1} - w_i (1-z_i))^2`.
Every summand has total degree at most four.  Hence its strict blocked SPDP
rank at derivative order five is zero.  The product of the five factors has
an admissible fifth derivative equal to minus one, so its rank is positive
at the same parameters and the same discrete partition.

Adding the final output wire `w_5` to the energy does not change this
obstruction: `E + w_5` still has degree at most four and strict rank zero.
Thus merely adjoining that output term does not repair the rank inequality.

Thus this concrete additive local energy cannot be the source of a
rank-nonincreasing extraction of this product for these strict parameters.
The recurrence can still correctly encode the product semantically: a
zero-energy constraint system and a polynomial identity are different
claims.  This result is not about the inclusive derivative convention, a
rank transport with changed parameters/loss, other source compilers, or
P versus NP.
-/

namespace GodMoveLocalEnergyRankObstruction

open MvPolynomial SPDP MultilinearSPDP
open scoped BigOperators

abbrev Poly := MvPolynomial (Fin 11) ℚ

def discreteBlocks : BlockPartition 11 where
  numBlocks := 11
  assign := id

def wireIndex (i : Fin 6) : Fin 11 := ⟨i.val, by omega⟩

def selectorIndex (i : Fin 5) : Fin 11 := ⟨6 + i.val, by omega⟩

noncomputable def wire (i : Fin 6) : Poly := X (wireIndex i)

noncomputable def factor (i : Fin 5) : Poly := 1 - X (selectorIndex i)

noncomputable def residual (i : Fin 5) : Poly :=
  wire i.succ - wire i.castSucc * factor i

noncomputable def localEnergy : Poly :=
  (wire 0 - 1) ^ 2 + ∑ i : Fin 5, residual i ^ 2

noncomputable def energyWithOutput : Poly := localEnergy + wire 5

noncomputable def productSheet : Poly := ∏ i : Fin 5, factor i

theorem factor_totalDegree_le_one (i : Fin 5) : (factor i).totalDegree ≤ 1 := by
  exact (totalDegree_sub _ _).trans (by simp)

theorem residual_totalDegree_le_two (i : Fin 5) : (residual i).totalDegree ≤ 2 := by
  have hmul : (wire i.castSucc * factor i).totalDegree ≤ 2 := by
    have h := totalDegree_mul (wire i.castSucc) (factor i)
    have hf := factor_totalDegree_le_one i
    have hw : (wire i.castSucc).totalDegree = 1 := by simp [wire]
    rw [hw] at h
    omega
  exact (totalDegree_sub _ _).trans (max_le (by simp [wire]) hmul)

theorem localEnergy_totalDegree_le_four : localEnergy.totalDegree ≤ 4 := by
  have hinit : ((wire 0 - 1) ^ 2).totalDegree ≤ 4 := by
    have hbase : (wire 0 - 1).totalDegree ≤ 1 :=
      (totalDegree_sub _ _).trans (by simp [wire])
    have h := totalDegree_pow (wire 0 - 1) 2
    omega
  have hsum : (∑ i : Fin 5, residual i ^ 2).totalDegree ≤ 4 := by
    apply totalDegree_finsetSum_le
    intro i _
    have h := totalDegree_pow (residual i) 2
    have hr := residual_totalDegree_le_two i
    omega
  exact (totalDegree_add _ _).trans (max_le hinit hsum)

theorem localEnergy_rank_zero :
    mlBlockedSpdpRank discreteBlocks 5 0 localEnergy = 0 := by
  have h := mlBlockedSpdpRank_add_lowDeg ℚ discreteBlocks 5 0 (0 : Poly) localEnergy
    (by have hd := localEnergy_totalDegree_le_four; omega)
  simpa [mlBlockedSpdpRank_zero] using h

theorem energyWithOutput_totalDegree_le_four : energyWithOutput.totalDegree ≤ 4 := by
  exact (totalDegree_add _ _).trans
    (max_le localEnergy_totalDegree_le_four (by simp [wire]))

theorem energyWithOutput_rank_zero :
    mlBlockedSpdpRank discreteBlocks 5 0 energyWithOutput = 0 := by
  have h := mlBlockedSpdpRank_add_lowDeg ℚ discreteBlocks 5 0 (0 : Poly) energyWithOutput
    (by have hd := energyWithOutput_totalDegree_le_four; omega)
  simpa [mlBlockedSpdpRank_zero] using h

theorem selector_list_admissible :
    isBlockAdmissible discreteBlocks ([6, 7, 8, 9, 10] : List (Fin 11)) := by
  constructor
  · decide
  · intro b
    fin_cases b <;> simp [discreteBlocks]

theorem product_fifth_derivative :
    iterDerivList ([6, 7, 8, 9, 10] : List (Fin 11)) productSheet = -1 := by
  simp [iterDerivList, productSheet, Fin.prod_univ_succ, factor, selectorIndex, map_sub]

theorem one_mem_product_subspace :
    (1 : Poly) ∈ mlBlockedSpdpSubspace discreteBlocks 5 0 productSheet := by
  apply Submodule.subset_span
  refine ⟨[6, 7, 8, 9, 10], (-1 : Poly), rfl, by simp, by simp,
    selector_list_admissible, ?_⟩
  rw [product_fifth_derivative]
  simp only [neg_mul_neg, one_mul]
  symm
  apply mlProj_of_isMultilinear
  intro a ha i
  have ha0 : a = 0 := by simpa [MvPolynomial.coeff_one, eq_comm] using ha
  simp [ha0]

theorem product_rank_pos : 0 < mlBlockedSpdpRank discreteBlocks 5 0 productSheet := by
  unfold mlBlockedSpdpRank
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨1, one_mem_product_subspace⟩, ?_⟩
  intro h
  exact one_ne_zero (congrArg Subtype.val h)

theorem product_rank_exceeds_localEnergy_rank :
    mlBlockedSpdpRank discreteBlocks 5 0 localEnergy <
      mlBlockedSpdpRank discreteBlocks 5 0 productSheet := by
  rw [localEnergy_rank_zero]
  exact product_rank_pos

/-- The desired no-loss strict-rank inequality fails for this actual local
sum-of-squares source and its five-factor product output. -/
theorem localEnergy_to_product_rank_bridge_false :
    ¬ mlBlockedSpdpRank discreteBlocks 5 0 productSheet ≤
      mlBlockedSpdpRank discreteBlocks 5 0 localEnergy :=
  not_le_of_gt product_rank_exceeds_localEnergy_rank

theorem product_rank_exceeds_energyWithOutput_rank :
    mlBlockedSpdpRank discreteBlocks 5 0 energyWithOutput <
      mlBlockedSpdpRank discreteBlocks 5 0 productSheet := by
  rw [energyWithOutput_rank_zero]
  exact product_rank_pos

/-- Including the final accumulator wire as an additive output term does
not repair the no-loss strict-rank bridge. -/
theorem energyWithOutput_to_product_rank_bridge_false :
    ¬ mlBlockedSpdpRank discreteBlocks 5 0 productSheet ≤
      mlBlockedSpdpRank discreteBlocks 5 0 energyWithOutput :=
  not_le_of_gt product_rank_exceeds_energyWithOutput_rank

end GodMoveLocalEnergyRankObstruction

#print axioms GodMoveLocalEnergyRankObstruction.localEnergy_totalDegree_le_four
#print axioms GodMoveLocalEnergyRankObstruction.localEnergy_rank_zero
#print axioms GodMoveLocalEnergyRankObstruction.product_rank_pos
#print axioms GodMoveLocalEnergyRankObstruction.localEnergy_to_product_rank_bridge_false
#print axioms GodMoveLocalEnergyRankObstruction.energyWithOutput_rank_zero
#print axioms GodMoveLocalEnergyRankObstruction.energyWithOutput_to_product_rank_bridge_false
