import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMPSCostLowerBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGlobalBestPartitionBond

/-!
# Global entanglement witness: bond and cost under EVERY ordering

The consequence of `exists_global_best_partition_bond`: the single function `QF A` has high tensor bond — and
exponential representation cost — under **every** variable ordering, because every ordering's first `h` variables
form a balanced cut, which is a balanced partition covered by the global bond.

* `evalOrd M L` — an MPS reading its sites in the arbitrary order `L`;
* `oms_bond_ge_rank` / `oms_cost_ge_rank` — bond `χ` (resp. cost) `≥` the Schmidt rank at the prefix cut
  `(take j L).toFinset` (the ordered generalization of `MPSCost.mps_bond_ge_rank`);
* `QF_ordered_bond` — **one function `QF A` such that every MPS computing it in any order has bond `≥ 2^r`**;
* `QF_ordered_cost` — **and cost `≥ 2^r = 2^{Ω(n)}`**: an all-order exponential representation-cost lower bound.

Existential (a random matrix); explicit is Valiant-open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.OrderedMPS

open Matrix
open PallLean.Paper93.DeepMath.PathB.MPSCost
open PallLean.Paper93.DeepMath.PathB.TensorEntanglement
open PallLean.Paper93.DeepMath.PathB.GlobalResidual
open PallLean.Paper93.DeepMath.PathB.GlobalBestPartitionBond

variable {K : Type*} [Field K] {N χ : ℕ}

/-- An MPS reading its sites in the order given by the list `L`. -/
def evalOrd (M : MPS N χ K) (L : List (Fin N)) (x : Fin N → Bool) : K :=
  (M.v ᵥ* prodOver M x L) ⬝ᵥ M.w

/-- The ordered MPS induces a bond-`χ` tensor factorization at each prefix of `L` (for `L` nodup). -/
noncomputable def omsTF (M : MPS N χ K) (L : List (Fin N)) (hL : L.Nodup) (j : ℕ) :
    TensorFactorization (List.take j L).toFinset (evalOrd M L) χ where
  left a x := (M.v ᵥ* prodOver M x (List.take j L)) a
  right a x := (prodOver M x (List.drop j L) *ᵥ M.w) a
  left_indep a x y h := by
    show (M.v ᵥ* prodOver M x (List.take j L)) a = (M.v ᵥ* prodOver M y (List.take j L)) a
    rw [prodOver_congr M x y _ (fun i hi => h i (List.mem_toFinset.mpr hi))]
  right_indep a x y h := by
    show (prodOver M x (List.drop j L) *ᵥ M.w) a = (prodOver M y (List.drop j L) *ᵥ M.w) a
    rw [prodOver_congr M x y _ (fun i hi => h i (fun hc =>
      List.disjoint_take_drop hL (le_refl j) (List.mem_toFinset.mp hc) hi))]
  factors x := by
    show (M.v ᵥ* prodOver M x L) ⬝ᵥ M.w = _
    conv_lhs => rw [show L = List.take j L ++ List.drop j L from (List.take_append_drop j L).symm,
      prodOver_append]
    rw [← Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec]
    rfl

/-- **Bond ≥ Schmidt rank at any prefix cut of any ordering.** -/
theorem oms_bond_ge_rank (M : MPS N χ K) (L : List (Fin N)) (hL : L.Nodup) (j : ℕ) :
    Module.finrank K
        (Submodule.span K (Set.range (residualOf (List.take j L).toFinset (evalOrd M L)))) ≤ χ :=
  finrank_residualSpan_le_bond (omsTF M L hL j)

/-- **Cost ≥ Schmidt rank at any prefix cut of any ordering.** -/
theorem oms_cost_ge_rank (M : MPS N χ K) (L : List (Fin N)) (hL : L.Nodup) (j : ℕ) (hN : 1 ≤ N) :
    Module.finrank K
        (Submodule.span K (Set.range (residualOf (List.take j L).toFinset (evalOrd M L)))) ≤ M.cost := by
  have hbond := oms_bond_ge_rank M L hL j
  have hle : χ ≤ M.cost := by
    unfold MPS.cost
    rcases Nat.eq_zero_or_pos χ with h | h
    · simp [h]
    · nlinarith [hN, h]
  omega

/-! ## Steps (2) and (3): applied to the global witness `QF A` -/

variable [CharZero K] {h r : ℕ}

theorem take_h_card (L : List (Fin (2 * h))) (hL : L.Nodup) (hLlen : h ≤ L.length) :
    (List.take h L).toFinset.card = h := by
  rw [List.toFinset_card_of_nodup (hL.sublist (List.take_sublist _ _)), List.length_take]
  omega

/-- **Step (2). One function, high bond under every ordering.**  For `4r + 2 < h`, there is an `A` such that every
MPS computing `QF A` in **any** order `L` has bond `χ ≥ 2^r`. -/
theorem QF_ordered_bond (hh : 4 * r + 2 < h) :
    ∃ A : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2),
      ∀ (χ : ℕ) (M : MPS (2 * h) χ K) (L : List (Fin (2 * h))),
        L.Nodup → h ≤ L.length → evalOrd M L = QF (K := K) A → 2 ^ r ≤ χ := by
  obtain ⟨A, hA⟩ := exists_global_best_partition_bond (K := K) hh
  refine ⟨A, fun χ M L hL hLlen hM => ?_⟩
  have hbond := oms_bond_ge_rank M L hL h
  rw [hM] at hbond
  exact le_trans (hA (List.take h L).toFinset (take_h_card L hL hLlen)) hbond

/-- **Step (3). All-order exponential representation cost.**  For `4r + 2 < h`, there is an `A` such that every MPS
computing `QF A` in **any** order has cost `≥ 2^r = 2^{Ω(n)}`. -/
theorem QF_ordered_cost (hh : 4 * r + 2 < h) :
    ∃ A : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2),
      ∀ (χ : ℕ) (M : MPS (2 * h) χ K) (L : List (Fin (2 * h))),
        L.Nodup → h ≤ L.length → evalOrd M L = QF (K := K) A → 2 ^ r ≤ M.cost := by
  obtain ⟨A, hA⟩ := exists_global_best_partition_bond (K := K) hh
  refine ⟨A, fun χ M L hL hLlen hM => ?_⟩
  have hcost := oms_cost_ge_rank M L hL h (by omega)
  rw [hM] at hcost
  exact le_trans (hA (List.take h L).toFinset (take_h_card L hL hLlen)) hcost

end PallLean.Paper93.DeepMath.PathB.OrderedMPS

#print axioms PallLean.Paper93.DeepMath.PathB.OrderedMPS.QF_ordered_bond
#print axioms PallLean.Paper93.DeepMath.PathB.OrderedMPS.QF_ordered_cost
