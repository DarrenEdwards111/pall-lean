import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTensorEntanglementLowerBound

/-!
# Fixed-ordering MPS cost lower bound

The bond-dimension lower bounds (`TensorEntanglementLowerBound`) become **representation-cost** lower bounds via
the standard fact that a matrix-product state's bond dimension at a cut equals its Schmidt rank there.  An MPS
`f(x) = vᵀ · A₁(x₁) ⋯ Aₙ(xₙ) · w` (bond `χ`, sites read in order) factors at every **prefix** cut into a bond-`χ`
`TensorFactorization`, so `finrank_residualSpan_le_bond` gives `χ ≥` the cross-cut rank at that cut.

* `mpsTF` — an MPS induces a `TensorFactorization` at each prefix cut, via matrix-product splitting
  (`List.take_append_drop`, `List.prod_append`, `Matrix.vecMul_vecMul`, `Matrix.dotProduct_mulVec`);
* `mps_bond_ge_rank` — hence bond `χ ≥` residual-span rank at the prefix cut;
* `mps_cost_ge_rank` — the parameter count `2·N·χ²` is `≥` the rank (bond) as well.

The deep content (`bond ≥ rank`) is already proved; this file is the framing layer that packages it into the
tensor-network cost language.

## Honest scope

A **fixed-ordering** result: the block must be read as a contiguous prefix (the same contiguity restriction as the
branching-program width bound).  The *min over orderings* collapses (equality has an `O(1)`-bond MPS with its pairs
adjacent), so this is a restricted lower bound, not a separation.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MPSCost

open PallLean.Paper93.DeepMath.PathB.TensorEntanglement
open Matrix

variable {K : Type*} [Field K] {N χ : ℕ}

/-- A **matrix-product state** of bond dimension `χ` on `N` sites: a per-site tensor and boundary vectors. -/
structure MPS (N χ : ℕ) (K : Type*) [Field K] where
  /-- Per-site tensors. -/
  A : Fin N → Bool → Matrix (Fin χ) (Fin χ) K
  /-- Left boundary. -/
  v : Fin χ → K
  /-- Right boundary. -/
  w : Fin χ → K

/-- The matrix product over a list of sites. -/
def prodOver (M : MPS N χ K) (x : Fin N → Bool) (L : List (Fin N)) : Matrix (Fin χ) (Fin χ) K :=
  (L.map (fun i => M.A i (x i))).prod

/-- The function computed by the MPS. -/
def MPS.eval (M : MPS N χ K) (x : Fin N → Bool) : K :=
  (M.v ᵥ* prodOver M x (List.finRange N)) ⬝ᵥ M.w

theorem prodOver_append (M : MPS N χ K) (x : Fin N → Bool) (L1 L2 : List (Fin N)) :
    prodOver M x (L1 ++ L2) = prodOver M x L1 * prodOver M x L2 := by
  simp only [prodOver, List.map_append, List.prod_append]

theorem prodOver_congr (M : MPS N χ K) (x y : Fin N → Bool) (L : List (Fin N))
    (h : ∀ i ∈ L, x i = y i) : prodOver M x L = prodOver M y L := by
  simp only [prodOver]
  exact congrArg List.prod (List.map_congr_left (fun i hi => by rw [h i hi]))

/-- The prefix block at cut `j`: the first `j` sites. -/
def cutBlock (N j : ℕ) : Finset (Fin N) := (List.take j (List.finRange N)).toFinset

/-- **An MPS induces a bond-`χ` tensor factorization at each prefix cut.** -/
noncomputable def mpsTF (M : MPS N χ K) (j : ℕ) : TensorFactorization (cutBlock N j) M.eval χ where
  left a x := (M.v ᵥ* prodOver M x (List.take j (List.finRange N))) a
  right a x := (prodOver M x (List.drop j (List.finRange N)) *ᵥ M.w) a
  left_indep a x y h := by
    show (M.v ᵥ* prodOver M x (List.take j (List.finRange N))) a
       = (M.v ᵥ* prodOver M y (List.take j (List.finRange N))) a
    rw [prodOver_congr M x y _ (fun i hi => h i (List.mem_toFinset.mpr hi))]
  right_indep a x y h := by
    show (prodOver M x (List.drop j (List.finRange N)) *ᵥ M.w) a
       = (prodOver M y (List.drop j (List.finRange N)) *ᵥ M.w) a
    rw [prodOver_congr M x y _ (fun i hi => h i (fun hc =>
      List.disjoint_take_drop (List.nodup_finRange N) (le_refl j) (List.mem_toFinset.mp hc) hi))]
  factors x := by
    show (M.v ᵥ* prodOver M x (List.finRange N)) ⬝ᵥ M.w = _
    conv_lhs => rw [show List.finRange N
          = List.take j (List.finRange N) ++ List.drop j (List.finRange N) from
        (List.take_append_drop j _).symm, prodOver_append]
    rw [← Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec]
    rfl

/-- **Bond dimension lower-bounds the prefix cross-cut rank.**  Any bond-`χ` MPS computing `f` has
`χ ≥` the residual-span dimension at each prefix cut. -/
theorem mps_bond_ge_rank (M : MPS N χ K) (j : ℕ) :
    Module.finrank K (Submodule.span K (Set.range (residualOf (cutBlock N j) M.eval))) ≤ χ :=
  finrank_residualSpan_le_bond (mpsTF M j)

/-- The MPS parameter count: `2·N·χ²` tensor entries. -/
def MPS.cost (_M : MPS N χ K) : ℕ := 2 * N * χ ^ 2

/-- **Cost lower bound.**  For `N ≥ 1`, the MPS parameter count is at least the prefix cross-cut rank. -/
theorem mps_cost_ge_rank (M : MPS N χ K) (j : ℕ) (hN : 1 ≤ N) :
    Module.finrank K (Submodule.span K (Set.range (residualOf (cutBlock N j) M.eval))) ≤ M.cost := by
  have hbond := mps_bond_ge_rank M j
  have hle : χ ≤ M.cost := by
    unfold MPS.cost
    rcases Nat.eq_zero_or_pos χ with h | h
    · simp [h]
    · nlinarith [hN, h]
  omega

end PallLean.Paper93.DeepMath.PathB.MPSCost

#print axioms PallLean.Paper93.DeepMath.PathB.MPSCost.mps_bond_ge_rank
#print axioms PallLean.Paper93.DeepMath.PathB.MPSCost.mps_cost_ge_rank
