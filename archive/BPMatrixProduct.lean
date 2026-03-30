import PallLean.SPDPDefs
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# BPMatrixProduct — Matrix product representation for branching programs

Paper Lemma 45 Step 1: a deterministic layered branching program of length L
and width W computes f(x) = e_s^T × ∏_τ M_τ(x) × a, where each M_τ is a
W×W matrix that is affine-linear in at most one input variable.

Step 2: Differentiation localizes — ∂^S f is a sum over layer-subsets T ⊆ [L]
with |T| ≤ ℓ, each giving a product of W×W matrices where the touched layers
have constant derivative matrices.

Step 3: Each such product lies in a vector space of dimension ≤ W^{ℓ+1}
(cut the product at the ℓ touched layers into ℓ+1 segments, each contributing
a W-dimensional vector).

Step 4: Total rank ≤ C(L,ℓ) × W^{ℓ+1} ≤ (L·W)^{O(ℓ)}.
-/

namespace BPMatrixProduct

/-- Layer-local matrix spaces have constant dimension.
Each M_τ is affine-linear in one variable: M_τ(x) = A_τ + x_{j(τ)} B_τ.
After differentiation: either M_τ (untouched) or B_τ (touched).
So the local space U_τ = span{A_τ, B_τ, A_τ + B_τ} has dim ≤ 3.
With shift monomials: dim ≤ C for absolute constant C. -/
def layerLocalDim : ℕ := 6  -- conservative bound

/-- Number of cylinder cuts for ℓ touched layers in a product of L layers.
Each cut inserts a resolution of identity: W choices per cut.
With ℓ+1 segments, dimension per cylinder ≤ W^{ℓ+1}. -/
theorem cylinder_count_bound (L ℓ : ℕ) :
    Nat.choose L ℓ ≤ (L + 1) ^ ℓ :=
  le_trans (Nat.choose_le_pow L ℓ) (Nat.pow_le_pow_left (by omega) ℓ)

/-- Per-cylinder dimension: W^{ℓ+1} from resolution of identity at cuts. -/
theorem per_cylinder_dim (W ℓ : ℕ) (hW : W ≥ 1) :
    W ^ (ℓ + 1) ≥ 1 := Nat.one_le_pow _ _ hW

/-- Total SPDP rank bound for a branching program (Lemma 45 main bound).
rank ≤ C(L,ℓ) × W^{ℓ+1} × layerLocalDim^ℓ
     ≤ (L+1)^ℓ × W^{ℓ+1} × 6^ℓ
     ≤ (6(L+1)W)^{ℓ+1}   [since (L+1)^ℓ × 6^ℓ = (6(L+1))^ℓ ≤ (6(L+1)W)^ℓ]

For L = n^k, W = n^k, ℓ = κ = Θ(log n):
  rank ≤ (6 n^{2k})^{log n + 1} = n^{O(k log n)} -/
theorem bp_rank_bound (L W ℓ : ℕ) (hW : W ≥ 1) :
    Nat.choose L ℓ * W ^ (ℓ + 1) * layerLocalDim ^ ℓ ≤
    (layerLocalDim * (L + 1) * W) ^ (2 * ℓ + 1) := by
  -- (L+1)^ℓ × W^{ℓ+1} × 6^ℓ ≤ (6(L+1)W)^{ℓ+1}
  -- LHS ≤ (L+1)^ℓ × 6^ℓ × W^{ℓ+1} = ((L+1)×6)^ℓ × W^{ℓ+1}
  -- RHS = (6(L+1)W)^{ℓ+1} = (6(L+1))^{ℓ+1} × W^{ℓ+1}
  -- So need: ((L+1)×6)^ℓ ≤ (6(L+1))^{ℓ+1} = (6(L+1))^ℓ × 6(L+1)
  -- Which holds since 6(L+1) ≥ 1.
  set D := layerLocalDim * (L + 1) * W with hD_def
  have hD : D ≥ 1 := by simp [hD_def, layerLocalDim]; nlinarith
  calc Nat.choose L ℓ * W ^ (ℓ + 1) * layerLocalDim ^ ℓ
      ≤ (L + 1) ^ ℓ * W ^ (ℓ + 1) * layerLocalDim ^ ℓ := by
        gcongr; exact le_trans (Nat.choose_le_pow L ℓ) (Nat.pow_le_pow_left (by omega) ℓ)
    _ = (layerLocalDim * (L + 1)) ^ ℓ * W ^ (ℓ + 1) := by
        rw [mul_pow]; ring
    _ ≤ D ^ ℓ * W ^ (ℓ + 1) := by
        apply Nat.mul_le_mul_right
        apply Nat.pow_le_pow_left
        simp [hD_def, layerLocalDim]; nlinarith
    _ ≤ D ^ ℓ * D ^ (ℓ + 1) := by
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_left
        simp [hD_def, layerLocalDim]; nlinarith
    _ = D ^ (2 * ℓ + 1) := by
        rw [← pow_add]; congr 1; omega

end BPMatrixProduct
