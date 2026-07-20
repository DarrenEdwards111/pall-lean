import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameLabelFirstPassage

/-!
# `rank ≤ sparsity`, the concrete edge-count bound, and the only rigidity we can prove

Two loose ends, treated honestly.

**The plumbing.**  `rank_le_sparsity`: `M.rank ≤ sparsity M` (a matrix's rank is at most its number of
nonzero entries), assembled from `M = ∑ single i j (M i j)`, rank subadditivity, and
`rank (single _ _ c) ≤ 1`.  This is pure Mathlib plumbing, not new mathematics.

**Item 1 — the `s/log d` bound made concrete.**  `highPart_rank_le_edges`: the first-passage long part
`pathMatrix · highMask j · lowPath j` has rank `≤ sparsity (highMask j)` — the **number of label-`> j`
edges**.  So the label first-passage gives `rank L ≤ #{label > j edges}` outright; the remaining
"`s / log d`" is the numeric choice of `j` trading this edge count against the sparse reach `2^j`, which
depends on the circuit's edge distribution.

**Item 2 — rigidity itself.**  `identity_rigid`: the identity matrix is `(r,s)`-rigid whenever
`s + r < n`.  This is the **trivial universal bound** `R(r) ≥ n − r` that *every* full-rank matrix
satisfies (change `< n − r` entries and rank stays `> r`).  It is the *only* rigidity provable
unconditionally, and it is far below what circuit lower bounds require — those need a *superlinear*
sparsity budget at rank `≈ εn`, which is the famous open problem.  Proving an explicit matrix rigid at
those parameters would be a `P ≠ NP`-strength result; it is **not** proved here, and cannot honestly be.

Nothing here proves `P ≠ NP`, resolves rigidity, discharges the capture, or is `NEXP ⊄ ACC⁰`.
-/

open Matrix
open scoped Classical

namespace PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity

variable {N : ℕ} {F : Type*} [Field F]

/-- Rank is subadditive: `rank (A + B) ≤ rank A + rank B`. -/
theorem rank_add_le (A B : Matrix (Fin N) (Fin N) F) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact le_trans (Submodule.finrank_mono (LinearMap.range_add_le _ _))
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- Rank is subadditive over a finite sum. -/
theorem rank_sum_le {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin N) (Fin N) F) :
    (∑ i ∈ s, f i).rank ≤ ∑ i ∈ s, (f i).rank := by
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    exact le_trans (rank_add_le _ _) (Nat.add_le_add_left ih _)

/-- A single-entry matrix has rank `≤ 1` (and `0` when the entry is `0`). -/
theorem rank_single_le (i j : Fin N) (c : F) :
    (Matrix.single i j c).rank ≤ if c = 0 then 0 else 1 := by
  by_cases hc : c = 0
  · subst hc; simp
  · rw [if_neg hc]
    have heq : Matrix.single i j c = Matrix.vecMulVec (Pi.single i c) (Pi.single j 1) := by
      ext k l
      simp only [Matrix.single, Matrix.of_apply, Matrix.vecMulVec_apply, Pi.single_apply]
      by_cases hk : k = i <;> by_cases hl : l = j <;> simp [hk, hl] <;> aesop
    rw [heq]; exact Matrix.rank_vecMulVec_le _ _

/-- **Rank is at most the number of nonzero entries.**  `M.rank ≤ sparsity M`. -/
theorem rank_le_sparsity (M : Matrix (Fin N) (Fin N) F) : M.rank ≤ sparsity M := by
  calc M.rank = (∑ i : Fin N, ∑ j : Fin N, Matrix.single i j (M i j)).rank := by
              rw [← Matrix.matrix_eq_sum_single]
    _ ≤ ∑ i : Fin N, (∑ j : Fin N, Matrix.single i j (M i j)).rank := rank_sum_le _ _
    _ ≤ ∑ i : Fin N, ∑ j : Fin N, (Matrix.single i j (M i j)).rank :=
              Finset.sum_le_sum (fun i _ => rank_sum_le _ _)
    _ ≤ ∑ i : Fin N, ∑ j : Fin N, (if M i j = 0 then 0 else 1) :=
              Finset.sum_le_sum (fun i _ =>
                Finset.sum_le_sum (fun j _ => rank_single_le i j (M i j)))
    _ = sparsity M := by
              rw [sparsity, Finset.card_filter, Fintype.sum_prod_type]
              apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
              by_cases h : M i j = 0 <;> simp [h]

/-- **The identity matrix is rigid — the trivial universal bound.**  `1` is `(r,s)`-rigid whenever
`s + r < n`: changing fewer than `n − r` entries leaves rank `> r`.  This is the rigidity that *every*
full-rank matrix has, and is far weaker than what circuit lower bounds need. -/
theorem identity_rigid {r s : ℕ} (h : s + r < N) :
    MatrixRigid (1 : Matrix (Fin N) (Fin N) F) r s := by
  intro C hC
  have hrankC : C.rank ≤ s := le_trans (rank_le_sparsity C) hC
  have hone : (1 : Matrix (Fin N) (Fin N) F).rank = N := by
    rw [Matrix.rank_one, Fintype.card_fin]
  have hsub : (1 : Matrix (Fin N) (Fin N) F).rank
      ≤ ((1 : Matrix (Fin N) (Fin N) F) - C).rank + C.rank := by
    calc (1 : Matrix (Fin N) (Fin N) F).rank
        = ((1 - C) + C).rank := by rw [sub_add_cancel]
      _ ≤ (1 - C).rank + C.rank := rank_add_le _ _
  rw [hone] at hsub
  omega

namespace LinCircuit

variable (G : LinCircuit F N)

/-- **Item 1, concrete.**  The label first-passage long part has rank at most the number of label-`> j`
edges: `rank (pathMatrix · highMask j · lowPath j) ≤ sparsity (highMask j)`. -/
theorem highPart_rank_le_edges (j : ℕ) :
    (G.pathMatrix * G.highMask j * G.lowPath j).rank ≤ sparsity (G.highMask j) :=
  (G.highPart_rank_le j).trans (rank_le_sparsity _)

end LinCircuit

end PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity
