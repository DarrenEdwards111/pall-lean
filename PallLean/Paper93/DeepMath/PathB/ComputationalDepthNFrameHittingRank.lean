import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCoveringLemma

/-!
# Hitting-set / rank assembly: the sparse + low-rank split

The final structural step of Valiant's reduction on the DAG model.  We split the path matrix by walk
length at a threshold `p`:

* `shortPart p = ∑_{k<p} W^k` — contributions of **short** walks (length `< p`);
* `longPart p  = ∑_{p≤k≤maxLvl} W^k` — contributions of **long** walks (length `≥ p`).

`pathMatrix = shortPart p + longPart p` (`pathMatrix_split`).  This is the `M = C + L` shape:

* the short part is **sparse-supported** — a nonzero entry needs an actual short walk
  (`shortPart_support`), so for a bounded-degree circuit few entries survive;
* the long part is **low rank** — `longPart p = W^p · (tail)` factors out `W^p`, so
  `rank (longPart p) ≤ rank (W^p)` *unconditionally* (`longPart_rank_le`).

A hitting set enters only to bound `rank (W^p)` further: if the length-`p` walk matrix `W^p` factors
through `r` shared vertices (`CircuitFactorsAt (W^p) r` — the covering lemma's output), then
`rank (longPart p) ≤ r` (`longPart_rank_le_of_factor`).  `pathMatrix_sparse_lowrank_split` packages the
whole `M = C + L` with the sparse-support and low-rank guarantees.

`rank_mul_mul_le_mid` is the reusable rank mechanism `rank (A·M·B) ≤ rank M` behind "a computation that
routes through `M` is no higher rank than `M`" — the crossing-block form of the same idea.

## Honest scope

Unconditional here: the split, the short part's sparse support, and `rank (longPart) ≤ rank (W^p)`.
The one hypothesis on the low-rank side — `CircuitFactorsAt (W^p) r` — is *exactly* the hitting-set
factorization the covering lemma is meant to produce, with `r ≈ s / log d`.  Discharging it
quantitatively (the pigeonhole over the `O(log d)` shallow classes of `valiant_covering_labeling`, and
the matching sparsity count for the short part) is the remaining step, **not** built here.  Rigidity
itself stays the open, P≠NP-strength input.

Nothing here proves `P ≠ NP`, resolves rigidity, discharges the capture, or is `NEXP ⊄ ACC⁰`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity

namespace LinCircuit

variable {F : Type*} [Field F] {N : ℕ}

/-- **Rank routes through the middle.**  A triple product `A·M·B` has rank at most `rank M`: routing a
computation through `M` cannot raise the rank above `M`'s.  (Crossing-block form: `rank (P_H·W_cross·P_L)
≤ rank W_cross`.) -/
theorem rank_mul_mul_le_mid {a b c d : ℕ} (A : Matrix (Fin a) (Fin b) F)
    (M : Matrix (Fin b) (Fin c) F) (B : Matrix (Fin c) (Fin d) F) :
    (A * M * B).rank ≤ M.rank :=
  (Matrix.rank_mul_le_left (A * M) B).trans (Matrix.rank_mul_le_right A M)

variable (G : LinCircuit F N)

/-- The **short-walk part** of the path matrix: walks of length `< p`. -/
def shortPart (p : ℕ) : Matrix (Fin N) (Fin N) F :=
  ∑ k ∈ Finset.range p, G.W ^ k

/-- The **long-walk part** of the path matrix: walks of length `≥ p` (up to the depth `maxLvl`). -/
def longPart (p : ℕ) : Matrix (Fin N) (Fin N) F :=
  ∑ k ∈ Finset.Ico p (G.maxLvl + 1), G.W ^ k

/-- **The split.**  For `p ≤ maxLvl + 1`, the path matrix is short part plus long part — the `M = C + L`
shape. -/
theorem pathMatrix_split (p : ℕ) (hp : p ≤ G.maxLvl + 1) :
    G.pathMatrix = G.shortPart p + G.longPart p := by
  unfold pathMatrix shortPart longPart
  rw [Finset.sum_range_add_sum_Ico _ hp]

/-- **The short part is sparse-supported.**  A nonzero entry of `shortPart p` requires an actual walk of
length `< p` between the two vertices. -/
theorem shortPart_support (p : ℕ) {u v : Fin N} (h : (G.shortPart p) u v ≠ 0) :
    ∃ k ∈ Finset.range p, (G.W ^ k) u v ≠ 0 := by
  unfold shortPart at h
  rw [Matrix.sum_apply] at h
  exact Finset.exists_ne_zero_of_sum_ne_zero h

/-- **The long part factors out `W^p`.**  `longPart p = W^p · (∑_{j<maxLvl+1-p} W^j)`. -/
theorem longPart_factor (p : ℕ) :
    G.longPart p = G.W ^ p * ∑ j ∈ Finset.range (G.maxLvl + 1 - p), G.W ^ j := by
  unfold longPart
  rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]

/-- **The long part is low rank (unconditional).**  `rank (longPart p) ≤ rank (W^p)`: the length-`≥ p`
walk contribution has rank at most that of the length-exactly-`p` walk matrix. -/
theorem longPart_rank_le (p : ℕ) : (G.longPart p).rank ≤ (G.W ^ p).rank := by
  rw [longPart_factor]
  exact Matrix.rank_mul_le_left _ _

/-- **Hitting set ⇒ low rank.**  If the length-`p` walk matrix `W^p` factors through `r` shared
vertices, the long part has rank `≤ r`. -/
theorem longPart_rank_le_of_factor (p r : ℕ) (h : CircuitFactorsAt (G.W ^ p) r) :
    (G.longPart p).rank ≤ r :=
  (G.longPart_rank_le p).trans (circuit_rank_le_width _ h)

/-- **The sparse + low-rank split.**  `pathMatrix = shortPart + longPart`, the short part sparse-
supported, and — given a hitting-set factorization of `W^p` through `r` vertices — the long part of rank
`≤ r`.  This is Valiant's `M = C + L` assembled on the DAG model, modulo the quantitative pigeonhole
that produces the factorization with `r ≈ s / log d`. -/
theorem pathMatrix_sparse_lowrank_split (p r : ℕ) (hp : p ≤ G.maxLvl + 1)
    (hfac : CircuitFactorsAt (G.W ^ p) r) :
    G.pathMatrix = G.shortPart p + G.longPart p ∧
      (∀ u v, (G.shortPart p) u v ≠ 0 → ∃ k ∈ Finset.range p, (G.W ^ k) u v ≠ 0) ∧
      (G.longPart p).rank ≤ r :=
  ⟨G.pathMatrix_split p hp, fun _ _ h => G.shortPart_support p h,
    G.longPart_rank_le_of_factor p r hfac⟩

end LinCircuit

end PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity
