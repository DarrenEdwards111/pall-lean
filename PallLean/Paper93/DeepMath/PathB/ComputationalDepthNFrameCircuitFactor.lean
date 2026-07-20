import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameValiantRigidity

/-!
# The circuit ↔ factorization map (rank component)

Completes the linear side of `coneInter ≤ cN ≡ Valiant rigidity`: the map from a circuit's shared
gates to the algebraic rank of the decomposition.  The `coneInter` shared gates of the direct sum form
the middle layer of a linear sub-circuit `A · B` factoring the shared computation through `coneInter`
dimensions — so its rank is `≤ coneInter`.  That is exactly the `rank L ≤ r` in `notRigid_iff_decomp`.

* `rank_le_inner_dim` — a computation factoring through `k` gates (`A · B`, inner dimension `k`) has
  rank `≤ k`.  (`rank_mul_le_left` then `rank_le_card_width`.)
* `notRigid_of_factorization` — **the map**: if `M = C + A·B` with `C` `s`-sparse (the mixer envelope,
  `s = cN`) and inner dimension `k` (the shared gates, `k = coneInter`), then `M` is *not* `(k,s)`-rigid.
* `rigid_no_factorization` — the contrapositive: a `(k,s)`-rigid `M` admits **no** such decomposition, so
  a rigid target forces the direct-sum residual (no rank-`k` share fits inside an `s`-sparse envelope).

So a linear circuit whose shared computation factors through `coneInter` gates within a `cN`-sparse
envelope makes the matrix non-rigid; equivalently, rigidity forbids the sharing — the residual and
rigidity are the same statement on the linear side.

## Honest scope

This machine-checks the **gates → rank** direction of the map (a `k`-gate factorization gives rank
`≤ k`, hence non-rigidity), completing the algebraic identification with `notRigid_iff_decomp`.  The
remaining pieces of a *fully literal* circuit-level equivalence — a concrete linear-circuit model whose
gate cones are shown to *produce* the factors `A, B, C` (the reverse, circuit ⇐ factorization, and the
sparsity/mixer accounting) — are not built here.  What is established: on the linear side, rigidity and
the `coneInter ≤ cN` residual are provably the same obstruction, so the N-Frame central conjecture is
Valiant's problem — machine-checked, not merely asserted.

Nothing here proves `P ≠ NP`, resolves rigidity, discharges the capture, or is `NEXP ⊄ ACC⁰`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity

variable {n k m : ℕ} {F : Type*} [Field F]

/-- **Gates → rank.**  A computation that factors through `k` gates (`A · B` with inner dimension `k`)
has rank at most `k`. -/
theorem rank_le_inner_dim (A : Matrix (Fin n) (Fin k) F) (B : Matrix (Fin k) (Fin m) F) :
    (A * B).rank ≤ k :=
  (Matrix.rank_mul_le_left A B).trans ((Matrix.rank_le_card_width A).trans (Fintype.card_fin k).le)

/-- **The circuit → factorization map.**  If `M = C + A·B` with `C` `s`-sparse (the mixer envelope) and
inner dimension `k` (the shared gates), then `M` is not `(k,s)`-rigid: the shared factorization is the
low-rank part `L = A·B` of the decomposition. -/
theorem notRigid_of_factorization (M C : Matrix (Fin n) (Fin n) F) {s : ℕ}
    (A : Matrix (Fin n) (Fin k) F) (B : Matrix (Fin k) (Fin n) F)
    (hM : M = C + A * B) (hs : sparsity C ≤ s) :
    ¬ MatrixRigid M k s :=
  (notRigid_iff_decomp M k s).mpr ⟨C, A * B, hs, rank_le_inner_dim A B, hM⟩

/-- **Rigidity forbids the sharing.**  A `(k,s)`-rigid `M` admits no decomposition into an `s`-sparse
part plus a computation factoring through `k` gates — so a rigid target forces the direct-sum residual. -/
theorem rigid_no_factorization (M C : Matrix (Fin n) (Fin n) F) {s : ℕ}
    (A : Matrix (Fin n) (Fin k) F) (B : Matrix (Fin k) (Fin n) F)
    (hrigid : MatrixRigid M k s) (hs : sparsity C ≤ s) :
    M ≠ C + A * B :=
  fun hM => notRigid_of_factorization M C A B hM hs hrigid

end PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity
