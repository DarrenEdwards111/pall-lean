import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMinimality

/-!
# Rigidity ⇒ circuit lower bound (Valiant's direction)

The payoff of the rigidity identification: a rigid matrix requires a large circuit.  Every realization
`M = C + L` of a rigid `M` must exceed the rigidity parameters in one axis — a size/rank trade-off —
and, translated through the gate correspondence, forces the middle-gate (`coneInter`) count above the
rank threshold.

* `rigid_circuit_tradeoff` — if `M` is `(r,s)`-rigid, every decomposition `M = C + L` has
  `sparsity C > s` **or** `rank L > r`: no realization is simultaneously `s`-sparse and rank-`≤ r`.
* `rigid_gates_lower_bound` — hence in any circuit realization `M = C + A·B` with `C` `s`-sparse, the
  shared middle-gate count `k` satisfies `r < k`: a rigid matrix forces `> r` middle gates once the
  sparse budget is `≤ s`.

So rigidity ⇒ a genuine circuit lower bound: `> s` sparse gates or `> r` middle gates.  This is
Valiant's rigidity ⇒ lower-bound direction, at the sparse-plus-low-rank circuit level that the
N-Frame `coneInter`/mixer decomposition uses.

## Honest scope

This gives the lower bound *against sparse + low-rank realizations* (the decomposition the residual is
about).  Valiant's full theorem also has the *other* half — that a genuine size-`s`, log-depth *linear
circuit* can be reduced to a sparse + low-rank form (the gate-removal argument) — which would upgrade
this to a lower bound against arbitrary log-depth linear circuits.  That classical reduction needs the
linear-circuit model and is **not** built here.  And rigidity itself remains the open, P≠NP-strength
input: this is the consequence *of* rigidity, not a proof of it.

Nothing here proves `P ≠ NP`, resolves rigidity, discharges the capture, or is `NEXP ⊄ ACC⁰`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity

variable {n k : ℕ} {F : Type*} [Field F]

/-- **Rigidity ⇒ size/rank trade-off.**  If `M` is `(r,s)`-rigid, no decomposition `M = C + L` is both
`s`-sparse in `C` and rank-`≤ r` in `L`: one of `sparsity C > s`, `rank L > r` must hold. -/
theorem rigid_circuit_tradeoff (M C L : Matrix (Fin n) (Fin n) F) (r s : ℕ)
    (hrigid : MatrixRigid M r s) (hM : M = C + L) :
    s < sparsity C ∨ r < L.rank := by
  by_contra hcon
  push_neg at hcon
  have hrank : (M - C).rank ≤ r := by rw [hM, add_sub_cancel_left]; exact hcon.2
  exact absurd (hrigid C hcon.1) (not_lt.mpr hrank)

/-- **Rigidity ⇒ middle-gate lower bound.**  In any circuit realization `M = C + A·B` of a rigid `M`
with `C` `s`-sparse, the shared middle-gate count `k` exceeds the rigidity rank `r`. -/
theorem rigid_gates_lower_bound (M C : Matrix (Fin n) (Fin n) F)
    (A : Matrix (Fin n) (Fin k) F) (B : Matrix (Fin k) (Fin n) F) (r s : ℕ)
    (hrigid : MatrixRigid M r s) (hM : M = C + A * B) (hs : sparsity C ≤ s) :
    r < k := by
  rcases rigid_circuit_tradeoff M C (A * B) r s hrigid hM with h | h
  · exact absurd hs (not_le.mpr h)
  · exact lt_of_lt_of_le h (rank_le_inner_dim A B)

end PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity
