import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameQuadForm

/-!
# N-Frame: cut-rigidity — the polarization is governed by `A + Aᵀ` (the design correction)

Pinning down the explicit `A` for the flat quadratic form `qform` forced a correction to the
design.  The detectable directions of `qform A` are the row space of `A + Aᵀ` (proved below),
so:

  `bilinSym_eq` — **PROVED**: `bilinSym A x δ = ∑_{i,j} (A_{ij} + A_{ji})·x_i·δ_j = xᵀ(A+Aᵀ)δ`.
        The polarization is the bilinear form of the SYMMETRIZED matrix.
  `bilinSym_symm_zero` — **PROVED, THE CORRECTION**: if `A` is SYMMETRIC (`A_{ij} = A_{ji}` —
        an undirected graph adjacency), then `bilinSym A ≡ 0`.  Over `F₂`, `x^T A x` for
        symmetric `A` is LINEAR (its diagonal), so an undirected-graph `A` gives a DEGENERATE
        `qform` with no detection.

Consequence: `A` must be an ORIENTATION (e.g. the strictly-upper-triangular part of a graph),
and the cut-rank of `qform A` across `(S, Sᶜ)` is `rank_{F₂}(M_{S,Sᶜ})` where `M = A + Aᵀ` is
the underlying UNDIRECTED graph's adjacency.  The cut-rigidity requirement is on `M`:
`rank_{F₂}(M_{S,Sᶜ}) = Θ(N)` for every balanced `S`.

## Honest scope — the explicit `A` is the rigidity frontier (NOT pinned down)

With the correction, "explicit cut-rigid `A`" becomes: an explicit symmetric `M` (an undirected
graph) with `rank_{F₂}(M_{S,Sᶜ}) = Θ(N)` at EVERY balanced cut `(S, Sᶜ)`.  This is exactly the
`F₂`-rank version of matrix rigidity / high rank-width-everywhere.  HONEST STATUS:

- **Random / ε-biased `M` works** (whp / by the pseudorandom rank property), but is not a
  PROVEN explicit construction of the every-cut bound.
- **Spectral expanders do NOT suffice**: the mixing lemma controls the REAL spectrum of
  `M_{S,Sᶜ}` (its top singular value ≈ `d|S||Sᶜ|/N`, a near-rank-1 real approximation), while
  the `F₂`-rank of the sub-block is a different, subtler quantity that the spectral gap does
  not bound.  A cycle (the extreme sparse expander) has interval cuts of `F₂`-rank `2`.
- **No explicit `M` is proven** to have `Θ(N)` `F₂`-rank at every balanced cut; this is
  open, at the level of explicit rigidity lower bounds.

So the explicit `A` cannot be honestly PINNED DOWN with a proof — the reduction is exact and
the target is precise (explicit every-balanced-cut `F₂`-rigid `M`), but that target is an open
rigidity problem.  The candidate to instantiate when/if an explicit rigid `M` is proven: `A` =
strict upper triangle of `M`, `qform A x = ∑_{i<j, M_{ij}=1} x_i x_j`.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameCutRigid

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameQuadForm

variable {N : ℕ}

/-- **THE POLARIZATION IS THE SYMMETRIZED FORM (proved)**:
`bilinSym A x δ = ∑_{i,j} (A_{ij} + A_{ji})·x_i·δ_j = xᵀ(A+Aᵀ)δ`. -/
theorem bilinSym_eq (A : Fin N → Fin N → ZMod 2) (x δ : Fin N → ZMod 2) :
    bilinSym A x δ = ∑ i, ∑ j, (A i j + A j i) * (x i * δ j) := by
  unfold bilinSym
  have split : (∑ i, ∑ j, A i j * (x i * δ j + δ i * x j))
      = (∑ i, ∑ j, A i j * (x i * δ j)) + (∑ i, ∑ j, A i j * (δ i * x j)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [split]
  have swap : (∑ i, ∑ j, A i j * (δ i * x j)) = (∑ i, ∑ j, A j i * (x i * δ j)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [swap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- **THE DESIGN CORRECTION (proved)**: a symmetric `A` (undirected graph adjacency) gives a
degenerate quadratic form — the polarization vanishes, so nothing is detectable.  `A` must be
an ORIENTATION. -/
theorem bilinSym_symm_zero (A : Fin N → Fin N → ZMod 2) (x δ : Fin N → ZMod 2)
    (hsym : ∀ i j, A i j = A j i) :
    bilinSym A x δ = 0 := by
  rw [bilinSym_eq]
  have h2 : ∀ z : ZMod 2, z + z = 0 := by decide
  refine Finset.sum_eq_zero (fun i _ => ?_)
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [hsym i j, h2, zero_mul]

end PallLean.Paper93.DeepMath.PathB.NFrameCutRigid

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCutRigid.bilinSym_eq
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCutRigid.bilinSym_symm_zero
