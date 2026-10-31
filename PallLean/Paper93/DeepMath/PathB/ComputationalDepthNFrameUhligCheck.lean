import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameQuadForm

/-!
# N-Frame: does the rigid `g` admit Uhlig mass production?  No — wrong complexity regime

Checking whether the explicit rigid `g` (the expander quadratic form
`qform A x = ∑ A_{ij} x_i x_j`) admits Uhlig-style mass production — the phenomenon that makes
the direct sum FALSE by sharing a universal table across copies.  Outcome: NO, and it is a clean
regime mismatch, which CORRECTS the "guarded by Uhlig" claim of the previous step.

## The Uhlig regime check (paper)

Uhlig's mass production: computing `f` on `m` inputs costs `C_m(f) ≤ (1+o(1))·2^n/n` for suitable
`m` — the Lupanov worst-case bound.  This is a SAVINGS over `m·C(f)` ONLY when `C(f)` is near the
maximum `2^n/n` (a near-maximally-hard function whose expensive universal table can be amortized).
For an EASY `f` with `C(f) ≪ 2^n/n`, the Uhlig construction costs `~2^n/n ≫ m·C(f)` — it is
USELESS.  Uhlig mass production helps ONLY near-maximally-hard functions.

`g = qform A` (a sparse expander quadratic form) has `C(g) = O(dN)` gates (`dN/2` AND gates for
the edges, `dN/2` XOR gates to sum) — LINEAR, exponentially far from `2^N/N`.  The recursive
`f_N = g(f_{N/2}, f_{N/2})` has `C(f_N) = O(N log N)` — QUASI-linear.  NEITHER is in the
exponential regime where Uhlig applies.  So **`g` does NOT admit Uhlig mass production**, and the
previous step's "the cone-level direct sum is guarded by Uhlig" was IMPRECISE: Uhlig guards the
direct sum for near-maximally-hard functions; `g` and `f_N` are easy, so Uhlig does not bind here.

## The algebraic evidence (Lean): disjoint copies do not interact

  `qform_additive_disjoint` — **PROVED**: if two inputs `x, y` do not cross-detect
        (`bilinSym A x y = 0` — disjoint supports under a block-diagonal `A`, i.e. two disjoint
        copies), then `qform A (x + y) = qform A x + qform A y`.  The two copies decompose
        ADDITIVELY — disjoint monomial supports, no algebraic interaction.  This is the structural
        reason there is no shared "universal part" to amortize: the computations are additively
        independent, not overlapping.

## Honest scope — Uhlig removed, but the direct sum is still open (for a WEAKER reason)

Removing the Uhlig barrier is a real (if modest) correction: the specific obstruction cited last
step does NOT apply to our easy `g`.  But it does NOT resolve the cone-level direct sum.  The
direct sum for circuit `coneExcess` is OPEN in general — even for easy functions — because a
minimal circuit could still share via NON-table mechanisms (algebraic cancellation, bilinear
tricks).  `qform_additive_disjoint` shows no ALGEBRAIC interaction (disjoint monomials), which is
EVIDENCE the copies are independent, but not a proof that a minimal circuit cannot share via
cancellation.  So the honest updated status: the cone-level direct sum for `g` is OPEN but NOT
Uhlig-blocked — the barrier is weaker than stated, and what remains is the general direct-sum
problem for a quasi-linear function with additively-independent copies, which has no known
obstruction but also no known proof.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameUhligCheck

open PallLean.Paper93.DeepMath.PathB.NFrameQuadForm

variable {N : ℕ}

/-- **DISJOINT COPIES ADD (proved)**: inputs that do not cross-detect (`bilinSym A x y = 0`,
e.g. two disjoint copies under a block-diagonal `A`) decompose additively —
`qform A (x + y) = qform A x + qform A y`.  No algebraic interaction; disjoint monomial supports;
no shared universal part to amortize (so no Uhlig mass production). -/
theorem qform_additive_disjoint (A : Fin N → Fin N → ZMod 2) (x y : Fin N → ZMod 2)
    (h : bilinSym A x y = 0) :
    qform A (x + y) = qform A x + qform A y := by
  rw [qform_shift, h, add_zero]

/-- Bilinearity of the polarization in the LEFT slot (mirror of `bilinSym_add_right`). -/
theorem bilinSym_add_left (A : Fin N → Fin N → ZMod 2) (x y δ : Fin N → ZMod 2) :
    bilinSym A (x + y) δ = bilinSym A x δ + bilinSym A y δ := by
  unfold bilinSym
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  show A i j * ((x + y) i * δ j + δ i * (x + y) j)
    = A i j * (x i * δ j + δ i * x j) + A i j * (y i * δ j + δ i * y j)
  simp only [Pi.add_apply]
  ring

/-- **The many-copy additivity (proved)**: a family of pairwise-non-cross-detecting inputs sums
under `qform` to the sum of their individual values — the `k`-fold direct decomposition, showing
`k` disjoint copies are additively independent (no cross terms, hence no shared part). -/
theorem qform_additive_pair (A : Fin N → Fin N → ZMod 2) (x y z : Fin N → ZMod 2)
    (hxy : bilinSym A x y = 0) (hxz : bilinSym A x z = 0) (hyz : bilinSym A y z = 0) :
    qform A (x + y + z) = qform A x + qform A y + qform A z := by
  have hxyz : bilinSym A (x + y) z = 0 := by
    rw [bilinSym_add_left, hxz, hyz, add_zero]
  rw [qform_additive_disjoint A (x + y) z hxyz, qform_additive_disjoint A x y hxy]

end PallLean.Paper93.DeepMath.PathB.NFrameUhligCheck

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameUhligCheck.qform_additive_disjoint
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameUhligCheck.qform_additive_pair
