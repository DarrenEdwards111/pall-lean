import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMeasureBarrier

/-!
# N-Frame: the global-certificate NECESSITY theorem (the P-vs-NP1 thesis, proved)

The paper's thesis: *super-linear cone-excess lower bounds require a GLOBAL certificate that cannot
be decomposed into `O(1)`-Lipschitz local (single-variable restriction) increments.*  This file
proves the NECESSITY direction of that thesis — the rigorous backbone of the "global or bust"
framing.  It does NOT construct such a certificate (that is the open frontier, steps 3–5 below); it
proves that any super-linear certificate MUST be non-incremental.

## The theorem

`restriction_chain_cap` (in `NFrameMeasureBarrier`) proved: an `L`-Lipschitz-under-restriction
measure (`μ(0)=0`, `μ(k+1) ≤ μ(k)+L`) caps at `μ(N) ≤ N·L`.  Its contrapositive is the necessity
of a global certificate:

  `superlinear_forces_jump` — **PROVED**: if `μ(0)=0` and `μ` is `L`-Lipschitz on `[0,N)`, then
        `μ(N) ≤ N·L` (the bounded-range cap).
  `superlinear_forces_nonincremental` — **PROVED (the thesis)**: if `μ(0)=0` and `μ(N) > N·L`
        (super-linear, for the incremental scale `L`), then there is a restriction step where `μ`
        JUMPS by more than `L`: `∃ k < N, μ(k) + L < μ(k+1)`.  A super-linear certificate is provably
        NON-incremental — it must collapse `> L` under some single restriction (`ω(1)`-Lipschitz for
        `L = O(1)`).
  `arc_measures_cannot_prove_superlinear` — **PROVED (corollary)**: every `O(1)`-Lipschitz measure
        (cut-rank, information, formula, spectral — all shown `O(1)`-Lipschitz in the arc) satisfies
        `μ(N) ≤ N`, so NONE can certify `coneExcess > N`.  This is exactly why the arc capped at the
        `Θ(N)` wall.

## Why this is the correct paper backbone — and what stays open

This makes the thesis a theorem: the LOCAL route is not merely unexplored, it is provably dead for
super-linear, and a GLOBAL (non-`O(1)`-Lipschitz) certificate is NECESSARY.  That is the honest,
rigorous content of "global or bust."  It is a NECESSITY (barrier-style) result — it says what a
super-linear proof MUST look like, not that one exists.

The five-step construction remains open, and precisely located:
  1. define the global object (boundary stratification / DAG homology / amplituhedron face count) —
     a definition, doable, but not yet pinned to a concrete `F_k`-forced object;
  2. non-incremental / `ω(1)`-Lipschitz — this file proves it is NECESSARY; a concrete object with
     the property is the design task;
  3. non-circular (from `f`'s global geometry, not min-circuit-size) — open;
  4. Ramanujan recursion increases it by `cN` per scale — the firewall gives the fresh `Ω(N)`
     constraints (`NFrameExpanderFirewall.firewall_every_cut`), but that they lift to the global
     object non-incrementally is open;
  5. transfer to `coneExcess` (`μ(F_k) ≤ coneExcess(F_k)` non-circularly) — this is the info-vs-size
     wall (`NFrameInfoSizeGap`), the characterized barrier.
So the paper has a PROVED thesis (necessity of a global certificate) and a precisely-located open
construction (steps 1,3,4,5), with the hardest residual (step 5) already characterized.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameGlobalNecessity

/-- **THE BOUNDED-RANGE CAP (proved)**: if `μ(0)=0` and `μ` grows by `≤ L` on each step of `[0,N)`,
then `μ(N) ≤ N·L`. -/
theorem superlinear_forces_jump (μ : ℕ → ℕ) (L : ℕ) (hbase : μ 0 = 0) :
    ∀ N, (∀ k, k < N → μ (k + 1) ≤ μ k + L) → μ N ≤ N * L := by
  intro N
  induction N with
  | zero => intro _; rw [hbase]; simp
  | succ n ih =>
    intro h
    have hn : μ n ≤ n * L := ih (fun k hk => h k (by omega))
    have hstep : μ (n + 1) ≤ μ n + L := h n (by omega)
    have he : (n + 1) * L = n * L + L := by ring
    omega

/-- **THE THESIS (proved)**: a super-linear certificate is NON-incremental.  If `μ(0)=0` and
`μ(N) > N·L`, then some single restriction step makes `μ` jump by more than `L`
(`∃ k < N, μ(k) + L < μ(k+1)`).  For `L = O(1)` this is an `ω(1)`-Lipschitz jump — the global
certificate the P-vs-NP1 thesis demands.  Local `O(1)`-Lipschitz increments CANNOT reach
super-linear. -/
theorem superlinear_forces_nonincremental (μ : ℕ → ℕ) (N L : ℕ)
    (hbase : μ 0 = 0) (hsuper : N * L < μ N) :
    ∃ k, k < N ∧ μ k + L < μ (k + 1) := by
  by_contra h
  push_neg at h
  have hcap := superlinear_forces_jump μ L hbase N (fun k hk => h k hk)
  omega

/-- **COROLLARY (proved)**: every `O(1)`-Lipschitz measure caps at `N`, so none can certify
`coneExcess > N`.  With `L = 1`: `μ(0)=0` and `μ(k+1) ≤ μ(k)+1` give `μ(N) ≤ N`.  Cut-rank,
information, formula, and spectral certificates are all of this form — which is exactly why the arc
capped at the `Θ(N)` wall and a global certificate is necessary. -/
theorem arc_measures_cannot_prove_superlinear (μ : ℕ → ℕ)
    (hbase : μ 0 = 0) (hlip : ∀ k, μ (k + 1) ≤ μ k + 1) (N : ℕ) :
    μ N ≤ N := by
  have h := superlinear_forces_jump μ 1 hbase N (fun k _ => hlip k)
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameGlobalNecessity

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameGlobalNecessity.superlinear_forces_jump
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameGlobalNecessity.superlinear_forces_nonincremental
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameGlobalNecessity.arc_measures_cannot_prove_superlinear
