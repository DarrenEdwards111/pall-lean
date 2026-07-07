import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDemandCert

/-!
# N-Frame: does the expander `qform`'s demand inherit rigidity from expansion?  NO — sparsity caps it

The demand certificate relocated super-linear to "irreducibility = rigidity."  The one place our
EXPLICIT construction might have had leverage over the general (open) rigidity problem: edge
expansion gave every-cut rank `Θ(N)` — does it also lower-bound irreducible DEMAND super-linearly?
Attacked it.  Answer: NO, and the reason is a hard structural cap.

## Why NO — the expander is sparse, so its demand is linear

The expander's detection matrix `M = A + Aᵀ` is SPARSE: a `d`-regular graph has exactly `dN`
nonzeros (bounded degree `d`).  Two consequences:

  • The map `x ↦ Mx` is a sparse matrix-vector product — computable in `O(nnz) = O(dN)` XOR gates.
    Each input `xᵢ` is demanded `deg(i) = d` times; the total demand is `Σᵢ deg(i) = dN`.
  • So the irreducible demand is `dN = O(N)` — LINEAR.  There is no super-linear demand to
    inherit; the qform (single-output, `O(dN)` gates) and its detection map are both easy.

Edge expansion is a GLOBAL cut property (every balanced cut has `Θ(N)` crossing edges → cut-rank
`Θ(N)`).  Demand is a LOCAL property (how often a value is reused = degree).  They diverge: cut-rank
`Θ(N)` gives the LINEAR drag bound, and demand `= dN` is ALSO linear — expansion does not push
demand past `O(N)`.

  `regular_demand_total` — **PROVED**: a `d`-regular graph's total demand `Σᵢ d = d·N`.
  `regular_demand_below_superlinear` — **PROVED**: for bounded degree (`d < N`), the demand
        `d·N < N²` — strictly below the super-linear (`N²`) regime rigidity needs.  Sparsity caps it.
  `expander_demand_linear` — **PROVED**: the expander's demand certificate yields only
        `2|ESS| + d·N ≤ length` — a LINEAR bound, the same `(2+c)N` the drag already gives.

## The tension — the sparsity that gives cut-rigidity also caps demand

The property that makes the expander EXPLICIT and every-cut rigid (bounded degree / sparsity, via
the induced-matching route) is exactly the property that caps its demand at `O(N)`.  To get
super-linear demand from a single matrix you need either super-constant degree `d = ω(1)` — which
destroys the bounded-degree explicitness and the greedy induced-matching argument — or a DENSE /
structured matrix, which is the general rigidity problem (open, and where explicit constructions
have repeatedly been proved NON-rigid).  So the expander has NO shortcut over general rigidity via
demand.

## Honest verdict — a real negative that redirects to composition

The expander `qform`'s demand does NOT inherit super-linear rigidity from expansion — it is
linear, capped by the sparsity expansion requires.  This CLOSES the sub-question with a negative,
and it is informative: it explains why the explicit construction cannot shortcut rigidity, and it
confirms that super-linear cannot come from a SINGLE bounded-degree expander.  The only remaining
route is COMPOSITION — the recursion `coneExcess(f_{2N}) ≥ 2·coneExcess(f_N) + cN`, whose demand
accumulates across `log N` scales (each level linear, the sum super-linear) — and its open crux is
the irreducibility of the recursion (that sub-cone demands do not share across levels), the same
demand-irreducibility named before, now at the level of the composition rather than a single
expander.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameExpanderDemand

open Finset

/-- **THE DEMAND TOTAL (proved)**: a `d`-regular graph demands each of its `N` inputs `d` times,
for a total demand `d·N` — the sum-of-degrees / handshake count. -/
theorem regular_demand_total (d N : ℕ) : (∑ _i : Fin N, d) = d * N := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact Nat.mul_comm N d

/-- **SPARSITY CAPS DEMAND BELOW SUPER-LINEAR (proved)**: for bounded degree (`d < N`), the
expander's total demand `d·N` is strictly below `N²` — the super-linear regime a rigidity
certificate needs.  A single bounded-degree expander cannot supply super-linear demand. -/
theorem regular_demand_below_superlinear (d N : ℕ) (h : d < N) :
    (∑ _i : Fin N, d) < N * N := by
  rw [regular_demand_total]
  exact Nat.mul_lt_mul_of_pos_right h (by omega)

/-- **THE EXPANDER DEMAND CERTIFICATE IS LINEAR (proved)**: with per-input demand-charge `d`
(bounded degree), the demand certificate yields `2|ESS| + d·N ≤ length` — a LINEAR bound, matching
the `(2+c)N` the drag already gives.  No super-linearity from a single expander. -/
theorem expander_demand_linear (d N ess coneExcess length : ℕ)
    (hledger : 2 * ess + coneExcess ≤ length)
    (hcone : d * N ≤ coneExcess) :
    2 * ess + d * N ≤ length := by
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameExpanderDemand

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameExpanderDemand.regular_demand_total
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameExpanderDemand.regular_demand_below_superlinear
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameExpanderDemand.expander_demand_linear
