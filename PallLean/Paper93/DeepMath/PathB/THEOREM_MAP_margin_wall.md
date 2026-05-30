# Theorem map: the margin wall for sign-rank ⇒ THR∘LTF lower bounds

**Tag:** `margin-thr-ltf-bound` (commit `92cd86d9`); no-go completed at `cf97dd35`.

This note maps the formalized arc from Forster's isotropic-position theorem to a
**theorem-shaped obstruction** on the "sign-rank ⇒ circuit lower bound" route.
The headline is the *three-part wall*: the margin bridge works quantitatively, a
hard function forces its cost exponentially high, and the constant-bias shortcut
is formally dead. What remains open is isolated as a single precise question
(margin lower-bounding), not a vague gap.

All theorems below are checked with axiom trace `[propext, Classical.choice,
Quot.sound]` (no `sorry`, no custom axioms), except where a single explicitly
named, classical, `γ`/`ε`-independent hypothesis (`CentralBinomGF`) is carried —
see *Caveat*.

Namespaces are under `PallLean.Paper93.DeepMath.PathB.*`.

---

## 1. Foundation: unconditional, concrete Forster sign-rank bound

| Result | Name | File |
|---|---|---|
| Radial isotropic position (∃T), unconditional | `ForsterIsotropic.exists_isotropic` | `ComputationalDepthForsterIsotropicMinimization.lean` |
| General-position ⇒ tight frame (matrix→EuclideanSpace) | `ForsterWiring.isTightFrame_of_genPos` | `ComputationalDepthForsterWiring.lean` |
| Restricted Forster capstone | `ForsterWiring.forster_bound_of_genPos` | `ComputationalDepthForsterWiring.lean` |
| **Unconditional Forster** (no general-position hyp.) | `ForsterUnconditional.forster_bound_unconditional` | `ComputationalDepthForsterUnconditional.lean` |
| General square-matrix Forster (sign-rank form) | `ForsterUPP.forster_signRank_lower` | `ComputationalDepthForsterUPP.lean` |
| `‖sgnMat M‖ ≥ √(rows)` | `ForsterUPP.sgnMat_opNorm_ge` | `ComputationalDepthForsterUPP.lean` |

**Concrete hard matrix (Walsh–Hadamard, sign-rank `≥ √N`):**

| Result | Name |
|---|---|
| Character (row) orthogonality | `ForsterUnconditional.walsh_orthogonality` |
| Hadamard ⇒ sign-rank `≥ √N` | `ForsterUnconditional.sqrt_le_of_hadamard` |
| `walsh_sign_rank` : Walsh of size `2^k` has sign-rank `≥ 2^{k/2}` | `ForsterUnconditional.walsh_sign_rank` |
| Discharges the framework's `ForsterLowerBound` for Walsh | `ForsterUPP.walsh_forsterLowerBound` |

UPP communication corollary (Paturi–Simon direction, existing bridge):
`ForsterUPP.walsh_uppCost_lower` — UPP cost of Walsh `≥ k/2`.

---

## 2. The three-part wall

Let `C` be a depth-2 `THR∘LTF` circuit (`Depth2Threshold`), with bottom gates
`sgn(α_k·i + β_k·j)`. A *bottom margin* `γ_k` means `γ_k ≤ |α_k i + β_k j| ≤ 1`
for all inputs (normalized halfspace). The *cost* of a margin realization is
`1 + ∑_k (D_k+1)²`, where `D_k` is the degree of the polynomial approximating the
`k`-th gate's sign — and `D_k ≈ 1/γ_k²` (see Part A).

### Part A — *With margin, the bridge works (quantitatively).*

| Result | Name | File |
|---|---|---|
| Margin sign-approx, explicit degree `N = Θ((1/γ²)log(1/(εγ)))` | `SignApproxMargin.exists_sign_approx_margin` | `ComputationalDepthSignApproxMargin.lean` |
| Polynomial-approx ⇒ weighted-approx realizer (cost `(d+1)²`) | `MarginFreeUPP.weightedApproxRealizer_ofPolyApprox` | `ComputationalDepthMarginFreeUPP.lean` |
| Whole-circuit sign-rank from poly approxes | `MarginFreeUPP.wholeCircuit_signRankBound_ofPolyApprox` | `ComputationalDepthMarginFreeUPP.lean` |
| **Circuit bound:** margins ⇒ sign-rank `≤ 1 + ∑_k (D_k+1)²` | `MarginCircuit.wholeCircuit_signRank_of_bottomMargin` | `ComputationalDepthMarginCircuitBound.lean` |

The degree blow-up `D_k ≈ 1/γ_k²` is an explicit theorem, not an estimate.

### Part B — *A hard function forces the cost exponentially high.*

| Result | Name |
|---|---|
| Cost formula `= 1 + ∑_k (D_k+1)²` | `MarginCircuit.card_cost` |
| **Margin cost ≥ Forster bound** (upper bound meets lower bound) | `MarginCircuit.margin_cost_ge_forster` |
| **Walsh blow-up:** computing Walsh ⇒ `1 + ∑_k (D_k+1)² ≥ 2^j` | `MarginCircuit.walsh_margin_blowup` |

Consequence: a `THR∘LTF` circuit computing the `2^{2j}×2^{2j}` Walsh matrix must
have **exponentially many gates or exponentially small margins** (`some γ_k ≤
2^{-Ω(k)}`). This is *not* a barrier — it is the margin upper bound (Part A)
meeting the Forster lower bound (§1).

### Part C — *The constant-bias shortcut is formally dead.*

| Result | Name | File |
|---|---|---|
| Constant-bias protocol ⇒ exact realizer ⇒ Forster-bounded | `ForsterUPP.forster_constantBias_lower` | `ComputationalDepthForsterUPP.lean` |
| **No small constant-bias protocol for Walsh** (`card τ ≥ 2^j`) | `ForsterUPP.walsh_constantBias_no_small` | `ComputationalDepthForsterUPP.lean` |

Constant bias = exact `±1` output (`ExactSignedOutputRealizer.ofConstantBiasUPPProtocol`
in `ComputationalDepthUPPBridge.lean`), so it buys no asymptotic saving over exact
realization: its transcript count is pinned to the Forster bound. The genuinely
cheap object must use *non-constant* (approximate) bias — i.e. Part A.

---

## 3. The isolated open problem

The route gives a real `THR∘LTF` lower bound **iff** the bottom-gate margins of a
small circuit can be kept from collapsing. Precisely:

> **Open:** does every poly-size `THR∘LTF` circuit (for a hard target) admit a
> normalization with bottom margins `γ_k ≥ 1/poly`? Part B shows that for a
> high-sign-rank function this is *exactly* what must fail.

This is the P≠NP-strength gap, now a single sharp question rather than a vague
wall. It is the only thing standing between the formalized machinery and a
circuit lower bound.

---

## Caveat (single carried hypothesis)

`SignApproxMargin.CentralBinomGF` : the classical central-binomial generating
function `(1−u)^{-1/2} = ∑_i C(2i,i)/4^i · uⁱ` (as a `HasSum`). It is `γ`- and
`ε`-**independent** and does not affect any quantitative content above; it is the
analytic input to the margin approximation only. Mathlib has the abstract
generalized binomial series (`Analysis/Analytic/Binomial.lean`, `Ring.choose`) but
not this central-binomial specialization; discharging it (`Ring.choose(−1/2,n) =
(−1)ⁿ·C(2n,n)/4ⁿ`, then `FormalMultilinearSeries.ofScalars` extraction) is a
self-contained ~200–300 line formalization, deferred as plumbing.
