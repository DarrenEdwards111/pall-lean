import PallLean.Paper93.DeepMath.PathB.ComputationalDepthForsterUPP
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthForsterUnconditional
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUPPBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSignRankRankLower

/-!
# Forster sign-rank / UPP capstone — the complete restricted lower bound

This file collects, under clean citable names, the **unconditional, `sorry`-free, custom-axiom-free** Forster
sign-rank lower bound and its UPP-communication consequence. Unlike memory's stale note ("coercivity + √S +
glue still open"), the sign-rank side is **complete**: the variational crux (isotropic position via
coercivity + EVT minimizer + Jacobi-determinant first-order optimality + √S), the glue, and the removal of
the general-position hypothesis by a Vandermonde/moment-curve perturbation are all proved.

Each capstone name is verified by `#print axioms` to depend on **only** `propext, Classical.choice,
Quot.sound` — on none of the repo's custom axioms. Complete proofs, not shells.

## The capstone theorems (all PROVED, clean-axiom, no `sorry`)

* **`forster_signrank`** (`= ForsterUPP.forster_signRank_lower`) — Forster's theorem, unconditional: for any
  square `±1` matrix `M` with `0 < ‖sgnMat M‖`, `HasSignRankLE M d ⇒ √(dim)·√(dim)/‖sgnMat M‖ ≤ d`, i.e.
  `signRank M ≥ n/‖sgnMat M‖`. No general-position hypothesis on the input.
* **`forster_signrank_rectangular`** (`= ForsterUnconditional.forster_bound_unconditional`) — the rectangular
  form; general position discharged by perturbation.
* **`forster_isotropic`** (`= ForsterIsotropic.exists_isotropic`) — the analytic crux: nonzero, spanning,
  general-position vectors admit an isotropic (tight-frame) transform `∑ᵢ ûᵢûᵢᵀ = (n/d)·I`. Contains the
  Jacobi-determinant first-order optimality (`d/dt log det`) that Mathlib lacks. The deepest proved result.
* **`walsh_signrank`** (`= ForsterUPP.walsh_forsterLowerBound`) — explicit witness: the `2^{2j}×2^{2j}`
  Walsh–Hadamard matrix has `signRank ≥ 2^j = √(dim)`.
* **`signrank_of_upp_cost`** (`= hasSignRankLE_of_uppProtocolCostLE`) — the Paturi–Simon bridge: a
  UPP protocol of cost `c` gives `HasSignRankLE M (2^c)`.
* **`walsh_upp_cost_lower`** (`= ForsterUPP.walsh_uppCost_lower`) — the consequence: any UPP protocol for the
  `2^k×2^k` Walsh matrix has cost `c ≥ k/2`. A genuine sign-rank ⇒ UPP communication lower bound.
* **`checker2_signrank`** (`= SignRankRankLower.checker2_signRankLowerBound`) — a minimal Mathlib-only
  witness: the `2×2` checkerboard has `signRank ≥ 2` (pure determinant/rank, no analysis).

## Honest scope

The Forster sign-rank bound and the Walsh UPP lower bound are **complete restricted-class results** — real
classical mathematics, machine-checked. The UPP lower bound is proved against a transcript/rectangle
normal-form UPP model (a reasonable modeling choice, flagged in `ComputationalDepthUPPBridge.lean`). What
remains **honestly fenced** is the *circuit application*: turning a poly-size `THR∘LTF` circuit into a cheap
UPP protocol (`ComputationalDepthMarginFreeUPP.wholeCircuit_signRankBound_ofPolyApprox`, socketed on the
open low-degree-approximation / margin hypotheses `happrox`/`hmargin`) — a genuine research wall, and the
only reason this does not yield a general circuit lower bound. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `FORSTER_CAPSTONE.md` and the master ledger `PRIME_ACC0_CAPSTONE.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ForsterCapstone

/-- Forster's sign-rank lower bound, unconditional for any square `±1` matrix:
`signRank M ≥ n/‖sgnMat M‖`. -/
alias forster_signrank := PallLean.Paper93.DeepMath.PathB.ForsterUPP.forster_signRank_lower

/-- Forster's bound, rectangular form (general position discharged by perturbation). -/
alias forster_signrank_rectangular :=
  PallLean.Paper93.DeepMath.PathB.ForsterUnconditional.forster_bound_unconditional

/-- The analytic crux: existence of an isotropic (tight-frame) transform — coercivity + EVT +
Jacobi-determinant first-order optimality + √S. -/
alias forster_isotropic := PallLean.Paper93.DeepMath.PathB.ForsterIsotropic.exists_isotropic

/-- Explicit witness: the Walsh–Hadamard matrix has `signRank ≥ √(dim)`. -/
alias walsh_signrank := PallLean.Paper93.DeepMath.PathB.ForsterUPP.walsh_forsterLowerBound

/-- Paturi–Simon bridge: UPP cost `c ⇒ HasSignRankLE M (2^c)`. -/
alias signrank_of_upp_cost := PallLean.Paper93.DeepMath.PathB.hasSignRankLE_of_uppProtocolCostLE

/-- UPP communication lower bound: any UPP protocol for the `2^k×2^k` Walsh matrix has cost `≥ k/2`. -/
alias walsh_upp_cost_lower := PallLean.Paper93.DeepMath.PathB.ForsterUPP.walsh_uppCost_lower

/-- Minimal Mathlib-only witness: the `2×2` checkerboard has `signRank ≥ 2`. -/
alias checker2_signrank := PallLean.Paper93.DeepMath.PathB.checker2_signRankLowerBound

end PallLean.Paper93.DeepMath.PathB.ForsterCapstone

#print axioms PallLean.Paper93.DeepMath.PathB.ForsterCapstone.forster_signrank
#print axioms PallLean.Paper93.DeepMath.PathB.ForsterCapstone.forster_signrank_rectangular
#print axioms PallLean.Paper93.DeepMath.PathB.ForsterCapstone.forster_isotropic
#print axioms PallLean.Paper93.DeepMath.PathB.ForsterCapstone.walsh_signrank
#print axioms PallLean.Paper93.DeepMath.PathB.ForsterCapstone.signrank_of_upp_cost
#print axioms PallLean.Paper93.DeepMath.PathB.ForsterCapstone.walsh_upp_cost_lower
#print axioms PallLean.Paper93.DeepMath.PathB.ForsterCapstone.checker2_signrank
