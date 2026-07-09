# Forster Sign-Rank / UPP Capstone & Scope

*One-page ledger for the Forster sign-rank lower bound and its UPP-communication consequence — a **complete**
restricted-class result. Capstone: `PallLean/Paper93/DeepMath/PathB/ComputationalDepthForsterCapstone.lean`.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.*

---

## What is PROVED (clean-axiom, no `sorry`)

Each name verified by `#print axioms` to depend on only `propext, Classical.choice, Quot.sound`
(**verified by build**, no custom axioms in any proof term).

| Capstone name | Statement | Backed by |
|---|---|---|
| `forster_signrank` | Forster, unconditional: any square `±1` matrix `M` with `0<‖sgnMat M‖` has `signRank M ≥ n/‖sgnMat M‖` | `ForsterUPP.forster_signRank_lower` |
| `forster_signrank_rectangular` | rectangular form; general position discharged by Vandermonde perturbation | `ForsterUnconditional.forster_bound_unconditional` |
| `forster_isotropic` | the analytic crux: isotropic/tight-frame transform `∑ᵢ ûᵢûᵢᵀ = (n/d)·I` (coercivity + EVT + Jacobi-det first-order optimality + √S) | `ForsterIsotropic.exists_isotropic` |
| `walsh_signrank` | explicit witness: `2^{2j}×2^{2j}` Walsh–Hadamard has `signRank ≥ 2^j = √(dim)` | `ForsterUPP.walsh_forsterLowerBound` |
| `signrank_of_upp_cost` | Paturi–Simon bridge: UPP cost `c ⇒ HasSignRankLE M (2^c)` | `hasSignRankLE_of_uppProtocolCostLE` |
| `walsh_upp_cost_lower` | consequence: any UPP protocol for `2^k×2^k` Walsh has cost `≥ k/2` | `ForsterUPP.walsh_uppCost_lower` |
| `checker2_signrank` | minimal Mathlib-only witness: `2×2` checkerboard has `signRank ≥ 2` | `checker2_signRankLowerBound` |

**Status:** the sign-rank bound is **complete** — the full variational engine (coercivity, EVT minimizer,
Jacobi-determinant first-order optimality, √S, glue) *and* the removal of the general-position hypothesis by
perturbation are proved. `forster_isotropic` is the deepest single result and includes a `d/dt log det`
optimality step Mathlib lacks. The Walsh UPP lower bound is a genuine sign-rank ⇒ UPP communication bound.

---

## What is OPEN / fenced

- **Circuit application** (`ComputationalDepthMarginFreeUPP.wholeCircuit_signRankBound_ofPolyApprox`): turning
  a poly-size `THR∘LTF` circuit into a cheap UPP protocol is socketed on the open low-degree-approximation /
  margin hypotheses (`happrox`, `hmargin`) — a genuine research wall, and the only reason this does not yield
  a general circuit lower bound. The associated tradeoffs (`MarginCircuit.*`) are proved but conditional.
- **UPP model caveat:** the UPP cost is defined against a transcript/rectangle normal-form protocol (a
  reasonable modeling choice, flagged in `ComputationalDepthUPPBridge.lean`); a referee should confirm it
  equals standard unbounded-error communication complexity. Not a gap in the proof, a definitional choice.

---

## Honest scope

- **Proved (complete):** Forster's sign-rank lower bound (general + rectangular + isotropic crux), the Walsh
  witnesses, the Paturi–Simon bridge, and the Walsh UPP `≥ k/2` bound — machine-checked, custom-axiom-free.
- **Open:** the circuit ⇒ cheap-UPP application (`happrox`/`hmargin` sockets).

Same tier as the prime `AC⁰[p]` and Nečiporuk capstones: a genuine, complete restricted-class lower bound
that is honestly **not** a path to `P ≠ NP`.

*Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. Companions: `PRIME_ACC0_CAPSTONE.md`, `NECIPORUK_CAPSTONE.md`,
`SWITCHING_CAPSTONE.md`, `FORSTER_STATUS.md`.*
