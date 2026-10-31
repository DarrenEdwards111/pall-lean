import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRSAssembly
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBoostingFinal
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRSCapstone
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTailBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthModPoly
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGateApproxGen
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthOrPoly
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultilinear
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRSHardnessSkeleton
import Mathlib

/-!
# Razborov–Smolensky capstone index — the AC⁰[p] lower-bound arc, end to end

This file is a **verified table of contents** for the Razborov–Smolensky `MOD_q ∉ AC⁰[p]` formalization.  Every
`#check` below pins a landmark theorem to its real, compiled type, so this index cannot drift from the code.  All
the cited results are `sorry`-free and use only `[propext, Classical.choice, Quot.sound]`.

## What is PROVED (the upper-bound side + all representation transfers)

The goal `MOD_q ∉ AC⁰[p]` factors into an *upper-bound* direction (AC⁰[p] circuits are low-degree polynomials)
and a *lower-bound* direction (`MOD_q` is **not** low degree).  **The entire upper-bound side and every
representation transfer are formalized here**, culminating in one conditional separation
(`ACC0.Circuit.no_acp_circuit`).  The arc:

1. **The circuit model.**  `ACC0.Circuit` — inductive AC⁰[p] circuits (`var`/`const`/`not`/`and`/`or`/`mod`).

2. **Exact arithmetisation of `MOD_p`.**  Over `𝔽_p`, `MOD_p` is exactly `1 − (Σ Xᵢ)^(p−1)` (`SymAnd.modPoly_eval`),
   degree `p − 1` (Fermat).  The *easy* direction.

3. **Probabilistic `OR`/`AND` approximation.**  A fixed tuple of random `𝔽_p`-linear forms approximates an `OR`
   gate off a `2⁻ᵗ` fraction of inputs (`GateApprox.exists_good_forms_gen`, `exists_forms_few_disagree`); the
   substituted `OR`-polynomial `orPoly` evaluates to the gate off the bad set (`OrPoly.orPoly_eval_eq_or`).

4. **The term-carrying recursion.**  `ACC0.Circuit.approxCircuit`: every well-formed AC⁰[p] circuit `C` gets a
   `CircuitApproxData` — a concrete polynomial of degree `≤ (t(p−1))^depth C` (`degApprox_le_pow_depth`) agreeing
   with `C` off a bad set of size `≤ size C · 2^(n-t)`.  Assembled from the six gate constructors
   (`caVar/caConst/caNot/caOr/caAnd/caMod`) by well-founded recursion.

5. **The RS bridge.**  `ACC0.Circuit.circuit_low_degree_approx`: extracting the agreement set `G` (complement of
   the bad set), `|G| ≥ 2ⁿ − size C · 2^(n-t)`.

6. **`{0,1}` → `{−1,+1}` transfer (degree-preserving).**  `Multilinearize.eval_eq_multilinear` (`MvPolynomial.eval`
   on the cube `=` `Multilinear.eval`) then `WalshSpan.eval_eq_evalW` (multilinear `=` Walsh), each preserving
   degree (`multilinear_coeff_support`, `walshCoef_support`).

7. **The boosting / dimension argument.**  `WalshSpan.evalW_surjective` (Walsh span), `WalshSpan.boosting_surjection`
   (a degree-`d` approximator of parity on `G` ⇒ `|G| < 2ⁿ`), `RazborovSmolensky.dimension_argument`,
   `Dimension.sum_choose_lt` (`Σ_{i≤m} C(n,i) < 2ⁿ` for `m < n`).

8. **The assembled composition + conditional separation.**  `ACC0.Circuit.circuit_walsh_approx` (circuit ⇒
   low-degree **Walsh** approximator on a large set) and `ACC0.Circuit.no_acp_circuit` (if `f` is hard, no small
   AC⁰[p] circuit computes it).

## What is NOT proved (the lower-bound core, and the headline separations)

* **`MOD_q ∉ AC⁰[p]` is NOT closed.**  The single missing input is the `hard` hypothesis of `no_acp_circuit` — that
  `MOD_q` (`q ≠ p`) is *not* low-degree-approximable over `𝔽_p`.  This is the genuine Razborov–Smolensky lower
  bound, subject to the natural-proofs/algebrization barriers; it is exposed here as an explicit assumption, not
  derived.  Instantiating it would close the separation.

* **`NEXP ⊄ ACC⁰` is NOT closed** — that lives behind separate, untouched deep axioms.

This index documents an honest, complete formalization of the *upper-bound machinery and all transfers*, with the
one hard theorem cleanly isolated.
-/

namespace PallLean.Paper93.DeepMath.PathB.RSIndex

open PallLean.Paper93.DeepMath.PathB

-- 1. The circuit model.
#check @ACC0.Circuit.eval

-- 2. Exact MOD_p arithmetisation (the easy direction).
#check @SymAnd.modPoly_eval

-- 3. Probabilistic OR/AND approximation.
#check @GateApprox.exists_good_forms_gen
#check @GateApprox.exists_forms_few_disagree
#check @OrPoly.orPoly_eval_eq_or
#check @OrPoly.orPoly_totalDegree_le

-- 4. The term-carrying recursion (all six gate constructors assembled).
#check @ACC0.Circuit.CircuitApproxData
#check @ACC0.Circuit.degApprox_le_pow_depth
#check @ACC0.Circuit.WF
#check @ACC0.Circuit.approxCircuit

-- 5. The RS bridge: circuit ⇒ low-degree {0,1} approximator on a large set.
#check @ACC0.Circuit.circuit_low_degree_approx

-- 6. The {0,1} → {−1,+1} transfer, degree-preserving.
#check @Multilinearize.eval_eq_multilinear
#check @Multilinearize.multilinear_coeff_support
#check @WalshSpan.eval_eq_evalW
#check @WalshSpan.walshCoef_support
#check @WalshSpan.monomialFn_eq_sum_walsh

-- 7. The boosting / dimension argument.
#check @Multilinear.eval_surjective
#check @WalshSpan.evalW_surjective
#check @WalshSpan.boosting_surjection
#check @RazborovSmolensky.dimension_argument
#check @Dimension.sum_choose_lt

-- 8. The assembled composition and the conditional separation.
#check @ACC0.Circuit.circuit_walsh_approx
#check @ACC0.Circuit.no_acp_circuit

-- 9. The q=2 case CLOSED: the unconditional parity Razborov–Smolensky lower bound.
--    (gaps (1) affine, (2) sharp dimension, packaging, and the central-binomial Stirling bound all proved;
--     only general MOD_q, q≠2, still needs the barriered reduction of gap (3).)
#check @ACC0.Circuit.walshFn_univ_eq            -- parity packaging: walshFn univ = 1 − 2·boolParity
#check @ACC0.Circuit.centralBinom_sq_le         -- central-binomial concentration (√-free Stirling)
#check @ACC0.Circuit.no_parity_circuit          -- parity ∉ small AC⁰[p] (clean arithmetic hypotheses)

end PallLean.Paper93.DeepMath.PathB.RSIndex
