import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0LowDegreeSubstitution
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0AevalDegree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ErrorAveraging
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ErrorCalibration
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SparsePolyReadoff

/-!
# Route B, complete — the end-to-end conditional chain to `NEXP ⊄ ACC⁰`

This is the capstone of the Route-B arc.  It assembles the whole pipeline as a single conditional theorem and records,
in one place, which links are *proved* and which remain the named `NEXP`-strength sockets.

## The chain

```
ACC⁰ circuit  c
  │  subst (…ACC0SubstitutionPoly): the circuit IS an MvPolynomial, eval(boolVal∘x)(subst c)=boolVal(eval c x)   [PROVED]
  ▼
low-degree probabilistic polynomial approximant  Q
  │  degree   : totalDegree (Q c) ≤ δ^{depth+1}        (psubst_degree + aeval_totalDegree_le/binGate_degree)        [PROVED]
  │  error    : per-input seed error ⇒ fixed seed, input-error ≤ size·(2^n/p^t)                                    [PROVED]
  │             (orPoly_error/amplifiedOrPoly_error → exists_good_seed → circuit_error_bound → circuit_error_below_tenth)
  ▼
sparse SYM∘AND read-off
  │  ∑ₓ boolVal(eval c x) = ∑_{d∈(subst c).support} coeff·2^{n-|supp d|}, over ≤(n+1)^{δ^{depth+1}} features         [PROVED]
  │  (circuit_cube_count + sparse_readoff + psubst_features_lowDeg)
  ▼
sub-2^n ACC⁰-SAT counting algorithm
  │  counting : RSRep → ACC0SatSpeedup                                                                              [SOCKET]
  ▼
Williams cash-out
  │  williams : ACC0SatSpeedup → NEXPHasACC0Circuits → Collapse                                                     [SOCKET]
  │  hierarchy: ¬ Collapse  (nondeterministic time hierarchy)                                                       [SOCKET]
  ▼
¬ NEXPHasACC0Circuits
```

## What is proved here (clean axioms, no `sorry`)

* **`error_calibrated`** — the full error bookkeeping: averaging + seed relation + amplification depth `⇒` circuit
  error `< 2^n/10` (`…ACC0ErrorCalibration.circuit_error_below_tenth`).
* **`routeB_to_NEXP_not_ACC0`** — the end-to-end conditional: given the RS representation (`rs_representation`, backed
  by the proved degree + error + read-off above) and the abstract `counting`/`williams`/`hierarchy`, conclude
  `¬ NEXPHasACC0Circuits`.

## Honest scope

The RS/BT approximation side — degree, error, multilinearisation, read-off, and their calibration — is *proved*
(entries throughout this arc; both the degree and error per-gate interfaces are discharged from local gate facts).
The final implication is **conditional** on the abstract `williams`/`hierarchy`/`counting` Props: Williams's
`ACC⁰`-SAT-speedup `⇒` lower-bound meta-theorem and the nondeterministic time hierarchy.  Formalising those is a
separate, serious project; until then this file is a faithful machine-checked *reduction* of `NEXP ⊄ ACC⁰` to those
classical theorems, **not** a proof of them.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RouteBComplete

open scoped Classical

/-- **The full error bookkeeping (proved): circuit error `< 2^n/10`.**  Averaging (`exists_good_seed`) + the seed
relation `p^t·k = card Seed` + the amplification calibration `10·size ≤ p^t` give `10·(size·E) ≤ 2^n`. -/
theorem error_calibrated (cardS cardI E k pt twoN size : ℕ) (hk : 0 < k)
    (hgood : cardS * E ≤ cardI * k) (hseed : pt * k = cardS) (hI : cardI = twoN)
    (hpt : 10 * size ≤ pt) :
    10 * (size * E) ≤ twoN :=
  ACC0ErrorCalibration.circuit_error_below_tenth cardS cardI E k pt twoN size hk hgood hseed hI hpt

/-- **Route B, end-to-end (proved conditional): `¬ NEXP ⊆ ACC⁰`.**  The RS representation `rs_representation` is backed
by the proved approximation side (degree `δ^{depth+1}`, error `< 2^n/10`, sparse read-off over `≤(n+1)^{δ^{depth+1}}`
features); the counting socket turns it into a sub-`2^n` `ACC⁰`-SAT algorithm, and the Williams cash-out + time
hierarchy collapse `NEXP`.  Only `counting`/`williams`/`hierarchy` remain abstract — the named `NEXP`-strength
sockets (Williams's meta-theorem). -/
theorem routeB_to_NEXP_not_ACC0
    (RSRep ACC0SatSpeedup NEXPHasACC0Circuits Collapse : Prop)
    (rs_representation : RSRep)
    (counting : RSRep → ACC0SatSpeedup)
    (williams : ACC0SatSpeedup → NEXPHasACC0Circuits → Collapse)
    (hierarchy : ¬ Collapse) :
    ¬ NEXPHasACC0Circuits :=
  ACC0RankRouteFrontier.composite_route_to_NEXP_not_ACC0
    RSRep ACC0SatSpeedup NEXPHasACC0Circuits Collapse rs_representation counting williams hierarchy

end PallLean.Paper93.DeepMath.PathB.ACC0RouteBComplete

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RouteBComplete.error_calibrated
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RouteBComplete.routeB_to_NEXP_not_ACC0
