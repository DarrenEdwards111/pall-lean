# Audit — is QF A a calibration falsifier for the SPDP method? (paper-only; SPDP route frozen)

Directed: audit the "QF A calibration falsifier" for the SPDP separation.  **This audit CORRECTS an error in my
two previous memos** (`SCOPE_UNIVERSAL_RESTRICTION_AUDIT.md`, round-4 notes), which asserted "QF A is a ready
falsifier for any SPDP measure."  That conflated two different rank measures.  Corrected finding: **QF A cleanly
falsifies communication/tensor-rank routes, but does NOT cleanly falsify the SPDP (shifted-partial-derivative)
method** — the natural quadratic has SPDP rank `0` at the matched parameters.  So the SPDP route's wall is *not*
the QF A easy-function gate; it remains check 2 (representation invariance = the separation).

## 1. The correction: two different rank measures

* **SPDP rank** (repo `SPDPDefs.spdpRank`): `Γ_{κ,ℓ}(p) = dim span{ m · ∂_S p : |S| = κ, deg m ≤ ℓ }` — the
  **shifted-partial-derivative** rank of a **polynomial** `p` (the Gupta–Kamath–Kayal–Saptharishi measure for
  arithmetic circuit lower bounds).  Matched params: `κ = ℓ = ⌊log₂ n⌋`.
* **Tensor / communication (Schmidt) rank**: the rank of the value matrix `M[z_S][z_{Sᶜ}] = f(z)` across a cut —
  what `exists_global_best_partition_bond` proves is `2^{Ω(n)}` for `QF A`.

These are **not the same quantity**, and one being high does not make the other high.  My prior memos treated
QF A's proved high *tensor* rank as if it were high *SPDP* rank.  It is not established to be, and — for the
natural quadratic — it is provably not.

## 2. What QF A provably has (machine-checked)

* **Poly-time:** `ChargedCompiler.qfProg_correct` / `qfProg_cost` — the Boolean core `decide(qf A z = 1)` is
  computed by `qfProg A` in `4n²` gates.
* **High tensor/communication rank:** `exists_global_best_partition_bond` — residual-span dimension `≥ 2^r`,
  `r = Ω(n)`, across every balanced cut.

So QF A **is** a genuine, machine-checked falsifier for any separation whose hardness measure is the
**communication-matrix / tensor / Schmidt rank of the value tensor**: it is a poly-time function with maximal
such rank, so "high value-tensor rank ⇒ hard decision" is false.  This part of the prior audit stands, once
restricted to communication/tensor-rank measures.

## 3. What QF A does to the SPDP method — three sub-cases, none a clean falsifier

* **(a) The natural quadratic `q_A(z) = ∑ Aᵢⱼ zᵢzⱼ` has SPDP rank `0` at matched params.**  `q_A` has total
  degree `2`, so any iterated partial derivative `∂_S q_A` with `|S| ≥ 3` vanishes.  At matched `κ = ⌊log₂ n⌋ ≥ 3`
  (for `n ≥ 8`), every generator `m · ∂_S q_A` is `0`, so `spdpSubspace κ ℓ q_A = {0}` and `spdpRank = 0`.  The
  SPDP measure correctly assigns the poly-time quadratic **minimal** rank — far below the exponential NP-side
  bound.  The natural quadratic **passes** the calibration; it is not a falsifier.  (This is elementary, not
  formalized — the SPDP route is frozen; but the vanishing of order-`≥3` derivatives of a degree-2 polynomial is
  unconditional.)
* **(b) The Boolean sign `sgn(q_A) = QF A` has a high-degree multilinear extension**, whose SPDP rank is a
  *separate, unresolved* quantity.  It could be high — but that is **not established**, and even if it were, it
  would be the SPDP rank of the *multilinear extension*, not of any *decider*.
* **(c) The SPDP separation framework measures compiled *decider* tableaux** (Cook–Levin polynomials), not
  multilinear extensions.  The SPDP rank of `qfProg A`'s compiled tableau is exactly an instance of the P-side
  hypothesis `CookLevinFrontierHyp` ("every poly-time compiled object has low SPDP rank").  So QF A's SPDP
  calibration here is **subsumed** by the already-unproved P-side claim — it neither independently falsifies nor
  supports it.

## 4. Verdict

* **Prior claim corrected:** QF A is a falsifier for **communication/tensor-rank** separation routes
  (machine-checked), **not** for the SPDP method.  Against SPDP the obvious easy-function test is *passed* — the
  natural quadratic has SPDP rank `0` at matched params.
* **Consequence for the SPDP route:** it is **not killed by the QF A easy-function gate** (check 3 passes for the
  natural quadratic).  Its wall is unchanged and is check 2: the representation-invariance / semantic-extraction
  bridge, which (per `SCOPE_UNIVERSAL_RESTRICTION_AUDIT.md`) is equivalent to the separation.  So the honest
  status of the SPDP route is "open at check 2," not "falsified at check 3."
* **What a real SPDP falsifier would require:** a poly-time function whose *compiled decider tableau* provably has
  high SPDP rank — i.e. a direct refutation of `CookLevinFrontierHyp`.  QF A is not shown to be one; exhibiting
  such a function (or proving none exists) is open and is exactly the P-side frontier.
* **Surviving honest assets** (unchanged): the axiom-free identity-minor NP-side SPDP bound (real mathematics, on
  the verifier representation), and QF A as the machine-checked *communication/tensor*-rank calibration falsifier
  (which keeps *tensor/entanglement*-based routes honest — e.g. it is exactly why the step-4 dynamic invariant
  must use log-rank, not raw rank).

## 5. Net

The QF A calibration audit **tightens honesty in both directions**: it removes an overclaim (QF A does not
falsify SPDP) and keeps a real one (QF A does falsify communication/tensor-rank routes, and is the reason the
dynamic-invariant program must avoid raw rank).  The SPDP route stays frozen — not because QF A kills it, but
because its load-bearing bridge (check 2) is the separation.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
