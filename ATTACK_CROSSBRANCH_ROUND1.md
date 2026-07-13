# Attack — the cross-branch no-amortization inequality (paper round 1)

Direct attack on `CE(F_{k+1}) ≥ 2·CE(F_k) + cN`, whose finishing target (per `NFrameShareChargeBound`:
`absolute_savings_bound_closes` proved, `half_charge_does_not_close` refuting the ratio route) is the **absolute**
routing bound `savings ≤ cN` on the mixer.  Result (**corrected per HAL's audit**): **no closure.  The two horns are two *candidate* sufficient mechanisms
for an `O(fresh)` savings bound (not proved equivalent); the expander imposes a *quantitative* induced-matching
tradeoff `ν_I ≤ N(1+λ)/(2d)` (NOT an absolute expansion-vs-fresh impossibility — constant-degree expanders can
have linear induced matchings); and the truncated-family escape is refuted modulo a parameter-precision caveat.**
Honest, partly-negative structural map; the earlier "hard conflict / reduction to rigidity" wording was
overstated.

## 1. Two candidate mechanisms for an `O(fresh)` savings bound (NOT proved equivalent)

* **Linear-mixer (rigidity) horn.**  A share of a *linear* mixer `M` is *conjectured* to correspond to a low-rank
  modification of `M`, so `savings ≤ cN` would follow from `M` being **Valiant-rigid** at the fresh scale.
  **Caveat (HAL):** cross-branch sharing has NOT been proved equivalent to a low-rank matrix modification — a
  shared *nonlinear/Boolean* subcircuit need not induce a rank-lowering entry change.  This is a **candidate
  sufficient bridge, not an iff.**
* **Nonlinear-mixer (Uhlig) horn.**  `savings ≤ cN` would follow if the mixer **decorrelates** the two copies so
  their sharable overlap is `≤ cN`.

These are **two possible sufficient mechanisms** for the same target ("bound cross-copy savings to `O(fresh)`"),
**not** one theorem: a common graph invariant translating both into `O(fresh)` is still missing.  For the
Ramanujan mixer, `fresh = cN ≈ ν_I` (induced-matching number), and the open question is whether the expander
bounds savings to `O(ν_I)`.

## 2. The QUANTITATIVE induced-matching tradeoff (corrected — NOT an absolute conflict)

`fresh` is an **induced-matching** quantity.  The expander mixing lemma gives, for the `2m` endpoints `S` of an
induced matching of size `m` (which induce exactly `m` edges):

> `|m − d·(2m)²/(2N)| ≤ λ·(2m)`,  hence  **`ν_I = m ≤ N(1+λ)/(2d)`.**

For a Ramanujan graph `λ = O(√d)`, so `ν_I = O(N/√d)` — **and for constant degree `d` this is `O(N)`, i.e.
bounded-degree expanders can have induced matchings of LINEAR size.**  So the earlier claims are WRONG as written
and are retracted:

* ✗ "expander ⇒ `ν_I ≪ N`" — false in general (fails at constant `d`);
* ✗ "large fresh `ν_I = Θ(N)` ⇒ not an expander" — false (constant-degree expanders can have linear `ν_I`);
* ✗ "no single mixer graph is both large-fresh and anti-sharing" — false as an absolute statement.

The **correct** statement is a *quantitative tradeoff that only bites as `d` grows*: denser spectral expansion
pushes the available induced matching down to `≈ N/√d`.  Useful, but a tradeoff, not an incompatibility.  (The
expander-mixing bound itself is clean and formalizable.)

## 3. The lean: NEGATIVE for the expander mixer

With `fresh ≤ O(N/d)`, the inequality needs `savings ≤ O(N/d)` — i.e. the **Ramanujan adjacency matrix must be
rigid at scale `N/d`** (linear horn) / must decorrelate to overlap `≤ O(N/d)` (nonlinear horn).  The honest
evidence leans against it: the adjacency matrices of structured/algebraic graphs are repeatedly found
**non-rigid** (Dvir–Edelman, Alman–Williams, Dvir–Liu: Hadamard, Fourier, and various algebraic matrices have
sub-maximal rigidity).  The Ramanujan mixer's rigidity is not established and trends non-rigid; so the linear horn
**probably fails** for the specific mixer — `savings` can exceed the small `fresh`, and the inequality fails as
constructed.  Closing it would require a genuinely **rigid** mixer = explicit Valiant rigidity (open), or a
two-component / non-graph mixer that escapes the §2 tension (no candidate).

## 4. The truncated-family escape is refuted

The one thing special about the *truncated* family is a Route-C **effective-dimension** bound: the truncated
reachable set has `d_eff ≤ poly(log)`.  Does that bound cross-copy savings?  **No.**  Effective dimension is a
**metric** (covering-number) quantity; it bounds the description size of the reachable *set*, not the
**computational** complexity `C(V)` of a sub-quantity `V` living in it.  A low-`d_eff` set routinely hosts
high-`C(V)` sub-functions (a one-parameter family can encode a hard function through the parameter).  So the
info-vs-size gap (`C(V)/|V|` large) — the exact nonlinear-horn threat — is **not** controlled by `d_eff`.  The
truncation gives geometry, not complexity; the escape fails.

## 5. Verdict (corrected)

* **No closure**, and no false one.
* **Correct content:** (a) two *candidate* sufficient mechanisms (rigidity; decorrelation) for an `O(fresh)`
  savings bound — NOT proved equivalent, and the sharing⇒low-rank-modification step is a candidate bridge, not an
  iff; (b) a **quantitative** induced-matching tradeoff `ν_I ≤ N(1+λ)/(2d) = O(N/√d)` for Ramanujan — a
  degree-dependent squeeze, NOT an absolute expansion-vs-fresh impossibility; (c) the negative *lean* (structured
  matrices trend non-rigid) as evidence only, not a refutation; (d) effective dimension alone does not bound
  computational complexity — correct, with the caveat that the one-parameter counterexample must **charge
  parameter precision/access** (else it repeats the free-real/oracle problem of the black-hole model).
* **Where it stands:** the reduction to Valiant rigidity is a *candidate* bridge, not established; the honest
  residue is the degree-dependent induced-matching squeeze plus the non-rigidity lean.  This memo is a working
  note and is **not** a premise for anything downstream.

This is the honest terminus of a direct assault on the inequality: it maps the obstruction sharply, formalizably,
and with a negative lean, without manufacturing a closure.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
