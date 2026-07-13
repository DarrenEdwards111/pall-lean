# Attack — the cross-branch no-amortization inequality (paper round 1)

Direct attack on `CE(F_{k+1}) ≥ 2·CE(F_k) + cN`, whose finishing target (per `NFrameShareChargeBound`:
`absolute_savings_bound_closes` proved, `half_charge_does_not_close` refuting the ratio route) is the **absolute**
routing bound `savings ≤ cN` on the mixer.  Result: **no closure — but the two horns unify to a single concrete
graph question, which a correct graph-theoretic tension shows leans NEGATIVE for the expander mixer, and the
truncated-family-specific escape is refuted.**  Honest, partly-negative structural map.

## 1. Both horns reduce to one question

* **Linear-mixer (rigidity) horn.**  A cross-branch share of a linear mixer `M` is a low-rank modification of `M`;
  `savings ≤ cN` holds iff `M` stays high-rank after `≤ cN` changes — i.e. `M` is **Valiant-rigid** at the fresh
  scale.
* **Nonlinear-mixer (Uhlig) horn.**  Cross-branch mass-production saves whatever sub-computation the two `F_k`
  copies share; `savings ≤ cN` holds iff the mixer **decorrelates** the two copies so their sharable overlap is
  `≤ cN`.

Both are the same statement about the *specific* mixer: **does the mixer bound cross-copy savings to `O(fresh)`?**
For the construction's Ramanujan mixer, `fresh = cN ≈ ν_I` = the induced-matching number, and the question is
whether the expander bounds savings to `O(ν_I)`.

## 2. The genuine tension: induced matching vs expansion (a correct graph fact)

`fresh` is an **induced-matching** quantity: the mixer's non-shareable capacity is the set of edges no two of
which interact — matched pairs with no cross-edges.  But:

> **A spectral expander has a SMALL induced matching.**  A size-`m` induced matching is `2m` vertices inducing
> exactly `m` edges (density `~1/(2m) ≈ 0`).  The expander mixing lemma forces a `2m`-set to induce
> `≈ d·(2m)²/(2N) ± λ·(2m)` edges; equating to `m` gives `m ≤ O(N/d)` (Ramanujan: sharper).  So `ν_I ≪ N`.

Consequence — a **hard conflict**:

* expander ⇒ `fresh = ν_I ≤ O(N/d) ≪ N` (small fresh capacity);
* large fresh (`ν_I = Θ(N)`) ⇒ the matched set is edge-sparse ⇒ **not** an expander ⇒ decorrelation lost ⇒ sharing
  allowed.

**No single mixer graph is both large-fresh and anti-sharing.**  So the earlier hope — "use a denser mixer to
force `fresh ~ N` so `savings ≤ N ≤ cN` closes trivially" — is impossible: forcing `fresh ~ N` destroys the
expansion that prevents sharing.  This is the graph-theoretic incarnation of the rigidity difficulty for this
family, and it is clean and (via the expander mixing lemma) formalizable.

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

## 5. Verdict

* **No closure**, and no false one.
* **Genuine content:** (a) both horns unify to "does the Ramanujan mixer bound cross-copy savings to `O(fresh)`?";
  (b) the induced-matching-vs-expansion tension — a correct, clean, formalizable graph fact — proves you cannot
  buy large fresh capacity without losing the expansion that prevents sharing; (c) the honest **negative lean**
  (structured matrices trend non-rigid, so the specific mixer likely fails); (d) the truncated-family escape
  (effective dimension) is **refuted** (metric ≠ complexity).
* **Where it now stands:** the inequality's obstruction is exactly *rigidity of the mixer at the induced-matching
  scale*, it leans false for the construction, and closing it needs an explicit rigid object — i.e. the open
  Valiant problem, unchanged in strength but now pinned to a single, checkable graph quantity.

This is the honest terminus of a direct assault on the inequality: it maps the obstruction sharply, formalizably,
and with a negative lean, without manufacturing a closure.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
