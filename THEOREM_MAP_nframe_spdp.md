# N-Frame → ACC⁰ arc: theorem map (proxy separation + literal-SPDP bridge)

Branch `razborov-recoverRho-wip`. This arc implements the user's 5-step "ACC from N-Frame" plan **at the level of a
concrete N-Frame proxy**, and connects that proxy to the repo's **literal** `SPDP.spdpRank` in the non-barriered
direction. Every theorem below is clean (`[propext, Classical.choice, Quot.sound]`, no `sorry`, no bespoke axioms).

The arc is **not** `NEXP ⊄ ACC⁰` and **not** `P ≠ NP`. It is the reachable scaffold; the two walls are stated
explicitly at the end.

---

## The invariant

`NFrameComplexity F f := sInf { D | f ∈ span(sqfGens F n D) }`
  — the minimal monomial-`AND` (SYM∘AND bottom-layer) span degree of a cube function `f : (Fin n → Bool) → F`.
  The concrete proxy for the N-Frame observer-dimension / SPDP-rank / boundary holonomy.
  File: `ComputationalDepthNFrameACC0Socket.lean` (namespace `NFrameACC0`).

`nframeComplexity_le_iff_exists_lowdeg`  (`ComputationalDepthNFrameDegreeChar.lean`)
  — `NFrameComplexity F f ≤ D ↔ ∃ Q supported on |S| ≤ D, f = Multilinear.eval Q`.
  So the proxy is **exactly the minimal multilinear-representation degree of `f`** — a literal, basis-free invariant.

---

## Step 2–3: AC⁰ ⇒ low N-Frame complexity (`acc0_implies_low_nframe`)

`ComputationalDepthACC0DepthTreeField.lean` / `ComputationalDepthNFrameACC0Socket.lean`.

`AndOrTree n`  — the bounded-fan-in AC⁰ de Morgan-basis circuit (monoAND leaves, binary `AND`/`OR`, unary `NOT`).
`AndOrTree.evalT_mem_span`  — `evalT F t ∈ span(sqfGens F n t.deg)` (one structural induction from the composition laws).
`andOrTree_nframeComplexity_le`  — `NFrameComplexity (evalT F t) ≤ t.deg`.
`nframeComplexity_le_two_pow_depth`  — `NFrameComplexity (evalT F t) ≤ 2^{treeDepth t} · treeLeafWidth t`.
  ⇒ constant depth + bounded fan-in/leaf-width ⇒ bounded N-Frame complexity.

## Step 4: the hard function has high N-Frame complexity (`target_has_high_nframe`)

`ComputationalDepthNFrameMODqHigh.lean`.

`omegaFn_univ_not_mem_sqfSpan`  — `MOD_q` (`omegaFn ω univ = ω^{∑xᵢ}`, `ω` a primitive `q`-th root, `q ≥ 2`) is in no
  degree-`<⌈n/2⌉` monomial-`AND` span. Mechanism: a degree-`D` representation, via the q-ary Razborov–Smolensky
  boosting `omega_boosting_le_multilinear` at `G = univ` (`2^n` points), forces `2^n ≤ ∑_{i≤n/2+D} C(n,i)`,
  contradicting `Dimension.sum_choose_lt` when `n/2+D < n`.
`nframeComplexity_omegaFn_univ_ge`  — `NFrameComplexity (omegaFn ω univ) ≥ n − n/2 = ⌈n/2⌉`.

## Step 5: the contradiction skeleton (`acc0_proxy_separation`)

`ComputationalDepthNFrameProxySeparation.lean`.

`andOrTree_computing_modq_large`  — any AC⁰ circuit computing `MOD_q` has `2^{depth}·leafWidth ≥ ⌈n/2⌉`.
`acc0_proxy_separation`  — no AC⁰ circuit with `2^{depth}·leafWidth < ⌈n/2⌉` computes `MOD_q` (`False`).
`modq_not_computable_by_small_tree`  — for fixed `d, w` with `2^d·w < ⌈n/2⌉` (all large `n`), no depth-`≤d`,
  width-`≤w` bounded-fan-in de Morgan circuit computes `MOD_q`.
  ⇒ `MOD_q ∉ AC⁰` (bounded-fan-in, de Morgan basis), re-expressed in the N-Frame invariant.

---

## Piece (1): proxy ⟶ literal `SPDP.spdpRank` (safe direction)

Connecting the proxy to the repo's literal `SPDP.spdpRank κ ℓ p = finrank(span{ m·∂_S p : |S|=κ, deg m ≤ ℓ })`
(`PallLean/SPDPDefs.lean`, namespace `SPDP`).

Rung 1 — `nframeComplexity_le_iff_exists_lowdeg` (above): proxy = minimal multilinear degree.

Rung 2 — `ComputationalDepthNFrameSPDPBridge.lean`:
  `pderiv_totalDegree_le` — `totalDegree(∂_i p) ≤ totalDegree p` (Mathlib lacks this; proved from `pderiv_monomial`).
  `iterDerivList_totalDegree_le`, `spdpSubspace_le_restrictTotalDegree`.
  `spdpRank_le_of_totalDegree_le` — `totalDegree p ≤ D ⇒ spdpRank κ ℓ p ≤ finrank(restrictTotalDegree (ℓ + D))`.
  ⇒ **low degree caps the literal SPDP rank.**

Rung 3 — `ComputationalDepthNFrameMlPoly.lean`:
  `mlPoly Q = ∑_S C(Q S)·∏_{i∈S} Xᵢ` — the literal multilinear `MvPolynomial` of a coefficient family.
  `mlPoly_eval` — it represents the function: `eval (boolToField∘x) (mlPoly Q) = Multilinear.eval Q x`.
  `mlPoly_totalDegree_le` — degree-`≤D` coefficients ⇒ `(mlPoly Q).totalDegree ≤ D`.
  `nframeComplexity_le_imp_spdpRank_le` — `NFrameComplexity f ≤ D ⇒ ∃ literal multilinear `p` representing `f` with
    `spdpRank κ ℓ p ≤ finrank(restrictTotalDegree (ℓ + D))`.

AC⁰ side, lifted to the literal object — `ComputationalDepthNFrameSPDPAC0.lean`:
  `andOrTree_spdpRank_le` — every AC⁰ circuit `t` has a literal multilinear representative `p` with
    `spdpRank κ ℓ p ≤ finrank(restrictTotalDegree (ℓ + 2^{depth}·leafWidth))`.  (`acc0_implies_low_spdpRank`.)

So a function of low N-Frame complexity has a literal multilinear `MvPolynomial` that both **represents it** and has
**bounded literal `SPDP.spdpRank`** — the proxy and the repo's actual SPDP object, joined end to end in the safe
direction.

---

## The two walls (genuinely open / barriered — NOT crossed, NOT faked)

1. **SPDP rank LOWER bound for an explicit family** (the hard direction of piece (1)). This is the `A3` hard-survival
   obligation, audited as barriered short of `P/poly` in `ComputationalDepthSPDPFeatureProjection.lean` and
   `ComputationalDepthNFrameHypercubeConstraint.lean`. Everything above is the *safe* direction (low complexity ⇒
   *bounded* rank); the separation needs the *lower* bound, which the polynomial method does not deliver for general
   circuits.

2. **Full ACC⁰ with unbounded composite `MOD`** (extending the low side past the de Morgan basis). This is the
   composite-`MOD` barrier — exactly where the polynomial method stops. The AC⁰ side here is bounded-fan-in,
   de Morgan basis, no `MOD` gates inside the circuit.

These two are where "N-Frame must contribute something genuinely new". The arc above gives N-Frame a clean,
fully-proved formal entry point into the ACC⁰ representation work — a literal invariant, a working separation
skeleton at the proxy level, and an end-to-end safe-direction bridge to the repo's literal `SPDP.spdpRank` — without
pretending to solve either wall.
