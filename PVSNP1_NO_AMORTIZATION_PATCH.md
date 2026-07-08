# P vs NP1 Patch — The P-side Gap as No Fixed-Structure Amortization

## Scope

This note does **not** prove `P ≠ NP`.  It records the honest replacement for the
paper's vague P-side claim: the missing P-side theorem is a **no-amortization**
statement.  Without this theorem, the P vs NP1 route remains conditional.

The goal is to make the load-bearing assumption explicit enough that the paper
cannot accidentally hide it inside language such as "compiled collapse", "global
godmove", or "low SPDP rank".

---

## The corrected P-side statement

Let `S_k` denote the compiled/search object at recursion level `k`, and let
`C_k` be an efficient compiled computation/circuit/procedure for `S_k`.

The P-side cannot merely assert that `C_k` has low rank/low complexity.  It must
prove that `C_k` cannot exploit the **fixed known structure** of `S_k` to reuse
work across levels.

Define the level-`k` amortization informally as

```text
Amort(C_k) = expected fresh recursive cost - actual cost paid by C_k.
```

A concrete recurrence-shaped form is:

```text
Amort(C_k) = 2·cost(C_{k-1}) + fresh_cost_k - cost(C_k).
```

Large positive amortization means the P-side computation has reused/cancelled
structure that the lower-bound argument intended to count as fresh.

The missing theorem should therefore be stated as follows.

> **No Fixed-Structure Amortization / P-side Freshness.**
> For every polynomial-time compiled computation `C_k` of the search object
> `S_k`, recursive-level sharing is bounded:
>
> ```text
> Amort(C_k) ≤ O(size_k)
> ```
>
> equivalently,
>
> ```text
> cost(C_k) ≥ 2·cost(C_{k-1}) + fresh_cost_k - O(size_k).
> ```
>
> In words: an efficient P-side computation cannot use the fixed known global
> structure of the compiled object to avoid paying the fresh cost introduced at
> each recursive/compositional level.

This is the P-side analogue of the Freshness/no-amortization condition isolated
in the N-frame/KRW arc.

---

## How this maps onto the existing Lean status

The existing clean route is already conditional on `CookLevinFrontierHyp`.
This patch identifies what that hypothesis must contain if it is to support the
paper's intended argument:

```text
CookLevinFrontierHyp
  = P-side low-complexity/low-rank bound
    + No Fixed-Structure Amortization for the compiled search object.
```

The NP-side lower bound and arithmetic sandwich remain the proved assets.  The
P-side remains the gap unless the no-amortization theorem is proved.

Route G / Global God-Move language should be treated similarly: any proposed
rank-monotone extraction or conserved global charge must either prove the same
no-amortization property, or be stated as an explicit hypothesis.  Otherwise it
is just the load-bearing assumption in disguise.

---

## Why the theorem is hard

The N-frame/KRW arc showed the common obstruction:

| Setting | No-amortization form | Where it is proved | Where it is open |
|---|---|---|---|
| Circuit direct-sum | mixed/cancellation gates cannot do double duty | formula, linear, monotone | general circuits with negation |
| KRW composition | transcript cannot amortize outer and inner games | universal relation, monotone, strong composition | standard composition with fixed known inner function |
| P vs NP1 P-side | compiled solver cannot reuse fixed structure across recursive levels | restricted/forced-independence analogues only | general P-time compiled computation |

The obstruction is not local hardness.  It is **amortized reuse of known global
structure**.  Counting, rank, and local restriction methods can see the bulk
floor, but miss the fine increment that must accumulate across levels.

Thus the correct paper statement is conditional:

> If No Fixed-Structure Amortization holds for the compiled/search object, then
> the existing lower-bound arithmetic can accumulate the fresh cost and produce
> the desired separation.

Without this lemma, the paper proves a conditional framework, not `P ≠ NP`.

---

## Suggested insertion into the paper

Add this after the P-side compiled upper-bound section and before the final
contradiction:

> The P-side upper bound used below requires a no-amortization condition.  It is
> not enough that the compiled solver has a succinct description or that each
> local component has bounded rank.  We require that the solver cannot exploit
> the fixed known structure of the compiled search object to reuse intermediate
> work across recursive levels.  Formally, for every compiled computation
> `C_k`, the amortization
> `2·cost(C_{k-1}) + fresh_cost_k - cost(C_k)` is bounded by `O(size_k)`.  We
> call this the No Fixed-Structure Amortization hypothesis.  The separation
> theorem is conditional on this hypothesis.

Then state the final theorem as:

> **Conditional P-side theorem.**
> Assuming No Fixed-Structure Amortization for the compiled search object, the
> P-side rank/cost bound contradicts the proved NP-side lower bound; hence under
> this hypothesis `P ≠ NP`.

And explicitly add:

> We do not prove No Fixed-Structure Amortization here.  It is the remaining
> load-bearing P-side frontier.
