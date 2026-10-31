# P vs NP1 Patch — The P-side Gap as No Fixed-Structure Amortization

## Scope

This note does **not** prove `P ≠ NP`.  It records the honest replacement for the
paper's vague P-side claim: one missing P-side theorem is a **no-amortization**
statement.  Without this theorem, the P vs NP1 route remains conditional.

It also records an important scale correction: the recurrence displayed here is
an `N log N` / super-linear mechanism.  By itself it is **P vs NC¹-scale**, not
`P ≠ NP`-scale.  To support a `P ≠ NP` conclusion, the paper needs additional
super-polynomial amplification or a direct bridge from the cost/rank recurrence
to the proved super-polynomial NP-side rank lower bound.  See
`PVSNP1_SCALE_AUDIT.md` for the full scale-and-structure audit.

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

For a recursive-doubling family of the N-frame/W-mixer type, the missing theorem
should therefore be stated as follows.

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
P-side remains the gap unless the no-amortization theorem is proved **and** the
paper supplies the correct scale bridge from this recurrence to the SPDP-rank
contradiction.

In particular, this patch does not by itself turn `CookLevinFrontierHyp` into a
proof of `P ≠ NP`.  It identifies one necessary subcondition.  The full P-side
hypothesis must include at least:

1. a recursive/compositional structure for the compiled/search objects `S_k`;
2. a per-level fresh-cost lower bound `fresh_cost_k` in the relevant rank/cost
   measure;
3. no fixed-structure amortization for P-time compiled computations;
4. a scale bridge showing that the accumulated cost/rank is super-polynomial or
   otherwise contradicts the proved NP-side lower bound.

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

Thus the correct paper statement is conditional, but the conditional must be
stated at the right scale:

> If the compiled/search object has the recursive fresh-cost structure above,
> and No Fixed-Structure Amortization holds, then the recurrence accumulates a
> super-linear `N log N`-type lower bound.

That conclusion is meaningful, but it is **not yet `P ≠ NP`**.  To obtain
`P ≠ NP`, the paper must additionally prove a super-polynomial scale bridge or
show that the accumulated no-amortization cost is exactly the SPDP-rank quantity
that contradicts the proved NP-side lower bound.

Without these extra scale assumptions, the paper proves a conditional framework,
not `P ≠ NP`.

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

Then state the conditional theorem at the correct strength:

> **Conditional no-amortization theorem.**
> Assuming the compiled search objects form a recursive fresh-cost family and
> No Fixed-Structure Amortization holds for them, the recurrence yields an
> accumulated super-linear lower bound of `N log N` type.

If the paper wants a `P ≠ NP` theorem, add a separate hypothesis:

> **Scale-bridge hypothesis.**
> The accumulated no-amortization cost/rank is super-polynomial in the original
> input size, or is the same SPDP-rank quantity used in the proved NP-side lower
> bound.

Only under **No Fixed-Structure Amortization + Scale Bridge** may the final
statement be phrased as a conditional route to `P ≠ NP`.

And explicitly add:

> We do not prove No Fixed-Structure Amortization or the required Scale Bridge
> here.  These are the remaining load-bearing P-side frontiers.
