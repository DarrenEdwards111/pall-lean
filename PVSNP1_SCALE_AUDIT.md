# P vs NP1 Scale and Structure Audit

## Purpose

This note records the scale correction for the P vs NP1 no-amortization patch.
It prevents a conditional `N log N` / super-linear lower-bound mechanism from
being mistaken for a conditional proof of `P ≠ NP`.

The conclusion is simple:

> **No Fixed-Structure Amortization is necessary but not sufficient for `P ≠ NP`.**
> In the recursive-doubling framework currently isolated, it yields at most a
> super-linear / `P ⊄ NC¹`-scale conditional lower bound unless additional
> scale and rank-bridge hypotheses are proved.

---

## 1. The scale arithmetic

The no-amortization recurrence has the form

```text
cost(C_k) ≥ 2·cost(C_{k-1}) + fresh_k - error_k.
```

For the N-frame/W-mixer-style recursive-doubling family, the natural parameters
are:

```text
N_k = 2^k,
fresh_k = Ω(N_k),
error_k = O(N_k) or lower-order.
```

Unrolling over `k = log N` levels gives

```text
cost(C_k) ≥ Ω(N log N)
```

under a genuine no-amortization theorem.

That is super-linear.  It is **not** super-polynomial.

Therefore this recurrence is naturally a route to:

```text
super-linear circuit lower bound
```

or, on the formula-depth/KRW side,

```text
super-logarithmic formula-depth lower bound / P ⊄ NC¹-scale statement.
```

It does **not** by itself prove `P ≠ NP`, because polynomial time permits
`N^100`, `N^1000`, etc.

---

## 2. Additional structure hypotheses required

To use the no-amortization recurrence inside the P vs NP1 paper, the paper must
make the following hypotheses explicit.

### H1. Recursive-doubling structure

The compiled/search objects `S_k` must actually form a recursive/compositional
family comparable to the N-frame/W-mixer construction:

```text
S_k = Compose(S_{k-1}, S_{k-1}, mixer_k)
```

or an equivalent structure where two lower-level subobjects plus a fresh mixer
are present at every level.

Without such a structure, the recurrence

```text
2·cost(C_{k-1}) + fresh_k
```

is imported from the W-mixer framework rather than derived for the P vs NP1
compiled object.

### H2. Per-level fresh cost

The paper must prove a per-level fresh-cost lower bound in the actual measure
used by the contradiction:

```text
fresh_k = Ω(N_k)
```

or stronger.

This cannot be merely a local rank/cut/counting statement unless it is connected
to the global SPDP-rank/cost measure used in the final sandwich.

### H3. No Fixed-Structure Amortization

For every P-time compiled computation `C_k`, reuse across recursive levels must
be bounded:

```text
Amort(C_k)
  = 2·cost(C_{k-1}) + fresh_k - cost(C_k)
  ≤ allowed_error_k.
```

This is the fixed-object amortization frontier isolated in the N-frame/KRW arc.
It is open in the general case.

### H4. Cost ↔ SPDP-rank bridge

The paper must explicitly connect the cost recurrence to the SPDP-rank quantity
that appears in the NP-side lower bound and arithmetic sandwich.

There are two possible ways this could work:

1. **Super-polynomial scale bridge:** show the accumulated no-amortization
   cost/rank is super-polynomial in the original input size.
2. **Same-measure bridge:** show the accumulated no-amortization quantity is
   exactly, or lower-bounds, the SPDP-rank quantity contradicted by the proved
   NP-side lower bound.

Without this bridge, the no-amortization recurrence may be a valid lower-bound
framework while still not touching the P vs NP1 SPDP-rank contradiction.

---

## 3. Correct conditional conclusions

### What no-amortization alone supports

Under H1-H3, the honest conclusion is:

```text
cost(C_k) ≥ Ω(N log N)
```

for the recursive-doubling family.

This is a super-linear / `P ⊄ NC¹`-scale conditional result, not `P ≠ NP`.

### What is needed for P vs NP1

To state a conditional route to `P ≠ NP`, the theorem must assume H1-H4:

> If the P vs NP1 compiled/search object has recursive-doubling structure,
> per-level fresh cost, No Fixed-Structure Amortization, and a scale/SPDP-rank
> bridge to the proved NP-side lower bound, then the existing arithmetic sandwich
> can support a conditional separation.

Without H4, the strongest honest conclusion is super-linear / formula-depth
scale.

---

## 4. Paper-facing replacement language

Replace any sentence of the form:

> Assuming No Fixed-Structure Amortization, we obtain `P ≠ NP`.

with:

> Assuming recursive-doubling structure, per-level fresh cost, and No
> Fixed-Structure Amortization, we obtain an `Ω(N log N)`-type super-linear lower
> bound.  To upgrade this to the P vs NP1 contradiction, we additionally require
> a Scale Bridge connecting this accumulated cost/rank to the SPDP-rank quantity
> used in the proved NP-side lower bound.

And replace any final theorem claiming `P ≠ NP` from no-amortization alone with:

> **Conditional Super-Linear Lower Bound.**
> Under recursive structure, fresh cost, and no-amortization, the framework yields
> a super-linear lower bound.
>
> **Conditional P vs NP1 Route.**
> Under the above assumptions plus the Scale Bridge to the proved SPDP-rank
> lower bound, the P vs NP1 contradiction follows conditionally.

---

## 5. Honest bottom line

The no-amortization patch is valuable because it replaces a vague/circular
P-side claim with a named, non-circular frontier.  But it must not be allowed to
silently overclaim on scale.

The corrected state is:

```text
No-amortization alone          -> Ω(N log N) / super-linear scale.
No-amortization + Scale Bridge -> possible conditional P vs NP1 route.
Neither is currently proved in the general P-side setting.
```
