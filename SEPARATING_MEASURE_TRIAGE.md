# Separating Measure Triage — P vs NP Route Filter

## Purpose

This note records the first-filter triage for any future candidate separating
measure `μ` intended to support a `P ≠ NP` route.

The immediate lesson from the SPDP/Cook--Levin audit is:

> Test `μ` on a trivial bounded-time DTM compilation first.

If `μ` is already high on a do-nothing / 4-step machine, then `μ` is measuring
compilation blow-up or representation structure, not computational hardness.
Discard it before doing any NP-side work.

---

## Required properties of a P vs NP separating measure

A candidate measure `μ` must satisfy all of the following:

1. **Low on easy compiled computations**

   ```text
   μ(P-compiled / trivial DTM object) ≤ poly(n)
   ```

2. **High on an NP-hard/search object**

   ```text
   μ(NP-hard/search object) ≥ superpoly(n)
   ```

3. **Non-circular**

   `μ` must not simply be circuit size, multiplicative complexity, or another
   direct restatement of the lower bound to be proved.

4. **Correct scale**

   The measure must naturally produce super-polynomial separation, not merely
   `N log N`, super-linear, super-log-depth, or other NC¹-scale bounds.

5. **Proved extraction/transport**

   Any map from the P-side compilation to the NP-side hard object must be a
   theorem, not an axiom or disguised assumption.

---

## Triage table

| Candidate measure `μ` | Trivial-DTM test | Scale | Non-circular? | Verdict |
|---|---:|---:|---:|---|
| Raw SPDP rank of Cook--Levin compiled polynomial | fails: high even for do-nothing / bounded-time DTM | n/a | n/a | dead; compilation artifact |
| Tensor rank of compiled tensor | fails: same compilation blow-up | n/a | n/a | dead; SPDP-type artifact |
| Circuit size / cbudget | passes: O(1) for trivial machine | right scale in principle | fails | circular: this is the lower bound itself |
| Multiplicative complexity | passes on trivial machine | right scale in principle | fails | circular / essentially circuit lower bound |
| Formula depth / KW communication | passes | wrong scale: NC¹ / super-log | yes | useful for P vs NC¹, not P vs NP |
| Matrix rigidity | maybe passes | wrong scale: super-linear / Valiant frontier | yes | wrong scale + open |
| Algebraic degree | passes | wrong scale: ≤ n | yes | does not separate P from NP |
| Proof size: Frege / EF | passes for simple objects | possible, but different question | yes | NP vs coNP / proof complexity frontier |
| Sign-rank / margin / approximate rank | maybe passes | different scale/class | yes | threshold/PP/communication frontier |
| Information / entropy | not a circuit measure | capped / wrong scale | n/a | information-vs-size gap |
| Fixed-object exploitation resistance | undefined | would need superpoly | would need non-circularity | name for missing object, not a measure yet |

---

## What the triage shows

The trivial-DTM test is a good first filter.  It kills SPDP and other raw
compiled-monomial/rank measures because they are high even for easy machines.

But passing the trivial-DTM test is not enough.  Every surviving candidate falls
into one of three buckets:

1. **Circular**

   Circuit size and multiplicative complexity pass the easy-object test and have
   the right scale, but lower-bounding them is essentially the original P vs NP
   problem.

2. **Wrong scale**

   Formula depth, KW communication, matrix rigidity, and degree can give
   meaningful restricted lower bounds, but they do not naturally reach
   super-polynomial P-vs-NP scale.

3. **Different frontier**

   Proof complexity, sign-rank, approximate rank, and related measures are real
   research programs, but they target different separations/classes.

---

## Natural proofs warning

A working `μ` would need to be:

```text
low on simple/easy objects,
high on random or NP-hard objects,
constructively checkable enough to prove/use,
and large enough to separate.
```

That is exactly where the Razborov--Rudich natural-proofs barrier applies.  If
`μ` is constructive and large, it threatens pseudorandom generators.  Therefore
a successful P-vs-NP measure likely has to be non-natural in a substantive way:
not merely a computable large property of truth tables or compiled polynomials.

The undefined candidate called **fixed-object exploitation resistance** is a name
for this missing kind of object.  It would have to quantify how much an efficient
computation can exploit a fully known random-looking/search object, while being
non-natural enough to avoid the natural-proofs barrier and strong enough to give
super-polynomial scale.

No such measure is currently known here.

---

## Permanent rule for future candidates

Before developing any candidate `μ`, run this checklist:

1. Evaluate or bound `μ` on a trivial bounded-time DTM compilation.
2. If high, discard it as a representation/compilation artifact.
3. If low, check scale: can it ever give super-polynomial lower bounds?
4. If yes, check circularity: is it just circuit size or equivalent?
5. If non-circular and right-scale, check natural-proofs risk.
6. Only then attempt NP-side lower bounds or extraction theorems.

Current honest state:

```text
No live P ≠ NP route is present in the repo.
The missing object is a non-natural, non-circular, right-scale separating measure
with a proved P-side upper bound and proved NP-side lower bound/transport.
```
