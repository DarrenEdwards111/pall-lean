# The Composite Separating Measure — the Attempt, and Where It Collapses

*Honest record of building the composite `μ` and running each layer through its filter. The composite is
a correct **checklist** for what a `P ≠ NP` separating measure must do, but it **cannot be built from what
exists**: it collapses at Layer 2, the hard-side witness, because that layer requires a super-polynomial
lower bound against general `P` — which is `P ≠ NP` itself. Demonstrated concretely, not just argued.*
*Nothing here is `P ≠ NP`.*

---

## The design (HAL 9000 / D)

```
μ(S) = hard_witness(S)
       subject to:  Layer 1  easy-side normalisation (trivial-DTM test),
                    Layer 3  no-amortization certificate (non-local),
                    Layer 4  scale bridge (super-polynomial),
                    +        extraction/transport validity.
```

Each layer blocks one failure mode. We built and tested them in order.

---

## Layer 1 — easy-side filter (trivial-DTM test): HAVE IT

A candidate `μ` must satisfy `μ(trivial 4-step DTM compilation) ≤ poly(n)`. This is the cheap first
filter, and it is decisive:

- **Raw SPDP rank of the Cook–Levin compiled polynomial FAILS it.** `GodMoveReal.compiledPoly_rank_gt_npow200_at_large_n`
  takes a bare DTM (`timeBound ≤ 4`, `numStates ≤ n`, no hardness) and gives rank `> n^200`, because the
  rank floor is a *monomial count* `C(n/3, log₂ n)`. Demonstration (`spdp_blowup.py`): for a *do-nothing*
  4-step machine at `n = 2^804`, rank `≈ 2^638536` while the P-side bound demands `≤ 2^160800` — it
  overshoots by `2^477736`. SPDP measures compilation blow-up, not hardness. Killed by Layer 1.

So Layer 1 works as a filter. The problem is Layer 2.

---

## Layer 2 — hard-side witness: COLLAPSES (the witness is in P)

The proposed hard witness is *identity minors / expansion / Tseitin rigidity* — the repo's genuine
lower-bound material. Both candidate forms fail:

- **SPDP identity-minors** → fail **Layer 1** (junk, high for the trivial machine, above).
- **Tseitin / expander rigidity** → fail **Layer 2**: the hardness is a **resolution** width bound (BSW),
  and resolution cannot do linear algebra. But a Tseitin formula is a **GF(2) linear system**, so **P
  solves it by Gaussian elimination in polynomial time.** Demonstration (`tseitin_in_P.py`):

  ```
  vertices  edges | even-charge SAT  odd-charge UNSAT | gaussian steps  ~E^2
       320    480 |           True             True   |         51040   230400
  ```

  Gaussian elimination decides every Tseitin instance in `O(V·E)` steps. **Tseitin ∈ P.** Its exponential
  hardness holds only for the weak resolution model. So the witness is *high on a P-easy object* — it
  witnesses resolution-hardness, not NP-hardness-against-`P`.

Layers 3–4 and the quotient/normalisation are never reached: there is no valid hard witness to feed them.

---

## The general obstruction — Tseitin is one instance of it

The collapse is not specific to Tseitin. **No object has a proven super-polynomial lower bound against
general `P` — because that object *is* `P ≠ NP`.** Every proven super-poly lower bound is for a *restricted
model*, and the objects are typically *`P`-easy*:

| Object | Proven super-poly LB in | The object itself is |
|---|---|---|
| Tseitin / expander | resolution (proof complexity) | **in P** (Gaussian elimination) |
| Parity | `AC⁰` (bounded depth) | **in P** (trivial) |
| Clique | monotone circuits | NP-hard, but the LB is *monotone-only* |

The pattern is exact: restricted-model lower bounds hold for objects the restricted model can't handle but
`P` can. No known method turns a restricted-model / resolution / monotone lower bound into a lower bound
against general `P`.

---

## Verdict

The composite is a **correct specification** of what a separating measure must do, and Layer 1 (the
trivial-DTM test) is a real, cheap, reusable filter. But the composite **cannot be built from what
exists**:

- Layer 1 kills SPDP-style artifacts (good), but
- Layer 2 requires an explicit object provably super-hard for general `P`, and **no such object exists** —
  the repo's assets are resolution / restricted-model lower bounds on objects that are *in `P`*.

So the whole composite reduces, at its hard-witness layer, to "exhibit an explicit object provably
super-polynomially hard for `P`" — which is the theorem, not a design step. The quotient/normalisation
problem is moot: there is no hard witness to normalise.

**Bottom line:** the three repo routes (SPDP — refuted; N-frame — `N log N`/super-linear; KRW —
`P ⊄ NC¹`) and the composite of them all terminate at the same place: a super-polynomial lower bound
against general `P` (or the non-natural separating measure that would give one). None exists; constructing
one is `P ≠ NP`. The honest state is that there is **no live `P ≠ NP` proof route**, and the missing piece
is not a design or a normalisation — it is the theorem itself.

*Demos: `spdp_blowup.py` (SPDP rank blow-up for a trivial machine), `tseitin_in_P.py` (Tseitin decided by
Gaussian elimination in poly time). Companion: `PVSNP1_SCALE_AUDIT.md`, `CookLevinFrontierRefutation.lean`,
`NFRAME_RESTRICTED_NOTE.md`. Nothing here is `P ≠ NP`, `P ⊄ NC¹`, or `NEXP ⊄ ACC⁰`.*
