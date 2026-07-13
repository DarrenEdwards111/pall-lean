# SCOPE: the shrinkage / Andreev `n^{3-o(1)}` route

`ComputationalDepthNeciporukCeiling` names this as the technique that goes *above* the `n²/log n` subfunction-
counting ceiling. This assesses whether it is a route to `P ≠ NP`, and what it costs to build. It is a **map of
the method and its walls**, not an attempt. **Verdict: it is a genuine, stronger method than Nečiporuk — but for a
*different, more restricted* model, with its *own* proven polynomial ceiling, aimed at the *wrong target* for
`P` vs `NP`. It is not a separation route; as a restricted result it is a large, deep new arc, not a quick build.**

## 1. What the method is

The technique proves **de Morgan formula-size** lower bounds (formulas over `{∧, ∨, ¬}`, fan-in 2 — the basis
`U₂`) via **shrinkage under random restrictions**:

* **Shrinkage.** A de Morgan formula of size `L`, hit by a random restriction `ρ` that keeps each variable alive
  independently with probability `p`, shrinks in expectation to size `O(p^Γ · L)`, where `Γ` is the *shrinkage
  exponent*. Subbotovskaya (1961): `Γ ≥ 1.5`. Håstad (1998): the tight `Γ = 2`.
* **Andreev's function.** `A(x,y)` uses `log n` "address" bits to select a block and computes the parity of a
  chosen block — engineered so that after a `p`-restriction some parity block survives with *all* its variables
  alive, forcing `L(A|ρ) ≥ (block size) − 1` (parity needs linear formula size).
* **Combining** shrinkage (upper bound on `L(A|ρ)` in expectation) with the survival lower bound gives
  `L(A) ≥ n^{Γ+1−o(1)}`, i.e. `n^{3−o(1)}` with `Γ = 2` (Håstad; constants/`o(1)` refined by Tal 2014 and others).

So it is a **restriction/probabilistic** method, categorically different from subfunction counting.

## 2. It genuinely beats Nečiporuk — but only in a different basis

For **de Morgan (`U₂`) formulas**, `n^{3−o(1)}` is the record, above Nečiporuk's `n²/log n`. That is a real step.

But the repository's Nečiporuk arc proves bounds for **`B₂` formulas** (all binary gates — `litCount` over `Tok =
gates ∪ literals`). The bases matter: the shrinkage exponent for `B₂` is only `Γ = 1` (a `B₂` formula need not
shrink — e.g. XOR-heavy formulas), so shrinkage gives **nothing better than the Nečiporuk `n²/log n` for `B₂`**.
The cubic bound lives *only* in the more restricted `U₂`. So "shrinkage is the next step after Nečiporuk" is
basis-dependent: it means *switch to the weaker `U₂` model* and get a higher exponent there — not a strictly
stronger statement in the model the repo uses. A `U₂` lower bound bounds a *subset* of `B₂` formulas.

## 3. It has its own proven polynomial ceiling

`Γ = 2` is **tight** (Håstad): de Morgan formulas provably do *not* shrink faster than `p²`. So the shrinkage
method's ceiling for Andreev-type functions is `n^{3−o(1)}` — it **provably cannot exceed cubic** by this route.
This is the *same species of wall* as the Nečiporuk `n²/log n` ceiling (`NeciporukCeilingTotal.neciporuk_ceiling`):
a hard, method-intrinsic **polynomial** cap. Shrinkage sits one exponent higher (cubic vs quadratic) and in a
smaller basis, but it is still polynomially capped, so — exactly like Nečiporuk — it can never certify a
super-polynomial bound, and therefore cannot separate any super-polynomial class.

## 4. It is aimed at the wrong target for `P` vs `NP`

Even a *hypothetical* super-polynomial de Morgan formula lower bound (which shrinkage cannot give) would not
separate `P` from `NP`:

* Formula size bounds **formula depth ≈ `NC¹`**, a *subclass* of `P`. A super-polynomial formula lower bound for
  an `NP` function shows `NP ⊄ NC¹` — implied by, but *not equal to*, `P ≠ NP`, and itself wide open.
* The program that pushes formula lower bounds toward a *class* separation is **Karchmer–Raz–Wigderson** (formula
  depth via composition / communication), whose target is `NC¹ ⊊ P` (formula depth vs time) — again *not* `P` vs
  `NP`, and stuck (progress by Dinur–Meir and others, no separation).

So there are two independent target gaps on top of the cubic cap: shrinkage bounds *formula size* (not time), and
even its natural class-level ambition (`NC¹ ⊊ P` via KRW) is a *different* open problem from `P` vs `NP`.

## 5. It is a natural proof

Restriction/switching-lemma methods are the archetypal **natural proofs** (Razborov–Rudich name them explicitly):
the underlying property ("shrinks under random restrictions" / "sensitive to restrictions") is constructive and
large. This is fine at the formula/`AC⁰` level, but any attempt to lift shrinkage-style arguments to super-
polynomial `P/poly` circuit bounds runs into the natural-proofs barrier. Shrinkage is powerful precisely where
natural proofs are permitted (restricted models) and blocked precisely where a separation would live.

## 6. Verdict and recommendation

The shrinkage/Andreev route is **not** a path to `P ≠ NP`. Three independent walls:

1. **Proven polynomial ceiling** — `Γ = 2` is tight (Håstad), capping the method at `n^{3−o(1)}`, the same *kind*
   of hard polynomial wall as the Nečiporuk `n²/log n` cap this repo just formalized;
2. **Wrong target** — it bounds `U₂`/`NC¹` formula size, not time; even super-polynomial formula bounds give
   `NP ⊄ NC¹` (or, via KRW, `NC¹ ⊊ P`), *different* open problems from `P` vs `NP`;
3. **Natural proof** — a restriction method, barred from the super-polynomial `P/poly` regime.

As a **restricted lower bound** it is genuine and famous, but building it is a **major, deep new arc**, not a quick
by-product: the shrinkage lemma is a real probabilistic argument over random restrictions (expectation of formula
size under `ρ`), far heavier than the counting arguments behind the completed Nečiporuk × BP-width matrix. The
tractable entry point is **Subbotovskaya's `Γ = 1.5`** (elementary, gives `n^{2.5−o(1)}` for Andreev); **Håstad's
`Γ = 2`** (the `n^3` record) is substantially harder; **KRW composition** (toward `NC¹ ⊊ P`) is a research program,
not a formalization target.

Honest recommendation: **do not pursue shrinkage as a route to `P ≠ NP`** — it converges to the same place every
other angle does (a proven polynomial method-ceiling, plus natural proofs, plus a target short of `P` vs `NP`). If
a *new restricted arc* is wanted for its own sake, a formalized **Subbotovskaya shrinkage + Andreev `n^{2.5}`**
bound would be a real, publishable-species result that beats `n²/log n` in the `U₂` model — but it is a large lift,
and the clean, complete, banked result remains the `B₂` Nečiporuk × BP-width matrix. Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.
