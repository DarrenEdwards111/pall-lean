# Scope — Layer 10A: the barrier landscape (which proof strategies are blocked)

**Status: scope/audit. The constructivity strengthening is formalized
(`ComputationalDepthLayer10BarrierLandscape.lean`); relativization and algebrization are mapped here as
scope — they need oracle-separation machinery beyond a single file, and are *not* claimed.**

Goal: know **exactly** which proof strategies the three barriers block, so any future attack is checked
against them up front.

---

## The three barriers, and what each blocks

### 1. Natural proofs (Razborov–Rudich 1994) — **formalized**

A lower-bound argument is *natural* if it yields a property of truth tables that is **constructive**
(efficiently checkable), **large** (holds for most functions), and **useful** (implies a circuit lower
bound).  Under "PRFs secure against the class exist", no natural property separates the class.

* **Formalized:** Layer 9 (`razborov_rudich_barrier`) + Layer 10A
  (`fullyNatural_breaks_secureTT`).  Layer 10A makes **constructivity concrete**: a property is
  constructive iff a size-`≤ s` circuit over the `2ⁿ`-bit **truth table** decides it (`Constructive`,
  `FullyNaturalProperty`).  The barrier theorem then uses the property's *own circuit* as the distinguisher
  — the "it is an efficient test" step is a theorem, not a hypothesis.
* **What it blocks:** essentially all known combinatorial/algebraic techniques that work by exhibiting a
  *constructive, large* hardness property — including the polynomial method of Razborov–Smolensky (Layers
  3–7).  These give lower bounds only against classes (like `AC⁰[p]`) that are *too weak to contain PRFs*;
  against `P/poly` (which is believed to contain PRFs) the natural route is blocked.
* **What it does NOT block:** *non-natural* arguments — those failing constructivity (e.g. pure counting,
  as in our Shannon bound, which names no function and checks no constructive property) or largeness
  (properties special to one function, not most).  Diagonalization-flavoured and
  interactive-proof-flavoured techniques can be non-natural.

### 2. Relativization (Baker–Gill–Solovay 1975) — **scope only**

There are oracles `A, B` with `P^A = NP^A` and `P^B ≠ NP^B`.  Any technique that *relativizes* (holds for
all oracles — simulation, diagonalization, most counting) cannot settle `P` vs `NP`.

* **Not formalized here.**  A faithful formalization needs *oracle circuits/machines* and the *construction
  of the two oracles* (a diagonalization for the `≠` side) — a substantial development.  Encoding it as a
  bare `Prop` would be a vacuous socket, so it is left as scope, not asserted.
* **What it blocks:** simulation/diagonalization arguments that go through unchanged with an oracle.
* **What it does NOT block:** *non-relativizing* techniques — arithmetization (`IP = PSPACE`,
  `MIP = NEXP`) and circuit lower bounds that exploit the *internal* structure of gates (no oracle access),
  such as Razborov–Smolensky and Williams' `NEXP ⊄ ACC⁰`.

### 3. Algebrization (Aaronson–Wigderson 2008) — **scope only**

A refinement: even *arithmetization*-based techniques (which beat relativization) provably cannot prove
`NP ⊄ P/poly` or `P ≠ NP`; there are "algebraic oracle" separations.

* **Not formalized here** (same reason as relativization, plus the low-degree-extension apparatus).
* **What it blocks:** techniques that relativize *with respect to algebraic (low-degree-extension)
  oracles* — i.e. arithmetization used "as a black box".
* **What it does NOT block:** techniques using algebra *non-black-box* — which is exactly what a future
  separation is conjectured to need.

---

## The combined wall (what a future circuit-route proof must evade)

To prove an explicit `NP` function `∉ P/poly` (the input fenced in Layer 10B `p_ne_np_of_np_hard`), an
argument must simultaneously be:

1. **Non-natural** — fail constructivity or largeness (counting alone is non-natural but, being
   nonconstructive, names no explicit function; so a *constructive* explicit argument must somehow dodge
   the PRF distinguisher).
2. **Non-relativizing** — exploit gate internals, not oracle-style simulation.
3. **Non-algebrizing** — use algebra non-black-box.

No known technique is all three for `P/poly`.  This is why the rung is *open*, not *unfinished* — and why
Layer 10B keeps the lower bound as an explicit hypothesis.

## Status of this rung

* **Formalized (sorry-free):** the natural-proofs barrier with concrete constructivity (Layer 10A) on top
  of Layer 9.  This is the one barrier expressible cleanly with the circuit machinery already built.
* **Scope only (honest):** relativization and algebrization — mapped above; formalizing them faithfully
  (oracle machines + the separating-oracle constructions) is a separate, large effort, deliberately *not*
  shortcut into vacuous definitions.
