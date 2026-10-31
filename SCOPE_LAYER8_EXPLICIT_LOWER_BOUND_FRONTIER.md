# Scope — The Explicit-Lower-Bound Frontier (the cliff above Shannon)

**Status: scope/audit only. No theorem claims. This maps the open cliff and why the next jump is hard —
it is *not* a proof effort.**

We have just finished the classical **nonconstructive** general-circuit lower bound
(`exists_function_needing_exp_size`: for every `n`, *some* Boolean function needs circuit size `> 2ⁿ/(n+6)
− 1 ≈ 2ⁿ/n`).  This document explains precisely why the *next* step — naming an **explicit** function with
a super-polynomial lower bound — is open, and why none of the formalized machinery (Layers 3–8) crosses it.

---

## 1. The one-word gap: "some" vs "this"

| Have (done, sorry-free) | Want (open) |
|---|---|
| `∃ f, f` needs size `≳ 2ⁿ/n` (`exists_function_needing_exp_size`) | a **named, explicit** `f` (SAT, an `NP`/`E` function, …) needs size `≥ n^{ω(1)}` |
| proof = **counting** (`#circuits < #functions`) | proof = ??? (no technique known) |

The counting argument gives existence *because* it inspects no particular function — it just compares
cardinalities.  The instant you demand a **specific** `f`, counting is useless: you must *prove* a hard
combinatorial property of that one `f`, and that is the entire unsolved core of circuit complexity.  The
gap is not a missing lemma; it is the subject.

## 2. The actual state of explicit general-circuit lower bounds

* Best known explicit lower bounds against general fan-in-2 circuits are **linear**: `≈ 3n − o(n)` (Blum
  1984), `≈ 5n − o(n)` (Find–Golovnev–Hirsch–Kulikov 2016, building on Iwama–Lachish, Demenkov–Kulikov).
* **No** explicit function is known to require even `n·log n` general-circuit size.
* So the climb from here is not "tighten a bound" — it is a `n^{ω(1)}` jump with *no* known method, for any
  explicit function.

## 3. The ladder above, and what each rung would imply

* **Explicit super-poly general-circuit bound for an `NP` function ⟺ `NP ⊄ P/poly`.**  Would, via
  Karp–Lipton (`NP ⊆ P/poly ⇒ PH = Σ₂`), collapse the polynomial hierarchy if false — and is the standard
  *circuit* route toward `P ≠ NP`.
* `NP ⊄ P/poly ⇒ P ≠ NP` (nonuniform separation implies uniform).
* `P ≠ NP` sits at the top; the circuit route goes *through* `NP ⊄ P/poly`, which goes through an explicit
  super-poly bound — the rung we cannot reach.

## 4. Why the formalized machinery does not cross the cliff

* **Shannon counting (Layer 8)** is nonconstructive *by design*; it cannot name a function. Pushing it to a
  specific `f` is not a refinement — it abandons the only tool (counting) that made it work.
* **Razborov–Smolensky (Layers 3–7)** is *depth-restricted* and *single-prime*; it gives explicit bounds
  only against `AC⁰[p]` (PARITY, `MOD_q`), which are *easy* functions, and says nothing about general
  circuits. (Layer 7's `parity_not_in_nonuniform_AC0p` is an explicit bound — but against a far weaker
  model, and for an easy language.)

## 5. The barriers (why no one has a method — to be respected, not "fixed")

* **Natural proofs (Razborov–Rudich 1994).**  Most known explicit lower-bound techniques yield a *natural
  property*: a property of truth tables that is (i) *constructive* (efficiently checkable), (ii) *large*
  (holds for most functions), (iii) *useful* (implies a circuit lower bound).  Under standard cryptographic
  assumptions (pseudorandom functions in the class), **no** natural property can separate the class — so a
  proof must be *unnatural*.  Note the contrast that makes our Shannon bound *fine*: it is large and useful
  but it is **not** a proof *about a specific function via a constructive property** — it is a pure
  cardinality count, so the barrier simply does not apply to "some function is hard." An *explicit* bound
  almost certainly would expose a natural property and hit the wall.
* **Relativization (Baker–Gill–Solovay 1975).**  Techniques that relativize cannot resolve `P` vs `NP`;
  diagonalization/simulation arguments relativize.
* **Algebrization (Aaronson–Wigderson 2008).**  Even arithmetization-based techniques (which beat
  relativization for `IP = PSPACE`, `NEXP ⊄ ACC⁰`) provably cannot reach `NP ⊄ P/poly` / `P ≠ NP`.

Any genuine attempt at the explicit frontier must evade **all three** barriers simultaneously. No known
technique does. This is why the rung is *open*, not *unfinished*.

## 6. What an honest Layer-9 could and could not be

* **Could (honest, achievable):** formalize *infrastructure* and *known* facts — `P/poly` definitions,
  Karp–Lipton-style implications as *conditional* theorems, the natural-proofs framework as a *definition*
  + the conditional "natural property ⇒ break PRF" statement (a theorem *about the barrier*, not a circuit
  lower bound), explicit *linear* bounds (Layer-8 R2). All of these are real and barrier-compatible.
* **Could not (would be fake):** an unconditional explicit super-poly general-circuit lower bound,
  `NP ⊄ P/poly`, or `P ≠ NP`. These are open; any Lean artifact claiming them is either false or smuggling
  the hard step into an unproved hypothesis. Per project discipline, such a step is only ever an **explicit
  named hypothesis**, never asserted.

## 7. Recommendation

Treat §6's "could" list as the menu for any further climbing, always with the open rung stated as open.
The completed, honest result to stand on is the pair:
`Layer 7` (explicit easy-function bounds vs `AC⁰[p]`) + `Layer 8` (nonconstructive Shannon bound vs general
circuits).  The cliff between them and `NP ⊄ P/poly` is mapped here and is not to be papered over.
