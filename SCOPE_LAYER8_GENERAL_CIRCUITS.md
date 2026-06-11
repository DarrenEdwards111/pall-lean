# Scope — Layer 8: General (unrestricted-depth) Circuit Lower Bounds

**Status: scope/audit only. No proofs of open results. This honestly fences what is open vs. achievable
and fixes the first achievable rung.**

The ladder (user's framing), bottom to top:
`general circuit lower bounds` → `deep NP ⊄ AC⁰[p]` → `NP ⊄ ACC⁰` → `P ≠ NP`.

This document concerns the bottom: **lower bounds against general Boolean circuits** (arbitrary depth,
no gate-modulus restriction — the model underlying `P/poly`).

---

## 1. The blunt truth about this rung

**A super-polynomial general-circuit lower bound for an *explicit* function is OPEN and far beyond current
technique.**

* Best known lower bounds for explicit functions against general fan-in-2 circuits are **linear**:
  ≈ `3n − o(n)` (Blum), ≈ `5n − o(n)` (Iwama–Lachish–…, Find–Golovnev–Hirsch–Kulikov). No explicit function
  is known to require even `n·log n` general circuit size.
* A super-polynomial bound for an explicit (e.g. `NP`) function would give `NP ⊄ P/poly`, hence (with
  Karp–Lipton) collapse consequences, and is essentially the circuit route to `P ≠ NP`.
* **Barriers** (must be respected; none of these are "bugs to fix"): natural proofs (Razborov–Rudich),
  relativization (Baker–Gill–Solovay), algebrization (Aaronson–Wigderson). The RS/`MOD_q` machinery of
  Layers 3–7 is *natural* and *depth-restricted*; it gives **no** leverage on general circuits.

**Therefore Layer 8 will NOT claim an explicit super-polynomial general-circuit lower bound.** Anything
that looks like one is either false or hiding an unproved hypothesis — to be flagged, never asserted.

## 2. What IS honestly achievable here (the real rungs)

* **(R0) The general circuit model + size + `SIZE(s)` / `P/poly`.**  A clean fan-in-`≤2` Boolean circuit
  type with a finite gate set so that *size-bounded circuits are countable* (needed for any counting
  argument). Pure infrastructure; no lower bound claimed.
* **(R1) Shannon counting lower bound.**  *Most* Boolean functions on `n` bits require circuits of size
  `≳ 2ⁿ/n`: the number of circuits of size `≤ s` is `< 2^{2ⁿ}` (the number of functions) once `s` is below
  the threshold, so a hard function **exists**. This is **classical, provable, barrier-free** (a counting
  argument, not a "natural property" against a function class). It is a genuine general-circuit lower
  bound — but **nonconstructive**: it does not exhibit an explicit hard function.
* **(R2, optional/harder) Explicit linear bounds** (e.g. a `2n`–`3n` gate bound for a concrete function).
  Formalizable in principle, fiddly; lower priority than R0/R1.

**The honest first deliverable of Layer 8 is R0 + R1.** It is real (a theorem about circuit size that is
*not* in the completed layers), and it is the correct foundation; it makes zero progress toward the
*explicit* super-poly frontier and will say so.

## 3. Why R1 is honest and the frontier is not

R1 proves `∃ f, every circuit computing f has size > s`. That is a lower bound on the **maximum** circuit
complexity over all functions — provable by counting. The OPEN frontier asks for a lower bound on the
circuit complexity of **one named, explicit** `f` (e.g. SAT, or any `NP`/`E` function). The gap between
"some function is hard" (easy, R1) and "this explicit function is hard" (open, frontier) is the entire
difficulty of circuit complexity. R1 does not shrink that gap; it is the floor everyone already stands on.

## 4. Plan for R0 + R1 (sorry-free, no custom axioms, no open claims)

1. **`Circuit n`** — inductive fan-in-`≤2` Boolean circuit on `n` inputs: `input i | const b | not c |
   and c₁ c₂ | or c₁ c₂` (finite gate set ⇒ countable). `eval : Circuit n → (Fin n → Bool) → Bool`,
   `size : Circuit n → ℕ` (# gates).
2. **`Computes` / `circuitComplexity`** — a function `f : (Fin n → Bool) → Bool` is computed by `c` iff
   `∀ x, c.eval x = f x`; `SIZE n s := { f | ∃ c, c.size ≤ s ∧ Computes c f }`.
3. **Counting bound** — `Fintype`/`Finset.card` argument: `card { c : Circuit n // c.size ≤ s } ≤ G(n,s)`
   for an explicit `G` (e.g. `(n + s + 2)^{O(s)}`), and `card (Fin n → Bool) → Bool = 2^{2ⁿ}`.
4. **`exists_hard_function`** — if `G(n,s) < 2^{2ⁿ}` then `∃ f, f ∉ SIZE n s` (pigeonhole / `card` strict
   inequality). Instantiate `s ≈ 2ⁿ/n` to state the Shannon bound.

Steps 1–2 are infrastructure; 3 is the technical core (bounding `card` of size-`≤s` circuits); 4 is a
short cardinality argument. **No step asserts an explicit lower bound.**

## 5. Guardrails (unchanged)

Sorry-free; no custom axioms; do not edit Layers 3–7 or `Step4Compiler`; **open targets stay open** —
R1's nonconstructive existence is *not* dressed up as an explicit bound, and no `P≠NP` / `NP ⊄ P/poly` /
explicit-super-poly progress is claimed. Small buildable commits; `lake build` + `#print axioms` per
capstone; push each clean commit. The explicit-super-poly frontier and its barriers are stated as the
permanent open boundary above this rung.
