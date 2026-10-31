# Scope — Layer 10D: observer-space / branching-holography invariant

**Status: research sandbox. The candidate is a named `Prop`
(`ComputationalDepthLayer10ObserverHolography.ObserverFrontierHyp`), never asserted; only conditional
bridges are proved.  This document answers "would this work?" precisely — and the answer is: it is a
*viable framework* but provably *not a shortcut*.**

---

## 1. The candidate, precisely

An **observer/holographic invariant** is a measure `I n : ((Fin n → Bool) → Bool) → ℕ` such that

* **(A) bounded under circuits:** `f ∈ SIZE n s ⇒ I n f ≤ h s` for a polynomial `h` — small circuits
  cannot make `I` large;
* **(B) large on the target:** for the target language `L`, no polynomial `p` gives `I n (L n) ≤ h(p n)`
  for all `n` — `I` on `L` outgrows every polynomial circuit-size budget.

`ObserverFrontierHyp L` is the existence of such an `I`.  An observer-space / branching-holographic map /
Ramanujan-expander construction is one *candidate source* of `I`.

**Filling in the framework (what an actual proposal must specify):**
* *Observer space* — the space of "views" the invariant integrates (e.g. branching-program states,
  communication transcripts, a holographic boundary).
* *Branching/holographic map* — how a function's behaviour is encoded into that space.
* *The invariant* `I` — the quantity read off (rank, spectral gap, entropy, capacity, …).  Ramanujan
  expanders enter here: their optimal spectral gap is a natural candidate for a quantity that is *large*
  generically yet *bounded* for structured (small-circuit) objects.
* *Monotonicity under circuits* — the proof of (A): each gate raises `I` by at most a controlled amount.
* *The violating function* — the target `L` with provably large `I` (proof of (B)).

## 2. Conditional consequences (formalized)

* `not_ppoly_of_observerHyp : ObserverFrontierHyp L → ¬ Ppoly L`.
* `p_ne_np_of_observerHyp : (P ⊆ P/poly) → L ∈ NP/poly → ObserverFrontierHyp L → P ≠ NP/poly`.

Both are sorry-free and axiom-clean; both keep every hard input explicit.

## 3. The honest verdict: relocation, not shortcut

`not_ppoly_of_observerHyp` proves `ObserverFrontierHyp L → ¬ Ppoly L`.  Read it the right way:

> **Establishing the observer hypothesis is *at least as hard* as proving the circuit lower bound.**

So the framework does not make the problem easier — it *relocates* it to "construct `I` with (A) and (B)".
In fact the two are **equivalent**: taking `I n f :=` the minimum circuit size of `f` and `h := id`
satisfies (A) trivially (`Nat.sInf_le`) and makes (B) literally `¬ Ppoly L` (this converse uses the
standard *universality* fact "every Boolean function has a circuit", a DNF construction — stated here, not
formalized).  The observer/holographic lens is a faithful reformulation, neither weaker nor stronger.

## 4. The barriers still apply

* **Natural proofs (Layer 10A, formalized).**  The invariant induces a property `P f := "I n f is large"`.
  If `P` is *constructive* (decided by a small truth-table circuit) **and** *large*, then by (A) it is also
  *useful* (`I n f` large ⇒ `f ∉ SIZE n s`), hence a **fully natural property** — and
  `fullyNatural_breaks_secureTT` then breaks any PRF in `P/poly`.  **A working `I` must therefore be
  non-natural:** its "large-invariant" set must fail constructivity or largeness.  A "global god move" that
  merely scans the whole truth table for a pattern is constructive+large — it dies here.
* **Relativization / algebrization (Layer 10A, scope).**  If `I` is defined via oracle-style access only,
  it relativizes and cannot reach `P/poly`.  A holographic/expander invariant has a chance precisely
  because it can read gate internals / algebraic structure non-black-box — but that is a *requirement on
  the construction*, not something this framework grants.

## 4½. Concrete spectral probe (done): `specMax` fails (A) at small `n`

`ComputationalDepthLayer10SpectralProbe.lean` instantiates `I := specMax` — the largest `|Walsh/Fourier
coefficient|`, i.e. the maximum-magnitude eigenvalue of the `(ℤ/2)ⁿ` Cayley-graph structure (the spectrum
where Ramanujan bounds live) — and tests (A) by `native_decide`:

* `dictator_in_SIZE_one`: the dictator `x ↦ x₀` is a **size-1** circuit.
* `specMax_dictator_two/three/four`: its spectral quantity is `4, 8, 16` = `2ⁿ`.
* `specMax_parity_two/three`: PARITY (also small-circuit) likewise has `specMax = 2ⁿ`.

**Result: (A) fails decisively.**  A size-`1` function already attains the maximal spectral value `2ⁿ`, so
no `h` satisfies `2ⁿ ≤ h 1`.  Worse, `specMax` is *large on trivially-easy functions* — the wrong shape for
an observer invariant (which needs to be *small on all small-circuit functions*).  This is the expected
negative result: the naive Fourier/expander spectral quantity is not the invariant, and any *constructive +
large* repair is killed by the Layer 10A natural-proofs barrier.  The sandbox falsified a concrete candidate
at small `n` — exactly its job.

## 5. Verdict

`ObserverFrontierHyp` is a **legitimate, precisely-stated research target**, with proven bridges to
`L ∉ P/poly` and `P ≠ NP/poly`.  It is **not** progress on those problems: it is equivalent to the lower
bound, and any *natural* (constructive + large) instantiation is killed by the Razborov–Rudich barrier
formalized in Layer 10A.  The only way it "works" is if observer-space / branching-holography / Ramanujan
expanders yield an invariant that is genuinely **non-natural and non-relativizing** — which remains open,
and is exactly the wall §3–§4 describe.  Per discipline: stated, bridged, barrier-checked — **never
asserted**.
