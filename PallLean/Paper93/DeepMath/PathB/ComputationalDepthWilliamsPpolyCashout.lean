/-!
# The Williams cash-out: a Circuit-SAT algorithm ⟹ `NEXP ⊄ P/poly`

The fuzzy pass identified the *one* technique that provably threads all three barriers
(relativization, natural proofs, algebrization): **Williams' algorithmic method** — "a faster-than-
brute-force SAT algorithm yields a circuit lower bound."  This file formalizes its logical skeleton for
the `P/poly` target, as an honest conditional with named sockets.

The chain (Williams 2010/2011, here for `C = P/poly`):

1. Assume `NEXP ⊆ P/poly` (for contradiction).
2. **`ikw_easy_witness`** — the Impagliazzo–Kabanets–Wigderson easy-witness lemma: then `NEXP` has
   *succinct (easy) witnesses*.  *(A proven theorem, socketed here — not re-proved.)*
3. **`algorithmic_speedup`** — combine the easy witnesses with a *nontrivial Circuit-SAT algorithm* to
   get a nondeterministic `NEXP`-simulation faster than the hierarchy allows.  *(Williams' combination
   step — proven, socketed.)*
4. **`nondet_time_hierarchy`** — the nondeterministic time hierarchy theorem forbids that speed-up.
   *(A proven theorem, socketed.)*
5. Contradiction, so `NEXP ⊄ P/poly`.

* **`williams_cashout` (proved)** — `CircuitSATFast → ¬ NEXPinPpoly`, i.e. a nontrivial Circuit-SAT
  algorithm forces `NEXP ⊄ P/poly`.

**Honest scope — two things stated flatly.**
- **The only *open* ingredient is `CircuitSATFast`**: a Circuit-SAT algorithm for general poly-size
  circuits beating brute force by a super-polynomial factor.  The other three sockets
  (`ikw_easy_witness`, `algorithmic_speedup`, `nondet_time_hierarchy`) are *proven* theorems in the
  literature, socketed here, not re-derived.  So "how to get the lower bound" is, honestly, an
  **algorithms** problem — find the algorithm, and the bound falls out the back.  That algorithm is
  itself a major open target (SETH-adjacent), not known.
- **The output is `NEXP ⊄ P/poly`, not `NP ⊄ P/poly`.**  The method runs through the nondeterministic
  *exponential*-time hierarchy; scaling it down to `NP` is a separate famous open problem.  This is the
  barrier-threading route, and its ceiling is `NEXP`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.WilliamsPpolyCashout

/-- **The Williams cash-out (proved).**  Given a nontrivial Circuit-SAT algorithm (`hAlg`), together
with the three proven-in-literature ingredients — the IKW easy-witness lemma, Williams' algorithmic
speed-up, and the nondeterministic time hierarchy — the assumption `NEXP ⊆ P/poly` is refuted:
`NEXP ⊄ P/poly`.  The one open input is the algorithm `CircuitSATFast`; the rest are named sockets for
established theorems.  Output ceiling: `NEXP`, not `NP`. -/
theorem williams_cashout
    (NEXPinPpoly CircuitSATFast EasyWitness FastNEXPAlg : Prop)
    (ikw_easy_witness : NEXPinPpoly → EasyWitness)
    (algorithmic_speedup : CircuitSATFast → EasyWitness → FastNEXPAlg)
    (nondet_time_hierarchy : FastNEXPAlg → False)
    (hAlg : CircuitSATFast) :
    ¬ NEXPinPpoly :=
  fun hNEXP => nondet_time_hierarchy (algorithmic_speedup hAlg (ikw_easy_witness hNEXP))

/-- **The barrier-threading form, isolated (proved).**  Reading it as "algorithm ⟹ lower bound": with
the established sockets fixed, the *existence* of a nontrivial Circuit-SAT algorithm is exactly what is
missing between here and `NEXP ⊄ P/poly`.  This is the honest relocation of the problem from proving
hardness to finding an algorithm. -/
theorem algorithm_is_the_missing_input
    (NEXPinPpoly CircuitSATFast EasyWitness FastNEXPAlg : Prop)
    (ikw_easy_witness : NEXPinPpoly → EasyWitness)
    (algorithmic_speedup : CircuitSATFast → EasyWitness → FastNEXPAlg)
    (nondet_time_hierarchy : FastNEXPAlg → False) :
    CircuitSATFast → ¬ NEXPinPpoly :=
  fun hAlg hNEXP => nondet_time_hierarchy (algorithmic_speedup hAlg (ikw_easy_witness hNEXP))

end PallLean.Paper93.DeepMath.PathB.WilliamsPpolyCashout

#print axioms PallLean.Paper93.DeepMath.PathB.WilliamsPpolyCashout.williams_cashout
#print axioms PallLean.Paper93.DeepMath.PathB.WilliamsPpolyCashout.algorithm_is_the_missing_input
