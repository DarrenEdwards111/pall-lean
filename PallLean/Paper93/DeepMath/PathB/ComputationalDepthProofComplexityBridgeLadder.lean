import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinInstance
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPolynomialCalculusRung
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMetacomplexityFrontier

/-!
# Proof-complexity bridge ladder (a map, with both ends anchored to real theorems)

**STATUS: A MAP, NOT A PROOF OF P≠NP.** This file records the stepwise ladder
from a real, proved lower bound up to the P-vs-NP wall.  Each rung is a
*theorem*, a *cited known result*, or an *explicitly open bridge* — never a wish,
and never an assumed `Prop` field.  Two rungs are anchored to actual Lean facts
in this repo: the bottom (proved) and the top (proven equal to the separation).

## The ladder

* **Rung 1 — Resolution width.  PROVED (here).**
  Expander-Tseitin forces resolution width `≥ c · |S|`.  Anchored by
  `ladder_rung1_width_lower_bound` (the kernel) and `ladder_rung1_concrete`
  (the `K4` instance with expansion proved by decision procedure).

* **Rung 2 — Resolution size / space.  CITED (known, exponential).**
  Width ⇒ size: Ben-Sasson–Wigderson, "Short proofs are narrow" (2001);
  exponential resolution size for Tseitin: Urquhart (1987); space lower bounds:
  Esteban–Torán, Ben-Sasson.  Not formalized here.

* **Rung 3 — Polynomial calculus / Nullstellensatz / cutting planes /
  bounded-depth Frege.  SUBSTRATE PROVED; SYSTEM LOWER BOUNDS CITED/OPEN.**
  This repo now proves a polynomial-calculus degree/size accounting substrate in
  `ComputationalDepthPolynomialCalculusRung`: signed 3-CNF axioms have degree
  `≤ 3`, and any degree lower bound `d` rules out tree-like PC refutations of
  size `s` whenever `3 + s < d`.  The hard family-specific lower bounds remain
  literature results, not assumed Lean fields: PC degree & size lower bounds for
  Tseitin: Buss–Grigoriev–Impagliazzo–Pitassi, Alekhnovich–Razborov;
  cutting-planes lower bounds via interpolation: Pudlák (1997); bounded-depth
  (AC⁰-)Frege lower bounds for Tseitin: Håstad, Pitassi–Rossman–Servedio–Tan.

* **Rung 4 — Bounded-depth circuits (AC⁰, AC⁰[p]).  CITED (real, unconditional).**
  Parity ∉ AC⁰: Håstad; AC⁰[p] lower bounds: Razborov–Smolensky.  Genuine circuit
  lower bounds — but a *restricted* class.

* **Rung 5 — TC⁰ / NC¹ / branching programs / bounded space.  MOSTLY OPEN.**
  Unconditional TC⁰ lower bounds for explicit functions are largely open;
  Barrington (width-5 BP = NC¹) shows how quickly "bounded" stops being weak.
  This is where current techniques stall — the barriers bite here.

* **Rung 6 — General polynomial-time computation.  OPEN = P vs NP.**
  THE WALL.  A general-model lower bound for the family is *equivalent* to the
  separation — anchored by `ladder_top_rung_iff_separation` (reusing the
  metacomplexity bridge): the top rung is P≠NP itself.

## The honest reading of the climb

The ladder is real and worth climbing rung by rung: rungs 1–4 are proved or
cited, the wall sits around rung 5, and rung 6 is the separation.  But the
pattern across rungs **cannot be assumed to generalise** to rung 6.  The final
generalisation is not a way around the wall — it *is* the wall: by
`ladder_top_rung_iff_separation`, the top-rung bridge is logically equivalent to
`¬(SAT ∈ P-class)`.  So this file gives a map for gradual progress and a precise
marker of where the wall stands; it does not, and cannot, cross it by extrapolating
a pattern that "P-observers can't see" — in formal mathematics the unseen
generalisation still needs a proof, and that proof is P≠NP.
-/

namespace PallLean.Paper93.DeepMath.PathB

open Finset

/-! ## Rung 1 (PROVED): expander-Tseitin forces resolution width -/

/-- **Rung 1, general.**  On any graph with vertex expansion `c`, the F₂
combination of a medium vertex set's Tseitin constraints has width `≥ c · |S|`.
This is the proved bottom of the ladder. -/
theorem ladder_rung1_width_lower_bound
    {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]
    (G : TseitinGraph V Edge) {c : ℕ} (hexp : G.HasExpansion c)
    (S : Finset V) (h1 : 1 ≤ S.card) (h2 : 2 * S.card ≤ Fintype.card V) :
    c * S.card ≤ (edgeSupport (G.combination S)).card :=
  G.combination_support_card_ge_of_expansion hexp S h1 h2

/-- **Rung 1, concrete witness.**  The bottom rung is non-vacuously inhabited by
`K4` (expansion proved by decision procedure). -/
theorem ladder_rung1_concrete (S : Finset (Fin 4))
    (h1 : 1 ≤ S.card) (h2 : 2 * S.card ≤ Fintype.card (Fin 4)) :
    2 * S.card ≤ (edgeSupport (K4.combination S)).card :=
  K4_combination_width S h1 h2

/-! ## Rung 3 (SUBSTRATE PROVED): polynomial-calculus degree to size -/

/-- **Rung 3, signed-3-CNF polynomial-calculus substrate.**  If a signed 3-CNF
formula has polynomial-calculus degree lower bound `d`, then no tree-like
polynomial-calculus refutation of size `s` exists whenever `3 + s < d`.

This is deliberately not advertised as the full Tseitin polynomial-calculus lower
bound; it is the formal accounting layer that such a lower bound plugs into. -/
theorem ladder_rung3_polynomial_calculus_substrate
    (φ : SignedThreeCNF) {d s : Nat}
    (Hdeg : PolynomialCalculusDegreeLowerBound
      (SignedThreeCNFPolynomialCalculusAxiom φ)
      polynomialCalculusContradictionLine d)
    (hgap : 3 + s < d) :
    Not (exists D : SignedThreeCNFPolynomialCalculusRefutation φ, D.size <= s) :=
  no_small_signedThreeCNF_polynomialCalculus_refutation_of_degree_lower_bound
    φ Hdeg hgap

/-! ## Top rung (THE WALL): the general-model bridge is the separation -/

/-- **Rung 6 is the wall.**  At a channel gap, the general-model boundary bridge
is *equivalent* to "no decider in the P-time class" — i.e. the top of the ladder
is P≠NP itself, not a further generalisation one can extrapolate into.  Anchored
to the metacomplexity bridge. -/
theorem ladder_top_rung_iff_separation
    {enc : SignedFormulaEncoding} (PT : PTimeSATPolynomialTime enc)
    (O : DimensionalObserver) (B : HighDimensionalBoundary)
    (hgap : O.channelCapacity < B.independentDirections) :
    Nonempty (PTimeDeciderDimensionalForce PT O B) ↔
      MetacomplexityNoPTimeDecider enc PT :=
  observerBoundary_iff_metacomplexityObstruction PT O B hgap

/-! ## Kernel-only axiom trace -/

#print axioms ladder_rung1_width_lower_bound
#print axioms ladder_rung1_concrete
#print axioms ladder_rung3_polynomial_calculus_substrate
#print axioms ladder_top_rung_iff_separation

end PallLean.Paper93.DeepMath.PathB
