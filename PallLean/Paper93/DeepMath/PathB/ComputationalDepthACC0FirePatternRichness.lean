import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CoFiring

/-!
# Fire-pattern richness — strengthening co-firing to *many distinct* patterns, + the implication bridge

Entry 260's `CoFiringRich` ("some input fires `≥ k` gates") is existential — necessary but, as the user noted, probably
too weak.  This file strengthens it to **pattern richness**: the firing map produces *many distinct* fire-patterns
(`PatternRich`).  This sharply separates the families and is the right shape for the count lower bound, and it states
the implication bridge to the `ACC⁰[composite]` component.

**The strengthened invariant.**  `PatternRich gates k` := the image of `firePattern gates` has `≥ k` elements (at least
`k` distinct fire-patterns).  Parallel/disjoint families have few, small patterns; the genuine hard families have
exponentially many, large ones.

## What is proved (clean axioms, no `sorry`)

* **`PatternRich gates k`** — `≥ k` distinct fire-patterns (`#(image (firePattern gates) univ)`).
* **`dictator_firePatternImage_eq_univ`** / **`dictator_patternRich`** (PROVED) — the dictator/`MOD_q` family realizes
  *every* subset as a fire-pattern, so it has `2^s` distinct patterns: `PatternRich (fun i x => x i) (2^s)` —
  exponentially rich.
* **`parallel_no_large_patterns`** (PROVED) — the parallel affine family has *no* fire-pattern of size `≥ 2` (all
  patterns `≤ 1`, entry 259): no co-firing, no large patterns.  It fails pattern richness in the strong (large-pattern)
  sense.

## The sockets (named, not proved)

* **`PatternRichCountObstruction`** — the strengthened socket: `AlgExpander gates → PatternRich gates (exp) →
  CrossFieldCountHard gates`.  (Pattern richness, not just one co-fire.)
* **`crossFieldHard_to_ACC0Component`** — the implication bridge: `CrossFieldCountHard gates → ACC0CompositeComponent`
  (the cross-field count hardness *is* the `ACC⁰[composite]` lower-bound component, upstream of Williams
  `NEXP ⊄ ACC⁰`).  Proven instance: the dictator/`MOD_q` family, via the in-arc `Layer4.mod_q_indicators_false`.

## Honest scope

This strengthens the co-firing invariant to *many distinct fire-patterns* and proves the separation in the strong sense
(dictator/`MOD_q`: `2^s` patterns; parallel: none of size `≥ 2`), and states the implication bridge to the
`ACC⁰[composite]` component (with the `MOD_q` proven instance in-arc).  It does **not** prove the general count lower
bound (Smolensky-strength) nor the general bridge.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0FirePatternRichness

open PallLean.Paper93.DeepMath.PathB.ACC0CoFiring (firePattern)

/-- **Pattern richness.**  The firing map produces `≥ k` *distinct* fire-patterns: `k ≤ #(image (firePattern gates)
univ)`.  Strengthens entry-260 `CoFiringRich` (one large co-fire) to many distinct patterns. -/
def PatternRich {X : Type} [Fintype X] {s : ℕ} (gates : Fin s → (X → Bool)) (k : ℕ) : Prop :=
  k ≤ (Finset.image (firePattern gates) Finset.univ).card

/-- **The dictator family realizes every subset as a fire-pattern (PROVED).**  For any `T ⊆ Fin s`, the input
`fun i => decide (i ∈ T)` has fire-pattern exactly `T`; so the image of `firePattern` is all of `Finset (Fin s)`. -/
theorem dictator_firePatternImage_eq_univ (s : ℕ) :
    Finset.image (firePattern (fun (i : Fin s) (x : Fin s → Bool) => x i)) Finset.univ
      = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  intro T
  rw [Finset.mem_image]
  refine ⟨fun i => decide (i ∈ T), Finset.mem_univ _, ?_⟩
  unfold firePattern
  ext i
  simp

/-- **The dictator/`MOD_q` family is exponentially pattern-rich (PROVED).**  `PatternRich (fun i x => x i) (2^s)`: it
has `2^s` distinct fire-patterns (every subset realized).  The genuine hard family has exponentially many patterns. -/
theorem dictator_patternRich (s : ℕ) :
    PatternRich (fun (i : Fin s) (x : Fin s → Bool) => x i) (2 ^ s) := by
  unfold PatternRich
  rw [dictator_firePatternImage_eq_univ, Finset.card_univ, Fintype.card_finset, Fintype.card_fin]

/-- **The parallel affine family has no large fire-pattern (PROVED).**  Every fire-pattern has size `≤ 1` (entry 259),
so none has size `≥ 2`: no co-firing, no large patterns — it fails pattern richness in the strong sense, matching its
easy fire-count. -/
theorem parallel_no_large_patterns {p n s : ℕ} (targets : Fin s → ZMod p)
    (hinj : Function.Injective targets) (x : Fin (n + 1) → ZMod p) :
    ¬ 2 ≤ (firePattern
        (fun (i : Fin s) (x : Fin (n + 1) → ZMod p) => decide ((∑ j, x j) = targets i)) x).card := by
  have hle := PallLean.Paper93.DeepMath.PathB.ACC0AffineHyperplaneLowerBound.affineHyperplane_fireCount_le_one
    targets hinj x
  unfold firePattern
  dsimp only
  omega

/-- **The strengthened count-hardness socket (Smolensky-strength, NOT proved).**  Non-redundant (`AlgExpander`) *and*
pattern-rich (`PatternRich`, exponentially many distinct fire-patterns) gate families have hard mod-`q` fire-counts.
Strengthens entry-260's existential `CoFiringRich` to many-distinct-patterns. -/
def PatternRichCountObstruction {X : Type} [Fintype X] {s : ℕ} (gates : Fin s → (X → Bool))
    (CrossFieldCountHard : Prop) (F : Type) [Field F] (k : ℕ) : Prop :=
  PallLean.Paper93.DeepMath.PathB.ACC0AlgebraicExpansion.AlgExpander (F := F) gates →
    PatternRich gates k → CrossFieldCountHard

/-- **The implication bridge (named socket).**  Cross-field count hardness *is* the `ACC⁰[composite]` lower-bound
component (`ACC0CompositeComponent`), formally upstream of Williams `NEXP ⊄ ACC⁰`.  Stated, not proved in general; the
proven instance is the dictator/`MOD_q` family via the in-arc `Layer4.mod_q_indicators_false`. -/
def crossFieldHard_to_ACC0Component (CrossFieldCountHard ACC0CompositeComponent : Prop) : Prop :=
  CrossFieldCountHard → ACC0CompositeComponent

/-!
**The corrected bridge.**  `AlgExpander → PatternRich → CrossFieldCountHard → ACC0CompositeComponent → (Williams) →
NEXP ⊄ ACC⁰`.  The two proved separations: dictator/`MOD_q` is `AlgExpander` (260) + `PatternRich (2^s)` (here) and
count-hard (in-arc `Layer4.mod_q_indicators_false`); parallel affine is `AlgExpander` (258) but has no large pattern
(here) and is count-easy (259).  The general count lower bound (`PatternRichCountObstruction`) and the general bridge
(`crossFieldHard_to_ACC0Component`) are the Smolensky-strength open core (entry-238 `CarryRefinementCrossing`); not
proved.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0FirePatternRichness

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FirePatternRichness.dictator_patternRich
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FirePatternRichness.parallel_no_large_patterns
