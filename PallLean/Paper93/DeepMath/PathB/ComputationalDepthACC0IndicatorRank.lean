import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0AlgebraicExpansion

/-!
# Indicator rank — the algebraic-hardness invariant (stronger than treewidth), a concrete family, the RS link

Entry 256 fixed the correct hypothesis for the count lower bound: **algebraic expansion** (`AlgExpander` = gate-indicator
functions linearly independent over `F`).  This file makes the invariant explicit and attacks it concretely, per the
focused program:

* **The invariant: indicator rank** (stronger than treewidth — treewidth is DP geometry; rank is the algebraic-hardness
  geometry).  `gateRank` = the dimension of the span of the gate-indicator functions over `F`.  Algebraic expansion is
  exactly *full* rank: `AlgExpander ⇒ gateRank = s`.
* **A concrete algebraically-expanding family** (the honest "one nontrivial family" step): the point/dictator gates
  (gate `i` fires iff input `= i`) have indicators equal to the standard basis `Pi.single i 1`, hence linearly
  independent — so they satisfy `AlgExpander` with full rank `s`.
* **The Razborov–Smolensky link.**  The general count lower bound under `AlgExpander` (the entry-256 socket
  `AlgExpanderCountObstruction`) is *formally upstream* of the `ACC⁰[composite]` lower bound: it is the Razborov–Smolensky
  statement (linearly-independent `F_p`-gate indicators ⇒ mod-`q` fire-count needs superpoly).  The arc already *proves*
  this for the `MOD_q` gate family — `Layer4.mod_q_indicators_false` (entry 244) — a proven restricted instance.

## What is proved (clean axioms, no `sorry`)

* **`gateRank gates := finrank F (span F (range (gateInd gates)))`** — the indicator-rank invariant.
* **`algExpander_gateRank_eq`** (PROVED) — `AlgExpander gates → gateRank gates = s`: algebraic expansion = full indicator
  rank (`finrank_span_eq_card`).
* **`pointFamily_algExpander`** (PROVED) — the point/dictator family `fun i x => decide (x = i)` satisfies `AlgExpander`:
  its indicators are the standard basis `Pi.basisFun`, hence linearly independent — a concrete full-rank algebraic
  expander.

## The RS link and the open target (named)

The count lower bound under `AlgExpander` (`AlgExpanderCountObstruction`, entry 256) is Razborov–Smolensky: it is the
`ACC⁰[composite]` lower-bound component, formally upstream of Williams `NEXP ⊄ ACC⁰`.  The arc proves it for the `MOD_q`
gate family (`Layer4.mod_q_indicators_false`, entry 244 — a proven restricted instance).  The *general* `AlgExpander`
bound — any low-rank observer/polynomial over `F = ZMod q` computing the fire-count needs degree/size `≥ n^c` — is the
open core; not proved here.

## Honest scope

This proves the indicator-rank invariant (`AlgExpander = full rank`) and exhibits a concrete full-rank algebraic-
expander family, and links the count lower bound to Razborov–Smolensky (proven for the `MOD_q` family in-arc).  It does
**not** prove the general `AlgExpander` count lower bound (Smolensky-strength, the socket).  The invariant is the
algebraic-hardness geometry (rank, not treewidth); a restricted bound for a non-trivial family beyond `MOD_q` is the
next target.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0IndicatorRank

open PallLean.Paper93.DeepMath.PathB.ACC0AlgebraicExpansion

variable {X : Type} {s : ℕ} {F : Type} [Field F]

/-- **The indicator-rank invariant.**  The dimension of the span of the gate-indicator functions over `F` — the
algebraic-hardness geometry (stronger than treewidth: treewidth governs DP, rank governs count-hardness). -/
noncomputable def gateRank (gates : Fin s → (X → Bool)) : ℕ :=
  Module.finrank F (Submodule.span F (Set.range (gateInd gates (F := F))))

/-- **Algebraic expansion = full indicator rank (PROVED).**  `AlgExpander gates → gateRank gates = s`: the `s` gate
indicators span an `s`-dimensional space (`finrank_span_eq_card`).  Algebraic expansion is exactly maximal rank. -/
theorem algExpander_gateRank_eq (gates : Fin s → (X → Bool)) (h : AlgExpander (F := F) gates) :
    gateRank (F := F) gates = s := by
  unfold gateRank
  rw [finrank_span_eq_card h, Fintype.card_fin]

/-- **A concrete full-rank algebraic-expander family (PROVED).**  The point/dictator gates — gate `i` fires iff the
input is `i` — have indicators equal to the standard basis `Pi.single i 1` (= `Pi.basisFun`), hence linearly
independent; so they satisfy `AlgExpander` (with `gateRank = s` by `algExpander_gateRank_eq`).  An honest nontrivial
algebraically-expanding family. -/
theorem pointFamily_algExpander (s : ℕ) :
    AlgExpander (F := F) (fun (i : Fin s) (x : Fin s) => decide (x = i)) := by
  have hb := (Pi.basisFun F (Fin s)).linearIndependent
  have heq : gateInd (F := F) (fun (i : Fin s) (x : Fin s) => decide (x = i))
      = ⇑(Pi.basisFun F (Fin s)) := by
    funext i x
    unfold gateInd
    simp only [Pi.basisFun_apply, Pi.single_apply]
    by_cases h : x = i <;> simp [h, eq_comm]
  unfold AlgExpander
  rw [heq]
  exact hb

/-!
**The Razborov–Smolensky link (named).**  The count lower bound under `AlgExpander` (entry-256
`AlgExpanderCountObstruction`) is the `ACC⁰[composite]` lower-bound component — Razborov–Smolensky: linearly-independent
`F_p`-gate indicators ⇒ the mod-`q` fire-count needs superpolynomial resources, formally upstream of Williams
`NEXP ⊄ ACC⁰`.  The arc *proves* it for the `MOD_q` gate family (`Layer4.mod_q_indicators_false`, entry 244 — a proven
restricted instance).  The general bound is the open Smolensky-strength core (entry-238 `CarryRefinementCrossing`); the
next target is a restricted bound for a non-trivial family beyond `MOD_q`, via the indicator-rank invariant.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0IndicatorRank

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0IndicatorRank.algExpander_gateRank_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0IndicatorRank.pointFamily_algExpander
