import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ExpanderFamilies

/-!
# Algebraic expansion — the refined condition: gate-function independence, not cut-expansion

Entry 255 found the honest negative: cut-expansion (`ExpanderIncidence`, no small separator) is *necessary* for
separator-DP failure but **not sufficient** for count-hardness — the full-support family is a cut-expander whose count
can be easy when its gates are redundant.  So the right hypothesis for the count lower bound is **algebraic**, about the
gate *functions*, not their variable supports.  This file makes that precise.

**The refined condition.**  `AlgExpander` := the gate-indicator functions `[gate i fires] : X → F` are **linearly
independent over the field `F`** (high rank).  This is about the gate functions, not the incidence cut, and it **rules
out the full-support / redundant-gate degeneracy**: duplicate (redundant) gates have equal indicators, hence are
linearly dependent, hence fail `AlgExpander`.

## What is proved (clean axioms, no `sorry`)

* **`gateInd gates i := fun x => if gates i x then 1 else 0`** — the gate indicator as an `F`-valued function.
* **`AlgExpander gates := LinearIndependent F (gateInd gates)`** — the gate indicators are linearly independent over `F`
  (algebraic expansion = high gate-function rank).
* **`not_algExpander_of_duplicate`** (PROVED) — duplicate gates (`i ≠ j`, `gates i = gates j`) ⇒ `¬ AlgExpander`: the
  redundant degeneracy is excluded (`LinearIndependent.injective`).
* **`algExpander_indicators_injective`** (PROVED) — `AlgExpander` ⇒ the gate-indicator family is injective (distinct
  gates give distinct indicators): genuine non-redundancy.

## The refined socket (named, not proved)

* **`AlgExpanderCountObstruction`** — `AlgExpander gates → ComputesCrossFieldCount obs → bound ≤ resources obs`: under
  *algebraic* expansion (gate-function independence over `F = ZMod q`), the mod-`q` fire-count needs superpolynomial
  resources.  This replaces the cut-based entry-254 socket with the *correct* (algebraic) hypothesis.  Still
  Smolensky-strength; not proved.

## Honest scope

This proves that **algebraic expansion (gate-function linear independence) is the right refinement** — it is about the
gate functions (not the cut), and it rules out the entry-255 full-support degeneracy (duplicate gates fail it).  It
restates the count lower bound under this correct hypothesis as the socket `AlgExpanderCountObstruction`.  The two
notions are genuinely different: **cut-expansion (treewidth) governs DP tractability exactly (251–253); algebraic
expansion (gate-function rank) is the hypothesis needed for count-hardness**.  The lower bound under it is the open
Smolensky-strength core (entry-238 `CarryRefinementCrossing`); not proved here.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0AlgebraicExpansion

variable {X : Type} {s : ℕ} {F : Type} [Field F]

/-- The gate indicator as an `F`-valued function: `1` if the gate fires on `x`, else `0`. -/
def gateInd (gates : Fin s → (X → Bool)) (i : Fin s) : X → F :=
  fun x => if gates i x then 1 else 0

/-- **Algebraic expansion.**  The gate-indicator functions are linearly independent over `F` — high gate-function rank.
This is about the gate *functions* (not the incidence cut), and is the hypothesis the count lower bound actually needs
(unlike cut-expansion, entry 255). -/
def AlgExpander (gates : Fin s → (X → Bool)) : Prop :=
  LinearIndependent F (gateInd gates (F := F))

/-- **Algebraic expansion rules out the redundant-gate degeneracy (PROVED).**  Duplicate gates (`i ≠ j` with
`gates i = gates j`) have equal indicators, hence are linearly dependent — so `¬ AlgExpander`.  The full-support family
of entry 255 (when its gates are redundant) is correctly excluded. -/
theorem not_algExpander_of_duplicate (gates : Fin s → (X → Bool)) (i j : Fin s)
    (hij : i ≠ j) (heq : gates i = gates j) : ¬ AlgExpander (F := F) gates := by
  intro h
  apply hij
  apply h.injective
  unfold gateInd
  rw [heq]

/-- **Algebraic expansion ⇒ non-redundant gates (PROVED).**  The gate-indicator family is injective: distinct gates
give distinct indicators.  Genuine non-redundancy, the property the full-support degeneracy lacked. -/
theorem algExpander_indicators_injective (gates : Fin s → (X → Bool))
    (h : AlgExpander (F := F) gates) : Function.Injective (gateInd gates (F := F)) :=
  h.injective

/-- **The refined count-obstruction socket (Smolensky-strength, NOT proved).**  Under *algebraic* expansion
(gate-function linear independence over `F = ZMod q`), any observer computing the mod-`q` fire-count
(`ComputesCrossFieldCount`, abstract) needs `≥ bound` resources.  This is the entry-254 socket restated under the
*correct* hypothesis (algebraic, not cut).  A named conjecture; proving it is the `ACC⁰[composite]` wall. -/
def AlgExpanderCountObstruction (gates : Fin s → (X → Bool))
    (ComputesCrossFieldCount : Prop) (resources bound : ℕ) : Prop :=
  AlgExpander (F := F) gates → ComputesCrossFieldCount → bound ≤ resources

/-!
**The refined bridge.**  Cut-expansion (treewidth, `ExpanderIncidence`) governs DP tractability *exactly* (251–253):
bounded ⇒ tractable, expander ⇒ DP fails.  But cut-expansion is *not* count-hardness (entry-255 full-support negative).
The correct hypothesis is **algebraic expansion** (`AlgExpander`, gate-function independence over `F`), which rules out
the redundant degeneracy (`not_algExpander_of_duplicate`).  The count lower bound under `AlgExpander`
(`AlgExpanderCountObstruction`) is the open Smolensky-strength core (entry-238 `CarryRefinementCrossing`); not proved.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0AlgebraicExpansion

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AlgebraicExpansion.not_algExpander_of_duplicate
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AlgebraicExpansion.algExpander_indicators_injective
