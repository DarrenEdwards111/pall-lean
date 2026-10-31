import PallLean.Paper93.DeepMath.PathB.ComputationalDepthToyRectangleLowerBounds
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverLowerBound

/-!
# Calibration 3: rederiving a communication rectangle-cover lower bound through the invariant

The third circuit/communication calibration (after AC⁰[p] degree and Nečiporuk formula size).  This one is
in the **deterministic communication** model, where the observer is a protocol — equivalently a partition of
the communication matrix into monochromatic rectangles — and its boundary is `log₂` of the number of
rectangles (the communication cost).  Once more, the known lower bound *is* the observer invariant.

## The dictionary

| observer notion | communication / rectangle-cover notion |
|---|---|
| sectors / behaviors | the `1`-entries of the matrix to be covered |
| non-mergeable / fooling set | the diagonal entries of EQUALITY: no `1`-rectangle covers two (`eq_of_same_oneRectangle_contains_two_diagonal`) |
| boundary entropy | `log₂ (#rectangles)` = communication cost |
| low-boundary observer | a protocol using few rectangles |

The fooling principle "`K` non-mergeable behaviors ⇒ boundary `≥ log₂ K`" is here exactly: `n` pairwise
non-mergeable diagonal entries force `≥ n` rectangles (`equalityMatrix_indexedDiagonalCover_lowerBound`),
hence communication boundary `≥ log₂ n`.

## What is proved (all clean axioms, no `sorry`; the rectangle bound is reused, recast)

* `rectangleObserverBoundary` — the communication observer's boundary, `log₂ (#rectangles)`.
* `diagonal_nonmergeable` — the EQUALITY diagonal is a fooling set (`pick` is injective).
* `equality_rectangle_boundary_ge` — every rectangle-cover observer of the EQUALITY matrix has boundary
  `≥ log₂ n` — the deterministic communication lower bound, rederived through the invariant.

## Honest scope

A third restricted-model calibration: deterministic communication / rectangle covers, bound `log₂ n` for the
identity matrix.  A toy ceiling (`log n`), explicitly — its value is being a *third independent model*
confirming the observer invariant rederives known lower bounds (degree, formula size, communication).  The
general machine-decomposition rung stays open.
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverRectangle

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.ObserverBoundary

/-- **The communication observer's boundary**: `log₂` of the number of monochromatic rectangles a cover uses
(the deterministic communication cost). -/
noncomputable def rectangleObserverBoundary {n : ℕ} (C : IndexedDiagonalCover n) : ℕ :=
  Nat.log 2 C.cover.length

/-- **The EQUALITY diagonal is a fooling set (non-mergeable behaviors).**  Distinct diagonal entries are kept
in distinct rectangles — no `1`-monochromatic rectangle covers two of them — so the diagonal-to-rectangle
map is injective.  (This is `IndexedDiagonalCover.pick_injective`, read as non-mergeability.) -/
theorem diagonal_nonmergeable {n : ℕ} (C : IndexedDiagonalCover n) : Function.Injective C.pick :=
  C.pick_injective

/-- **The communication lower bound, rederived through the invariant.**  Every rectangle-cover observer of
the `n × n` EQUALITY matrix has boundary `≥ log₂ n`: its `n` pairwise non-mergeable diagonal entries force
`≥ n` rectangles (`equalityMatrix_indexedDiagonalCover_lowerBound`), and the observer boundary is
`log₂ (#rectangles)`.  This is the fooling principle (`foolingSet_forces_boundary`) in the communication
model. -/
theorem equality_rectangle_boundary_ge {n : ℕ} (C : IndexedDiagonalCover n) :
    Nat.log 2 n ≤ rectangleObserverBoundary C :=
  Nat.log_mono_right (equalityMatrix_indexedDiagonalCover_lowerBound C)

end PallLean.Paper93.DeepMath.PathB.ObserverRectangle

#print axioms PallLean.Paper93.DeepMath.PathB.ObserverRectangle.diagonal_nonmergeable
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverRectangle.equality_rectangle_boundary_ge
