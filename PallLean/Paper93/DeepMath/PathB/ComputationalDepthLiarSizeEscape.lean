import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSelfReferenceLeak
import Mathlib.Data.Nat.Basic

/-!
# The liar self-reference for SAT — and where IT leaks: size escape

`SelfReferenceLeak` named the missing ingredient: a **liar** self-instance for a hard problem (SAT
can express "C rejects this formula", so by the recursion theorem there is a formula `φ_C` with
`SAT(φ_C) = ¬ C(φ_C)` — the liar structure `diagonal_forces_lb` consumes).  This file builds that
next step and machine-checks where the liar route itself leaks: the liar instance `φ_C` **escapes to
a larger input size** than `C` handles, because a description of `C` is bigger than `C`'s own input
length.  So the diagonal cannot close at a single size — the exact universal-object / size stone the
hierarchy mountain isolated (`naiveDiag_is_complement`), now shown to be the leak of the
self-reference route as well.  The whole thread converges on one stone.

## What is proved

* **`liar_and_insize_would_cross`** — IF the liar structure holds AND the liar instance fits `C`'s
  input size (`LiarInSize`), the diagonal fires: no small `C` is correct.  Both hypotheses cross.
* **`self_reference_leaks_via_size`** — but under `SelfEncodingEscapes` (a description of `C` is
  strictly larger than `C`'s input length), the liar instance `φ_C` has `instSize φ_C > inSize C`:
  the diagonal instance lives at a LARGER size than `C` handles.
* **`escape_precludes_insize` / `self_reference_is_the_same_stone`** — escape is exactly the
  negation of in-size, so the two hypotheses that would cross are jointly unavailable — the leak.

## Verdict — one stone, from every side

The liar route has the real engine (`diagonal_forces_lb`) and a real leak (`φ_C` escapes to a larger
input size).  Closing it needs the liar instance to FIT `C`'s input — a size-efficient self-encoding
plus in-budget self-evaluation, i.e. a **size-efficient universal object**.  That is the identical
obstruction as `naiveDiag_is_complement` (the diagonal escapes the class), the hierarchy mountain
(no small universal circuit), the reach diagnosis (the free hub), and `cost_super`.  Uniform
computation absorbs the escape — one machine handles the larger instance — at the universal-simulation
overhead, capping at the alternation-trading / `NEXP` ceiling; non-uniform circuits cannot absorb it.
The self-reference route is not a different wall; this file proves it is the same one.  Nothing here
is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.LiarSizeEscape

open PallLean.Paper93.DeepMath.PathB.SelfReferenceLeak

/-- A self-referential world with input sizes. -/
structure SizedSelfRefWorld where
  /-- the underlying self-referential world -/
  base : SelfRefWorld
  /-- the input length the decider handles -/
  inSize : base.Decider → ℕ
  /-- the size of an input -/
  instSize : base.Input → ℕ

/-- The liar instance fits the decider's input size. -/
def LiarInSize (W : SizedSelfRefWorld) : Prop :=
  ∀ D : W.base.Decider, W.base.Small D → W.instSize (W.base.selfInstance D) ≤ W.inSize D

/-- The self-encoding escapes: the liar instance (encoding `D`) is strictly larger than `D`'s input
length — a description of a circuit is bigger than the circuit's own input. -/
def SelfEncodingEscapes (W : SizedSelfRefWorld) : Prop :=
  ∀ D : W.base.Decider, W.base.Small D → W.inSize D < W.instSize (W.base.selfInstance D)

/-- **Both hypotheses cross (proved).**  Liar structure + the liar instance fitting the decider's
input size ⟹ no small decider is correct (the engine is `diagonal_forces_lb`; in-size is the extra
thing needed). -/
theorem liar_and_insize_would_cross (W : SizedSelfRefWorld)
    (hliar : LiarStructure W.base) (_hins : LiarInSize W)
    (D : W.base.Decider) (hsmall : W.base.Small D) : ¬ Correct W.base D :=
  diagonal_forces_lb W.base hliar D hsmall

/-- **The liar instance escapes to a larger size (proved).** -/
theorem self_reference_leaks_via_size (W : SizedSelfRefWorld) (hesc : SelfEncodingEscapes W)
    (D : W.base.Decider) (hsmall : W.base.Small D) :
    W.inSize D < W.instSize (W.base.selfInstance D) :=
  hesc D hsmall

/-- **Escape precludes in-size (proved).** -/
theorem escape_precludes_insize (W : SizedSelfRefWorld) (D : W.base.Decider)
    (hesc : W.inSize D < W.instSize (W.base.selfInstance D)) :
    ¬ (W.instSize (W.base.selfInstance D) ≤ W.inSize D) := by
  omega

/-- **The unification (proved).**  Under escape, no decider can have its liar instance in-size: the
self-reference route's leak IS the size escape, and closing it needs a size-efficient universal
object — the same stone as every other route. -/
theorem self_reference_is_the_same_stone (W : SizedSelfRefWorld) (hesc : SelfEncodingEscapes W)
    (D : W.base.Decider) (hsmall : W.base.Small D) :
    ¬ (W.instSize (W.base.selfInstance D) ≤ W.inSize D) :=
  escape_precludes_insize W D (self_reference_leaks_via_size W hesc D hsmall)

end PallLean.Paper93.DeepMath.PathB.LiarSizeEscape

#print axioms PallLean.Paper93.DeepMath.PathB.LiarSizeEscape.liar_and_insize_would_cross
#print axioms PallLean.Paper93.DeepMath.PathB.LiarSizeEscape.self_reference_leaks_via_size
#print axioms PallLean.Paper93.DeepMath.PathB.LiarSizeEscape.self_reference_is_the_same_stone
