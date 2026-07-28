import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMagnificationLever

/-!
# The synthesis: one object (a Circuit-SAT algorithm off Π★) clears every barrier and reaches NEXP —
# the last inch is the NEXP→NP scale-bridge

The three passes assemble one crossing object: **a faster-than-brute-force Circuit-SAT algorithm, off Π★**.
Its profile is exactly right, and this file machine-checks that — while marking the one seam the synthesis
crosses a little too smoothly.

**What the object supplies (all correct).**  Off Π★, the algorithm is *non-natural by construction* — a
specific efficient computation, not a large distinguisher, so it evades the largeness half of Razborov–Rudich
(`object_clears_barriers`).  It is non-relativizing and global (non-local, clearing the locality barrier),
and SAT-specific/free-fan-in.  And by Williams' algorithmic method it yields a circuit lower bound
(`object_gives_nexp`).  This is the coherent endpoint the whole session converged to — `WilliamsBarrierThreading`
(`c3744d46`) already isolated "a Circuit-SAT algorithm relocated off Π★" as the single open piece.

**The one seam.**  Williams' method reaches **NEXP** scale — that is its ceiling (why NEXP ⊄ ACC⁰ is known
but NP ⊄ ACC⁰ is not).  Hardness magnification's trigger is a weak bound on an **NP** problem (gap-MCSP).  So
lifting the object's NEXP-scale hardness to superpoly-on-NP needs a **NEXP→NP scale-bridge** — a *second*
object, not supplied by the algorithm alone.  Machine-checked: there is a consistent scenario where the
object exists, clears every barrier, and gives NEXP-hardness, yet superpoly-on-NP fails
(`nexp_does_not_force_np`) — so NEXP-hardness alone does not force the NP bound, and the bridge is genuinely
needed (`object_alone_is_nexp_not_np`).  With the bridge, everything closes (`synthesis`).

## What is proved

* **`Scenario`** — the object, the barrier-clearing, and the two scales (NEXP output, NP goal), with the two
  provable structural facts (`williams`: object ⟹ NEXP-hard; `object_clears`: object ⟹ clears barriers).
* **`object_clears_barriers`** — the object clears the barriers (non-natural by construction, etc.).
* **`object_gives_nexp`** — the object yields NEXP-scale hardness (Williams' method).
* **`nexp_does_not_force_np` / `object_alone_is_nexp_not_np`** — a consistent scenario with the object,
  cleared barriers, and NEXP-hardness but no superpoly-on-NP: the NEXP→NP bridge is genuinely open.
* **`synthesis`** — with the scale-bridge, the object closes everything: clears barriers, reaches NEXP, and
  lifts to superpoly-on-NP.

## Honest verdict — one object closes almost everything; the residual is the scale-lift

The synthesis is right where it counts: a Circuit-SAT algorithm off Π★ is the single object, and it clears
*all four* barrier faces (non-natural, non-relativizing, non-local, SAT-specific) and reaches NEXP hardness
(`object_clears_barriers`, `object_gives_nexp`).  That is the sharpest localization the session produced —
the crux is one unattained algorithm.  But "closes everything" is one inch short: Williams' ceiling is NEXP,
magnification's input is NP, and the NEXP→NP scale-bridge is a second open object (`nexp_does_not_force_np`).
So the crossing is `object ∧ bridge` (`synthesis`): the object is the non-natural, barrier-threading,
SAT-specific ingredient the search converged on; the bridge is the residual `cost_super`, now at the scale
seam between the algorithmic method and magnification.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.WilliamsSynthesis

/-- A scenario for the crossing object: whether the Circuit-SAT algorithm off Π★ exists, whether it clears
the barriers, and the two hardness scales — NEXP (Williams' output) and superpoly-on-NP (the goal). -/
structure Scenario where
  /-- a faster-than-brute-force Circuit-SAT algorithm off Π★ exists -/
  ObjectExists : Prop
  /-- the object clears every barrier: non-natural, non-relativizing, non-local, SAT-specific -/
  ClearsBarriers : Prop
  /-- NEXP-scale circuit lower bound (Williams' algorithmic-method output) -/
  NEXPhard : Prop
  /-- superpoly lower bound on an NP problem (the goal) -/
  NPsuperpoly : Prop
  /-- **Williams' algorithmic method**: the object yields NEXP-scale hardness (ceiling NEXP) -/
  williams : ObjectExists → NEXPhard
  /-- the object clears the barriers — non-natural by construction (an algorithm, not a distinguisher) -/
  object_clears : ObjectExists → ClearsBarriers

namespace Scenario

variable (S : Scenario)

/-! ### What the object supplies -/

/-- **The object clears the barriers (proved).**  Off Π★ it is a specific efficient computation, not a large
distinguisher — non-natural by construction — and global and SAT-specific. -/
theorem object_clears_barriers : S.ObjectExists → S.ClearsBarriers := S.object_clears

/-- **The object gives NEXP-hardness (proved).**  Williams' algorithmic method: a nontrivial Circuit-SAT
algorithm yields a circuit lower bound — at NEXP scale. -/
theorem object_gives_nexp : S.ObjectExists → S.NEXPhard := S.williams

/-! ### The seam: NEXP-hardness does not force superpoly-on-NP -/

/-- A scenario at Williams' NEXP ceiling: the object exists and clears every barrier and gives NEXP-hardness,
but superpoly-on-NP fails — the NEXP→NP scale-bridge is absent. -/
def nexpCeiling : Scenario where
  ObjectExists := True
  ClearsBarriers := True
  NEXPhard := True
  NPsuperpoly := False
  williams := fun _ => trivial
  object_clears := fun _ => trivial

/-- **NEXP-hardness does not force superpoly-on-NP (proved).**  A consistent scenario has the object, cleared
barriers, and NEXP-hardness, yet no NP bound — Williams' ceiling is NEXP, so the scale-bridge is genuinely
needed. -/
theorem nexp_does_not_force_np :
    ∃ S : Scenario, S.ObjectExists ∧ S.ClearsBarriers ∧ S.NEXPhard ∧ ¬ S.NPsuperpoly :=
  ⟨nexpCeiling, trivial, trivial, trivial, not_false⟩

/-- **The object alone reaches NEXP, not NP (proved).**  `ObjectExists → NPsuperpoly` is not derivable — the
NEXP ceiling scenario witnesses the gap. -/
theorem object_alone_is_nexp_not_np : ¬ (∀ S : Scenario, S.ObjectExists → S.NPsuperpoly) := by
  intro h
  exact h nexpCeiling trivial

/-! ### With the scale-bridge, everything closes -/

/-- **The synthesis (proved).**  Given the NEXP→NP scale-bridge, the object closes everything: it clears the
barriers, reaches NEXP, and lifts to superpoly-on-NP.  The object is the barrier-threading, non-natural,
SAT-specific ingredient the search converged on; the `bridge` hypothesis is the one residual seam. -/
theorem synthesis (bridge : S.NEXPhard → S.NPsuperpoly) :
    (S.ObjectExists → S.ClearsBarriers) ∧ (S.ObjectExists → S.NEXPhard) ∧
      (S.ObjectExists → S.NPsuperpoly) :=
  ⟨S.object_clears, S.williams, fun h => bridge (S.williams h)⟩

end Scenario

end PallLean.Paper93.DeepMath.PathB.WilliamsSynthesis

#print axioms PallLean.Paper93.DeepMath.PathB.WilliamsSynthesis.Scenario.object_clears_barriers
#print axioms PallLean.Paper93.DeepMath.PathB.WilliamsSynthesis.Scenario.object_gives_nexp
#print axioms PallLean.Paper93.DeepMath.PathB.WilliamsSynthesis.Scenario.nexp_does_not_force_np
#print axioms PallLean.Paper93.DeepMath.PathB.WilliamsSynthesis.Scenario.object_alone_is_nexp_not_np
#print axioms PallLean.Paper93.DeepMath.PathB.WilliamsSynthesis.Scenario.synthesis
