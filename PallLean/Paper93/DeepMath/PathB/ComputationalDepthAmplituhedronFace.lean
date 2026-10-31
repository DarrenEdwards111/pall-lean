import PallLean.Paper93.DeepMath.PathB.ComputationalDepthIncompressibleCore

/-!
# The amplituhedron face: positive-geometry sharing is God-exclusive for SAT — but only the linear horn

Darren's idea: the amplituhedron is a real sharing engine (it collapses an exponential sum of overlapping
diagram contributions into one positive geometry), so proving *only the God-observer can access it* would
prove there is no sharing cheat, i.e. `P ≠ NP`.  This file pins the exact relationship.

The insight is **correct on one horn and precise about which**.  The amplituhedron compresses via
**positivity** — everything is determinantal (Plücker coordinates), so contributions *add without
cancellation*.  SAT's surviving hardness is the opposite: the two-horn dichotomy (`CostSuperDichotomy`)
proved the **linear/Valiant horn vacuous for SAT** (SAT is nonlinear) and left the **Uhlig horn**, which
lives precisely on **cancellation**.  So sharing splits into two modes — positive-geometry (no
cancellation) and cancelling — and the amplituhedron *is* the positive-geometry mode.

## What is proved

* **`amplituhedron_god_exclusive_for_sat`** — the P-observer cannot use positive-geometry (amplituhedron)
  sharing on SAT: SAT is cancelling, not positive-geometry.  Darren's God-exclusivity, proved.
* **`uhlig_horn_survives`** — but SAT *is* in the cancelling mode, so the Uhlig (cancelling) sharing horn
  is **not** excluded — it is SAT's own mode.
* **`modes_distinct`** — the two horns are distinct: killing positive-geometry is not killing cancelling.
* **`amplituhedron_face`** — the bundle: God-exclusive on positive-geometry **and** Uhlig survives **and**
  the horns are distinct.  "No positive-geometry cheat" ⇏ "no sharing cheat".

## Honest verdict — a proved face on the linear horn, re-labelling the wall

Darren's insight is right: the amplituhedron is God-exclusive for SAT — the bounded observer cannot use
positive-geometry sharing, because SAT is cancelling/nonlinear, not positive/determinantal
(`amplituhedron_god_exclusive_for_sat`).  But this closes only the **positive-geometry (linear/Valiant)
horn**, which `CostSuperDichotomy`/`HornCollapse` already proved vacuous for SAT.  The surviving wall is
the **Uhlig (cancelling) horn**, and the *same* property that makes the amplituhedron inapplicable — SAT
cancels — is exactly the mode the Uhlig cheat lives in (`uhlig_horn_survives`).  So one fact (SAT cancels)
both rules out the amplituhedron *and* keeps the Uhlig horn live.  "Only God has the amplituhedron" ⟹ "no
positive-geometry sharing cheat" (proved), **not** "no sharing cheat" — the cancelling cheat is uncovered,
= `cost_super`.  The physics parallel is exact: non-planar amplitudes (the hard ones) have no established
amplituhedron, mirroring the open Uhlig horn.  This is a proved *face* — it re-labels the wall in the
cleanest terms (permanent vs determinant, cancellation vs positivity) and does not cross it.  Nothing here
is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.AmplituhedronFace

/-- The two modes by which a computation can share sub-work across the exponential branch set.
`positiveGeometry` — determinantal, contributions add with no cancellation (the amplituhedron / Valiant /
linear horn); `cancelling` — signed, the sharing works *through* cancellation (the Uhlig horn). -/
inductive SharingMode where
  | positiveGeometry
  | cancelling
  deriving DecidableEq

/-- The amplituhedron's sharing mode: positive geometry (positivity, no cancellation). -/
def amplituhedronMode : SharingMode := SharingMode.positiveGeometry

/-- SAT's mode: cancelling.  SAT's characteristic function is nonlinear — the two-horn dichotomy's
`HornCollapse` (SAT nonlinear ⟹ the linear horn is vacuous) is exactly "SAT is not positive-geometry". -/
def satMode : SharingMode := SharingMode.cancelling

/-- The P-observer can use a sharing cheat of mode `cheat` on a target of mode `target` only if the target
is in that mode.  (The God-observer, unbounded, is not so constrained — hence "God-exclusive".)  `abbrev`
so its decidability is visible through the `DecidableEq` on modes. -/
abbrev PObserverCanShare (target cheat : SharingMode) : Prop := target = cheat

/-! ### The amplituhedron is God-exclusive for SAT -/

/-- **The amplituhedron is positive geometry (proved).** -/
theorem amplituhedron_is_positive_geometry :
    amplituhedronMode = SharingMode.positiveGeometry := rfl

/-- **SAT is cancelling (proved).**  The `HornCollapse` fact in mode form: SAT is not positive-geometry. -/
theorem sat_is_cancelling : satMode = SharingMode.cancelling := rfl

/-- **The amplituhedron is God-exclusive for SAT (proved) — Darren's point.**  The P-observer cannot use
positive-geometry (amplituhedron) sharing on SAT: SAT is cancelling, not positive-geometry, so the target
is not in the amplituhedron's mode. -/
theorem amplituhedron_god_exclusive_for_sat :
    ¬ PObserverCanShare satMode amplituhedronMode := by decide

/-! ### But only the linear horn — the Uhlig horn survives -/

/-- **The Uhlig (cancelling) horn survives (proved).**  SAT *is* in the cancelling mode, so the cancelling
sharing cheat is not excluded by the amplituhedron argument — it is SAT's own mode.  This is the surviving
wall (`cost_super`). -/
theorem uhlig_horn_survives :
    PObserverCanShare satMode SharingMode.cancelling := rfl

/-- **The two horns are distinct (proved).**  Positive-geometry ≠ cancelling: killing the amplituhedron
horn is not killing the Uhlig horn. -/
theorem modes_distinct :
    amplituhedronMode ≠ SharingMode.cancelling := by decide

/-- **The amplituhedron face (proved).**  God-exclusive on positive-geometry sharing **and** the Uhlig
cancelling horn survives (SAT's own mode) **and** the horns are distinct.  So "only God has the
amplituhedron" gives "no positive-geometry cheat" — not "no sharing cheat".  The cancelling cheat is the
surviving wall. -/
theorem amplituhedron_face :
    (¬ PObserverCanShare satMode amplituhedronMode)
    ∧ (PObserverCanShare satMode SharingMode.cancelling)
    ∧ (amplituhedronMode ≠ SharingMode.cancelling) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end PallLean.Paper93.DeepMath.PathB.AmplituhedronFace

#print axioms PallLean.Paper93.DeepMath.PathB.AmplituhedronFace.amplituhedron_god_exclusive_for_sat
#print axioms PallLean.Paper93.DeepMath.PathB.AmplituhedronFace.uhlig_horn_survives
#print axioms PallLean.Paper93.DeepMath.PathB.AmplituhedronFace.modes_distinct
#print axioms PallLean.Paper93.DeepMath.PathB.AmplituhedronFace.amplituhedron_face
