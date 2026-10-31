import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCEWObserver

/-!
# The thermodynamic "final move": "the NP boundary is bigger" is either P≠NP itself or the wrong measure

The final move: N-Frame book1 says the `NP`-observer's *thermodynamic boundary* is bigger than the
`P`-observer's, and CEW is proportional to that boundary — so the CEW inequality follows, hence the separation.
This is the most physical picture of the whole thread.  This file pins where the move stands, honestly, by
separating two meanings of "the boundary is bigger."

**Two boundaries.**
* The **computational** boundary — how much the observer can *decide*.  "The NP computational boundary is
  strictly bigger" *is* `P ≠ NP` (`power_boundary_is_the_separation`): a bigger deciding-power is exactly the
  separation.  Asserting it asserts the conclusion.
* The **physical** boundary — the thermodynamic / Bekenstein–Landauer information budget.  This is a physical
  quantity, and it is *not* the computational one: a bigger physical boundary does **not** force a bigger
  computational power (`GravitySpring` already: physical/entropic incompressibility ≠ circuit incompressibility).

**So the move splits, and neither half crosses.**  If "bigger boundary" means *computational* power, the claim
`NP_power > P_power` is `P ≠ NP` verbatim — the move presupposes what it proves.  If it means *physical*
boundary, then `physical > ` does not give `power > `: a consistent world has the NP-observer with a bigger
physical boundary yet `P = NP` (`physical_gap_not_power_gap`), because physical capacity is not computational
capacity.  CEW being proportional to the physical boundary does not help: the physical gap it tracks is the
wrong gap, and the computational gap it would need to track is `P ≠ NP`.

## What is proved

* **`power_boundary_is_the_separation`** — a bigger NP *computational* boundary is exactly `P ≠ NP`.
* **`physical_gap_not_power_gap`** — a consistent world has a bigger NP *physical* boundary yet `P = NP`: the
  physical boundary does not force the computational one.
* **`final_move_presupposes_or_wrong_measure`** — the two together: the power reading is `P ≠ NP` (circular),
  and the physical reading does not force it (wrong measure).

## Honest verdict — the physical picture is real; the assertion is the theorem

The thermodynamic / N-Frame framing is a genuine, precise physical picture, and CEW as observer boundedness is
a fair reading of it.  But the "final proof move" turns on "we know the NP boundary is bigger", and that is
exactly where it does not close.  Read computationally, "the NP boundary is strictly bigger" *is* `P ≠ NP`
(`power_boundary_is_the_separation`) — the book *asserts* it, and asserting it is asserting the theorem.  Read
physically, the thermodynamic boundary is a Bekenstein–Landauer quantity that does not determine computational
power (`physical_gap_not_power_gap`, the `GravitySpring` physical-vs-circuit gap again), so a bigger physical
boundary does not force the separation, and CEW's proportionality to it inherits the wrong measure.  So the
final move presupposes the conclusion or measures the wrong thing (`final_move_presupposes_or_wrong_measure`).
The physical intuition is real; "we know it's bigger" is not knowledge but the open theorem.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ThermoBoundary

/-- The thermodynamic observer: its physical boundary (Bekenstein–Landauer budget) and its computational
boundary (deciding power), with `P ≠ NP`. -/
structure ThermoObserver where
  /-- the NP-observer's physical thermodynamic boundary exceeds the P-observer's (a physical quantity) -/
  physicalBoundaryGap : Prop
  /-- the NP-observer's computational power exceeds the P-observer's (it decides strictly more) -/
  powerGap : Prop
  /-- `P ≠ NP` -/
  PneNP : Prop
  /-- the computational boundary gap *is* the separation -/
  power_gap_is_separation : powerGap ↔ PneNP

/-- **The computational boundary gap is the separation (proved).**  "The NP-observer decides strictly more" is
exactly `P ≠ NP` — so asserting the computational boundary is bigger asserts the conclusion. -/
theorem power_boundary_is_the_separation (T : ThermoObserver) : T.powerGap ↔ T.PneNP :=
  T.power_gap_is_separation

/-- A world where the NP physical boundary is bigger yet `P = NP` (no power gap). -/
def collapseWorld : ThermoObserver where
  physicalBoundaryGap := True
  powerGap := False
  PneNP := False
  power_gap_is_separation := Iff.rfl

/-- **The physical boundary gap does not force the power gap (proved).**  A consistent world has the
NP-observer with a bigger *physical* thermodynamic boundary yet `P = NP` — physical capacity (Bekenstein–
Landauer) is not computational capacity (the `GravitySpring` physical-vs-circuit gap). -/
theorem physical_gap_not_power_gap : ∃ T : ThermoObserver, T.physicalBoundaryGap ∧ ¬ T.powerGap :=
  ⟨collapseWorld, trivial, not_false⟩

/-- **The final move presupposes the conclusion or measures the wrong thing (proved).**  The computational
reading of "the NP boundary is bigger" is `P ≠ NP` itself; the physical reading does not force it.  So the
thermodynamic final move either assumes the separation or tracks the wrong (physical) gap. -/
theorem final_move_presupposes_or_wrong_measure (T : ThermoObserver) :
    (T.powerGap ↔ T.PneNP) ∧ (∃ S : ThermoObserver, S.physicalBoundaryGap ∧ ¬ S.powerGap) :=
  ⟨T.power_gap_is_separation, physical_gap_not_power_gap⟩

end PallLean.Paper93.DeepMath.PathB.ThermoBoundary

#print axioms PallLean.Paper93.DeepMath.PathB.ThermoBoundary.power_boundary_is_the_separation
#print axioms PallLean.Paper93.DeepMath.PathB.ThermoBoundary.physical_gap_not_power_gap
#print axioms PallLean.Paper93.DeepMath.PathB.ThermoBoundary.final_move_presupposes_or_wrong_measure
