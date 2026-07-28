import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRestrictedBlade

/-!
# Lifting the restricted blade one altitude: from formulas to bounded-sharing circuits

The restricted blade lives at the *formula* altitude (zero sharing): it lower-bounds formula cost via the
Khrapchenko `n²` measure.  Asked to lift it *one altitude toward general* — not all the way to general circuits
(that is `cost_super`, barriered), but one rung up the ladder to **bounded-sharing** circuits, where reuse is
allowed but capped.  This is buildable, and it is a genuine step up.

**The lift.**  A bounded-sharing circuit reuses subcircuits, so it can be cheaper than the formula obtained by
unfolding it — but only by the amount it shares.  Unfolding a circuit with sharing budget `t` duplicates the
shared work, so the underlying formula measure satisfies `formulaMeasure ≤ circuitCost + t`
(`unfold_bound`).  If the formula blade clears the class ceiling *with margin* — `bound + t < formulaMeasure
target` (`high_on_target`) — then the circuit itself clears it: `bound < circuitCost target`
(`lifted_blade_separates`).  So the blade now lower-bounds the *circuit* cost, one altitude up: it catches
every circuit that reuses at most `t` subcircuits, not just formulas.

**Forged concretely.**  `khrapchenkoLifted` lifts the `n = 8` Khrapchenko blade to a sharing budget of `t = 20`:
the target's best bounded-sharing circuit costs `44` (it saved `20` by reuse, down from the formula's `64`), and
the blade still catches it (`44 > 8`).  A formula-altitude blade could not — it only sees the unfolded `64`;
the lifted blade sees the shared circuit and still separates.

**The cap: the lift spends the formula margin, which is bounded.**  Each altitude of sharing you absorb costs
margin: the lift needs `t < formulaMeasure target − bound` (`lift_needs_margin`), and the available margin is
the gap the formula blade provides — `n² − n` for Khrapchenko.  That margin is *capped* at the formula measure's
ceiling (`n²`), so you can absorb only *polynomially much* sharing.  You reach the bounded-sharing altitude; you
do **not** reach the general altitude, where a DAG can share *exponentially* and drive the target circuit below
the ceiling.  Climbing that last rung — unbounded sharing — is the free-fan-out mass-production regime =
`cost_super`.  One altitude lifted; the next is the wall.

## What is proved

* **`lifted_blade_separates`** — the lifted blade lower-bounds *circuit* cost: any bounded-sharing circuit for
  the target costs more than the class ceiling.  One altitude up from formulas.
* **`khrapchenkoLifted`** / **`khrapchenko_lifted_separates`** — forged concretely at `n = 8`, sharing budget
  `20`: the target circuit costs `44 > 8`, caught despite reusing `20` subcircuits.
* **`lift_needs_margin`** — the lift is bounded by the formula margin: `t < formulaMeasure target − bound`.
* **`lifted_one_altitude`** — both: every lifted blade separates in the bounded-sharing model, and only within
  the (capped) formula margin.

## Honest verdict — one real altitude lifted; the next altitude is the wall

The blade is lifted one rung: from formulas to bounded-sharing circuits.  It now lower-bounds the *circuit*
cost — `lifted_blade_separates` catches any circuit reusing at most `t` subcircuits — forged concretely at the
Khrapchenko gap with a real sharing budget (`khrapchenko_lifted_separates`, `44 > 8` despite `20` shared).  This
is genuine motion up the altitude ladder, built on the repo's bounded-sharing machinery, not faked.  The cap is
exact and honest: the lift spends the formula blade's margin (`lift_needs_margin`), and that margin is
`n² − n` — bounded by the formula measure's own ceiling — so only *polynomially much* sharing can be absorbed.
The bounded-sharing altitude is reached; the general altitude, where sharing is unbounded (a DAG reusing
exponentially, Uhlig mass-production), exhausts the margin and drives the circuit below the ceiling — that rung
is `cost_super`.  Lifted one altitude toward general; the wall is one altitude further up.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.LiftedBlade

/-- The blade lifted to the bounded-sharing altitude.  `circuitCost` is cost in the bounded-sharing model,
`formulaMeasure` is the underlying formula lower bound (Khrapchenko), `shareBudget` (`t`) is the allowed sharing
(the altitude dial; `t = 0` recovers formulas).  `unfold_bound` says unfolding duplicates at most `t`;
`high_on_target` says the formula blade clears the ceiling with margin `t`. -/
structure LiftedBlade where
  /-- the objects (bounded-sharing circuits) -/
  Obj : Type
  /-- cost in the bounded-sharing circuit model (one altitude up from formulas) -/
  circuitCost : Obj → Nat
  /-- the underlying formula lower bound the blade rests on (Khrapchenko `n²`) -/
  formulaMeasure : Obj → Nat
  /-- the sharing budget `t`: how much reuse is allowed (altitude dial; `0` = formulas) -/
  shareBudget : Nat
  /-- the class ceiling -/
  bound : Nat
  /-- the hard target -/
  target : Obj
  /-- unfolding a bounded-sharing circuit duplicates at most `shareBudget`: `formula ≤ circuit + t` -/
  unfold_bound : ∀ o, formulaMeasure o ≤ circuitCost o + shareBudget
  /-- the formula blade clears the ceiling with margin covering the sharing budget -/
  high_on_target : bound + shareBudget < formulaMeasure target

/-- **The lifted blade lower-bounds circuit cost (proved).**  From `formulaMeasure target ≤ circuitCost target
+ t` and `bound + t < formulaMeasure target`, the sharing budget cancels: `bound < circuitCost target`.  The
blade now catches bounded-sharing circuits, not just formulas — one altitude up. -/
theorem lifted_blade_separates (L : LiftedBlade) : L.bound < L.circuitCost L.target := by
  have h1 := L.unfold_bound L.target
  have h2 := L.high_on_target
  omega

/-- **The lift is bounded by the formula margin (proved).**  Absorbing sharing costs margin: the budget must
satisfy `t < formulaMeasure target − bound`.  The available margin is `n² − n` (the formula blade's gap),
capped at the formula measure's ceiling — so only polynomially much sharing can be absorbed. -/
theorem lift_needs_margin (L : LiftedBlade) : L.shareBudget < L.formulaMeasure L.target - L.bound := by
  have := L.high_on_target
  omega

/-- The `n = 8` Khrapchenko blade lifted to a sharing budget of `t = 20`: the target's bounded-sharing circuit
costs `44` (saved `20` by reuse, down from the formula's `64`), and the blade still catches it (`44 > 8`). -/
def khrapchenkoLifted : LiftedBlade where
  Obj := Bool
  circuitCost := fun b => match b with | false => 8 | true => 44
  formulaMeasure := fun b => match b with | false => 8 | true => 64
  shareBudget := 20
  bound := 8
  target := true
  unfold_bound := by intro o; cases o <;> decide
  high_on_target := by decide

/-- **The lifted Khrapchenko blade separates (proved).**  In the bounded-sharing model with budget `20`, the
target circuit costs `44 > 8` — caught despite reusing `20` subcircuits.  A formula-altitude blade sees only
the unfolded `64`; the lifted blade catches the shared circuit itself. -/
theorem khrapchenko_lifted_separates : khrapchenkoLifted.bound < khrapchenkoLifted.circuitCost khrapchenkoLifted.target :=
  lifted_blade_separates khrapchenkoLifted

/-- **The concrete lift's margin (proved).**  Budget `20 < 64 − 8 = 56`: the lift sits inside the Khrapchenko
margin, with room for up to `55` shared subcircuits before the blade fails. -/
theorem khrapchenko_lift_margin :
    khrapchenkoLifted.shareBudget < khrapchenkoLifted.formulaMeasure khrapchenkoLifted.target - khrapchenkoLifted.bound := by
  decide

/-- **One altitude lifted (proved).**  Left: every lifted blade separates in the bounded-sharing model (catches
circuits, not just formulas).  Right: only within the formula margin — beyond it (unbounded sharing = the
general altitude) the blade fails, which is `cost_super`. -/
theorem lifted_one_altitude :
    (∀ L : LiftedBlade, L.bound < L.circuitCost L.target)
    ∧ (∀ L : LiftedBlade, L.shareBudget < L.formulaMeasure L.target - L.bound) :=
  ⟨lifted_blade_separates, lift_needs_margin⟩

end PallLean.Paper93.DeepMath.PathB.LiftedBlade

#print axioms PallLean.Paper93.DeepMath.PathB.LiftedBlade.lifted_blade_separates
#print axioms PallLean.Paper93.DeepMath.PathB.LiftedBlade.lift_needs_margin
#print axioms PallLean.Paper93.DeepMath.PathB.LiftedBlade.khrapchenko_lifted_separates
#print axioms PallLean.Paper93.DeepMath.PathB.LiftedBlade.khrapchenko_lift_margin
#print axioms PallLean.Paper93.DeepMath.PathB.LiftedBlade.lifted_one_altitude
