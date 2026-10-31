import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSingleWallCapstone

/-!
# Proving the socket for SAT's specific seam — the attempt, the regime where it holds, and the wall

The ask: prove `SATSeamBoundedProduction` for SAT's *specific* seam — that SAT's composition seam never
mass-produces more than half a copy at any rung (`∀ d, 2·shared d ≤ D d`).  That statement, for SAT's
actual optimal-circuit demand, **is** `cost_super` = `P ≠ NP`.  This file attempts it honestly: it
isolates the exact regime in which the socket provably holds, gives the machine-checked proof there, and
shows precisely where SAT's *known* structure runs out — which is exactly the wall.

## The dichotomy: reach is the only lever

`SeamDisjointnessProbe` already established (with concrete circuits, machine-checked) the decisive fact:
**disjointness of the two copies does NOT bound the seam-collision — only a gate's REACH does**
(`collision_bounded_by_reach = mult_le_depCard`; `disjoint_admits_collision`: a disjoint tower still
carries a full-copy straddler).  So the socket for SAT's seam turns entirely on whether the collision
is bounded, and the only thing that bounds it is a reach bound.

## What is proved (the regime, and the failure mode — NOT the socket for SAT)

* **`socket_iff_no_large_collision`** — the socket holds **iff** no rung carries a near-total (`> ½`
  copy) straddler.  The exact obstruction, named at the seam.
* **`demand_stays_large` / `socket_holds_of_bounded_reach`** — THE positive result: if the seam-collision
  is bounded by a fixed reach budget `σ` (`∀ d, shared d ≤ σ`) and the base demand exceeds twice it
  (`2σ ≤ D 0`), then the demand stays `≥ 2σ` at every rung and the socket **holds for SAT's seam**.
  This is the bounded-reach / localized / formula regime — exactly where the crossing-number and
  Nečiporuk methods give real bounds, and exactly where they cap (`P ⊄ NC¹`).
* **`large_collision_breaks_socket`** — the failure mode: a single near-total straddler at any rung
  breaks the socket there.  So the socket needs the collision held below half a copy at *every* rung.
* **`free_reach_straddler_breaks_socket`** — the concrete free-reach witness: a seam whose straddler
  serves a *full* copy (`shared 0 = D 0`) violates the socket.  Without a reach bound, this is admitted.

## Honest verdict — proved where reach is bounded, open (= cost_super) where it is free

The socket for SAT's specific seam is **proved in the bounded-reach regime** (`socket_holds_of_bounded_reach`)
— which is every model where a circuit lower bound is actually proved, capped at `P ⊄ NC¹`.  It is
**open in the free-reach (general DAG) model**, because there the only ceiling on the collision is a
gate's reach, which is free — one global straddler serves a full copy (`free_reach_straddler_breaks_socket`),
and SAT's *known* structure (disjointness + the `O(1)` combiner) provably does **not** forbid it
(`SeamDisjointnessProbe`).  Proving the socket for SAT there means bounding SAT's optimal-circuit seam
collision below half a copy = ruling out the Uhlig global straddler = `cost_super` = `P ≠ NP`.  I have
proved it exactly as far as reach is bounded and stated plainly that the free-reach case is the wall.
Nothing here proves the socket for SAT in the general model, and nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SATSeamSocket

open PallLean.Paper93.DeepMath.PathB.DemandGrowthSeam
open PallLean.Paper93.DeepMath.PathB.SingleWallCapstone

/-! ### The exact obstruction, named at the seam -/

/-- **The socket ⟺ no near-total straddler (proved).**  SAT's seam satisfies the socket exactly when no
rung carries a collision exceeding half that copy.  The socket is precisely "no near-total mass
production at any rung". -/
theorem socket_iff_no_large_collision (S : SeamDemand) :
    SATSeamBoundedProduction S ↔ ∀ d, ¬ (S.D d < 2 * S.shared d) := by
  constructor
  · intro h d hbig; have hd := h d; omega
  · intro h d; have hd := h d; omega

/-! ### The regime where the socket holds: bounded reach -/

/-- **Bounded reach keeps the demand large (proved).**  If every seam-collision is at most a fixed reach
budget `σ` and the base demand is at least `2σ`, then the demand stays `≥ 2σ` at every rung: the seam law
`D(d+1) = 2·D d − shared d` loses at most `σ` per level from a base `≥ 2σ`, so it can never fall below
`2σ`.  This is the localized regime — bounded reach per gate. -/
theorem demand_stays_large (S : SeamDemand) (σ : ℕ)
    (hreach : ∀ d, S.shared d ≤ σ) (hbase : 2 * σ ≤ S.D 0) :
    ∀ d, 2 * σ ≤ S.D d := by
  intro d
  induction d with
  | zero => exact hbase
  | succ d ih =>
    have hs := S.seam d
    have hr := hreach d
    omega

/-- **Bounded reach ⟹ the socket holds for SAT's seam (proved) — the positive result, restricted.**  If
the seam-collision is bounded by a fixed reach budget `σ` (`∀ d, shared d ≤ σ`) and the base demand
exceeds twice it (`2σ ≤ D 0`), then `∀ d, 2·shared d ≤ D d`: the socket holds at every rung.  This is
exactly the bounded-reach / localized / formula regime — where the crossing-number and Nečiporuk methods
give real lower bounds, and exactly where they cap (`P ⊄ NC¹`).  The hypothesis `hreach` (a *fixed* reach
budget) IS the localization restriction; in the free-reach DAG model it fails. -/
theorem socket_holds_of_bounded_reach (S : SeamDemand) (σ : ℕ)
    (hreach : ∀ d, S.shared d ≤ σ) (hbase : 2 * σ ≤ S.D 0) :
    SATSeamBoundedProduction S := by
  intro d
  have hlarge := demand_stays_large S σ hreach hbase d
  have hr := hreach d
  omega

/-! ### The failure mode: an unbounded (free-reach) straddler -/

/-- **A near-total straddler breaks the socket (proved).**  If at some rung the collision exceeds half
that copy (`D d < 2·shared d`), the socket fails there.  So the socket requires the collision held below
half a copy at *every* rung — a reach bound that the free-reach model does not supply. -/
theorem large_collision_breaks_socket (S : SeamDemand) (d : ℕ)
    (hbig : S.D d < 2 * S.shared d) :
    ¬ SATSeamBoundedProduction S := by
  intro h
  have hd := h d
  omega

/-- **The free-reach witness (proved).**  A seam whose straddler serves a *full* copy at the base
(`shared 0 = D 0`) violates the socket.  Without a reach bound this straddler is admitted — the exact
escape `SeamDisjointnessProbe` exhibits with a concrete disjoint circuit: disjointness does not forbid a
full-copy global gate, only bounded reach does. -/
theorem free_reach_straddler_breaks_socket :
    collapsedSeam.shared 0 = collapsedSeam.D 0 ∧ ¬ SATSeamBoundedProduction collapsedSeam :=
  ⟨rfl, collapsed_violates_socket⟩

end PallLean.Paper93.DeepMath.PathB.SATSeamSocket

#print axioms PallLean.Paper93.DeepMath.PathB.SATSeamSocket.socket_iff_no_large_collision
#print axioms PallLean.Paper93.DeepMath.PathB.SATSeamSocket.demand_stays_large
#print axioms PallLean.Paper93.DeepMath.PathB.SATSeamSocket.socket_holds_of_bounded_reach
#print axioms PallLean.Paper93.DeepMath.PathB.SATSeamSocket.large_collision_breaks_socket
#print axioms PallLean.Paper93.DeepMath.PathB.SATSeamSocket.free_reach_straddler_breaks_socket
