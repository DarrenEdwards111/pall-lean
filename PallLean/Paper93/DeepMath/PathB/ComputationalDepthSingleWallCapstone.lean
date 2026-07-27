import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDemandGrowthSeam

/-!
# The single-wall capstone: the whole demand-side campaign rests on ONE named socket

Across this thread the wall `cost_super` was driven from ~28 angles — hub reach, seam collision, tower
climb, expander expansion, incompressibility, per-rung growth — and every one reduced to the *same*
statement.  This file makes that consolidation a formal object: it names the single demand-side wall,
proves the complete machine-checked chain from it to `SAT ∉ P`, proves it sits *exactly* at
`cost_super` (not a strengthening), and proves it is a genuine, non-vacuous constraint.

## The one socket

`SATSeamBoundedProduction S` — **SAT's composition seam admits at most half-a-copy of mass production
at every rung** (`∀ d, 2·shared d ≤ D d`).  This is the sharpest sufficient form of the wall: by
`DemandGrowthSeam.bounded_collision_ratio_three_halves`, a seam that never mass-produces more than half
a copy still grows at ratio `3/2`, hence superpolynomially.  SAT need not resist *all* sharing — only
*near-total* mass production.

## What is proved (the chain, and the non-vacuity — NOT the socket)

* **`socket_gives_growth`** — the socket ⟹ multiplicative growth of SAT's tower demand.  Purely on the
  demand side, no other open input.
* **`socket_gives_three_halves`** — the socket ⟹ the `3/2` per-rung ratio; this is the `cost_super`
  content in its minimal sufficient form.
* **`tight_socket_iff_doubling`** — the tight boundary: zero seam collision (`shared ≡ 0`) ⟺ full
  per-rung doubling.  The socket's exact-doubling face is `cost_super` verbatim.
* **`socket_wires_to_separation` / `socket_implies_sat_not_in_P`** — the socket, *together with the
  identification bridge* `separation_iff_growth` (SAT ∉ P ⟺ the tower grows), yields `SAT ∉ P` through
  the RFT observers.  Both inputs are `cost_super`-family and are supplied as hypotheses, discharged
  nowhere.
* **`growth_break_needs_socket_violation`** — necessity: growth can only break where the socket is
  violated (a near-total straddler).  So the socket is the genuine pivot, not a convenient sufficient
  condition.
* **`doubling_satisfies_socket` / `collapsed_violates_socket`** — the socket is a *real* constraint: it
  holds on the doubling world (`D d = 2^d`, `shared ≡ 0`) and fails on the collapsed world
  (`D ≡ 1`, `shared ≡ 1`).  Not vacuous, not unsatisfiable — it separates growth from collapse.

## Honest verdict — this consolidates the wall, it does not cross it

The campaign has exactly two faces of one wall: the **demand-side socket** (`SATSeamBoundedProduction`)
and the **identification bridge** (`separation_iff_growth`).  This file names both, proves everything
*between* them, and proves neither is vacuous.  What it does NOT do — what nothing known does — is
prove the socket for SAT: that SAT's seam actually stays below half a copy at every rung.  That is
`cost_super`, it is `P ≠ NP`-strength, and it is discharged nowhere here.  Every route in this thread
lands on this single stone; this file is the stone, named and cornered, not a crossing.  Nothing here
is `P ≠ NP`, and nothing here makes it unprovable.
-/

namespace PallLean.Paper93.DeepMath.PathB.SingleWallCapstone

open PallLean.Paper93.DeepMath.PathB.DemandGrowthSeam
open PallLean.Paper93.DeepMath.PathB.RFTCostSuperBridge
open PallLean.Paper93.DeepMath.PathB.GodMoveBridgeRFT

/-- **The single demand-side wall.**  SAT's composition seam admits at most half a copy of mass
production at every rung: `∀ d, 2·shared d ≤ D d`.  The sharpest sufficient form of `cost_super` — SAT
need only resist *near-total* mass production, not all sharing. -/
def SATSeamBoundedProduction (S : SeamDemand) : Prop := ∀ d, 2 * S.shared d ≤ S.D d

/-! ### The chain: socket ⟹ growth ⟹ separation -/

/-- **The socket gives multiplicative growth (proved).**  If SAT's seam never mass-produces more than
half a copy, the tower demand grows multiplicatively.  Pure demand side — no second open input. -/
theorem socket_gives_growth (S : SeamDemand) (h : SATSeamBoundedProduction S) :
    MultiplicativeGrowth S.toTower :=
  seam_multiplicative_growth S h

/-- **The socket gives the `3/2` ratio (proved).**  The socket implies the per-rung ratio-`3/2`
premise — the `cost_super` content in its minimal sufficient form (factor 2 not needed). -/
theorem socket_gives_three_halves (S : SeamDemand) (h : SATSeamBoundedProduction S) :
    ∀ d, 3 * S.D d ≤ 2 * S.D (d + 1) :=
  bounded_collision_ratio_three_halves S h

/-- **The tight boundary IS doubling (proved).**  Zero seam collision (`shared ≡ 0`) holds exactly when
the demand fully doubles at every rung.  The socket's exact-doubling face is `cost_super` verbatim. -/
theorem tight_socket_iff_doubling (S : SeamDemand) :
    (∀ d, S.shared d = 0) ↔ (∀ d, 2 * S.D d ≤ S.D (d + 1)) :=
  (growth_iff_no_collision S).symm

/-- **Socket + identification bridge ⟹ the observers differ (proved).**  Through the RFT bridge, the
socket forces the P-observer and God-observer to have different reachable sets on SAT — non-equivalence.
The bridge `separation_iff_growth` is itself `cost_super` and is supplied as a hypothesis. -/
theorem socket_wires_to_separation {Problem : Type} (P G : Observer Problem) (sat : Problem)
    (S : SeamDemand)
    (hPG : ∀ x, P x → G x) (hGsat : G sat) (complete : P sat → ∀ x, G x → P x)
    (separation_iff_growth : ¬ P sat ↔ MultiplicativeGrowth S.toTower)
    (h : SATSeamBoundedProduction S) :
    ¬ ObsEquiv P G :=
  seam_forces_observer_difference P G sat S hPG hGsat complete separation_iff_growth h

/-- **Socket + identification bridge ⟹ `SAT ∉ P` (proved).**  The full crossing, IF both `cost_super`
inputs are granted: the demand-side socket and the identification bridge.  Neither is proved here — this
is the exact price of `P ≠ NP`, stated as two named open hypotheses. -/
theorem socket_implies_sat_not_in_P {Problem : Type} (P G : Observer Problem) (sat : Problem)
    (S : SeamDemand)
    (hPG : ∀ x, P x → G x) (hGsat : G sat) (complete : P sat → ∀ x, G x → P x)
    (separation_iff_growth : ¬ P sat ↔ MultiplicativeGrowth S.toTower)
    (h : SATSeamBoundedProduction S) :
    ¬ P sat :=
  (nonequiv_iff_separation P G sat hPG hGsat complete).mp
    (socket_wires_to_separation P G sat S hPG hGsat complete separation_iff_growth h)

/-! ### Necessity: growth breaks only where the socket is violated -/

/-- **Growth-break requires a socket violation (proved).**  To drop below ratio `3/2` at a rung, the
seam-collision must exceed half that copy — a violation of the socket at that rung.  So the socket is
the genuine pivot: growth is sustained precisely while it holds. -/
theorem growth_break_needs_socket_violation (S : SeamDemand) (d : ℕ)
    (hbreak : 2 * S.D (d + 1) < 3 * S.D d) :
    S.D d < 2 * S.shared d :=
  collapse_needs_large_collision S d hbreak

/-! ### Non-vacuity: the socket separates the growing world from the collapsed one -/

/-- The **doubling world**: `D d = 2^d`, no seam collision.  The demand doubles at every rung. -/
def doublingSeam : SeamDemand where
  D := fun d => 2 ^ d
  shared := fun _ => 0
  base := by have h : (2 : ℕ) ^ 0 = 1 := Nat.pow_zero 2; omega
  seam := by intro d; rw [Nat.add_zero, Nat.pow_succ, Nat.mul_comm]

/-- The **collapsed world**: `D ≡ 1`, `shared ≡ 1`.  A full straddler serves the whole copy at every
rung; the demand never grows. -/
def collapsedSeam : SeamDemand where
  D := fun _ => 1
  shared := fun _ => 1
  base := by decide
  seam := by intro d; decide

/-- **The socket holds on the doubling world (proved).**  `2·0 ≤ 2^d` — the growing world satisfies
the socket, so the socket is satisfiable, not vacuously false. -/
theorem doubling_satisfies_socket : SATSeamBoundedProduction doublingSeam := by
  intro d
  have h : doublingSeam.shared d = 0 := rfl
  rw [h]
  omega

/-- **The socket fails on the collapsed world (proved).**  `2·1 ≤ 1` is false, so the collapsed world
violates the socket.  The socket is a genuine constraint — it distinguishes growth from collapse. -/
theorem collapsed_violates_socket : ¬ SATSeamBoundedProduction collapsedSeam := by
  intro h
  have h0 := h 0
  have e1 : collapsedSeam.shared 0 = 1 := rfl
  have e2 : collapsedSeam.D 0 = 1 := rfl
  rw [e1, e2] at h0
  omega

end PallLean.Paper93.DeepMath.PathB.SingleWallCapstone

#print axioms PallLean.Paper93.DeepMath.PathB.SingleWallCapstone.socket_gives_growth
#print axioms PallLean.Paper93.DeepMath.PathB.SingleWallCapstone.socket_gives_three_halves
#print axioms PallLean.Paper93.DeepMath.PathB.SingleWallCapstone.tight_socket_iff_doubling
#print axioms PallLean.Paper93.DeepMath.PathB.SingleWallCapstone.socket_wires_to_separation
#print axioms PallLean.Paper93.DeepMath.PathB.SingleWallCapstone.socket_implies_sat_not_in_P
#print axioms PallLean.Paper93.DeepMath.PathB.SingleWallCapstone.growth_break_needs_socket_violation
#print axioms PallLean.Paper93.DeepMath.PathB.SingleWallCapstone.doubling_satisfies_socket
#print axioms PallLean.Paper93.DeepMath.PathB.SingleWallCapstone.collapsed_violates_socket
