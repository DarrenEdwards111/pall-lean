import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATSeamSocket

/-!
# The next step: attacking the reach bound directly — the exact threshold, and the Uhlig wall it hits

`SATSeamSocket` reduced the socket for SAT's seam to a reach bound and proved it in the bounded-reach
regime.  The next step is to attack that reach bound head-on: *how much* reach does a socket-breaking
straddler actually need, and is there a SAT-specific reason it can't have it?  This file sharpens the
requirement to an exact threshold and lands on precisely what SAT would have to defeat — Uhlig's mass
production.

## The sharpening: the reach bound is only needed at the half-copy threshold

You do not need bounded reach (a fixed `σ`) for the socket — you only need the straddler's reach held
**below half a copy at each rung**.  Proved both directions:

* **`socket_breaker_is_near_global`** — a straddler that breaks the socket at rung `d` must have reach
  `> ½·D d`: it reads *more than half a copy*.  A socket-breaker is a **near-global** gate.
* **`half_copy_reach_forces_socket`** — conversely, if every rung's straddler reach is `≤ ½·D d`, the
  socket holds.  No induction, no base condition: the per-rung half-copy reach bound alone suffices.
* **`socket_iff_reach_below_half`** — for a tight straddler (reach = collision served), the socket holds
  **iff** the reach stays `≤ ½·D d` at every rung.  The socket for SAT's seam IS "the seam straddler
  reads at most half a copy, forever".

## Where it lands: the near-global straddler is a Uhlig mass-production template

* **`full_copy_straddler_breaks`** — the witness: a straddler reading a *full* copy (`reach = D 0`) is
  near-global and breaks the socket.  This is admitted in the free-reach model.

A gate that reads `> ½` of a copy and serves *both* disjoint copies is exactly an Uhlig
mass-production template — a single high-reach sub-computation reused across disjoint outputs via
downstream cancellation.  Uhlig's theorem says such sharing across disjoint copies **is** possible in
general; that is why `SeamDisjointnessProbe` found disjointness insufficient.

## Honest verdict — sharpened to the half-copy threshold, still the same wall

The reach bound for SAT's seam is sharpened to its exact form: **no straddler reads more than half a
copy at any rung**.  That is strictly a threshold statement (not "bounded reach"), and it is still open,
because a socket-breaker is precisely a near-global gate reading `> ½` a copy and serving both copies —
an Uhlig mass-production template.  Forbidding it for SAT is forbidding beneficial mass production across
SAT's seam = the surviving Uhlig `NonlinearHorn` of `CostSuperDichotomy` = `cost_super` = `P ≠ NP`.  The
next step reaches the wall from the reach direction and pins the exact threshold; SAT's known structure
(disjointness, which Uhlig's theorem shows does *not* forbid mass production) does not cross it.  Nothing
here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SATSeamReachThreshold

open PallLean.Paper93.DeepMath.PathB.DemandGrowthSeam
open PallLean.Paper93.DeepMath.PathB.SingleWallCapstone

/-- **A seam straddler at rung `d`**: a gate carrying the rung's cross-copy collision, with a `reach`
(how many variables it reads).  The ruler `shared d ≤ reach` is `SeamDisjointnessProbe`'s
`collision_bounded_by_reach = mult_le_depCard`, lifted to the demand level: a gate cannot serve more
copies' demand than it reaches. -/
structure SeamStraddler (S : SeamDemand) (d : ℕ) where
  /-- variables the straddler reads (its reach / depCard) -/
  reach : ℕ
  /-- the ruler: the collision it carries is bounded by its reach -/
  ruler : S.shared d ≤ reach

/-! ### The threshold: a socket-breaker is near-global -/

/-- **A socket-breaker reads more than half a copy (proved).**  If the straddler breaks the socket at
rung `d` (`D d < 2·shared d`), then its reach exceeds half the copy: `D d < 2·reach`.  A socket-breaker
is a **near-global** gate — it reads `> ½` of a copy. -/
theorem socket_breaker_is_near_global (S : SeamDemand) (d : ℕ) (st : SeamStraddler S d)
    (hbreak : S.D d < 2 * S.shared d) :
    S.D d < 2 * st.reach := by
  have hr := st.ruler
  omega

/-- **Half-copy reach at one rung forces the socket there (proved).**  If the straddler's reach is at
most half the copy (`2·reach ≤ D d`), the socket holds at that rung.  The local converse of
`socket_breaker_is_near_global`. -/
theorem half_copy_reach_forces_socket_at (S : SeamDemand) (d : ℕ) (st : SeamStraddler S d)
    (hlocal : 2 * st.reach ≤ S.D d) :
    2 * S.shared d ≤ S.D d := by
  have hr := st.ruler
  omega

/-! ### The exact reach bound for the whole socket -/

/-- **Half-copy reach at every rung ⟹ the socket holds (proved) — the sharpened positive result.**  If
the seam-collision's reach is at most half the copy at *every* rung (`∀ d, 2·reach d ≤ D d`), the socket
holds.  No fixed reach budget, no base condition, no induction — the per-rung half-copy threshold alone
suffices.  Strictly weaker hypothesis than `SATSeamSocket.socket_holds_of_bounded_reach`. -/
theorem half_copy_reach_forces_socket (S : SeamDemand) (reach : ℕ → ℕ)
    (hruler : ∀ d, S.shared d ≤ reach d) (hlocal : ∀ d, 2 * reach d ≤ S.D d) :
    SATSeamBoundedProduction S := by
  intro d
  have hr := hruler d
  have hl := hlocal d
  omega

/-- **The socket IS "reach stays below half a copy, forever" (proved).**  For a tight straddler (reach
equals the collision it serves), the socket holds **iff** the reach is `≤ ½·D d` at every rung.  This is
the exact reach-threshold form of the socket for SAT's seam. -/
theorem socket_iff_reach_below_half (S : SeamDemand) (reach : ℕ → ℕ)
    (htight : ∀ d, reach d = S.shared d) :
    SATSeamBoundedProduction S ↔ ∀ d, 2 * reach d ≤ S.D d := by
  constructor
  · intro h d; rw [htight d]; exact h d
  · intro h d; have hd := h d; rw [htight d] at hd; exact hd

/-! ### The free-reach witness: a full-copy straddler -/

/-- **A full-copy straddler breaks the socket (proved).**  A straddler reading a *full* copy
(`reach = D 0`) is near-global (`D 0 < 2·reach`) and breaks the socket — the concrete Uhlig
mass-production template, admitted in the free-reach model.  Instantiated on `collapsedSeam`. -/
theorem full_copy_straddler_breaks :
    ∃ (S : SeamDemand) (st : SeamStraddler S 0),
      S.D 0 < 2 * st.reach ∧ ¬ SATSeamBoundedProduction S := by
  refine ⟨collapsedSeam, ⟨1, ?_⟩, ?_, collapsed_violates_socket⟩
  · show collapsedSeam.shared 0 ≤ 1
    decide
  · show collapsedSeam.D 0 < 2 * 1
    decide

end PallLean.Paper93.DeepMath.PathB.SATSeamReachThreshold

#print axioms PallLean.Paper93.DeepMath.PathB.SATSeamReachThreshold.socket_breaker_is_near_global
#print axioms PallLean.Paper93.DeepMath.PathB.SATSeamReachThreshold.half_copy_reach_forces_socket_at
#print axioms PallLean.Paper93.DeepMath.PathB.SATSeamReachThreshold.half_copy_reach_forces_socket
#print axioms PallLean.Paper93.DeepMath.PathB.SATSeamReachThreshold.socket_iff_reach_below_half
#print axioms PallLean.Paper93.DeepMath.PathB.SATSeamReachThreshold.full_copy_straddler_breaks
