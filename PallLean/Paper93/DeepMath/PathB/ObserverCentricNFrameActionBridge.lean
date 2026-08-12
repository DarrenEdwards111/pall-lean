import PallLean.Paper93.DeepMath.PathB.ObserverTrajectoryDCEW
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverTimeDebt
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFoolingDebt

/-!
# Observer-centric N-frame action bridge

This file connects the trajectory-local N-frame/God-Move minor to observer
time.  It does not assume the missing SAT extraction theorem.  Instead it
isolates the exact dynamic certificate that extraction must produce and proves
the complete cash-out:

* the minor supplies a binomial lower bound on live distinguishability;
* debt conservation forces any correct observer to service that debt through
  its time-integrated boundary action;
* therefore an exponent-parametric supply of such certificates rules out every
  fixed polynomial action bound.

The remaining open statement is now a single operational quantifier: construct
one such certificate for every polynomial-time SAT trajectory.  No machine
construction or tape-layout premise appears in that statement.
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverCentricNFrameActionBridge

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ObserverTimeDebt
open PallLean.Paper93.DeepMath.PathB.BoundaryDebt

/-- Observer-time servicing data attached to a concrete trajectory-local
N-frame minor.  `initialDebt_ge_liveRank` is the substantive semantic link:
the distinguishability exposed by the minor is present in the observer's
initial unresolved debt. -/
structure TrajectoryNFrameActionCertificate
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    (minor : TrajectoryGodMoveBoundaryMinor enc T n) where
  debt : Nat → Nat
  rate : Nat → Nat
  horizon : Nat
  service : ∀ t, debt t ≤ debt (t + 1) + rate t
  cleared : debt horizon = 0
  initialDebt_ge_liveRank : minor.liveRank ≤ debt 0

/-- A grounded certificate replaces the free inequality
`liveRank ≤ initialDebt` by an explicit family `mergedPairs` of
must-separate continuation pairs that the initial boundary view merges.

The only substantive inputs are now visible data: the pairs really belong to
the must-separate relation, the view really merges them, and there are at least
`liveRank` of them. -/
structure GroundedTrajectoryNFrameActionCertificate
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    (minor : TrajectoryGodMoveBoundaryMinor enc T n)
    (X S : Type*) [DecidableEq S] where
  mustSeparate : Finset (X × X)
  initialView : X → S
  mergedPairs : Finset (X × X)
  mergedPairs_subset : mergedPairs ⊆ mustSeparate
  mergedPairs_merged :
    ∀ p ∈ mergedPairs, initialView p.1 = initialView p.2
  liveRank_le_mergedPairs : minor.liveRank ≤ mergedPairs.card
  debt : Nat → Nat
  rate : Nat → Nat
  horizon : Nat
  initialDebt : debt 0 = debtCount mustSeparate initialView
  service : ∀ t, debt t ≤ debt (t + 1) + rate t
  cleared : debt horizon = 0

/-- Explicit merged must-separate pairs generate the abstract action
certificate.  Thus the live-rank/debt link is no longer an unconstrained field. -/
def GroundedTrajectoryNFrameActionCertificate.toActionCertificate
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    {minor : TrajectoryGodMoveBoundaryMinor enc T n}
    {X S : Type*} [DecidableEq S]
    (cert : GroundedTrajectoryNFrameActionCertificate minor X S) :
    TrajectoryNFrameActionCertificate minor where
  debt := cert.debt
  rate := cert.rate
  horizon := cert.horizon
  service := cert.service
  cleared := cert.cleared
  initialDebt_ge_liveRank := by
    rw [cert.initialDebt]
    exact le_trans cert.liveRank_le_mergedPairs
      (merge_creates_debt cert.mustSeparate cert.initialView
        cert.mergedPairs_subset cert.mergedPairs_merged)

/-- Construct the explicit merged-pair geometry canonically from a fooling set
and a finite boundary view.  The merged family is exactly the filtered
must-separate relation.  Pigeonhole counting supplies
`P.card - m ≤ debtCount`, so it suffices that the N-frame live rank fit below
that unavoidable collision count. -/
def groundedCertificateOfFoolingSet
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    (minor : TrajectoryGodMoveBoundaryMinor enc T n)
    {X : Type*} [DecidableEq X]
    {m : Nat}
    (P : Finset X) (view : X → Fin m) (F : Finset (X × X))
    (hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ F)
    (hrank : minor.liveRank ≤ P.card - m)
    (debt : Nat → Nat) (rate : Nat → Nat) (horizon : Nat)
    (hinitial : debt 0 = debtCount F view)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + rate t)
    (hcleared : debt horizon = 0) :
    GroundedTrajectoryNFrameActionCertificate minor X (Fin m) where
  mustSeparate := F
  initialView := view
  mergedPairs := F.filter (fun p => view p.1 = view p.2)
  mergedPairs_subset := Finset.filter_subset _ _
  mergedPairs_merged := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  liveRank_le_mergedPairs := by
    change minor.liveRank ≤ debtCount F view
    exact le_trans hrank (foolingSet_forces_debt P view F hfool)
  debt := debt
  rate := rate
  horizon := horizon
  initialDebt := hinitial
  service := hservice
  cleared := hcleared

/-- The minimal combinatorial certificate now required from SAT/N-frame
geometry.  It contains a large continuation fooling set and a finite boundary
view; the merged-pair family itself is derived, not supplied. -/
structure TrajectoryNFrameFoolingCertificate
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    (minor : TrajectoryGodMoveBoundaryMinor enc T n)
    (X : Type*) [DecidableEq X] where
  stateCount : Nat
  sectors : Finset X
  view : X → Fin stateCount
  mustSeparate : Finset (X × X)
  fooling : ∀ x ∈ sectors, ∀ y ∈ sectors, x ≠ y →
    (x, y) ∈ mustSeparate
  rank_fits_collisions : minor.liveRank ≤ sectors.card - stateCount
  debt : Nat → Nat
  rate : Nat → Nat
  horizon : Nat
  initialDebt : debt 0 = debtCount mustSeparate view
  service : ∀ t, debt t ≤ debt (t + 1) + rate t
  cleared : debt horizon = 0

/-- Static half of the remaining theorem: SAT continuation geometry at one
live N-frame minor.  This contains no temporal accounting. -/
structure TrajectoryNFrameContinuationGeometry
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    (minor : TrajectoryGodMoveBoundaryMinor enc T n)
    (X : Type*) [DecidableEq X] where
  stateCount : Nat
  sectors : Finset X
  view : X → Fin stateCount
  mustSeparate : Finset (X × X)
  fooling : ∀ x ∈ sectors, ∀ y ∈ sectors, x ≠ y →
    (x, y) ∈ mustSeparate
  rank_fits_collisions : minor.liveRank ≤ sectors.card - stateCount

/-- Dynamic half of the remaining theorem for a fixed continuation geometry:
the actual initial collision debt evolves locally and is cleared by the
observer's successful computation. -/
structure TrajectoryNFrameLocalServicing
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    {minor : TrajectoryGodMoveBoundaryMinor enc T n}
    {X : Type*} [DecidableEq X]
    (geometry : TrajectoryNFrameContinuationGeometry minor X) where
  debt : Nat → Nat
  rate : Nat → Nat
  horizon : Nat
  initialDebt : debt 0 = debtCount geometry.mustSeparate geometry.view
  service : ∀ t, debt t ≤ debt (t + 1) + rate t
  cleared : debt horizon = 0

/-- Static continuation geometry and dynamic local servicing assemble into the
minimal fooling certificate. -/
def TrajectoryNFrameContinuationGeometry.withServicing
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    {minor : TrajectoryGodMoveBoundaryMinor enc T n}
    {X : Type*} [DecidableEq X]
    (geometry : TrajectoryNFrameContinuationGeometry minor X)
    (servicing : TrajectoryNFrameLocalServicing geometry) :
    TrajectoryNFrameFoolingCertificate minor X where
  stateCount := geometry.stateCount
  sectors := geometry.sectors
  view := geometry.view
  mustSeparate := geometry.mustSeparate
  fooling := geometry.fooling
  rank_fits_collisions := geometry.rank_fits_collisions
  debt := servicing.debt
  rate := servicing.rate
  horizon := servicing.horizon
  initialDebt := servicing.initialDebt
  service := servicing.service
  cleared := servicing.cleared

/-- A fooling-set certificate canonically produces the grounded merged-pair
certificate. -/
def TrajectoryNFrameFoolingCertificate.toGrounded
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    {minor : TrajectoryGodMoveBoundaryMinor enc T n}
    {X : Type*} [DecidableEq X]
    (cert : TrajectoryNFrameFoolingCertificate minor X) :
    GroundedTrajectoryNFrameActionCertificate minor X (Fin cert.stateCount) :=
  groundedCertificateOfFoolingSet minor cert.sectors cert.view
    cert.mustSeparate cert.fooling cert.rank_fits_collisions cert.debt
    cert.rate cert.horizon cert.initialDebt cert.service cert.cleared

/-- A correct observer carrying a trajectory-local N-frame minor must spend at
least the minor's live rank in time-integrated boundary action. -/
theorem liveRank_le_action
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    (minor : TrajectoryGodMoveBoundaryMinor enc T n)
    (cert : TrajectoryNFrameActionCertificate minor) :
    minor.liveRank ≤ observerTimeAction cert.rate cert.horizon := by
  exact le_trans cert.initialDebt_ge_liveRank
    (correct_needs_action cert.debt cert.rate cert.service cert.horizon
      cert.cleared)

/-- The full N-frame lower bound transfers to observer-time action. -/
theorem binomial_le_action
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    (minor : TrajectoryGodMoveBoundaryMinor enc T n)
    (cert : TrajectoryNFrameActionCertificate minor) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      observerTimeAction cert.rate cert.horizon :=
  le_trans minor.rank_lower (liveRank_le_action minor cert)

/-- Fully grounded cash-out: an explicit merged family of continuation pairs
forces the binomial N-frame action lower bound. -/
theorem binomial_le_action_of_grounded
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    (minor : TrajectoryGodMoveBoundaryMinor enc T n)
    {X S : Type*} [DecidableEq S]
    (cert : GroundedTrajectoryNFrameActionCertificate minor X S) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      observerTimeAction cert.rate cert.horizon :=
  binomial_le_action minor cert.toActionCertificate

/-- A trajectory has an N-frame action certificate at length `n` when it has a
live minor together with honest observer-time debt servicing data. -/
def HasTrajectoryNFrameActionCertificateAt
    (enc : ThreeCNFEncoding) (T : TrajectoryObserverMachine) (n : Nat) : Prop :=
  ∃ minor : TrajectoryGodMoveBoundaryMinor enc T n,
    Nonempty (TrajectoryNFrameActionCertificate minor)

/-- Grounded version of the fixed-length certificate: the witness includes an
actual continuation universe, boundary-state type, and merged must-separate
pair family. -/
def HasGroundedTrajectoryNFrameActionCertificateAt
    (enc : ThreeCNFEncoding) (T : TrajectoryObserverMachine) (n : Nat) : Prop :=
  ∃ (minor : TrajectoryGodMoveBoundaryMinor enc T n)
      (X S : Type) (_inst : DecidableEq S),
    Nonempty (GroundedTrajectoryNFrameActionCertificate minor X S)

/-- Fixed-length certificate phrased only through a fooling set and finite
boundary capacity. -/
def HasTrajectoryNFrameFoolingCertificateAt
    (enc : ThreeCNFEncoding) (T : TrajectoryObserverMachine) (n : Nat) : Prop :=
  ∃ (minor : TrajectoryGodMoveBoundaryMinor enc T n)
      (X : Type) (_inst : DecidableEq X),
    Nonempty (TrajectoryNFrameFoolingCertificate minor X)

/-- Fixed-length frontier split into its static and dynamic halves. -/
def HasTrajectoryNFrameGeometryAndServicingAt
    (enc : ThreeCNFEncoding) (T : TrajectoryObserverMachine) (n : Nat) : Prop :=
  ∃ (minor : TrajectoryGodMoveBoundaryMinor enc T n)
      (X : Type) (_inst : DecidableEq X)
      (geometry : TrajectoryNFrameContinuationGeometry minor X),
    Nonempty (TrajectoryNFrameLocalServicing geometry)

/-- The two honest obligations assemble without any further mathematical
assumption. -/
theorem hasFoolingCertificate_of_geometryAndServicing
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    (h : HasTrajectoryNFrameGeometryAndServicingAt enc T n) :
    HasTrajectoryNFrameFoolingCertificateAt enc T n := by
  rcases h with ⟨minor, X, inst, geometry, hservicing⟩
  letI : DecidableEq X := inst
  rcases hservicing with ⟨servicing⟩
  exact ⟨minor, X, inferInstance,
    ⟨geometry.withServicing servicing⟩⟩

/-- Fooling-set geometry supplies the fully grounded action certificate. -/
theorem hasGroundedCertificate_of_fooling
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    (h : HasTrajectoryNFrameFoolingCertificateAt enc T n) :
    HasGroundedTrajectoryNFrameActionCertificateAt enc T n := by
  rcases h with ⟨minor, X, inst, hcert⟩
  letI : DecidableEq X := inst
  rcases hcert with ⟨cert⟩
  exact ⟨minor, X, Fin cert.stateCount, inferInstance,
    ⟨cert.toGrounded⟩⟩

/-- Forgetting the explicit pair geometry yields the abstract action
certificate used by the generic conservation cash-out. -/
theorem hasTrajectoryCertificate_of_grounded
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    (h : HasGroundedTrajectoryNFrameActionCertificateAt enc T n) :
    HasTrajectoryNFrameActionCertificateAt enc T n := by
  rcases h with ⟨minor, X, S, inst, hcert⟩
  letI : DecidableEq S := inst
  rcases hcert with ⟨cert⟩
  exact ⟨minor, ⟨cert.toActionCertificate⟩⟩

/-- The action paid by a chosen certificate. -/
def certificateAction
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    {minor : TrajectoryGodMoveBoundaryMinor enc T n}
    (cert : TrajectoryNFrameActionCertificate minor) : Nat :=
  observerTimeAction cert.rate cert.horizon

/-- At the arithmetic extraction scale, every N-frame action certificate costs
strictly more than `n^c`. -/
theorem action_gt_polynomial_of_certificate
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n c : Nat}
    (hn20 : n ≥ 2 ^ 20)
    (hlog : 4 * (c + 1) ≤ Nat.log 2 n)
    (minor : TrajectoryGodMoveBoundaryMinor enc T n)
    (cert : TrajectoryNFrameActionCertificate minor) :
    n ^ c < certificateAction cert := by
  exact lt_of_lt_of_le
    (arithmetic_gap_for_exponent c n hn20 hlog)
    (binomial_le_action minor cert)

/-- The exact observer-centric N-frame frontier, with the DTM time exponent
visible.  For each time exponent `e` and candidate action exponent `c`, one
length works for every SAT observer backed by a DTM of exponent at most `e`.

This is deliberately a definition, not an assertion. -/
def TimeExponentParametricOperationalSATNFrameActionExtraction
    (enc : ThreeCNFEncoding) : Prop :=
  ∀ e c : Nat, ∃ n : Nat,
    n ≥ 2 ^ 20 ∧
    4 * (c + 1) ≤ Nat.log 2 n ∧
    ∀ T : TrajectoryObserverMachine,
      OperationalTrajectoryObserverDecidesSATAtMost enc e T →
      HasTrajectoryNFrameActionCertificateAt enc T n

/-- Fully grounded observer-centric frontier.  This is the precise new-math
target: every bounded-time SAT trajectory must exhibit enough explicitly
merged, must-separate continuations to support its live N-frame minor. -/
def TimeExponentParametricOperationalSATGroundedNFrameActionExtraction
    (enc : ThreeCNFEncoding) : Prop :=
  ∀ e c : Nat, ∃ n : Nat,
    n ≥ 2 ^ 20 ∧
    4 * (c + 1) ≤ Nat.log 2 n ∧
    ∀ T : TrajectoryObserverMachine,
      OperationalTrajectoryObserverDecidesSATAtMost enc e T →
      HasGroundedTrajectoryNFrameActionCertificateAt enc T n

/-- Universal static+dynamic N-frame program.  This formulation identifies
the two remaining theorem families separately: continuation non-collapse and
local debt servicing. -/
def TimeExponentParametricOperationalSATNFrameGeometryAndServicing
    (enc : ThreeCNFEncoding) : Prop :=
  ∀ e c : Nat, ∃ n : Nat,
    n ≥ 2 ^ 20 ∧
    4 * (c + 1) ≤ Nat.log 2 n ∧
    ∀ T : TrajectoryObserverMachine,
      OperationalTrajectoryObserverDecidesSATAtMost enc e T →
      HasTrajectoryNFrameGeometryAndServicingAt enc T n

/-- The split static/dynamic program implies the fully grounded extraction
theorem. -/
theorem groundedExtraction_of_geometryAndServicing
    (enc : ThreeCNFEncoding)
    (hprogram :
      TimeExponentParametricOperationalSATNFrameGeometryAndServicing enc) :
    TimeExponentParametricOperationalSATGroundedNFrameActionExtraction enc := by
  intro e c
  rcases hprogram e c with ⟨n, hn20, hlog, hcert⟩
  refine ⟨n, hn20, hlog, ?_⟩
  intro T hT
  exact hasGroundedCertificate_of_fooling
    (hasFoolingCertificate_of_geometryAndServicing (hcert T hT))

/-- The grounded continuation-pair theorem supplies the abstract extraction
socket without any additional hypothesis. -/
theorem nframeActionExtraction_of_grounded
    (enc : ThreeCNFEncoding)
    (hgrounded :
      TimeExponentParametricOperationalSATGroundedNFrameActionExtraction enc) :
    TimeExponentParametricOperationalSATNFrameActionExtraction enc := by
  intro e c
  rcases hgrounded e c with ⟨n, hn20, hlog, hcert⟩
  exact ⟨n, hn20, hlog, fun T hT =>
    hasTrajectoryCertificate_of_grounded (hcert T hT)⟩

/-- Cash-out of the observer-centric frontier: the extracted certificate for
every bounded-time SAT trajectory necessarily has super-`n^c` action at the
chosen scale. -/
theorem operationalSAT_action_lower_of_nframe_extraction
    (enc : ThreeCNFEncoding)
    (hextract : TimeExponentParametricOperationalSATNFrameActionExtraction enc)
    (e c : Nat) :
    ∃ n : Nat,
      n ≥ 2 ^ 20 ∧
      4 * (c + 1) ≤ Nat.log 2 n ∧
      ∀ T : TrajectoryObserverMachine,
        OperationalTrajectoryObserverDecidesSATAtMost enc e T →
        ∃ minor : TrajectoryGodMoveBoundaryMinor enc T n,
          ∃ cert : TrajectoryNFrameActionCertificate minor,
            n ^ c < certificateAction cert := by
  rcases hextract e c with ⟨n, hn20, hlog, hextract_at⟩
  refine ⟨n, hn20, hlog, ?_⟩
  intro T hT
  rcases hextract_at T hT with ⟨minor, hcert⟩
  rcases hcert with ⟨cert⟩
  exact ⟨minor, cert,
    action_gt_polynomial_of_certificate hn20 hlog minor cert⟩

#print axioms liveRank_le_action
#print axioms GroundedTrajectoryNFrameActionCertificate.toActionCertificate
#print axioms groundedCertificateOfFoolingSet
#print axioms TrajectoryNFrameFoolingCertificate.toGrounded
#print axioms TrajectoryNFrameContinuationGeometry.withServicing
#print axioms binomial_le_action
#print axioms binomial_le_action_of_grounded
#print axioms hasTrajectoryCertificate_of_grounded
#print axioms hasGroundedCertificate_of_fooling
#print axioms hasFoolingCertificate_of_geometryAndServicing
#print axioms nframeActionExtraction_of_grounded
#print axioms groundedExtraction_of_geometryAndServicing
#print axioms action_gt_polynomial_of_certificate
#print axioms operationalSAT_action_lower_of_nframe_extraction

end PallLean.Paper93.DeepMath.PathB.ObserverCentricNFrameActionBridge
