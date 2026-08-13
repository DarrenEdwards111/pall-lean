import PallLean.Paper93.DeepMath.PathB.ObserverTrajectoryDCEW
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverTimeDebt
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFoolingDebt
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderNoHiding
import PallLean.Paper93.DeepMath.PathB.OperationalZeroBoundaryObstruction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUCRDTseitinBoundedReuse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthThermodynamicObserver
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameInfoBoundaryTest
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSeamForcesHub
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameBudgetCashout
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCrossBranch
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameNonlinearShare
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameRestrictedFreshness

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
open PallLean.Paper93.DeepMath.PathB.UCRDTseitinBoundedReuse

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

/-- A surjective residual map supplies the entire static continuation geometry.
The only quantitative premise left is the transparent collision budget
`liveRank ≤ 2^r - 2^B`.  Thus the expander/no-hiding route need not construct
sectors, fooling pairs, or a boundary view by hand: a section of the residual
map gives canonical representatives of all residual outcomes. -/
noncomputable def continuationGeometryOfSurjectiveResidual
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n r B : Nat}
    (minor : TrajectoryGodMoveBoundaryMinor enc T n)
    {C : Type*} [Fintype C] [DecidableEq C]
    (residual : C → Fin (2 ^ r))
    (hsurj : Function.Surjective residual)
    (view : C → Fin (2 ^ B))
    (hrank : minor.liveRank ≤ 2 ^ r - 2 ^ B) :
    TrajectoryNFrameContinuationGeometry minor C := by
  classical
  let representative : Fin (2 ^ r) → C := Function.surjInv hsurj
  let sectors : Finset C := Finset.univ.image representative
  have hrepresentative_injective : Function.Injective representative :=
    Function.injective_surjInv hsurj
  have hrepresentative_residual :
      ∀ o : Fin (2 ^ r), residual (representative o) = o :=
    Function.surjInv_eq hsurj
  have hsectors_card : sectors.card = 2 ^ r := by
    simp [sectors, Finset.card_image_of_injective _ hrepresentative_injective]
  refine
    { stateCount := 2 ^ B
      sectors := sectors
      view := view
      mustSeparate := residualFooling residual
      fooling := ?_
      rank_fits_collisions := ?_ }
  · intro x hx y hy hxy
    rw [residualFooling, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨ox, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨oy, _, rfl⟩ := Finset.mem_image.mp hy
    simpa [hrepresentative_residual] using
      (show ox ≠ oy from fun h => hxy (congrArg representative h))
  · simpa [hsectors_card] using hrank

/-- Existential residual non-collapse is exactly sufficient for the new static
geometry socket.  This is the reusable adapter for expander-derived residual
maps at a concrete observer trajectory. -/
theorem hasContinuationGeometry_of_surjectiveResidual
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n r B : Nat}
    (minor : TrajectoryGodMoveBoundaryMinor enc T n)
    {C : Type*} [Fintype C] [DecidableEq C]
    (residual : C → Fin (2 ^ r))
    (hsurj : Function.Surjective residual)
    (view : C → Fin (2 ^ B))
    (hrank : minor.liveRank ≤ 2 ^ r - 2 ^ B) :
    Nonempty (TrajectoryNFrameContinuationGeometry minor C) :=
  ⟨continuationGeometryOfSurjectiveResidual minor residual hsurj view hrank⟩

/-- The irreducible static witness in residual language.  Unlike the derived
geometry, every load-bearing quantity is visible: residual dimension `r`,
boundary exponent `B`, surjectivity, and the collision surplus needed by the
live minor. -/
structure TrajectoryNFrameResidualNoncollapse
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    (minor : TrajectoryGodMoveBoundaryMinor enc T n)
    (C : Type*) [Fintype C] [DecidableEq C] where
  residualDimension : Nat
  boundaryExponent : Nat
  residual : C → Fin (2 ^ residualDimension)
  residual_surjective : Function.Surjective residual
  view : C → Fin (2 ^ boundaryExponent)
  rank_fits_residual_surplus :
    minor.liveRank ≤ 2 ^ residualDimension - 2 ^ boundaryExponent

/-- Canonical DTM-level residual/action certificate.  This decisive interface
contains no observer-supplied width or live-rank annotation.  Static residual
surplus is compared directly with the N-frame binomial scale, while dynamic
servicing is charged at one unit per actual DTM transition and must finish
within the DTM's declared runtime. -/
structure CanonicalDTMResidualActionCertificate
    (M : TuringMachine.DTM) (n : Nat)
    (C : Type*) [Fintype C] [DecidableEq C] where
  residualDimension : Nat
  boundaryExponent : Nat
  residual : C → Fin (2 ^ residualDimension)
  residual_surjective : Function.Surjective residual
  view : C → Fin (2 ^ boundaryExponent)
  binomial_fits_residual_surplus :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      2 ^ residualDimension - 2 ^ boundaryExponent
  debt : Nat → Nat
  horizon : Nat
  initialDebt : debt 0 = debtCount (residualFooling residual) view
  service : ∀ t, debt t ≤ debt (t + 1) + 1
  cleared : debt horizon = 0
  horizon_le_runtime : horizon ≤ TuringMachine.timeSteps M n

/-- Configuration-grounded replacement for the canonical DTM certificate.
Debt is no longer an arbitrary sequence: it is definitionally the number of
must-separate continuation pairs merged by a finite observation of the actual
DTM configurations reached from those continuations at time `t`.

The one-step service field is intentionally explicit.  It is the genuine local
transition theorem and is not derivable merely from determinism: one observed
transition may split many pairs at once. -/
structure ConfigurationGroundedDTMResidualActionCertificate
    (M : TuringMachine.DTM) (n : Nat)
    (C : Type*) [Fintype C] [DecidableEq C] where
  positiveLength : 1 ≤ n
  residualDimension : Nat
  boundaryExponent : Nat
  residual : C → Fin (2 ^ residualDimension)
  residual_surjective : Function.Surjective residual
  continuationInput : C → (Fin n → Bool)
  observe : TuringMachine.Configuration M (TuringMachine.tapeSize M n) →
    Fin (2 ^ boundaryExponent)
  binomial_fits_residual_surplus :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      2 ^ residualDimension - 2 ^ boundaryExponent
  horizon : Nat
  service : ∀ t,
    debtCount (residualFooling residual)
        (fun c => observe (TuringMachine.run M n t
          (TuringMachine.initialConfig M n positiveLength
            (continuationInput c)))) ≤
      debtCount (residualFooling residual)
        (fun c => observe (TuringMachine.run M n (t + 1)
          (TuringMachine.initialConfig M n positiveLength
            (continuationInput c)))) + 1
  separatedAtHorizon :
    debtCount (residualFooling residual)
      (fun c => observe (TuringMachine.run M n horizon
        (TuringMachine.initialConfig M n positiveLength
          (continuationInput c)))) = 0
  horizon_le_runtime : horizon ≤ TuringMachine.timeSteps M n

/-- Configuration-grounded certificates still force binomial DTM runtime, but
now every debt term refers to an actual run configuration. -/
theorem binomial_le_runtime_of_configurationGroundedDTMCertificate
    {M : TuringMachine.DTM} {n : Nat}
    {C : Type*} [Fintype C] [DecidableEq C]
    (cert : ConfigurationGroundedDTMResidualActionCertificate M n C) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤ TuringMachine.timeSteps M n := by
  let debt : Nat → Nat := fun t =>
    debtCount (residualFooling cert.residual)
      (fun c => cert.observe (TuringMachine.run M n t
        (TuringMachine.initialConfig M n cert.positiveLength
          (cert.continuationInput c))))
  have hinitial :
      2 ^ cert.residualDimension - 2 ^ cert.boundaryExponent ≤ debt 0 := by
    change 2 ^ cert.residualDimension - 2 ^ cert.boundaryExponent ≤
      debtCount (residualFooling cert.residual) _
    exact surjective_residual_forces_debt cert.residual
      cert.residual_surjective _
  have haction : debt 0 ≤ cert.horizon := by
    have h := correct_needs_action debt (fun _ => 1) cert.service
      cert.horizon cert.separatedAtHorizon
    simpa [observerTimeAction] using h
  exact le_trans cert.binomial_fits_residual_surplus
    (le_trans hinitial (le_trans haction cert.horizon_le_runtime))

/-- Canonical action cash-out: an honest residual/action certificate forces the
full binomial N-frame scale below the actual number of DTM transitions. -/
theorem binomial_le_runtime_of_canonicalDTMCertificate
    {M : TuringMachine.DTM} {n : Nat}
    {C : Type*} [Fintype C] [DecidableEq C]
    (cert : CanonicalDTMResidualActionCertificate M n C) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤ TuringMachine.timeSteps M n := by
  have hdebt :
      2 ^ cert.residualDimension - 2 ^ cert.boundaryExponent ≤ cert.debt 0 := by
    rw [cert.initialDebt]
    exact surjective_residual_forces_debt cert.residual
      cert.residual_surjective cert.view
  have haction : cert.debt 0 ≤ cert.horizon := by
    have h := correct_needs_action cert.debt (fun _ => 1) cert.service
      cert.horizon cert.cleared
    simpa [observerTimeAction] using h
  exact le_trans cert.binomial_fits_residual_surplus
    (le_trans hdebt (le_trans haction cert.horizon_le_runtime))

/-- Residual non-collapse compiles to static continuation geometry with no
additional combinatorial premise. -/
noncomputable def TrajectoryNFrameResidualNoncollapse.toGeometry
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    {minor : TrajectoryGodMoveBoundaryMinor enc T n}
    {C : Type*} [Fintype C] [DecidableEq C]
    (cert : TrajectoryNFrameResidualNoncollapse minor C) :
    TrajectoryNFrameContinuationGeometry minor C :=
  continuationGeometryOfSurjectiveResidual minor cert.residual
    cert.residual_surjective cert.view cert.rank_fits_residual_surplus

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

/-- Audit witness: the certificate-chosen servicing interface above is
inhabited for every geometry, independently of the observer.  Put all initial
debt into one freely chosen rate payment and clear at time one.  Consequently
this interface by itself is bookkeeping, not a dynamic lower-bound premise. -/
def TrajectoryNFrameContinuationGeometry.freeServicing
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    {minor : TrajectoryGodMoveBoundaryMinor enc T n}
    {X : Type*} [DecidableEq X]
    (geometry : TrajectoryNFrameContinuationGeometry minor X) :
    TrajectoryNFrameLocalServicing geometry where
  debt := fun t => if t = 0 then debtCount geometry.mustSeparate geometry.view else 0
  rate := fun t => if t = 0 then debtCount geometry.mustSeparate geometry.view else 0
  horizon := 1
  initialDebt := by simp
  service := by
    intro t
    by_cases ht : t = 0
    · subst t
      simp
    · simp [ht]
  cleared := by simp

/-- Honest dynamic interface: the servicing rate is no longer selected by the
certificate.  It is definitionally the concrete trajectory observer's live
boundary rank along the minor's actual input. -/
structure TrajectoryNFrameObservedServicing
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    {minor : TrajectoryGodMoveBoundaryMinor enc T n}
    {X : Type*} [DecidableEq X]
    (geometry : TrajectoryNFrameContinuationGeometry minor X) where
  debt : Nat → Nat
  horizon : Nat
  initialDebt : debt 0 = debtCount geometry.mustSeparate geometry.view
  service : ∀ t,
    debt t ≤ debt (t + 1) + T.liveBoundaryRank n minor.input t
  cleared : debt horizon = 0

/-- An observed servicing certificate forgets to the earlier generic
interface, but fixes its rate to the actual trajectory data. -/
def TrajectoryNFrameObservedServicing.toLocal
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    {minor : TrajectoryGodMoveBoundaryMinor enc T n}
    {X : Type*} [DecidableEq X]
    {geometry : TrajectoryNFrameContinuationGeometry minor X}
    (servicing : TrajectoryNFrameObservedServicing geometry) :
    TrajectoryNFrameLocalServicing geometry where
  debt := servicing.debt
  rate := fun t => T.liveBoundaryRank n minor.input t
  horizon := servicing.horizon
  initialDebt := servicing.initialDebt
  service := servicing.service
  cleared := servicing.cleared

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

/-- Static residual non-collapse at one trajectory and input length. -/
def HasTrajectoryNFrameResidualNoncollapseAt
    (enc : ThreeCNFEncoding) (T : TrajectoryObserverMachine) (n : Nat) : Prop :=
  ∃ (minor : TrajectoryGodMoveBoundaryMinor enc T n)
      (C : Type) (_fintype : Fintype C) (_decEq : DecidableEq C),
    Nonempty (TrajectoryNFrameResidualNoncollapse minor C)

/-- A concrete DTM has a canonical residual/action certificate at length `n`.
No trajectory-observer presentation occurs in this predicate. -/
def HasCanonicalDTMResidualActionCertificateAt
    (M : TuringMachine.DTM) (n : Nat) : Prop :=
  ∃ (C : Type) (_fintype : Fintype C) (_decEq : DecidableEq C),
    Nonempty (CanonicalDTMResidualActionCertificate M n C)

/-- Configuration-grounded canonical certificate at one length. -/
def HasConfigurationGroundedDTMResidualActionCertificateAt
    (M : TuringMachine.DTM) (n : Nat) : Prop :=
  ∃ (C : Type) (_fintype : Fintype C) (_decEq : DecidableEq C),
    Nonempty (ConfigurationGroundedDTMResidualActionCertificate M n C)

theorem binomial_le_runtime_of_hasConfigurationGroundedDTMCertificate
    {M : TuringMachine.DTM} {n : Nat}
    (h : HasConfigurationGroundedDTMResidualActionCertificateAt M n) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤ TuringMachine.timeSteps M n := by
  rcases h with ⟨C, fintype, decEq, hcert⟩
  letI : Fintype C := fintype
  letI : DecidableEq C := decEq
  rcases hcert with ⟨cert⟩
  exact binomial_le_runtime_of_configurationGroundedDTMCertificate cert

theorem binomial_le_runtime_of_hasCanonicalDTMCertificate
    {M : TuringMachine.DTM} {n : Nat}
    (h : HasCanonicalDTMResidualActionCertificateAt M n) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤ TuringMachine.timeSteps M n := by
  rcases h with ⟨C, fintype, decEq, hcert⟩
  letI : Fintype C := fintype
  letI : DecidableEq C := decEq
  rcases hcert with ⟨cert⟩
  exact binomial_le_runtime_of_canonicalDTMCertificate cert

/-- Static continuation geometry at one trajectory and input length. -/
def HasTrajectoryNFrameContinuationGeometryAt
    (enc : ThreeCNFEncoding) (T : TrajectoryObserverMachine) (n : Nat) : Prop :=
  ∃ (minor : TrajectoryGodMoveBoundaryMinor enc T n)
      (C : Type) (_decEq : DecidableEq C),
    Nonempty (TrajectoryNFrameContinuationGeometry minor C)

/-- The residual formulation implies the static geometry formulation. -/
theorem hasContinuationGeometry_of_residualNoncollapse
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    (h : HasTrajectoryNFrameResidualNoncollapseAt enc T n) :
    HasTrajectoryNFrameContinuationGeometryAt enc T n := by
  rcases h with ⟨minor, C, fintype, decEq, hcert⟩
  letI : Fintype C := fintype
  letI : DecidableEq C := decEq
  rcases hcert with ⟨cert⟩
  exact ⟨minor, C, inferInstance, ⟨cert.toGeometry⟩⟩

/-- Fixed-length frontier split into its static and dynamic halves. -/
def HasTrajectoryNFrameGeometryAndServicingAt
    (enc : ThreeCNFEncoding) (T : TrajectoryObserverMachine) (n : Nat) : Prop :=
  ∃ (minor : TrajectoryGodMoveBoundaryMinor enc T n)
      (X : Type) (_inst : DecidableEq X)
      (geometry : TrajectoryNFrameContinuationGeometry minor X),
    Nonempty (TrajectoryNFrameLocalServicing geometry)

/-- Honest fixed-length frontier: geometry plus servicing charged to the
observer's own live boundary-rank trajectory. -/
def HasTrajectoryNFrameGeometryAndObservedServicingAt
    (enc : ThreeCNFEncoding) (T : TrajectoryObserverMachine) (n : Nat) : Prop :=
  ∃ (minor : TrajectoryGodMoveBoundaryMinor enc T n)
      (X : Type) (_inst : DecidableEq X)
      (geometry : TrajectoryNFrameContinuationGeometry minor X),
    Nonempty (TrajectoryNFrameObservedServicing geometry)

/-- The older generic servicing predicate is automatically inhabited once
static geometry exists.  This formally exposes why its free `rate` field
cannot be treated as observer action. -/
theorem hasGeometryAndServicing_of_continuationGeometry
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    (h : HasTrajectoryNFrameContinuationGeometryAt enc T n) :
    HasTrajectoryNFrameGeometryAndServicingAt enc T n := by
  rcases h with ⟨minor, X, inst, hgeometry⟩
  letI : DecidableEq X := inst
  rcases hgeometry with ⟨geometry⟩
  exact ⟨minor, X, inferInstance, geometry, ⟨geometry.freeServicing⟩⟩

/-- Honest observed servicing still feeds the existing conservation wiring. -/
theorem hasGeometryAndServicing_of_observed
    {enc : ThreeCNFEncoding} {T : TrajectoryObserverMachine} {n : Nat}
    (h : HasTrajectoryNFrameGeometryAndObservedServicingAt enc T n) :
    HasTrajectoryNFrameGeometryAndServicingAt enc T n := by
  rcases h with ⟨minor, X, inst, geometry, hservicing⟩
  letI : DecidableEq X := inst
  rcases hservicing with ⟨servicing⟩
  exact ⟨minor, X, inferInstance, geometry, ⟨servicing.toLocal⟩⟩

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

/-- Exact universal static frontier in residual language.  This is where the
fixed-decomposition expander theorem must be upgraded to every bounded-time
adaptive SAT trajectory. -/
def TimeExponentParametricOperationalSATResidualNoncollapse
    (enc : ThreeCNFEncoding) : Prop :=
  ∀ e c : Nat, ∃ n : Nat,
    n ≥ 2 ^ 20 ∧
    4 * (c + 1) ≤ Nat.log 2 n ∧
    ∀ T : TrajectoryObserverMachine,
      OperationalTrajectoryObserverDecidesSATAtMost enc e T →
      HasTrajectoryNFrameResidualNoncollapseAt enc T n

/-- Canonical DTM frontier with no observer annotations: every SAT-deciding DTM
of exponent at most `e` must expose residual debt that can only be serviced by
its actual transition budget. -/
def TimeExponentParametricSATCanonicalDTMResidualAction
    (enc : ThreeCNFEncoding) : Prop :=
  ∀ e : Nat, ∃ n : Nat,
    n ≥ 2 ^ 20 ∧
    4 * (e + 1) ≤ Nat.log 2 n ∧
    ∀ M : TuringMachine.DTM,
      DTMDecidesSATWithEncodingAtMost enc e M →
      HasCanonicalDTMResidualActionCertificateAt M n

/-- Fully configuration-grounded canonical DTM frontier. -/
def TimeExponentParametricSATConfigurationGroundedDTMResidualAction
    (enc : ThreeCNFEncoding) : Prop :=
  ∀ e : Nat, ∃ n : Nat,
    n ≥ 2 ^ 20 ∧
    4 * (e + 1) ≤ Nat.log 2 n ∧
    ∀ M : TuringMachine.DTM,
      DTMDecidesSATWithEncodingAtMost enc e M →
      HasConfigurationGroundedDTMResidualActionCertificateAt M n

theorem no_DTMDecidesSAT_of_configurationGroundedResidualAction
    (enc : ThreeCNFEncoding)
    (hprogram :
      TimeExponentParametricSATConfigurationGroundedDTMResidualAction enc) :
    Not (∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) := by
  rintro ⟨M, hdec⟩
  rcases hprogram M.timeBound with ⟨n, hn20, hlog, hcert⟩
  have hlower :=
    binomial_le_runtime_of_hasConfigurationGroundedDTMCertificate
      (hcert M ⟨hdec, le_rfl⟩)
  have hgap := arithmetic_gap_for_exponent M.timeBound n hn20 hlog
  exact (not_le_of_gt hgap) (by
    simpa [TuringMachine.timeSteps] using hlower)

/-- The canonical DTM residual/action frontier directly rules out every
polynomial-time SAT DTM.  The contradiction uses the real identity
`timeSteps M n = n ^ M.timeBound`, not an observer width annotation. -/
theorem no_DTMDecidesSAT_of_canonicalResidualAction
    (enc : ThreeCNFEncoding)
    (hprogram : TimeExponentParametricSATCanonicalDTMResidualAction enc) :
    Not (∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) := by
  rintro ⟨M, hdec⟩
  rcases hprogram M.timeBound with ⟨n, hn20, hlog, hcert⟩
  have hsat : DTMDecidesSATWithEncodingAtMost enc M.timeBound M :=
    ⟨hdec, le_rfl⟩
  have hlower :
      Nat.choose (n / 3) (Nat.log 2 n) ≤ TuringMachine.timeSteps M n :=
    binomial_le_runtime_of_hasCanonicalDTMCertificate (hcert M hsat)
  have hgap :
      n ^ M.timeBound < Nat.choose (n / 3) (Nat.log 2 n) :=
    arithmetic_gap_for_exponent M.timeBound n hn20 hlog
  exact (not_le_of_gt hgap) (by simpa [TuringMachine.timeSteps] using hlower)

/-- Universal residual non-collapse gives the universal static geometry
program.  It does not supply dynamic locality/servicing. -/
def TimeExponentParametricOperationalSATContinuationGeometry
    (enc : ThreeCNFEncoding) : Prop :=
  ∀ e c : Nat, ∃ n : Nat,
    n ≥ 2 ^ 20 ∧
    4 * (c + 1) ≤ Nat.log 2 n ∧
    ∀ T : TrajectoryObserverMachine,
      OperationalTrajectoryObserverDecidesSATAtMost enc e T →
      HasTrajectoryNFrameContinuationGeometryAt enc T n

theorem continuationGeometry_of_residualNoncollapse
    (enc : ThreeCNFEncoding)
    (hnoncollapse :
      TimeExponentParametricOperationalSATResidualNoncollapse enc) :
    TimeExponentParametricOperationalSATContinuationGeometry enc := by
  intro e c
  rcases hnoncollapse e c with ⟨n, hn20, hlog, hcert⟩
  exact ⟨n, hn20, hlog, fun T hT =>
    hasContinuationGeometry_of_residualNoncollapse (hcert T hT)⟩

/-- Audit: if a polynomial-time SAT DTM exists, the universal residual
non-collapse program is false for its zero-boundary operational presentation.
The residual witness contains a positive-rank live minor, which cannot exist
in that presentation.  Thus this static frontier already carries the complete
P-vs-NP lower-bound strength. -/
theorem not_residualNoncollapse_of_zeroBoundaryDecider
    {enc : ThreeCNFEncoding} {M : TuringMachine.DTM}
    (hdec : DTMDecidesSATWithEncoding enc M) :
    Not (TimeExponentParametricOperationalSATResidualNoncollapse enc) := by
  intro hprogram
  rcases hprogram M.timeBound 0 with ⟨n, hn20, hlog, hcert⟩
  have hgap : n ^ 0 < Nat.choose (n / 3) (Nat.log 2 n) :=
    arithmetic_gap_for_exponent 0 n hn20 hlog
  have hchoose_pos : 0 < Nat.choose (n / 3) (Nat.log 2 n) := by
    exact lt_trans (by simp) hgap
  have hsat :=
    zeroBoundaryOperationalTrajectoryObserver_decidesSATAtMost hdec
  rcases hcert (zeroBoundaryOperationalTrajectoryObserver M) hsat with
    ⟨minor, C, fintype, decEq, _⟩
  exact
    (no_trajectoryMinor_of_zeroBoundaryOperationalObserver
      (enc := enc) M hchoose_pos) ⟨minor⟩

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

/-- Corrected static+dynamic frontier: servicing is charged to the concrete
observer trajectory rather than to a certificate-chosen rate. -/
def TimeExponentParametricOperationalSATNFrameGeometryAndObservedServicing
    (enc : ThreeCNFEncoding) : Prop :=
  ∀ e c : Nat, ∃ n : Nat,
    n ≥ 2 ^ 20 ∧
    4 * (c + 1) ≤ Nat.log 2 n ∧
    ∀ T : TrajectoryObserverMachine,
      OperationalTrajectoryObserverDecidesSATAtMost enc e T →
      HasTrajectoryNFrameGeometryAndObservedServicingAt enc T n

/-- The corrected frontier implies the older generic program, preserving all
downstream kernel-checked conservation results. -/
theorem geometryAndServicing_of_observedProgram
    (enc : ThreeCNFEncoding)
    (hprogram :
      TimeExponentParametricOperationalSATNFrameGeometryAndObservedServicing enc) :
    TimeExponentParametricOperationalSATNFrameGeometryAndServicing enc := by
  intro e c
  rcases hprogram e c with ⟨n, hn20, hlog, hcert⟩
  exact ⟨n, hn20, hlog, fun T hT =>
    hasGeometryAndServicing_of_observed (hcert T hT)⟩

/-- The corrected observed-servicing program has the same zero-boundary
obstruction: its required live minor cannot exist for the operationally valid
zero-boundary presentation of a hypothetical SAT decider. -/
theorem not_geometryAndObservedServicing_of_zeroBoundaryDecider
    {enc : ThreeCNFEncoding} {M : TuringMachine.DTM}
    (hdec : DTMDecidesSATWithEncoding enc M) :
    Not
      (TimeExponentParametricOperationalSATNFrameGeometryAndObservedServicing
        enc) := by
  intro hprogram
  rcases hprogram M.timeBound 0 with ⟨n, hn20, hlog, hcert⟩
  have hgap : n ^ 0 < Nat.choose (n / 3) (Nat.log 2 n) :=
    arithmetic_gap_for_exponent 0 n hn20 hlog
  have hchoose_pos : 0 < Nat.choose (n / 3) (Nat.log 2 n) := by
    exact lt_trans (by simp) hgap
  have hsat :=
    zeroBoundaryOperationalTrajectoryObserver_decidesSATAtMost hdec
  rcases hcert (zeroBoundaryOperationalTrajectoryObserver M) hsat with
    ⟨minor, X, inst, geometry, servicing⟩
  exact
    (no_trajectoryMinor_of_zeroBoundaryOperationalObserver
      (enc := enc) M hchoose_pos) ⟨minor⟩

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

/-! ## Locality and Boolean-output audits

The configuration-grounded certificate deliberately retains its `service`
field.  The following finite counterexample explains why it cannot be filled
from determinism alone: a single one-bit refinement can separate several raw
must-separate pairs simultaneously.  Thus raw pair count is not a
one-transition-Lipschitz potential.
-/

private def threeWayResidual : Fin 3 → Fin 3 := id

private def constantThreeWayView : Fin 3 → Fin 1 := fun _ => 0

private def binaryThreeWayView : Fin 3 → Fin 2 := fun x =>
  if x = 0 then 0 else 1

private def twoBitThreeWayView : Fin 3 → (Fin 2 → Bool) := fun x i =>
  match x.1, i.1 with
  | 0, _ => false
  | 1, 0 => false
  | 1, _ => true
  | _, 0 => true
  | _, _ => false

/-- A binary refinement drops ordered residual-pair debt from six to two in
one step.  In particular, the unit-service inequality required by the raw
pair-count certificate is false for arbitrary deterministic observations. -/
theorem rawPairDebt_not_unitLipschitz :
    debtCount (residualFooling threeWayResidual) constantThreeWayView >
      debtCount (residualFooling threeWayResidual) binaryThreeWayView + 1 := by
  decide

/-- After only two binary observations, the same three residual classes are
completely separated and all six ordered pair-debts have vanished.  Pair debt
therefore overcounts the information that an adaptive transcript must acquire. -/
theorem twoBits_clear_threeWayPairDebt :
    debtCount (residualFooling threeWayResidual) twoBitThreeWayView = 0 := by
  decide

/-- If a family is pairwise distinguished solely by a Boolean decision, it
has at most two members.  Consequently a binomial-size continuation family
cannot be justified merely by assigning different final SAT answer bits; it
requires a contextual residual/continuation semantics. -/
theorem booleanOutputSeparated_card_le_two
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Finset X) (out : X → Bool)
    (hseparate :
      ∀ x ∈ P, ∀ y ∈ P, out x = out y → x = y) :
    P.card ≤ 2 := by
  let f : {x : X // x ∈ P} → Bool := fun x => out x.1
  have hinjective : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact hseparate x.1 x.2 y.1 y.2 hxy
  have hcard := Fintype.card_le_of_injective f hinjective
  simpa [f] using hcard

/-- The honest generic information bound: a length-`T` binary transcript can
distinguish as many as `2^T` sectors.  Thus pairwise collision counts cannot be
charged one-for-one to transitions; only logarithmic transcript information is
generic without an additional direct-sum/non-amortization theorem. -/
theorem binaryTranscriptSeparated_card_le_pow
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Finset X) (transcript : X → (Fin T → Bool))
    (hseparate :
      ∀ x ∈ P, ∀ y ∈ P, transcript x = transcript y → x = y) :
    P.card ≤ 2 ^ T := by
  let f : {x : X // x ∈ P} → (Fin T → Bool) := fun x => transcript x.1
  have hinjective : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact hseparate x.1 x.2 y.1 y.2 hxy
  have hcard := Fintype.card_le_of_injective f hinjective
  simpa [f, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using hcard

/-! ## Direct-transition charging audit

A tempting repair is to demand that every contextual residual obligation be
charged to a distinct transition.  For finite index sets this demand is
exactly equivalent to the desired lower bound, so it is not an independently
weaker certificate.  A valid use must derive the injection from SAT/machine
topology (as formula trees do), rather than postulate it.
-/

/-- A non-amortized transition charge assigns each of `K` obligations to a
different one of `T` physical transitions. -/
def NonAmortizedTransitionCharge (K T : Nat) : Prop :=
  ∃ charge : Fin K → Fin T, Function.Injective charge

/-- A non-amortized charge immediately gives the claimed transition lower
bound. -/
theorem obligations_le_transitions_of_nonAmortizedCharge
    {K T : Nat} (h : NonAmortizedTransitionCharge K T) : K ≤ T := by
  rcases h with ⟨charge, hinjective⟩
  simpa using Fintype.card_le_of_injective charge hinjective

/-- Conversely, the numerical lower bound already constructs such a charge.
Thus in the unrestricted finite model, non-amortized transition charging is
logically equivalent to the lower bound it is meant to prove. -/
theorem nonAmortizedTransitionCharge_iff (K T : Nat) :
    NonAmortizedTransitionCharge K T ↔ K ≤ T := by
  constructor
  · exact obligations_le_transitions_of_nonAmortizedCharge
  · intro hKT
    exact ⟨Fin.castLE hKT, Fin.castLE_injective hKT⟩

/-! ## Bounded transition reuse

Allowing reuse replaces the injective charge by the repository's existing
bounded-fiber accounting.  The generic law is `K ≤ T * readK`; without an
independently derived sub-total-use bound on `readK`, it gives no runtime
lower bound.
-/

/-- `K` obligations charged to `T` transitions, with each transition serving
at most `readK` obligations. -/
abbrev BoundedTransitionReuse (K T readK : Nat) :=
  BoundedReuseReconstruction K 1 T readK

theorem obligations_le_transitions_mul_reuse
    {K T readK : Nat} (R : BoundedTransitionReuse K T readK) :
    K ≤ T * readK := by
  simpa using direct_sum_le_resource_reuse R

/-- Full amortization is always available for a nonempty transition pool: one
physical transition may be declared to serve all `K` obligations, with reuse
multiplicity exactly the total-use scale `K`. -/
def fullTransitionAmortization (K : Nat) :
    BoundedTransitionReuse K 1 K where
  resourceOf := fun _ => 0
  fiber_le := by
    intro r
    calc
      Fintype.card
          {x : Fin K × Fin 1 // (fun _ : Fin K × Fin 1 => (0 : Fin 1)) x = r}
          ≤ Fintype.card (Fin K × Fin 1) := Fintype.card_subtype_le _
      _ = K := by simp

/-- The generic capacity bound is exactly saturated by full amortization and
therefore supplies no separation. -/
theorem fullTransitionAmortization_saturates (K : Nat) :
    K = 1 * K := by simp

/-- **Runtime-or-reuse dichotomy.**  If `K` obligations are served by `T`
transitions and `T * r` is still too small, then some transition must be reused
more than `r` times.  This is the unconditional conclusion that survives when
anti-sharing is unavailable. -/
theorem reuse_gt_of_runtime_capacity_gap
    {K T readK r : Nat} (R : BoundedTransitionReuse K T readK)
    (hgap : T * r < K) : r < readK := by
  by_contra h
  have hre : readK ≤ r := Nat.le_of_not_gt h
  have hcapacity : K ≤ T * readK :=
    obligations_le_transitions_mul_reuse R
  have hmono : T * readK ≤ T * r := Nat.mul_le_mul_left T hre
  exact (Nat.not_lt_of_ge (hcapacity.trans hmono)) hgap

/-- In particular, any schedule beating the obligation count in runtime must
reuse at least one transition.  Fast computation is not ruled out; it is
forced into the sharing regime. -/
theorem nontrivial_reuse_of_runtime_lt_obligations
    {K T readK : Nat} (R : BoundedTransitionReuse K T readK)
    (hfast : T < K) : 1 < readK := by
  apply reuse_gt_of_runtime_capacity_gap R
  simpa using hfast

/-- At the calibrated N-frame scale, polynomial runtime can cover the
binomial obligation family only through reuse exceeding any preselected
polynomial degree.  This is an honest reuse lower bound, not a runtime lower
bound: unrestricted machines are allowed to realize that sharing. -/
theorem nframePolynomialRuntime_forces_superpolynomialReuse
    {n e c readK : Nat}
    (R : BoundedTransitionReuse
      (Nat.choose (n / 3) (Nat.log 2 n)) (n ^ e) readK)
    (hn20 : n ≥ 2 ^ 20)
    (hlog : 4 * (e + c + 1) ≤ Nat.log 2 n) :
    n ^ c < readK := by
  apply reuse_gt_of_runtime_capacity_gap R
  rw [← pow_add]
  exact arithmetic_gap_for_exponent (e + c) n hn20 (by omega)

/-- **Sharp observer-centric N-frame dichotomy.**  Any bounded-reuse schedule
for the binomial obligation family has either runtime above `n^e` or reuse
above `n^c`.  No anti-sharing premise is used.  Turning this disjunction into
a runtime lower bound requires independently ruling out the reuse branch. -/
theorem nframe_runtime_or_reuse
    {n e c T readK : Nat}
    (R : BoundedTransitionReuse
      (Nat.choose (n / 3) (Nat.log 2 n)) T readK)
    (hn20 : n ≥ 2 ^ 20)
    (hlog : 4 * (e + c + 1) ≤ Nat.log 2 n) :
    n ^ e < T ∨ n ^ c < readK := by
  by_cases htime : n ^ e < T
  · exact Or.inl htime
  · right
    have hT : T ≤ n ^ e := Nat.le_of_not_gt htime
    by_contra hre
    have hread : readK ≤ n ^ c := Nat.le_of_not_gt hre
    have hcapacity := obligations_le_transitions_mul_reuse R
    have hproduct : T * readK ≤ n ^ e * n ^ c :=
      Nat.mul_le_mul hT hread
    have hgap : n ^ (e + c) < Nat.choose (n / 3) (Nat.log 2 n) :=
      arithmetic_gap_for_exponent (e + c) n hn20 (by omega)
    rw [pow_add] at hgap
    exact (Nat.not_lt_of_ge (hcapacity.trans hproduct)) hgap

/-- Conditional cash-out of anti-sharing.  A polynomial reuse cap eliminates
the second branch of `nframe_runtime_or_reuse` and forces the runtime lower
bound.  This theorem performs only the accounting implication; establishing
`readK ≤ n^c` for SAT DTMs remains the missing lower-bound theorem. -/
theorem nframe_runtime_lower_of_polynomialReuse
    {n e c T readK : Nat}
    (R : BoundedTransitionReuse
      (Nat.choose (n / 3) (Nat.log 2 n)) T readK)
    (hn20 : n ≥ 2 ^ 20)
    (hlog : 4 * (e + c + 1) ≤ Nat.log 2 n)
    (hreuse : readK ≤ n ^ c) :
    n ^ e < T := by
  rcases nframe_runtime_or_reuse R hn20 hlog with htime | hhighReuse
  · exact htime
  · exact absurd hhighReuse (Nat.not_lt_of_ge hreuse)

/-- Pointwise form of the exact missing anti-sharing input at one calibrated
length.  It is deliberately a property of the concrete obligation schedule,
not an observer-chosen annotation. -/
def PolynomialReuseAt
    (n c T readK : Nat)
    (_R : BoundedTransitionReuse
      (Nat.choose (n / 3) (Nat.log 2 n)) T readK) : Prop :=
  readK ≤ n ^ c

theorem nframe_runtime_lower_of_polynomialReuseAt
    {n e c T readK : Nat}
    (R : BoundedTransitionReuse
      (Nat.choose (n / 3) (Nat.log 2 n)) T readK)
    (hn20 : n ≥ 2 ^ 20)
    (hlog : 4 * (e + c + 1) ≤ Nat.log 2 n)
    (hanti : PolynomialReuseAt n c T readK R) :
    n ^ e < T :=
  nframe_runtime_lower_of_polynomialReuse R hn20 hlog hanti

/-- The polynomial-reuse property is not universal over obligation schedules.
At the calibrated scale, the one-transition full-amortization schedule has
reuse equal to the whole binomial family and therefore violates every chosen
`n^c` cap.  Any successful anti-sharing theorem must exclude this schedule
using concrete SAT/DTM semantics. -/
theorem fullAmortization_not_polynomialReuseAt
    {n c : Nat}
    (hn20 : n ≥ 2 ^ 20)
    (hlog : 4 * (c + 1) ≤ Nat.log 2 n) :
    ¬ PolynomialReuseAt n c 1
      (Nat.choose (n / 3) (Nat.log 2 n))
      (fullTransitionAmortization
        (Nat.choose (n / 3) (Nat.log 2 n))) := by
  intro hreuse
  have hgap := arithmetic_gap_for_exponent c n hn20 hlog
  exact (Nat.not_lt_of_ge hreuse) hgap

/-- Consequently there is no schedule-independent theorem asserting a
polynomial reuse cap at the calibrated N-frame scale. -/
theorem not_allSchedules_polynomialReuseAt
    {n c : Nat}
    (hn20 : n ≥ 2 ^ 20)
    (hlog : 4 * (c + 1) ≤ Nat.log 2 n) :
    ¬ (∀ (R : BoundedTransitionReuse
          (Nat.choose (n / 3) (Nat.log 2 n)) 1
          (Nat.choose (n / 3) (Nat.log 2 n))),
        PolynomialReuseAt n c 1
          (Nat.choose (n / 3) (Nat.log 2 n)) R) := by
  intro hall
  exact fullAmortization_not_polynomialReuseAt hn20 hlog
    (hall (fullTransitionAmortization
      (Nat.choose (n / 3) (Nat.log 2 n))))

/-! ## Canonical first-separation schedule from an actual DTM

The preceding counterexample rules out quantifying over arbitrary schedules.
The following object instead starts with concrete pairs of DTM inputs and a
fixed observation of their real run configurations.  Each obligation is
charged, definitionally, to the first transition at which its two observed
traces differ.  No charge map is supplied by the certificate.
-/

/-- `K` contextual obligations realized by pairs of actual inputs to `M`.
Every pair must become distinguishable before transition `T`; the canonical
charge below chooses its least separating transition. -/
structure CanonicalDTMFirstSeparationData
    (M : TuringMachine.DTM) (n K T : Nat) (S : Type*) where
  positiveLength : 1 ≤ n
  leftInput : Fin K → (Fin n → Bool)
  rightInput : Fin K → (Fin n → Bool)
  observe : TuringMachine.Configuration M (TuringMachine.tapeSize M n) → S
  separatedWithin : ∀ k : Fin K, ∃ t : Nat, t < T ∧
    observe (TuringMachine.run M n (t + 1)
      (TuringMachine.initialConfig M n positiveLength (leftInput k))) ≠
    observe (TuringMachine.run M n (t + 1)
      (TuringMachine.initialConfig M n positiveLength (rightInput k)))

namespace CanonicalDTMFirstSeparationData

/-- The least physical transition that separates obligation `k`. -/
noncomputable def firstSeparationTime
    {M : TuringMachine.DTM} {n K T : Nat} {S : Type*} [DecidableEq S]
    (D : CanonicalDTMFirstSeparationData M n K T S) (k : Fin K) : Nat :=
  Nat.find (D.separatedWithin k)

theorem firstSeparationTime_lt
    {M : TuringMachine.DTM} {n K T : Nat} {S : Type*} [DecidableEq S]
    (D : CanonicalDTMFirstSeparationData M n K T S) (k : Fin K) :
    D.firstSeparationTime k < T :=
  (Nat.find_spec (D.separatedWithin k)).1

theorem separated_at_firstSeparationTime
    {M : TuringMachine.DTM} {n K T : Nat} {S : Type*} [DecidableEq S]
    (D : CanonicalDTMFirstSeparationData M n K T S) (k : Fin K) :
    D.observe (TuringMachine.run M n (D.firstSeparationTime k + 1)
      (TuringMachine.initialConfig M n D.positiveLength (D.leftInput k))) ≠
    D.observe (TuringMachine.run M n (D.firstSeparationTime k + 1)
      (TuringMachine.initialConfig M n D.positiveLength (D.rightInput k))) :=
  (Nat.find_spec (D.separatedWithin k)).2

/-- The canonical charge is derived from the traces, rather than included as
free accounting data. -/
noncomputable def canonicalCharge
    {M : TuringMachine.DTM} {n K T : Nat} {S : Type*} [DecidableEq S]
    (D : CanonicalDTMFirstSeparationData M n K T S) : Fin K → Fin T :=
  fun k => ⟨D.firstSeparationTime k, D.firstSeparationTime_lt k⟩

/-- Every canonical schedule has the trivial total-use bound `K`.  Improving
this to a polynomial bound from SAT semantics is exactly the anti-sharing
problem; the schedule itself is no longer arbitrary. -/
noncomputable def toBoundedTransitionReuse
    {M : TuringMachine.DTM} {n K T : Nat} {S : Type*} [DecidableEq S]
    (D : CanonicalDTMFirstSeparationData M n K T S) :
    BoundedTransitionReuse K T K where
  resourceOf := fun x => D.canonicalCharge x.1
  fiber_le := by
    intro r
    calc
      Fintype.card
          {x : Fin K × Fin 1 // (fun y => D.canonicalCharge y.1) x = r}
          ≤ Fintype.card (Fin K × Fin 1) := Fintype.card_subtype_le _
      _ = K := by simp

/-- A reuse bound for the canonical map is just a bound on the number of
actual trace pairs whose *first* separating transition is `r`. -/
def CanonicalReuseBound
    {M : TuringMachine.DTM} {n K T : Nat} {S : Type*} [DecidableEq S]
    (D : CanonicalDTMFirstSeparationData M n K T S) (readK : Nat) : Prop :=
  ∀ r : Fin T,
    Fintype.card
      {x : Fin K × Fin 1 // D.canonicalCharge x.1 = r} ≤ readK

/-- A concrete fiber bound packages the canonical charge as a bounded-reuse
schedule; no alternative obligation assignment can be chosen. -/
noncomputable def boundedTransitionReuseOfCanonicalBound
    {M : TuringMachine.DTM} {n K T readK : Nat} {S : Type*} [DecidableEq S]
    (D : CanonicalDTMFirstSeparationData M n K T S)
    (hbound : D.CanonicalReuseBound readK) :
    BoundedTransitionReuse K T readK where
  resourceOf := fun x => D.canonicalCharge x.1
  fiber_le := hbound

/-- The sharp N-frame dichotomy now applies to the canonical, machine-derived
first-separation map.  The high-reuse branch refers to actual pairs of DTM
traces sharing their first separating transition. -/
theorem nframe_runtime_or_canonicalDTMReuse
    {M : TuringMachine.DTM} {n e c T readK : Nat} {S : Type*} [DecidableEq S]
    (D : CanonicalDTMFirstSeparationData M n
      (Nat.choose (n / 3) (Nat.log 2 n)) T S)
    (hbound : D.CanonicalReuseBound readK)
    (hn20 : n ≥ 2 ^ 20)
    (hlog : 4 * (e + c + 1) ≤ Nat.log 2 n) :
    n ^ e < T ∨ n ^ c < readK := by
  exact nframe_runtime_or_reuse
    (D.boundedTransitionReuseOfCanonicalBound hbound) hn20 hlog

/-- A polynomial fiber bound on the canonical first-separation map eliminates
the sharing branch and forces a strict runtime lower bound. -/
theorem nframe_runtime_lower_of_canonicalDTMReuseBound
    {M : TuringMachine.DTM} {n e c T : Nat} {S : Type*} [DecidableEq S]
    (D : CanonicalDTMFirstSeparationData M n
      (Nat.choose (n / 3) (Nat.log 2 n)) T S)
    (hbound : D.CanonicalReuseBound (n ^ c))
    (hn20 : n ≥ 2 ^ 20)
    (hlog : 4 * (e + c + 1) ≤ Nat.log 2 n) :
    n ^ e < T := by
  rcases D.nframe_runtime_or_canonicalDTMReuse hbound hn20 hlog with
    htime | hre
  · exact htime
  · exact absurd hre (Nat.lt_irrefl _)

end CanonicalDTMFirstSeparationData

/-! ## Exact SAT/DTM semantic frontier

The canonical map removes freedom from the accounting.  Two semantic tasks
remain and are kept separate below:

1. SAT correctness must generate the binomial family of concrete input pairs
   whose actual traces separate within the declared runtime.
2. Those canonical first-separation fibers must obey a polynomial cap.

The second task is the anti-sharing lower bound.  The theorem below proves that
after these data exist, no further combinatorial bridge is missing.
-/

/-- At length `n`, `M` exposes the full N-frame obligation family as concrete
pairs of inputs, with charges derived from its real transition traces. -/
def HasCanonicalDTMNFrameFirstSeparationDataAt
    (M : TuringMachine.DTM) (n : Nat) : Prop :=
  ∃ (S : Type) (_decEq : DecidableEq S),
    Nonempty (CanonicalDTMFirstSeparationData M n
      (Nat.choose (n / 3) (Nat.log 2 n))
      (TuringMachine.timeSteps M n) S)

/-- Extraction half of the frontier: SAT correctness supplies the canonical
N-frame pair family at the calibrated length. -/
def TimeExponentParametricSATCanonicalPairExtraction
    (enc : ThreeCNFEncoding) : Prop :=
  ∀ e c : Nat, ∃ n : Nat,
    n ≥ 2 ^ 20 ∧
    4 * (e + c + 1) ≤ Nat.log 2 n ∧
    ∀ M : TuringMachine.DTM,
      DTMDecidesSATWithEncodingAtMost enc e M →
      HasCanonicalDTMNFrameFirstSeparationDataAt M n

/-- Anti-concentration half of the frontier: every extracted canonical family
has at most `n^c` obligations sharing one first separating transition.  The
quantification is only over machine-derived maps, never arbitrary schedules. -/
def TimeExponentParametricSATCanonicalFiberBound
    (enc : ThreeCNFEncoding) : Prop :=
  ∀ e : Nat, ∃ c : Nat, ∀ n : Nat, ∀ M : TuringMachine.DTM,
    DTMDecidesSATWithEncodingAtMost enc e M →
    ∀ (S : Type) (_decEq : DecidableEq S),
      ∀ D : CanonicalDTMFirstSeparationData M n
        (Nat.choose (n / 3) (Nat.log 2 n))
        (TuringMachine.timeSteps M n) S,
        D.CanonicalReuseBound (n ^ c)

/-- SAT-derived canonical pairs plus canonical fiber anti-concentration rule
out every polynomial-time SAT DTM.  This is the complete cash-out of the new
machine-semantic formulation. -/
theorem no_DTMDecidesSAT_of_canonicalPairExtraction_and_fiberBound
    (enc : ThreeCNFEncoding)
    (hextract : TimeExponentParametricSATCanonicalPairExtraction enc)
    (hfiber : TimeExponentParametricSATCanonicalFiberBound enc) :
    ¬ ∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M := by
  rintro ⟨M, hdec⟩
  obtain ⟨c, hc⟩ := hfiber M.timeBound
  obtain ⟨n, hn20, hlog, hdata⟩ := hextract M.timeBound c
  have hsat : DTMDecidesSATWithEncodingAtMost enc M.timeBound M :=
    ⟨hdec, le_rfl⟩
  obtain ⟨S, decEq, hD⟩ := hdata M hsat
  letI : DecidableEq S := decEq
  obtain ⟨D⟩ := hD
  have hlower : n ^ M.timeBound < TuringMachine.timeSteps M n :=
    D.nframe_runtime_lower_of_canonicalDTMReuseBound
      (hc n M hsat S inferInstance D) hn20 hlog
  exact (Nat.lt_irrefl (n ^ M.timeBound)) (by
    simpa [TuringMachine.timeSteps] using hlower)

/-- If no SAT-deciding DTM exists, canonical pair extraction is inhabited
vacuously.  This converse audit matters: extraction cannot be advertised as
an independently established consequence of the current SAT contract. -/
theorem canonicalPairExtraction_of_no_DTMDecidesSAT
    (enc : ThreeCNFEncoding)
    (hno : ¬ ∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) :
    TimeExponentParametricSATCanonicalPairExtraction enc := by
  intro e c
  refine ⟨2 ^ (4 * (e + c + 1) + 20), ?_, ?_, ?_⟩
  · exact Nat.pow_le_pow_right (by omega : 1 ≤ (2 : Nat)) (by omega)
  · rw [Nat.log_pow]
    · omega
    · omega
  · intro M hsat
    exact False.elim (hno ⟨M, hsat.1⟩)

/-- Likewise, absence of SAT DTMs vacuously supplies every canonical fiber
bound (already with exponent zero). -/
theorem canonicalFiberBound_of_no_DTMDecidesSAT
    (enc : ThreeCNFEncoding)
    (hno : ¬ ∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) :
    TimeExponentParametricSATCanonicalFiberBound enc := by
  intro e
  refine ⟨0, ?_⟩
  intro n M hsat
  exact False.elim (hno ⟨M, hsat.1⟩)

/-- Exact logical audit: the conjunction of canonical pair extraction and
canonical fiber anti-concentration is equivalent to nonexistence of a
polynomial-time SAT DTM in the repository's machine model.  Therefore proving
that conjunction is not a preliminary lemma toward P != NP; it is precisely
the separation theorem in decomposed semantic form. -/
theorem canonicalPairExtraction_and_fiberBound_iff_no_DTMDecidesSAT
    (enc : ThreeCNFEncoding) :
    (TimeExponentParametricSATCanonicalPairExtraction enc ∧
      TimeExponentParametricSATCanonicalFiberBound enc) ↔
    ¬ ∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M := by
  constructor
  · rintro ⟨hextract, hfiber⟩
    exact no_DTMDecidesSAT_of_canonicalPairExtraction_and_fiberBound
      enc hextract hfiber
  · intro hno
    exact ⟨canonicalPairExtraction_of_no_DTMDecidesSAT enc hno,
      canonicalFiberBound_of_no_DTMDecidesSAT enc hno⟩

/-! ## Duplicate-pair audit

The pair-extraction predicate above still does not encode N-frame geometry:
its `Fin K` indexing permits the same separating pair to be repeated `K`
times.  The construction below makes that collapse explicit.  Consequently a
non-vacuous extraction theorem must additionally prove pair injectivity (or a
stronger residual-label embedding) from SAT/N-frame semantics.
-/

/-- One concrete separating pair can be copied into an arbitrarily large
canonical family.  Thus cardinality of the index type alone is not cardinality
of distinct semantic obligations. -/
def duplicateCanonicalDTMFirstSeparationData
    {M : TuringMachine.DTM} {n K T t : Nat} {S : Type*}
    (hn : 1 ≤ n)
    (left right : Fin n → Bool)
    (observe : TuringMachine.Configuration M (TuringMachine.tapeSize M n) → S)
    (ht : t < T)
    (hsep :
      observe (TuringMachine.run M n (t + 1)
        (TuringMachine.initialConfig M n hn left)) ≠
      observe (TuringMachine.run M n (t + 1)
        (TuringMachine.initialConfig M n hn right))) :
    CanonicalDTMFirstSeparationData M n K T S where
  positiveLength := hn
  leftInput := fun _ => left
  rightInput := fun _ => right
  observe := observe
  separatedWithin := fun _ => ⟨t, ht, hsep⟩

/-- Honest distinctness condition missing from the weak extraction predicate:
different obligation indices must denote different ordered input pairs. -/
def CanonicalDTMFirstSeparationData.PairInjective
    {M : TuringMachine.DTM} {n K T : Nat} {S : Type*}
    (D : CanonicalDTMFirstSeparationData M n K T S) : Prop :=
  Function.Injective (fun k => (D.leftInput k, D.rightInput k))

/-- A duplicated family with at least two indices cannot satisfy semantic pair
injectivity. -/
theorem duplicateCanonicalData_not_pairInjective
    {M : TuringMachine.DTM} {n K T t : Nat} {S : Type*}
    (hK : 2 ≤ K)
    (hn : 1 ≤ n)
    (left right : Fin n → Bool)
    (observe : TuringMachine.Configuration M (TuringMachine.tapeSize M n) → S)
    (ht : t < T)
    (hsep :
      observe (TuringMachine.run M n (t + 1)
        (TuringMachine.initialConfig M n hn left)) ≠
      observe (TuringMachine.run M n (t + 1)
        (TuringMachine.initialConfig M n hn right))) :
    ¬ CanonicalDTMFirstSeparationData.PairInjective
      (duplicateCanonicalDTMFirstSeparationData
        (K := K) hn left right observe ht hsep) := by
  intro hinj
  let k0 : Fin K := ⟨0, by omega⟩
  let k1 : Fin K := ⟨1, by omega⟩
  have hpair :
      ((duplicateCanonicalDTMFirstSeparationData
          (K := K) hn left right observe ht hsep).leftInput k0,
        (duplicateCanonicalDTMFirstSeparationData
          (K := K) hn left right observe ht hsep).rightInput k0) =
      ((duplicateCanonicalDTMFirstSeparationData
          (K := K) hn left right observe ht hsep).leftInput k1,
        (duplicateCanonicalDTMFirstSeparationData
          (K := K) hn left right observe ht hsep).rightInput k1) := rfl
  have hk : k0 = k1 := hinj hpair
  have hval := congrArg Fin.val hk
  simp [k0, k1] at hval

/-! ## Duplication-free canonical frontier

We now strengthen extraction itself, rather than merely documenting the
missing condition.  Every extracted binomial family must consist of distinct
ordered input pairs.  This closes the duplicate-index loophole definitionally.
-/

/-- Canonical first-separation data together with semantic distinctness of all
indexed obligations. -/
structure InjectiveCanonicalDTMFirstSeparationData
    (M : TuringMachine.DTM) (n K T : Nat) (S : Type*) where
  data : CanonicalDTMFirstSeparationData M n K T S
  pairInjective : data.PairInjective

/-- Duplication-free N-frame data at one length. -/
def HasInjectiveCanonicalDTMNFrameFirstSeparationDataAt
    (M : TuringMachine.DTM) (n : Nat) : Prop :=
  ∃ (S : Type) (_decEq : DecidableEq S),
    Nonempty (InjectiveCanonicalDTMFirstSeparationData M n
      (Nat.choose (n / 3) (Nat.log 2 n))
      (TuringMachine.timeSteps M n) S)

/-- The honest extraction program: SAT semantics must produce a binomial
family of genuinely distinct ordered input pairs on actual DTM traces. -/
def TimeExponentParametricSATInjectiveCanonicalPairExtraction
    (enc : ThreeCNFEncoding) : Prop :=
  ∀ e c : Nat, ∃ n : Nat,
    n ≥ 2 ^ 20 ∧
    4 * (e + c + 1) ≤ Nat.log 2 n ∧
    ∀ M : TuringMachine.DTM,
      DTMDecidesSATWithEncodingAtMost enc e M →
      HasInjectiveCanonicalDTMNFrameFirstSeparationDataAt M n

/-- Injective extraction forgets to the earlier weak extraction interface. -/
theorem canonicalPairExtraction_of_injective
    {enc : ThreeCNFEncoding}
    (h : TimeExponentParametricSATInjectiveCanonicalPairExtraction enc) :
    TimeExponentParametricSATCanonicalPairExtraction enc := by
  intro e c
  obtain ⟨n, hn20, hlog, hdata⟩ := h e c
  refine ⟨n, hn20, hlog, ?_⟩
  intro M hsat
  obtain ⟨S, decEq, hD⟩ := hdata M hsat
  obtain ⟨D⟩ := hD
  exact ⟨S, decEq, ⟨D.data⟩⟩

/-- Distinct-pair extraction plus the canonical fiber bound still yields the
runtime contradiction, now without the duplicate-family loophole. -/
theorem no_DTMDecidesSAT_of_injectiveCanonicalPairExtraction_and_fiberBound
    (enc : ThreeCNFEncoding)
    (hextract : TimeExponentParametricSATInjectiveCanonicalPairExtraction enc)
    (hfiber : TimeExponentParametricSATCanonicalFiberBound enc) :
    ¬ ∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M :=
  no_DTMDecidesSAT_of_canonicalPairExtraction_and_fiberBound enc
    (canonicalPairExtraction_of_injective hextract) hfiber

/-- Under nonexistence of SAT DTMs, even the strengthened injective extraction
program is vacuously true. -/
theorem injectiveCanonicalPairExtraction_of_no_DTMDecidesSAT
    (enc : ThreeCNFEncoding)
    (hno : ¬ ∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) :
    TimeExponentParametricSATInjectiveCanonicalPairExtraction enc := by
  intro e c
  refine ⟨2 ^ (4 * (e + c + 1) + 20), ?_, ?_, ?_⟩
  · exact Nat.pow_le_pow_right (by omega : 1 ≤ (2 : Nat)) (by omega)
  · rw [Nat.log_pow]
    · omega
    · omega
  · intro M hsat
    exact False.elim (hno ⟨M, hsat.1⟩)

/-- Final duplication-free audit: injective canonical extraction together with
canonical fiber anti-concentration remains exactly equivalent to excluding all
polynomial-time SAT DTMs.  Pair injectivity repairs the formulation, but does
not make the missing mathematics weaker than separation. -/
theorem injectiveCanonicalPairExtraction_and_fiberBound_iff_no_DTMDecidesSAT
    (enc : ThreeCNFEncoding) :
    (TimeExponentParametricSATInjectiveCanonicalPairExtraction enc ∧
      TimeExponentParametricSATCanonicalFiberBound enc) ↔
    ¬ ∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M := by
  constructor
  · rintro ⟨hextract, hfiber⟩
    exact no_DTMDecidesSAT_of_injectiveCanonicalPairExtraction_and_fiberBound
      enc hextract hfiber
  · intro hno
    exact ⟨injectiveCanonicalPairExtraction_of_no_DTMDecidesSAT enc hno,
      canonicalFiberBound_of_no_DTMDecidesSAT enc hno⟩

/-! ## Initially-merged semantic repair

Pair injectivity blocks duplication, but an unrestricted observation can still
distinguish the two raw input configurations before the DTM performs any work.
The next interface requires every obligation pair to be merged at time zero.
Its canonical charge therefore records a genuine transition-created
distinction rather than pre-existing visibility of the input tape.
-/

/-- Duplication-free canonical data whose two observed traces agree initially
for every obligation. -/
structure InitiallyMergedInjectiveCanonicalDTMFirstSeparationData
    (M : TuringMachine.DTM) (n K T : Nat) (S : Type*) where
  data : InjectiveCanonicalDTMFirstSeparationData M n K T S
  initiallyMerged : ∀ k : Fin K,
    data.data.observe
      (TuringMachine.initialConfig M n data.data.positiveLength
        (data.data.leftInput k)) =
    data.data.observe
      (TuringMachine.initialConfig M n data.data.positiveLength
        (data.data.rightInput k))

/-- Initially merged, distinct N-frame obligations at one input length. -/
def HasInitiallyMergedInjectiveCanonicalDTMNFrameDataAt
    (M : TuringMachine.DTM) (n : Nat) : Prop :=
  ∃ (S : Type) (_decEq : DecidableEq S),
    Nonempty (InitiallyMergedInjectiveCanonicalDTMFirstSeparationData M n
      (Nat.choose (n / 3) (Nat.log 2 n))
      (TuringMachine.timeSteps M n) S)

/-- Fully repaired extraction program: obligations are distinct and invisible
to the chosen observation before actual DTM transitions separate them. -/
def TimeExponentParametricSATInitiallyMergedInjectiveExtraction
    (enc : ThreeCNFEncoding) : Prop :=
  ∀ e c : Nat, ∃ n : Nat,
    n ≥ 2 ^ 20 ∧
    4 * (e + c + 1) ≤ Nat.log 2 n ∧
    ∀ M : TuringMachine.DTM,
      DTMDecidesSATWithEncodingAtMost enc e M →
      HasInitiallyMergedInjectiveCanonicalDTMNFrameDataAt M n

/-- Initially-merged extraction forgets to injective extraction. -/
theorem injectiveCanonicalPairExtraction_of_initiallyMerged
    {enc : ThreeCNFEncoding}
    (h : TimeExponentParametricSATInitiallyMergedInjectiveExtraction enc) :
    TimeExponentParametricSATInjectiveCanonicalPairExtraction enc := by
  intro e c
  obtain ⟨n, hn20, hlog, hdata⟩ := h e c
  refine ⟨n, hn20, hlog, ?_⟩
  intro M hsat
  obtain ⟨S, decEq, hD⟩ := hdata M hsat
  obtain ⟨D⟩ := hD
  exact ⟨S, decEq, ⟨D.data⟩⟩

/-- The fully repaired extraction plus canonical anti-sharing still yields
separation. -/
theorem no_DTMDecidesSAT_of_initiallyMergedInjectiveExtraction_and_fiberBound
    (enc : ThreeCNFEncoding)
    (hextract : TimeExponentParametricSATInitiallyMergedInjectiveExtraction enc)
    (hfiber : TimeExponentParametricSATCanonicalFiberBound enc) :
    ¬ ∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M :=
  no_DTMDecidesSAT_of_injectiveCanonicalPairExtraction_and_fiberBound enc
    (injectiveCanonicalPairExtraction_of_initiallyMerged hextract) hfiber

/-- If SAT has no polynomial-time DTM, the initially-merged extraction target
is vacuously inhabited, just like the weaker formulations. -/
theorem initiallyMergedInjectiveExtraction_of_no_DTMDecidesSAT
    (enc : ThreeCNFEncoding)
    (hno : ¬ ∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) :
    TimeExponentParametricSATInitiallyMergedInjectiveExtraction enc := by
  intro e c
  refine ⟨2 ^ (4 * (e + c + 1) + 20), ?_, ?_, ?_⟩
  · exact Nat.pow_le_pow_right (by omega : 1 ≤ (2 : Nat)) (by omega)
  · rw [Nat.log_pow]
    · omega
    · omega
  · intro M hsat
    exact False.elim (hno ⟨M, hsat.1⟩)

/-- Exact audit of the fully repaired route.  Even with distinct obligations
and time-zero merging, extraction plus polynomial canonical fibers is
equivalent to the desired SAT lower bound. -/
theorem initiallyMergedInjectiveExtraction_and_fiberBound_iff_no_DTMDecidesSAT
    (enc : ThreeCNFEncoding) :
    (TimeExponentParametricSATInitiallyMergedInjectiveExtraction enc ∧
      TimeExponentParametricSATCanonicalFiberBound enc) ↔
    ¬ ∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M := by
  constructor
  · rintro ⟨hextract, hfiber⟩
    exact no_DTMDecidesSAT_of_initiallyMergedInjectiveExtraction_and_fiberBound
      enc hextract hfiber
  · intro hno
    exact ⟨initiallyMergedInjectiveExtraction_of_no_DTMDecidesSAT enc hno,
      canonicalFiberBound_of_no_DTMDecidesSAT enc hno⟩

/-! ## SAT-semantic obligation repair

The initially-merged interface still permits arbitrary input pairs unrelated
to SAT correctness.  We finally require each left input to encode a
satisfiable formula and each right input to encode an unsatisfiable formula.
Thus every demanded eventual distinction is semantically forced by a correct
SAT decider, rather than chosen by the extraction certificate alone.
-/

/-- Fully SAT-grounded canonical obligations: distinct, initially merged, and
carrying opposite SAT truth values under the repository encoding. -/
structure SATSemanticCanonicalDTMFirstSeparationData
    (enc : ThreeCNFEncoding) (M : TuringMachine.DTM)
    (n K T : Nat) (S : Type*) where
  data : InitiallyMergedInjectiveCanonicalDTMFirstSeparationData M n K T S
  leftFormula : Fin K → PaperFaithfulSeparation.ThreeCNF
  rightFormula : Fin K → PaperFaithfulSeparation.ThreeCNF
  leftEncoded : ∀ k, enc.Encodes (data.data.data.leftInput k) (leftFormula k)
  rightEncoded : ∀ k, enc.Encodes (data.data.data.rightInput k) (rightFormula k)
  leftSatisfiable : ∀ k, (leftFormula k).IsSatisfiable
  rightUnsatisfiable : ∀ k, ¬ (rightFormula k).IsSatisfiable

/-- Fully SAT-semantic N-frame data at one length. -/
def HasSATSemanticCanonicalDTMNFrameDataAt
    (enc : ThreeCNFEncoding) (M : TuringMachine.DTM) (n : Nat) : Prop :=
  ∃ (S : Type) (_decEq : DecidableEq S),
    Nonempty (SATSemanticCanonicalDTMFirstSeparationData enc M n
      (Nat.choose (n / 3) (Nat.log 2 n))
      (TuringMachine.timeSteps M n) S)

/-- The final honest extraction target for this route. -/
def TimeExponentParametricSATSemanticCanonicalExtraction
    (enc : ThreeCNFEncoding) : Prop :=
  ∀ e c : Nat, ∃ n : Nat,
    n ≥ 2 ^ 20 ∧
    4 * (e + c + 1) ≤ Nat.log 2 n ∧
    ∀ M : TuringMachine.DTM,
      DTMDecidesSATWithEncodingAtMost enc e M →
      HasSATSemanticCanonicalDTMNFrameDataAt enc M n

/-- SAT-semantic extraction forgets to initially-merged injective extraction. -/
theorem initiallyMergedInjectiveExtraction_of_SATSemantic
    {enc : ThreeCNFEncoding}
    (h : TimeExponentParametricSATSemanticCanonicalExtraction enc) :
    TimeExponentParametricSATInitiallyMergedInjectiveExtraction enc := by
  intro e c
  obtain ⟨n, hn20, hlog, hdata⟩ := h e c
  refine ⟨n, hn20, hlog, ?_⟩
  intro M hsat
  obtain ⟨S, decEq, hD⟩ := hdata M hsat
  obtain ⟨D⟩ := hD
  exact ⟨S, decEq, ⟨D.data⟩⟩

/-- Fully SAT-grounded extraction plus canonical anti-sharing yields the SAT
lower bound. -/
theorem no_DTMDecidesSAT_of_SATSemanticExtraction_and_fiberBound
    (enc : ThreeCNFEncoding)
    (hextract : TimeExponentParametricSATSemanticCanonicalExtraction enc)
    (hfiber : TimeExponentParametricSATCanonicalFiberBound enc) :
    ¬ ∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M :=
  no_DTMDecidesSAT_of_initiallyMergedInjectiveExtraction_and_fiberBound enc
    (initiallyMergedInjectiveExtraction_of_SATSemantic hextract) hfiber

/-- With no SAT DTM, the fully semantic extraction program is vacuous. -/
theorem SATSemanticExtraction_of_no_DTMDecidesSAT
    (enc : ThreeCNFEncoding)
    (hno : ¬ ∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) :
    TimeExponentParametricSATSemanticCanonicalExtraction enc := by
  intro e c
  refine ⟨2 ^ (4 * (e + c + 1) + 20), ?_, ?_, ?_⟩
  · exact Nat.pow_le_pow_right (by omega : 1 ≤ (2 : Nat)) (by omega)
  · rw [Nat.log_pow]
    · omega
    · omega
  · intro M hsat
    exact False.elim (hno ⟨M, hsat.1⟩)

/-- Final semantic audit: even after requiring opposite encoded SAT outcomes,
distinct pairs, time-zero merging, actual DTM traces, and canonical charges,
extraction plus polynomial fibers is exactly the separation statement. -/
theorem SATSemanticExtraction_and_fiberBound_iff_no_DTMDecidesSAT
    (enc : ThreeCNFEncoding) :
    (TimeExponentParametricSATSemanticCanonicalExtraction enc ∧
      TimeExponentParametricSATCanonicalFiberBound enc) ↔
    ¬ ∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M := by
  constructor
  · rintro ⟨hextract, hfiber⟩
    exact no_DTMDecidesSAT_of_SATSemanticExtraction_and_fiberBound
      enc hextract hfiber
  · intro hno
    exact ⟨SATSemanticExtraction_of_no_DTMDecidesSAT enc hno,
      canonicalFiberBound_of_no_DTMDecidesSAT enc hno⟩

/-! ## Run-local transition-event audit

The canonical charge above maps every obligation to a *time index* in
`Fin T`.  But obligations are evaluated on different pairs of DTM runs.
Transition `t` in run `k` and transition `t` in run `j` are different physical
events.  The honest event space is therefore `Fin K × Fin T`, not `Fin T`.
Once run identity is retained, the event charge is automatically injective and
its capacity bound is only `K ≤ K*T`, which cannot imply `K ≤ T`.
-/

/-- Honest run-local event charged by obligation `k`: the event remembers both
the run-family index and its canonical first-separation time. -/
noncomputable def CanonicalDTMFirstSeparationData.runLocalEventCharge
    {M : TuringMachine.DTM} {n K T : Nat} {S : Type*} [DecidableEq S]
    (D : CanonicalDTMFirstSeparationData M n K T S) :
    Fin K → Fin K × Fin T :=
  fun k => (k, D.canonicalCharge k)

/-- Run-local event charging is injective for purely structural reasons. -/
theorem CanonicalDTMFirstSeparationData.runLocalEventCharge_injective
    {M : TuringMachine.DTM} {n K T : Nat} {S : Type*} [DecidableEq S]
    (D : CanonicalDTMFirstSeparationData M n K T S) :
    Function.Injective D.runLocalEventCharge := by
  intro i j hij
  exact congrArg Prod.fst hij

/-- The honest event capacity law retains the factor `K` for the number of
separate runs.  This is the unconditional statement supported by physical
transition events. -/
theorem obligations_le_runLocalEvents
    {M : TuringMachine.DTM} {n K T : Nat} {S : Type*} [DecidableEq S]
    (D : CanonicalDTMFirstSeparationData M n K T S) :
    K ≤ K * T := by
  have hcard := Fintype.card_le_of_injective D.runLocalEventCharge
    D.runLocalEventCharge_injective
  simpa using hcard

/-- When at least one transition exists, the run-local capacity law is
automatic.  It contains no runtime lower bound regardless of the number of
obligations. -/
theorem obligations_le_runLocalEvents_of_positiveHorizon
    (K T : Nat) (hT : 1 ≤ T) : K ≤ K * T := by
  simpa using Nat.mul_le_mul_left K hT

/-- A time-index collision does not identify physical events: two obligations
with equal canonical times still have unequal run-local charges whenever their
run indices differ. -/
theorem CanonicalDTMFirstSeparationData.runLocalEvent_ne_of_index_ne
    {M : TuringMachine.DTM} {n K T : Nat} {S : Type*} [DecidableEq S]
    (D : CanonicalDTMFirstSeparationData M n K T S)
    {i j : Fin K} (hij : i ≠ j) :
    D.runLocalEventCharge i ≠ D.runLocalEventCharge j :=
  fun h => hij (D.runLocalEventCharge_injective h)

/-! ## Single-run repair and circularity audit

To obtain a one-run runtime lower bound, all `K` obligations must be charged to
events of one concrete run.  If every event may discharge at most one
obligation, the required charge is an injection `Fin K -> Fin T`.  The next
theorems show this condition is exactly equivalent to `K <= T`; it is not an
independently weaker bridge.
-/

/-- A physically valid non-amortized schedule inside one actual DTM run.  The
configuration trace is explicit; `eventOf` selects one of its `T` transition
events for each obligation. -/
structure SingleRunNonAmortizedObligationSchedule
    (M : TuringMachine.DTM) (n K T : Nat) where
  positiveLength : 1 ≤ n
  input : Fin n → Bool
  eventOf : Fin K → Fin T
  eventOf_injective : Function.Injective eventOf

/-- A single-run non-amortized schedule immediately forces the runtime-event
lower bound. -/
theorem obligations_le_singleRunTransitions
    {M : TuringMachine.DTM} {n K T : Nat}
    (S : SingleRunNonAmortizedObligationSchedule M n K T) : K ≤ T := by
  simpa using Fintype.card_le_of_injective S.eventOf S.eventOf_injective

/-- Conversely, once `K <= T` is already known, any positive-length DTM input
can be decorated with a single-run non-amortized schedule. -/
def singleRunScheduleOfLe
    {M : TuringMachine.DTM} {n K T : Nat}
    (hn : 1 ≤ n) (input : Fin n → Bool) (hKT : K ≤ T) :
    SingleRunNonAmortizedObligationSchedule M n K T where
  positiveLength := hn
  input := input
  eventOf := Fin.castLE hKT
  eventOf_injective := Fin.castLE_injective hKT

/-- Exact audit: for a fixed concrete run input, existence of a one-use event
charge is equivalent to the desired numerical runtime bound. -/
theorem nonempty_singleRunSchedule_iff
    {M : TuringMachine.DTM} {n K T : Nat}
    (hn : 1 ≤ n) (input : Fin n → Bool) :
    Nonempty (SingleRunNonAmortizedObligationSchedule M n K T) ↔ K ≤ T := by
  constructor
  · rintro ⟨S⟩
    exact obligations_le_singleRunTransitions S
  · intro hKT
    exact ⟨singleRunScheduleOfLe hn input hKT⟩

/-- At the N-frame scale, postulating a non-amortized single-run schedule is
therefore literally equivalent to the binomial runtime lower bound. -/
theorem nframe_singleRunSchedule_iff_runtimeLower
    {M : TuringMachine.DTM} {n : Nat}
    (hn : 1 ≤ n) (input : Fin n → Bool) :
    Nonempty (SingleRunNonAmortizedObligationSchedule M n
      (Nat.choose (n / 3) (Nat.log 2 n))
      (TuringMachine.timeSteps M n)) ↔
    Nat.choose (n / 3) (Nat.log 2 n) ≤ TuringMachine.timeSteps M n :=
  nonempty_singleRunSchedule_iff hn input

/-! ## Bounded-reuse single-run audit

Allowing each event in the one run to serve at most `r` obligations changes
the capacity target to `K <= T*r`.  The converse below constructs the schedule
from exactly that inequality, so bounded-reuse charging also contains no
semantic content beyond its desired arithmetic conclusion.
-/

/-- A bounded-reuse obligation schedule inside one concrete DTM run. -/
structure SingleRunBoundedReuseObligationSchedule
    (M : TuringMachine.DTM) (n K T r : Nat) where
  positiveLength : 1 ≤ n
  input : Fin n → Bool
  eventOf : Fin K → Fin T
  fiber_le : ∀ event : Fin T,
    Fintype.card {k : Fin K // eventOf k = event} ≤ r

/-- Bounded reuse inside one run gives exactly the usual capacity inequality. -/
theorem obligations_le_singleRunTransitions_mul_reuse
    {M : TuringMachine.DTM} {n K T r : Nat}
    (S : SingleRunBoundedReuseObligationSchedule M n K T r) :
    K ≤ T * r := by
  let R : BoundedTransitionReuse K T r :=
    { resourceOf := fun x => S.eventOf x.1
      fiber_le := by
        intro event
        let forgetUnit :
            {x : Fin K × Fin 1 // S.eventOf x.1 = event} →
              {k : Fin K // S.eventOf k = event} :=
          fun x => ⟨x.1.1, x.2⟩
        have hinj : Function.Injective forgetUnit := by
          intro x y hxy
          apply Subtype.ext
          apply Prod.ext
          · exact congrArg Subtype.val hxy
          · exact Subsingleton.elim _ _
        exact (Fintype.card_le_of_injective forgetUnit hinj).trans
          (S.fiber_le event) }
  exact obligations_le_transitions_mul_reuse R

/-- Arithmetic capacity alone constructs a balanced event assignment with
fiber size at most `r`. -/
noncomputable def singleRunBoundedReuseScheduleOfCapacity
    {M : TuringMachine.DTM} {n K T r : Nat}
    (hn : 1 ≤ n) (input : Fin n → Bool) (hcap : K ≤ T * r) :
    SingleRunBoundedReuseObligationSchedule M n K T r := by
  classical
  let embed : Fin K → Fin (T * r) := Fin.castLE hcap
  refine
    { positiveLength := hn
      input := input
      eventOf := fun k =>
        ⟨(embed k).val / r, by
          have hv : (embed k).val < T * r := (embed k).isLt
          by_cases hr : r = 0
          · subst r
            simp at hv
          · exact (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hr)).2 (by
              simpa [Nat.mul_comm] using hv)⟩
      fiber_le := ?_ }
  intro event
  by_cases hr : r = 0
  · subst r
    have hK : K = 0 := by omega
    subst K
    simp
  · let fiberEmbed :
        {k : Fin K //
          (⟨(embed k).val / r, by
            have hv : (embed k).val < T * r := (embed k).isLt
            exact (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hr)).2 (by
              simpa [Nat.mul_comm] using hv)⟩ : Fin T) = event} → Fin r :=
      fun k => ⟨(embed k.1).val % r, Nat.mod_lt _ (Nat.pos_of_ne_zero hr)⟩
    have hinj : Function.Injective fiberEmbed := by
      intro x y hxy
      apply Subtype.ext
      apply Fin.ext
      have hdivx : (embed x.1).val / r = event.val :=
        congrArg Fin.val x.2
      have hdivy : (embed y.1).val / r = event.val :=
        congrArg Fin.val y.2
      have hembed : embed x.1 = embed y.1 := by
        apply Fin.ext
        have hmod : (embed x.1).val % r = (embed y.1).val % r :=
          congrArg Fin.val hxy
        have hx := Nat.mod_add_div (embed x.1).val r
        have hy := Nat.mod_add_div (embed y.1).val r
        rw [hdivx] at hx
        rw [hdivy] at hy
        omega
      exact congrArg Fin.val ((Fin.castLE_injective hcap) hembed)
    simpa using Fintype.card_le_of_injective fiberEmbed hinj

/-- Exact bounded-reuse audit for one run. -/
theorem nonempty_singleRunBoundedReuseSchedule_iff
    {M : TuringMachine.DTM} {n K T r : Nat}
    (hn : 1 ≤ n) (input : Fin n → Bool) :
    Nonempty (SingleRunBoundedReuseObligationSchedule M n K T r) ↔
      K ≤ T * r := by
  constructor
  · rintro ⟨S⟩
    exact obligations_le_singleRunTransitions_mul_reuse S
  · intro hcap
    exact ⟨singleRunBoundedReuseScheduleOfCapacity hn input hcap⟩

/-! ## Thermodynamic boundary of transition reuse

This is the direct splice between the repository's thermodynamic sharing
model and the physically valid one-run transition accounting above.  The
thermodynamic premise is not merely decorative: a positive energy charge per
unit of reuse converts a finite energy budget into a reuse cap.  At zero
charge, the coupling collapses exactly to ordinary free fanout.
-/

/-- A one-run obligation schedule whose reuse multiplicity is charged against
a thermodynamic energy budget. -/
structure ThermodynamicSingleRunReuseSchedule
    (M : TuringMachine.DTM) (n K T r eps energy : Nat) : Type where
  schedule : SingleRunBoundedReuseObligationSchedule M n K T r
  energy_bound : eps * r ≤ energy

/-- **Thermodynamic sharing boundary.**  If every unit of transition reuse has
positive energy cost, then a run serving `K` obligations in `T` transitions
must satisfy `K ≤ T * energy`. -/
theorem obligations_le_transitions_mul_thermodynamicEnergy
    {M : TuringMachine.DTM} {n K T r eps energy : Nat}
    (S : ThermodynamicSingleRunReuseSchedule M n K T r eps energy)
    (hε : 1 ≤ eps) :
    K ≤ T * energy := by
  have hr : r ≤ energy := by
    have h1 : 1 * r ≤ eps * r := Nat.mul_le_mul hε (Nat.le_refl r)
    rw [Nat.one_mul] at h1
    exact h1.trans S.energy_bound
  exact (obligations_le_singleRunTransitions_mul_reuse S.schedule).trans
    (Nat.mul_le_mul_left T hr)

/-- With free sharing (`eps = 0`), thermodynamics adds no restriction: a
thermodynamic schedule exists exactly when the underlying arithmetic capacity
`K ≤ T*r` already holds. -/
theorem nonempty_freeThermodynamicReuseSchedule_iff
    {M : TuringMachine.DTM} {n K T r energy : Nat}
    (hn : 1 ≤ n) (input : Fin n → Bool) :
    Nonempty (ThermodynamicSingleRunReuseSchedule M n K T r 0 energy) ↔
      K ≤ T * r := by
  constructor
  · rintro ⟨S⟩
    exact obligations_le_singleRunTransitions_mul_reuse S.schedule
  · intro hcap
    exact ⟨{
      schedule := singleRunBoundedReuseScheduleOfCapacity hn input hcap
      energy_bound := ThermodynamicObserver.free_fanout_vacuous energy r
    }⟩

/-- Full one-run amortization survives every finite thermodynamic budget when
fanout/reuse has zero charge.  Thus the physical boundary constrains sharing
only after a positive charge has been derived for the computational model. -/
theorem freeThermodynamicFullAmortization
    {M : TuringMachine.DTM} {n K T energy : Nat}
    (hn : 1 ≤ n) (hT : 1 ≤ T) (input : Fin n → Bool) :
    Nonempty (ThermodynamicSingleRunReuseSchedule M n K T K 0 energy) := by
  apply (nonempty_freeThermodynamicReuseSchedule_iff hn input).2
  simpa [Nat.mul_comm] using
    obligations_le_runLocalEvents_of_positiveHorizon K T hT

/-! ## Information-boundary obstruction to charging reuse

The repository's information-boundary test now meets the transition-reuse
model directly.  A Landauer/entropy-bounded charge cannot certify a reuse
multiplicity larger than the observer information.  Thus the fact that
sharing crosses a physical boundary is not yet the positive-charge theorem:
one must prove a charge exceeding the information carried by that boundary.
-/

/-- A proposed observer boundary whose charge is dominated by its information,
together with the claim that this charge pays for every unit of reuse. -/
structure InformationBoundedReuseCharge (r boundaryCharge information : Nat) : Prop where
  charge_le_information : boundaryCharge ≤ information
  reuse_le_charge : r ≤ boundaryCharge

/-- An information-bounded thermodynamic boundary cannot certify reuse above
its information content. -/
theorem no_informationBoundedReuseCharge_of_information_lt_reuse
    {r boundaryCharge information : Nat}
    (hgap : information < r) :
    ¬ InformationBoundedReuseCharge r boundaryCharge information := by
  intro H
  have hcharge := NFrameInfoBoundaryTest.charge_must_exceed_info_to_certify_sharing
    (Cfg := Unit) (fun _ => boundaryCharge) (fun _ => information)
    (fun _ => r) () H.reuse_le_charge hgap
  exact Nat.not_lt_of_ge H.charge_le_information hcharge

/-- **Thermodynamic-sharing frontier.**  If the observer boundary carries
less information than the reuse multiplicity, no Landauer/information-bounded
charge can justify the reuse cap needed by the runtime argument.  Any working
charge must therefore be super-informational (for example an independently
proved geometric/topological congestion charge), not entropy alone. -/
theorem thermodynamicReuseCharge_must_exceed_information
    {r boundaryCharge information : Nat}
    (hreuse : r ≤ boundaryCharge)
    (hgap : information < r) :
    information < boundaryCharge :=
  NFrameInfoBoundaryTest.charge_must_exceed_info_to_certify_sharing
    (Cfg := Unit) (fun _ => boundaryCharge) (fun _ => information)
    (fun _ => r) () hreuse hgap

/-! ## Geometric congestion: the seam-forced hub

Unlike entropy, hub reach is genuinely sharing-sensitive: the repository
proves that a hub serving `r` contexts has fan-in at least `r`.  Coupling that
fact to the one-run schedule gives a valid geometric capacity theorem.  The
remaining distinction is quantitative: merely being a hub does not bound its
fan-in, and free fan-in realizes arbitrary reuse.
-/

/-- A one-run reuse schedule grounded in the actual seam-forced hub that
serves those reused contexts. -/
structure HubGroundedSingleRunReuseSchedule
    (M : TuringMachine.DTM) (n K T r : Nat) : Type where
  schedule : SingleRunBoundedReuseObligationSchedule M n K T r
  hub : SeamForcesHub.Hub
  hub_serves_reuse : hub.serves = r

/-- **Geometric sharing charge.**  Hub reach replaces the failed entropy
charge: `K` obligations served in `T` events are bounded by `T` times the
hub's fan-in. -/
theorem obligations_le_transitions_mul_hubFanIn
    {M : TuringMachine.DTM} {n K T r : Nat}
    (S : HubGroundedSingleRunReuseSchedule M n K T r) :
    K ≤ T * S.hub.fanIn := by
  have hr : r ≤ S.hub.fanIn := by
    calc
      r = S.hub.serves := S.hub_serves_reuse.symm
      _ ≤ S.hub.fanIn := S.hub.capacity
  exact (obligations_le_singleRunTransitions_mul_reuse S.schedule).trans
    (Nat.mul_le_mul_left T hr)

/-- A polynomial/finite reach cap on the seam hub therefore supplies the
thermodynamic-style capacity inequality without appealing to Landauer
information. -/
theorem obligations_le_transitions_mul_hubReachBudget
    {M : TuringMachine.DTM} {n K T r reachBudget : Nat}
    (S : HubGroundedSingleRunReuseSchedule M n K T r)
    (hreach : S.hub.fanIn ≤ reachBudget) :
    K ≤ T * reachBudget :=
  (obligations_le_transitions_mul_hubFanIn S).trans
    (Nat.mul_le_mul_left T hreach)

/-- **Free-reach escape.**  The qualitative fact that sharing creates a hub
does not itself cap sharing.  For every `r ≥ 2` satisfying the ordinary
capacity law, there is a hub-grounded schedule whose single hub has fan-in
exactly `r`. -/
theorem hubGroundedReuseSchedule_of_freeReach
    {M : TuringMachine.DTM} {n K T r : Nat}
    (hn : 1 ≤ n) (input : Fin n → Bool) (hr : 2 ≤ r)
    (hcap : K ≤ T * r) :
    Nonempty (HubGroundedSingleRunReuseSchedule M n K T r) := by
  obtain ⟨H, hserves, _hfanIn⟩ := SeamForcesHub.hub_escapes r hr
  exact ⟨{
    schedule := singleRunBoundedReuseScheduleOfCapacity hn input hcap
    hub := H
    hub_serves_reuse := hserves
  }⟩

/-! ## DTM-local spacetime ceiling

A local Turing run cannot realize an instantaneous unbounded-fan-in gate.  The
honest replacement is a hub whose reach is accumulated through its `T` local
transition opportunities, hence at most `T+1`.  This yields a quadratic
spacetime capacity.  It is a real improvement over free fan-in, but remains
polynomial and therefore does not by itself produce the N-frame extraction.
-/

/-- A hub-grounded schedule whose geometric reach is local to a `T`-step DTM
run.  `fanIn ≤ T+1` is the explicit machine-locality bridge. -/
structure DTMLocalHubReuseSchedule
    (M : TuringMachine.DTM) (n K T r : Nat) : Type where
  grounded : HubGroundedSingleRunReuseSchedule M n K T r
  fanIn_le_local_accesses : grounded.hub.fanIn ≤ T + 1

/-- **Local DTM spacetime capacity.**  A `T`-step local run with one
seam-grounded hub can service at most `T(T+1)` contextual obligations. -/
theorem obligations_le_DTM_local_spacetime_capacity
    {M : TuringMachine.DTM} {n K T r : Nat}
    (S : DTMLocalHubReuseSchedule M n K T r) :
    K ≤ T * (T + 1) :=
  obligations_le_transitions_mul_hubReachBudget S.grounded
    S.fanIn_le_local_accesses

/-- The local-hub certificate is impossible beyond the quadratic spacetime
capacity. -/
theorem no_DTMLocalHubReuseSchedule_of_quadratic_gap
    {M : TuringMachine.DTM} {n K T r : Nat}
    (hgap : T * (T + 1) < K) :
    IsEmpty (DTMLocalHubReuseSchedule M n K T r) :=
  ⟨fun S => Nat.not_lt_of_ge
    (obligations_le_DTM_local_spacetime_capacity S) hgap⟩

/-- Conversely, whenever arithmetic capacity already permits reuse `r` and
`r ≤ T+1`, the free-reach hub construction is DTM-local.  Thus the quadratic
ceiling is the exact content of this locality abstraction, not an additional
SAT lower bound. -/
theorem DTMLocalHubReuseSchedule_of_capacity
    {M : TuringMachine.DTM} {n K T r : Nat}
    (hn : 1 ≤ n) (input : Fin n → Bool) (hr2 : 2 ≤ r)
    (hrT : r ≤ T + 1) (hcap : K ≤ T * r) :
    Nonempty (DTMLocalHubReuseSchedule M n K T r) := by
  exact ⟨{
    grounded := {
      schedule := singleRunBoundedReuseScheduleOfCapacity hn input hcap
      hub := ⟨r, r, r, hr2, hr2, le_rfl⟩
      hub_serves_reuse := rfl
    }
    fanIn_le_local_accesses := hrT
  }⟩

/-! ## SAT extraction frontier and full quadratic cash-out -/

/-- The exact remaining SAT-semantic assertion: at a calibrated length, every
claimed exponent-`e` SAT DTM exposes the full binomial obligation family in
one actual local hub/run. -/
def TimeExponentParametricSATSingleLocalHubExtraction
    (enc : ThreeCNFEncoding) : Prop :=
  ∀ e : Nat, ∃ n : Nat,
    n ≥ 2 ^ 20 ∧
    4 * ((2 * e + 1) + 1) ≤ Nat.log 2 n ∧
    ∀ M : TuringMachine.DTM,
      DTMDecidesSATWithEncodingAtMost enc e M →
      ∃ r : Nat, Nonempty (DTMLocalHubReuseSchedule M n
        (Nat.choose (n / 3) (Nat.log 2 n))
        (TuringMachine.timeSteps M n) r)

/-- A polynomial DTM's quadratic local spacetime capacity remains bounded by
the next calibrated polynomial exponent. -/
theorem timeSteps_mul_succ_le_nextPolynomial
    (M : TuringMachine.DTM) {n e : Nat}
    (hn : 2 ≤ n) (he : M.timeBound ≤ e) :
    TuringMachine.timeSteps M n * (TuringMachine.timeSteps M n + 1) ≤
      n ^ (2 * e + 1) := by
  have htime : TuringMachine.timeSteps M n ≤ n ^ e := by
    simp only [TuringMachine.timeSteps]
    exact Nat.pow_le_pow_right (by omega) he
  have hpowpos : 1 ≤ n ^ e := Nat.one_le_pow e n (by omega)
  have hsucc : n ^ e + 1 ≤ n ^ (e + 1) := by
    rw [pow_succ]
    nlinarith
  calc
    TuringMachine.timeSteps M n * (TuringMachine.timeSteps M n + 1)
        ≤ n ^ e * (n ^ e + 1) := Nat.mul_le_mul htime (Nat.add_le_add_right htime 1)
    _ ≤ n ^ e * n ^ (e + 1) := Nat.mul_le_mul_left _ hsucc
    _ = n ^ (2 * e + 1) := by rw [← pow_add]; congr 1; omega

/-- **Complete cash-out.**  Single-local-hub extraction contradicts every
polynomial-time SAT DTM: locality gives a quadratic capacity, while the
calibrated binomial family exceeds the corresponding polynomial. -/
theorem no_DTMDecidesSAT_of_singleLocalHubExtraction
    (enc : ThreeCNFEncoding)
    (hextract : TimeExponentParametricSATSingleLocalHubExtraction enc) :
    Not (∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) := by
  rintro ⟨M, hdec⟩
  rcases hextract M.timeBound with ⟨n, hn20, hlog, hlocal⟩
  rcases hlocal M ⟨hdec, le_rfl⟩ with ⟨r, ⟨S⟩⟩
  have hn2 : 2 ≤ n := le_trans (by norm_num : 2 ≤ 2 ^ 20) hn20
  have hcapacity := obligations_le_DTM_local_spacetime_capacity S
  have hpoly := timeSteps_mul_succ_le_nextPolynomial M hn2 le_rfl
  have hchoose_le :
      Nat.choose (n / 3) (Nat.log 2 n) ≤ n ^ (2 * M.timeBound + 1) :=
    hcapacity.trans hpoly
  have hgap :
      n ^ (2 * M.timeBound + 1) <
        Nat.choose (n / 3) (Nat.log 2 n) :=
    arithmetic_gap_for_exponent (2 * M.timeBound + 1) n hn20 hlog
  exact Nat.not_lt_of_ge hchoose_le hgap

/-- If no encoded polynomial-time SAT DTM exists, the local-hub extraction
property holds vacuously. -/
theorem singleLocalHubExtraction_of_no_DTMDecidesSAT
    (enc : ThreeCNFEncoding)
    (hno : Not (∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M)) :
    TimeExponentParametricSATSingleLocalHubExtraction enc := by
  intro e
  let n := 2 ^ (4 * ((2 * e + 1) + 1) + 20)
  refine ⟨n, ?_, ?_, ?_⟩
  · dsimp [n]
    exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : Nat))
      (by omega : 20 ≤ 4 * (2 * e + 1 + 1) + 20)
  · dsimp [n]
    rw [Nat.log_pow (by norm_num : 1 < 2)]
    omega
  · intro M hM
    exact False.elim (hno ⟨M, hM.1⟩)

/-- The proposed simultaneous local-hub extraction is exactly separation in
this model.  All thermodynamic, geometric, locality, and arithmetic work after
extraction is complete; extraction itself is the breakthrough. -/
theorem singleLocalHubExtraction_iff_no_DTMDecidesSAT
    (enc : ThreeCNFEncoding) :
    TimeExponentParametricSATSingleLocalHubExtraction enc ↔
      Not (∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) :=
  ⟨no_DTMDecidesSAT_of_singleLocalHubExtraction enc,
    singleLocalHubExtraction_of_no_DTMDecidesSAT enc⟩

/-! ## Distributed local-hub audit

The only alternative to simultaneous extraction is to keep one local hub per
obligation/run.  Physical event identity then includes the run index, and the
obligation factor returns.  The resulting bound is automatic at every
positive horizon, even though each individual run obeys the quadratic local
spacetime ceiling.
-/

/-- Run-local quadratic spacetime events: an obligation index, a transition
time, and one of the at most `T+1` local access/reach slots. -/
abbrev DistributedLocalHubEvent (K T : Nat) := Fin K × Fin T × Fin (T + 1)

/-- Every obligation can be assigned injectively to its own run-local event
at any positive transition horizon. -/
def distributedLocalHubEventCharge
    (K T : Nat) (hT : 1 ≤ T) : Fin K → DistributedLocalHubEvent K T :=
  fun k => (k, ⟨0, hT⟩, ⟨0, by omega⟩)

theorem distributedLocalHubEventCharge_injective
    (K T : Nat) (hT : 1 ≤ T) :
    Function.Injective (distributedLocalHubEventCharge K T hT) := by
  intro x y hxy
  exact congrArg (fun z => z.1) hxy

/-- Honest distributed capacity retains the run factor:
`K ≤ K*T*(T+1)`. -/
theorem obligations_le_distributed_local_spacetime
    (K T : Nat) (hT : 1 ≤ T) :
    K ≤ K * T * (T + 1) := by
  let charge := distributedLocalHubEventCharge K T hT
  have hinj : Function.Injective charge :=
    distributedLocalHubEventCharge_injective K T hT
  have hcard := Fintype.card_le_of_injective charge hinj
  simpa [DistributedLocalHubEvent, Nat.mul_assoc] using hcard

/-- The distributed thermodynamic bound is automatic and cancels no
obligation factor.  Consequently, per-run local hubs cannot replace the
single-run extraction premise. -/
theorem distributed_local_spacetime_bound_is_automatic
    (K T : Nat) :
    1 ≤ T → K ≤ K * T * (T + 1) :=
  obligations_le_distributed_local_spacetime K T

/-! ## Final thermodynamic-locality verdict -/

/-- The complete numerical content of the thermodynamic/locality route at
fixed parameters.  It records both physically honest event interpretations:
one local run gives quadratic capacity, while `K` separate local runs retain
the factor `K`. -/
def ThermodynamicLocalityAuditVerdict
    {M : TuringMachine.DTM} (n K T r : Nat) : Prop :=
  (∀ S : DTMLocalHubReuseSchedule M n K T r, K ≤ T * (T + 1)) ∧
  (1 ≤ T → K ≤ K * T * (T + 1))

/-- **Exhaustive thermodynamic-locality audit.**  Local reach gives the useful
quadratic law only when all obligations inhabit one run.  Across distinct
runs, physical event identity restores the obligation factor and the bound is
automatic. -/
theorem thermodynamicLocalityAuditVerdict
    {M : TuringMachine.DTM} (n K T r : Nat) :
    ThermodynamicLocalityAuditVerdict (M := M) n K T r := by
  exact ⟨obligations_le_DTM_local_spacetime_capacity,
    distributed_local_spacetime_bound_is_automatic K T⟩

/-- Final encoded-SAT classification: the only thermodynamic/locality premise
that removes the run factor—the universal single-local-hub extraction—is
logically equivalent to the desired no-polynomial-SAT-decider conclusion. -/
theorem thermodynamicObserverFrontier_iff_no_DTMDecidesSAT
    (enc : ThreeCNFEncoding) :
    TimeExponentParametricSATSingleLocalHubExtraction enc ↔
      Not (∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) :=
  singleLocalHubExtraction_iff_no_DTMDecidesSAT enc

/-! ## Where the sharing boundary is already non-vacuous

The failure of the universal DTM transfer must not be confused with failure of
the geometric invariant itself.  In the repository's boundary-transducer
circuit model, the selector/sign semantics, minimal-DAG normal forms, and
fanout curvature have already been connected without an extraction premise.
The resulting lower bound is modest (linear plus `Omega(sqrt N)`), but it is a
genuine SAT-semantic sharing charge rather than a restatement of the desired
runtime inequality.
-/

/-- **Non-vacuous restricted-model sharing boundary.**  Every minimal circuit
for the encoded N-frame SAT family pays the full live-region reading cost plus
an unconditional curvature term.  This is the proved setting in which
geometric sharing congestion really does become computational cost. -/
theorem restrictedCircuitSATSharingBoundary
    (N : Nat) (hv : 1 ≤ NFrameBoundaryTransducer.sat3V N)
    (hm3 : 3 ≤ NFrameBoundaryTransducer.sat3M N)
    (c : List (NFrameBoundaryTransducer.CGate N))
    (hcomp : NFrameBoundaryTransducer.computes c
      (NFrameBoundaryTransducer.sat3Family N))
    (hmin : c.length = NFrameBoundaryTransducer.cbudget
      (NFrameBoundaryTransducer.sat3Family N)) :
    64 * (NFrameBoundaryTransducer.sat3M N *
        NFrameBoundaryTransducer.sat3D N) + NFrameBoundaryTransducer.sat3M N
      ≤ 32 * NFrameBoundaryTransducer.cbudget
          (NFrameBoundaryTransducer.sat3Family N) + 95 :=
  NFrameBoundaryTransducer.sat3_cbudget_omega N hv hm3 c hcomp hmin

/-- **Quantitative transfer audit.**  The entire left-hand demand certified by
`restrictedCircuitSATSharingBoundary` is at most linear in the input length.
Thus it is a genuine congestion charge, but it is compatible with the
polynomial circuit upper bound obtained from a polynomial-time machine; this
particular charge cannot by itself establish `SuperPolyCBudget`. -/
theorem restrictedCircuitSharingDemand_le_linear (N : Nat) :
    64 * (NFrameBoundaryTransducer.sat3M N *
        NFrameBoundaryTransducer.sat3D N) + NFrameBoundaryTransducer.sat3M N
      ≤ 65 * N := by
  have hlive : NFrameBoundaryTransducer.sat3M N *
      NFrameBoundaryTransducer.sat3D N ≤ N :=
    Nat.div_mul_le_self N (NFrameBoundaryTransducer.sat3D N)
  have hm : NFrameBoundaryTransducer.sat3M N ≤ N :=
    Nat.div_le_self N (NFrameBoundaryTransducer.sat3D N)
  omega

/-! The natural next move is to repeat the charge over many scales.  Mere
pointwise scale bounds do not justify summing, however: every scale may use
the same geometric resource.  The following finite countermodel is the
arithmetic core of the repository's “flat bus” obstruction. -/

/-- **Flat-bus amplification obstruction.**  With at least two scales and a
positive shared resource of size `E`, there is a scale-charge profile in
which every individual scale is bounded by `E`, yet the formal sum of the
scale charges exceeds `E`.  Consequently an additive amplification theorem
must prove freshness/disjointness; pointwise SAT curvature bounds alone are
insufficient. -/
theorem pointwiseScaleCharge_not_additive (K E : Nat)
    (hK : 2 ≤ K) (hE : 1 ≤ E) :
    ∃ scaleCharge : Nat → Nat,
      (∀ j, j < K → scaleCharge j ≤ E) ∧
      E < ∑ j ∈ Finset.range K, scaleCharge j := by
  refine ⟨fun _ => E, ?_, ?_⟩
  · intro j hj
    exact Nat.le_refl E
  · rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    exact lt_mul_of_one_lt_left hE (by omega)

/-! The horizontal audit has a stronger positive conclusion.  At one binary
branch, the circuit partition isolates the only mechanism that can defeat
doubling: gates depending on both input blocks below the legitimate mixer. -/

/-- **Exact horizontal escape condition.**  Under the proved cross-branch
partition/restriction hypotheses, failure of the desired doubling inequality
forces the cancellation-sharing population to exceed the fresh mixer budget.
Thus any successful SAT amplification proof may focus on the single semantic
inequality `CE_share ≤ fresh`; every counterexample must violate it. -/
theorem failure_of_branch_doubling_forces_share_gt_fresh
    (CE CE_L CE_R CE_mix CE_share CEF fresh : Nat)
    (hpartition : CE_L + CE_R + CE_mix + CE_share ≤ CE)
    (hL : CEF ≤ CE_L + CE_share) (hR : CEF ≤ CE_R + CE_share)
    (hmix : fresh ≤ CE_mix) (hfail : CE < 2 * CEF) :
    fresh < CE_share := by
  by_contra hnot
  have habsorb : CE_share ≤ fresh := by omega
  have hdoubling := NFrameCrossBranch.share_absorbed_gives_doubling
    CE CE_L CE_R CE_mix CE_share CEF fresh hpartition hL hR hmix habsorb
  omega

/-- **Nonlinear mass-production certificate.**  Under the concrete gate
partition and restriction bounds, failure of the full fresh-cost direct sum
can occur only if the mixed gates yield more usable pure-left plus pure-right
content than there are mixed gates.  Linear sharing cannot realize this
inequality (rank-nullity), so every escaping circuit must use genuinely
nonlinear cross-branch mass production. -/
theorem failure_of_fresh_directSum_forces_nonlinear_net_saving
    (CE CE_L CE_R CE_mix CE_share shareLeft shareRight CEF fresh : Nat)
    (hpartition : CE_L + CE_R + CE_mix + CE_share ≤ CE)
    (hmix : fresh ≤ CE_mix)
    (hPL : CEF ≤ CE_L + shareLeft)
    (hPR : CEF ≤ CE_R + shareRight)
    (hfail : CE < 2 * CEF + fresh) :
    CE_share < shareLeft + shareRight := by
  by_contra hnot
  have hnosaving : shareLeft + shareRight ≤ CE_share := by omega
  have hdirect := NFrameNonlinearShare.direct_sum_from_no_net_saving
    CE CE_L CE_R CE_mix CE_share shareLeft shareRight CEF fresh
    hpartition hmix hPL hPR hnosaving
  omega

/-- The complete signature of a cross-branch computation that escapes the
geometric direct-sum recurrence. -/
structure NonlinearThermodynamicEscape
    (CE_share shareLeft shareRight fresh : Nat) : Prop where
  share_overruns_fresh : fresh < CE_share
  nonlinear_net_saving : CE_share < shareLeft + shareRight

/-- **Combined escape theorem.**  If the same concrete branch defeats plain
doubling, then it also defeats the stronger fresh-cost recurrence.  Hence its
mixed gates must both overrun fresh geometry and mass-produce more usable
one-sided computation than their population.  This is the exact conjunction
that a SAT-specific invariant must rule out. -/
theorem branch_doubling_failure_has_nonlinearThermodynamicEscape
    (CE CE_L CE_R CE_mix CE_share shareLeft shareRight CEF fresh : Nat)
    (hpartition : CE_L + CE_R + CE_mix + CE_share ≤ CE)
    (hL : CEF ≤ CE_L + CE_share) (hR : CEF ≤ CE_R + CE_share)
    (hPL : CEF ≤ CE_L + shareLeft)
    (hPR : CEF ≤ CE_R + shareRight)
    (hmix : fresh ≤ CE_mix) (hfail : CE < 2 * CEF) :
    NonlinearThermodynamicEscape CE_share shareLeft shareRight fresh := by
  refine ⟨?_, ?_⟩
  · exact failure_of_branch_doubling_forces_share_gt_fresh
      CE CE_L CE_R CE_mix CE_share CEF fresh
      hpartition hL hR hmix hfail
  · apply failure_of_fresh_directSum_forces_nonlinear_net_saving
      CE CE_L CE_R CE_mix CE_share shareLeft shareRight CEF fresh
      hpartition hmix hPL hPR
    omega

/-- **Escape exclusion closes the branch.**  Under the same concrete
partition and restriction hypotheses, proving that the combined nonlinear
thermodynamic escape signature is absent is sufficient for the exact doubling
bound.  This packages the remaining mathematical target as one negated
semantic structure. -/
theorem branch_doubling_of_no_nonlinearThermodynamicEscape
    (CE CE_L CE_R CE_mix CE_share shareLeft shareRight CEF fresh : Nat)
    (hpartition : CE_L + CE_R + CE_mix + CE_share ≤ CE)
    (hL : CEF ≤ CE_L + CE_share) (hR : CEF ≤ CE_R + CE_share)
    (hPL : CEF ≤ CE_L + shareLeft)
    (hPR : CEF ≤ CE_R + shareRight)
    (hmix : fresh ≤ CE_mix)
    (hno : ¬ NonlinearThermodynamicEscape CE_share shareLeft shareRight fresh) :
    2 * CEF ≤ CE := by
  by_contra hfail
  apply hno
  apply branch_doubling_failure_has_nonlinearThermodynamicEscape
    CE CE_L CE_R CE_mix CE_share shareLeft shareRight CEF fresh
    hpartition hL hR hPL hPR hmix
  omega

/-- **Unconditional horizontal frontier.**  Every branch satisfying the
concrete partition and restriction accounting either pays exact doubling or
exhibits the complete nonlinear thermodynamic escape signature.  This is a
true dichotomy, not an extra semantic assumption. -/
theorem branch_doubling_or_nonlinearThermodynamicEscape
    (CE CE_L CE_R CE_mix CE_share shareLeft shareRight CEF fresh : Nat)
    (hpartition : CE_L + CE_R + CE_mix + CE_share ≤ CE)
    (hL : CEF ≤ CE_L + CE_share) (hR : CEF ≤ CE_R + CE_share)
    (hPL : CEF ≤ CE_L + shareLeft)
    (hPR : CEF ≤ CE_R + shareRight)
    (hmix : fresh ≤ CE_mix) :
    2 * CEF ≤ CE ∨
      NonlinearThermodynamicEscape CE_share shareLeft shareRight fresh := by
  rcases le_or_gt (2 * CEF) CE with hpay | hfail
  · exact Or.inl hpay
  · exact Or.inr
      (branch_doubling_failure_has_nonlinearThermodynamicEscape
        CE CE_L CE_R CE_mix CE_share shareLeft shareRight CEF fresh
        hpartition hL hR hPL hPR hmix hfail)

/-- **The escape signature is necessary, not sufficient.**  There are
numerical branch parameters satisfying all partition/restriction hypotheses
and the full nonlinear thermodynamic escape signature while exact doubling
still holds.  Hence the signature correctly identifies every failure, but it
must not be read as a characterization of failure without additional
SAT-machine semantics. -/
theorem nonlinearThermodynamicEscape_does_not_force_doubling_failure :
    ∃ (CE CE_L CE_R CE_mix CE_share shareLeft shareRight CEF fresh : Nat),
      CE_L + CE_R + CE_mix + CE_share ≤ CE ∧
      CEF ≤ CE_L + CE_share ∧ CEF ≤ CE_R + CE_share ∧
      CEF ≤ CE_L + shareLeft ∧ CEF ≤ CE_R + shareRight ∧
      fresh ≤ CE_mix ∧
      NonlinearThermodynamicEscape CE_share shareLeft shareRight fresh ∧
      2 * CEF ≤ CE := by
  exact ⟨20, 4, 4, 4, 8, 5, 5, 6, 3,
    by omega, by omega, by omega, by omega, by omega, by omega,
    ⟨by omega, by omega⟩, by omega⟩

/-- **Finite synthesis cannot certify the all-scale freshness theorem.**  For
every tested cutoff there is a scale predicate that holds at every checked
scale and fails immediately afterwards.  Consequently the repository's exact
small-circuit searches are legitimate evidence, but no finite cutoff can
replace the uniform nonlinear restriction-profile theorem needed by the
amplification. -/
theorem finiteFreshnessChecks_do_not_imply_uniformFreshness (cutoff : Nat) :
    ∃ FreshAtScale : Nat → Prop,
      (∀ k, k ≤ cutoff → FreshAtScale k) ∧
      ¬ (∀ k, FreshAtScale k) := by
  refine ⟨fun k => k ≤ cutoff, ?_, ?_⟩
  · intro k hk
    exact hk
  · intro hall
    have := hall (cutoff + 1)
    omega

/-- **Aggregate Boolean restriction-profile capacity.**  If all `r`
independent binary restriction coordinates inject into the Boolean profiles
exposed by `g` mixed gates, then at least `r` mixed gates are necessary.

Unlike the per-distinction firewall, this theorem counts the whole family at
once: the source contains `2^r` profiles while the target contains only
`2^g`.  The remaining SAT-specific task is to construct this injection from
the semantics of the recursive restriction family. -/
theorem booleanRestrictionProfile_capacity {r g : Nat}
    (profile : (Fin r → Bool) → (Fin g → Bool))
    (hprofile : Function.Injective profile) :
    r ≤ g := by
  have hcard : Fintype.card (Fin r → Bool) ≤ Fintype.card (Fin g → Bool) :=
    Fintype.card_le_of_injective profile hprofile
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at hcard
  by_contra hrg
  have hgr : g < r := by omega
  have hp : 2 ^ g < 2 ^ r := Nat.pow_lt_pow_right (by omega) hgr
  omega

/-- Reconstruction is the semantic form of aggregate profile injectivity.  If
one can recover every `r`-bit restriction witness from the `g` mixed-gate
outputs, then those outputs must contain at least `r` Boolean coordinates. -/
theorem booleanRestrictionProfile_capacity_of_reconstruction {r g : Nat}
    (encode : (Fin r → Bool) → (Fin g → Bool))
    (decode : (Fin g → Bool) → (Fin r → Bool))
    (hreconstruct : ∀ witness, decode (encode witness) = witness) :
    r ≤ g := by
  apply booleanRestrictionProfile_capacity encode
  intro x y hxy
  calc
    x = decode (encode x) := (hreconstruct x).symm
    _ = decode (encode y) := by rw [hxy]
    _ = y := hreconstruct y

/-- Two Boolean observer banks have only the sum of their coordinate
capacities.  Thus an aggregate family of `r` independent witnesses cannot be
reconstructed by `g` mixed coordinates together with `p` pure coordinates
unless `r ≤ g + p`. -/
theorem pairedBooleanRestrictionProfile_capacity {r g p : Nat}
    (profile : (Fin r → Bool) → (Fin g → Bool) × (Fin p → Bool))
    (hprofile : Function.Injective profile) :
    r ≤ g + p := by
  have hcard : Fintype.card (Fin r → Bool) ≤
      Fintype.card ((Fin g → Bool) × (Fin p → Bool)) :=
    Fintype.card_le_of_injective profile hprofile
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    Fintype.card_prod] at hcard
  have hpow : 2 ^ r ≤ 2 ^ (g + p) := by
    simpa [pow_add] using hcard
  by_contra hrgp
  have hlt : g + p < r := by omega
  have hp : 2 ^ (g + p) < 2 ^ r := Nat.pow_lt_pow_right (by omega) hlt
  omega

/-- **SAT aggregate restriction-profile bridge.**  The repository's concrete
block contexts generate `2^k` distinct SAT subfunctions.  Consequently, if
each such subfunction is reconstructed from `g` mixed-gate bits and `p`
pure-side bits, their joint restriction profile must satisfy `k ≤ g + p`.

This is the aggregate form of `firewall_covers_distinction` specialized to
the actual recursive SAT family.  It does not assume that the mixed bank is
injective by itself; proving that the pure bank cannot absorb the required
coordinates is the remaining nonlinear sharing problem. -/
theorem sat3AggregateRestrictionProfile_capacity
    (N : Nat) (hv : 1 ≤ NFrameBoundaryTransducer.sat3V N)
    {k g p : Nat}
    (hk : k + 1 ≤ NFrameBoundaryTransducer.sat3M N)
    (hkv : k ≤ NFrameBoundaryTransducer.sat3V N)
    (c : Fin (NFrameBoundaryTransducer.sat3M N))
    (mixed : (Fin k → Bool) → (Fin g → Bool))
    (pure : (Fin k → Bool) → (Fin p → Bool))
    (reconstruct : (Fin g → Bool) → (Fin p → Bool) →
      ((Fin N → Bool) → Bool))
    (hrec : ∀ b uu,
      NFrameBoundaryTransducer.sat3Family N
          (NFrameBoundaryTransducer.sat3Patch N c
            (NFrameBoundaryTransducer.sat3Context N c hk b) uu)
        = reconstruct (mixed b) (pure b) uu) :
    k ≤ g + p := by
  apply pairedBooleanRestrictionProfile_capacity (fun b => (mixed b, pure b))
  intro b b' hprofiles
  by_contra hne
  obtain ⟨uu, huu⟩ :=
    NFrameBoundaryTransducer.sat3_block_subfunctions_distinct
      N hv hk hkv c b b' hne
  have hmixed : mixed b = mixed b' := congrArg Prod.fst hprofiles
  have hpure : pure b = pure b' := congrArg Prod.snd hprofiles
  apply huu
  rw [hrec b uu, hrec b' uu, hmixed, hpure]

/-- A common Boolean bank is charged only once when two independent witness
families share it.  Injecting `rL + rR` independent coordinates into one
`g`-bit mixed bank and two pure banks of sizes `pL`, `pR` forces the joint
capacity inequality `rL + rR ≤ g + pL + pR`. -/
theorem siblingBooleanRestrictionProfile_capacity
    {rL rR g pL pR : Nat}
    (profile : ((Fin rL → Bool) × (Fin rR → Bool)) →
      ((Fin g → Bool) × (Fin pL → Bool)) × (Fin pR → Bool))
    (hprofile : Function.Injective profile) :
    rL + rR ≤ g + pL + pR := by
  have hcard :
      Fintype.card ((Fin rL → Bool) × (Fin rR → Bool)) ≤
        Fintype.card (((Fin g → Bool) × (Fin pL → Bool)) ×
          (Fin pR → Bool)) :=
    Fintype.card_le_of_injective profile hprofile
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    Fintype.card_prod] at hcard
  have hpow : 2 ^ (rL + rR) ≤ 2 ^ (g + pL + pR) := by
    simpa [pow_add] using hcard
  by_contra hcap
  have hlt : g + pL + pR < rL + rR := by omega
  have hp : 2 ^ (g + pL + pR) < 2 ^ (rL + rR) :=
    Nat.pow_lt_pow_right (by omega) hlt
  omega

/-- **Two-sibling SAT allocation law.**  Let two independently varying SAT
block-context families share one mixed-gate profile while retaining separate
pure profiles.  If each sibling subfunction is reconstructed from the common
mixed profile and its own pure profile, then

`2 * k ≤ g + pL + pR`.

The mixed bank is counted once, so this is the desired horizontal aggregate
accounting statement.  The remaining direct-sum issue is quantitative: relate
`pL` and `pR` to the actual pure gate classes strongly enough that this bound
forces the mixed/fresh cost. -/
theorem sat3SiblingRestrictionProfile_capacity
    (N : Nat) (hv : 1 ≤ NFrameBoundaryTransducer.sat3V N)
    {k g pL pR : Nat}
    (hk : k + 1 ≤ NFrameBoundaryTransducer.sat3M N)
    (hkv : k ≤ NFrameBoundaryTransducer.sat3V N)
    (cL cR : Fin (NFrameBoundaryTransducer.sat3M N))
    (mixed : ((Fin k → Bool) × (Fin k → Bool)) → (Fin g → Bool))
    (pureL : (Fin k → Bool) → (Fin pL → Bool))
    (pureR : (Fin k → Bool) → (Fin pR → Bool))
    (reconstructL : (Fin g → Bool) → (Fin pL → Bool) →
      ((Fin N → Bool) → Bool))
    (reconstructR : (Fin g → Bool) → (Fin pR → Bool) →
      ((Fin N → Bool) → Bool))
    (hrecL : ∀ bL bR uu,
      NFrameBoundaryTransducer.sat3Family N
          (NFrameBoundaryTransducer.sat3Patch N cL
            (NFrameBoundaryTransducer.sat3Context N cL hk bL) uu)
        = reconstructL (mixed (bL, bR)) (pureL bL) uu)
    (hrecR : ∀ bL bR uu,
      NFrameBoundaryTransducer.sat3Family N
          (NFrameBoundaryTransducer.sat3Patch N cR
            (NFrameBoundaryTransducer.sat3Context N cR hk bR) uu)
        = reconstructR (mixed (bL, bR)) (pureR bR) uu) :
    2 * k ≤ g + pL + pR := by
  have hjoint : Function.Injective
      (fun b : (Fin k → Bool) × (Fin k → Bool) =>
        ((mixed b, pureL b.1), pureR b.2)) := by
    intro b b' hprofiles
    have hmixed : mixed b = mixed b' := congrArg (fun z => z.1.1) hprofiles
    have hpureL : pureL b.1 = pureL b'.1 :=
      congrArg (fun z => z.1.2) hprofiles
    have hpureR : pureR b.2 = pureR b'.2 := congrArg Prod.snd hprofiles
    have hbL : b.1 = b'.1 := by
      by_contra hne
      obtain ⟨uu, huu⟩ :=
        NFrameBoundaryTransducer.sat3_block_subfunctions_distinct
          N hv hk hkv cL b.1 b'.1 hne
      apply huu
      rw [hrecL b.1 b.2 uu, hrecL b'.1 b'.2 uu, hmixed, hpureL]
    have hbR : b.2 = b'.2 := by
      by_contra hne
      obtain ⟨uu, huu⟩ :=
        NFrameBoundaryTransducer.sat3_block_subfunctions_distinct
          N hv hk hkv cR b.2 b'.2 hne
      apply huu
      rw [hrecR b.1 b.2 uu, hrecR b'.1 b'.2 uu, hmixed, hpureR]
    exact Prod.ext hbL hbR
  have hcap := siblingBooleanRestrictionProfile_capacity
    (fun b : (Fin k → Bool) × (Fin k → Bool) =>
      ((mixed b, pureL b.1), pureR b.2)) hjoint
  simpa [two_mul] using hcap

/-- **Cone-excess cash-out of sibling profile capacity.**  When the two pure
profile banks are realized by the pure-left and pure-right gate classes, and
the common profile by the share-gate class, the four-way gate partition turns
the joint capacity inequality directly into `2*k + fresh ≤ CE`. -/
theorem siblingProfileCapacity_cashout
    (k CE CE_L CE_R CE_mix CE_share fresh : Nat)
    (hprofile : 2 * k ≤ CE_share + CE_L + CE_R)
    (hpartition : CE_L + CE_R + CE_mix + CE_share ≤ CE)
    (hmix : fresh ≤ CE_mix) :
    2 * k + fresh ≤ CE := by
  omega

/-- **Concrete SAT sibling-profile cone-excess bound.**  Reconstruction of
the two independent recursive SAT restriction families from the actual
four-way gate banks yields the unconditional single-scale lower bound

`2*k + fresh ≤ CE`.

This is a genuine SAT-semantic cash-out of aggregate profile capacity.  Its
current strength is logarithmic in the `2^k` subfunction family; identifying
`k` with the full child cone-excess would be the stronger nonlinear direct-sum
claim and is deliberately not assumed here. -/
theorem sat3SiblingRestrictionProfile_coneExcess
    (N : Nat) (hv : 1 ≤ NFrameBoundaryTransducer.sat3V N)
    {k CE CE_L CE_R CE_mix CE_share fresh : Nat}
    (hk : k + 1 ≤ NFrameBoundaryTransducer.sat3M N)
    (hkv : k ≤ NFrameBoundaryTransducer.sat3V N)
    (cL cR : Fin (NFrameBoundaryTransducer.sat3M N))
    (mixed : ((Fin k → Bool) × (Fin k → Bool)) →
      (Fin CE_share → Bool))
    (pureL : (Fin k → Bool) → (Fin CE_L → Bool))
    (pureR : (Fin k → Bool) → (Fin CE_R → Bool))
    (reconstructL : (Fin CE_share → Bool) → (Fin CE_L → Bool) →
      ((Fin N → Bool) → Bool))
    (reconstructR : (Fin CE_share → Bool) → (Fin CE_R → Bool) →
      ((Fin N → Bool) → Bool))
    (hrecL : ∀ bL bR uu,
      NFrameBoundaryTransducer.sat3Family N
          (NFrameBoundaryTransducer.sat3Patch N cL
            (NFrameBoundaryTransducer.sat3Context N cL hk bL) uu)
        = reconstructL (mixed (bL, bR)) (pureL bL) uu)
    (hrecR : ∀ bL bR uu,
      NFrameBoundaryTransducer.sat3Family N
          (NFrameBoundaryTransducer.sat3Patch N cR
            (NFrameBoundaryTransducer.sat3Context N cR hk bR) uu)
        = reconstructR (mixed (bL, bR)) (pureR bR) uu)
    (hpartition : CE_L + CE_R + CE_mix + CE_share ≤ CE)
    (hmix : fresh ≤ CE_mix) :
    2 * k + fresh ≤ CE := by
  have hprofile : 2 * k ≤ CE_share + CE_L + CE_R :=
    sat3SiblingRestrictionProfile_capacity N hv hk hkv cL cR
      mixed pureL pureR reconstructL reconstructR hrecL hrecR
  exact siblingProfileCapacity_cashout k CE CE_L CE_R CE_mix CE_share fresh
    hprofile hpartition hmix

/-- **Profile dimension alone does not imply child-cost doubling.**  At every
profile dimension `k`, there are gate-ledger parameters satisfying the exact
sibling profile capacity, the four-way partition, and its cone-excess cash-out,
while doubling fails for the slightly larger child cost `CEF = k + 1`.

This formally prevents the logarithm of the SAT subfunction count from being
silently identified with the circuit cone-excess of a child. -/
theorem siblingProfileCashout_does_not_force_childDoubling (k : Nat) :
    ∃ (CE CE_L CE_R CE_mix CE_share fresh CEF : Nat),
      2 * k ≤ CE_share + CE_L + CE_R ∧
      CE_L + CE_R + CE_mix + CE_share ≤ CE ∧
      fresh ≤ CE_mix ∧
      2 * k + fresh ≤ CE ∧
      CE < 2 * CEF := by
  refine ⟨2 * k, k, k, 0, 0, 0, k + 1, ?_⟩
  omega

/-- The missing quantitative bridge, isolated without circuit syntax: the
profile cash-out yields child doubling as soon as the child cone-excess is no
larger than the independent SAT profile dimension.  The preceding countermodel
shows that this comparison is essential rather than arithmetic bookkeeping. -/
theorem childDoubling_of_coneExcess_le_profileDimension
    (k CE fresh CEF : Nat)
    (hcashout : 2 * k + fresh ≤ CE)
    (hchild : CEF ≤ k) :
    2 * CEF ≤ CE := by
  omega

/-- **Exact profile-versus-child frontier.**  Once the aggregate SAT profile
cash-out `2*k + fresh ≤ CE` is known, either the desired child-cost doubling
already holds or the child cone-excess strictly exceeds the independent
restriction-profile dimension.  Hence all remaining nonlinear difficulty is
localized in the strict gap `k < CEF`. -/
theorem childDoubling_or_profileIncompressibilityGap
    (k CE fresh CEF : Nat)
    (hcashout : 2 * k + fresh ≤ CE) :
    2 * CEF ≤ CE ∨ k < CEF := by
  by_cases hchild : CEF ≤ k
  · exact Or.inl
      (childDoubling_of_coneExcess_le_profileDimension
        k CE fresh CEF hcashout hchild)
  · exact Or.inr (by omega)

/-- Even adding the usual lower-bound polarity `k ≤ CEF` does not remove the
gap: for every `k`, the profile cash-out and `k ≤ CEF` coexist with failed
doubling at `CEF = k+1`.  A theorem closing the route must control the strict
excess of circuit cost over profile dimension, not merely prove another lower
bound on circuit cost. -/
theorem profileLowerBound_does_not_close_childDoubling (k : Nat) :
    ∃ (CE fresh CEF : Nat),
      2 * k + fresh ≤ CE ∧ k ≤ CEF ∧ CE < 2 * CEF := by
  exact ⟨2 * k, 0, k + 1, by omega⟩

/-- **The profile-incompressibility gap is the exact recurrence deficit.**
When `k ≤ CEF`, the SAT profile cash-out can be rewritten as

`2*CEF + fresh ≤ CE + 2*(CEF-k)`.

Thus no additional loss is hidden in the conversion from aggregate profiles
to child cost: the entire deficit is twice the uncaptured child complexity. -/
theorem childRecurrence_deficit_eq_profileGap
    (k CE fresh CEF : Nat)
    (hcashout : 2 * k + fresh ≤ CE)
    (hprofileLower : k ≤ CEF) :
    2 * CEF + fresh ≤ CE + 2 * (CEF - k) := by
  omega

/-- If the fresh geometric budget pays twice the uncaptured profile gap, the
desired child-cost doubling survives.  This is the quantitative thermodynamic
absorption condition exposed by the aggregate SAT profile theorem. -/
theorem profileGap_absorbed_by_fresh_gives_childDoubling
    (k CE fresh CEF : Nat)
    (hcashout : 2 * k + fresh ≤ CE)
    (hprofileLower : k ≤ CEF)
    (habsorb : 2 * (CEF - k) ≤ fresh) :
    2 * CEF ≤ CE := by
  have hdeficit := childRecurrence_deficit_eq_profileGap
    k CE fresh CEF hcashout hprofileLower
  omega

/-- Failure of child doubling forces the uncaptured profile gap to exceed
half of the fresh budget.  This is the converse escape certificate: a circuit
can evade growth only by producing child complexity not represented in the
SAT restriction profiles faster than fresh geometry is created. -/
theorem childDoubling_failure_forces_profileGap_overrun
    (k CE fresh CEF : Nat)
    (hcashout : 2 * k + fresh ≤ CE)
    (hprofileLower : k ≤ CEF)
    (hfail : CE < 2 * CEF) :
    fresh < 2 * (CEF - k) := by
  by_contra h
  have habsorb : 2 * (CEF - k) ≤ fresh := by omega
  have := profileGap_absorbed_by_fresh_gives_childDoubling
    k CE fresh CEF hcashout hprofileLower habsorb
  omega

/-- **Multiscale profile-gap cash-out.**  If fresh geometry absorbs twice the
uncaptured child complexity at every scale, every scale pays exact child-cost
doubling.  The fresh term is consumed by that absorption, so this theorem does
not claim the stronger doubling-plus-fresh recurrence. -/
theorem profileGapAbsorption_gives_allScalesDoubling
    (c : Nat) (T profile : Nat → Nat)
    (hprofileLower : ∀ k, profile k ≤ T k)
    (hcashout : ∀ k,
      2 * profile k + c * 2 ^ (k + 1) ≤ T (k + 1))
    (habsorb : ∀ k,
      2 * (T k - profile k) ≤ c * 2 ^ (k + 1)) :
    ∀ k, 2 * T k ≤ T (k + 1) := by
  intro k
  exact profileGap_absorbed_by_fresh_gives_childDoubling
    (profile k) (T (k + 1)) (c * 2 ^ (k + 1)) (T k)
    (hcashout k) (hprofileLower k) (habsorb k)

/-- Exact doubling unrolls to the base-cost bound `T 0 * 2^b ≤ T b`.
This is linear in the scale size `2^b`; retaining an unspent fresh margin is
still necessary for the stronger `N log N` amplification. -/
theorem allScalesDoubling_amplifies_base (T : Nat → Nat)
    (hdouble : ∀ k, 2 * T k ≤ T (k + 1)) :
    ∀ b, T 0 * 2 ^ b ≤ T b := by
  intro b
  induction b with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      have hmul : 2 * (T 0 * 2 ^ k) ≤ 2 * T k :=
        Nat.mul_le_mul_left 2 ih
      calc
        T 0 * (2 ^ k * 2) = 2 * (T 0 * 2 ^ k) := by ring
        _ ≤ 2 * T k := hmul
        _ ≤ T (k + 1) := hdouble k

/-- **All-scale frontier.**  Under the aggregate SAT profile cash-out, either
every recursive scale pays child-cost doubling, or a concrete scale exhibits
fresh-budget overrun by the uncaptured nonlinear profile gap. -/
theorem allScalesDoubling_or_exists_profileGapOverrun
    (c : Nat) (T profile : Nat → Nat)
    (hprofileLower : ∀ k, profile k ≤ T k)
    (hcashout : ∀ k,
      2 * profile k + c * 2 ^ (k + 1) ≤ T (k + 1)) :
    (∀ k, 2 * T k ≤ T (k + 1)) ∨
      ∃ k, c * 2 ^ (k + 1) < 2 * (T k - profile k) := by
  by_cases hall : ∀ k, 2 * T k ≤ T (k + 1)
  · exact Or.inl hall
  · right
    push_neg at hall
    obtain ⟨k, hk⟩ := hall
    refine ⟨k, ?_⟩
    exact childDoubling_failure_forces_profileGap_overrun
      (profile k) (T (k + 1)) (c * 2 ^ (k + 1)) (T k)
      (hcashout k) (hprofileLower k) hk

/-- **Leftover fresh margin restores the full amplifier.**  Here `freshRate`
is the total geometric budget per scale and `marginRate` is the portion left
after paying twice the uncaptured child/profile gap.  The leftover margin
survives in the recurrence and yields `marginRate * N log N`. -/
theorem profileGapMargin_amplifies
    (freshRate marginRate : Nat) (T profile : Nat → Nat)
    (hprofileLower : ∀ k, profile k ≤ T k)
    (hcashout : ∀ k,
      2 * profile k + freshRate * 2 ^ (k + 1) ≤ T (k + 1))
    (hmargin : ∀ k,
      2 * (T k - profile k) + marginRate * 2 ^ (k + 1) ≤
        freshRate * 2 ^ (k + 1)) :
    ∀ b, marginRate * (b * 2 ^ b) ≤ T b := by
  apply NFrameConeAmplify.coneExcess_amplify marginRate T
  intro k
  have hgap := hprofileLower k
  have hcash := hcashout k
  have hm := hmargin k
  omega

/-- The margin condition is also the exact local frontier.  If the desired
doubling-plus-margin recurrence fails at a scale, then the total fresh budget
is strictly smaller than the profile-gap payment plus that margin. -/
theorem recurrenceMargin_failure_forces_profileGapBudgetOverrun
    (profile child next fresh margin : Nat)
    (hprofileLower : profile ≤ child)
    (hcashout : 2 * profile + fresh ≤ next)
    (hfail : next < 2 * child + margin) :
    fresh < 2 * (child - profile) + margin := by
  omega

/-- **All-scale margin frontier.**  Either the full margin recurrence holds at
every level, or there is a concrete scale where fresh geometry cannot pay
both the uncaptured nonlinear profile gap and the requested amplification
margin. -/
theorem allScalesMarginRecurrence_or_exists_budgetOverrun
    (freshRate marginRate : Nat) (T profile : Nat → Nat)
    (hprofileLower : ∀ k, profile k ≤ T k)
    (hcashout : ∀ k,
      2 * profile k + freshRate * 2 ^ (k + 1) ≤ T (k + 1)) :
    (∀ k, 2 * T k + marginRate * 2 ^ (k + 1) ≤ T (k + 1)) ∨
      ∃ k, freshRate * 2 ^ (k + 1) <
        2 * (T k - profile k) + marginRate * 2 ^ (k + 1) := by
  by_cases hall : ∀ k,
      2 * T k + marginRate * 2 ^ (k + 1) ≤ T (k + 1)
  · exact Or.inl hall
  · right
    push_neg at hall
    obtain ⟨k, hk⟩ := hall
    exact ⟨k, recurrenceMargin_failure_forces_profileGapBudgetOverrun
      (profile k) (T k) (T (k + 1))
      (freshRate * 2 ^ (k + 1)) (marginRate * 2 ^ (k + 1))
      (hprofileLower k) (hcashout k) hk⟩

/-- **Hybrid nonlinear deficit bound.**  The traditional gate partition says
the recurrence deficit is at most `CE_share`; the aggregate SAT profile law
says it is at most `2*(CEF-profile)`.  Therefore the actual certified deficit
is bounded by their minimum. -/
theorem childRecurrence_deficit_le_min_share_profileGap
    (profile CE fresh CEF CE_share : Nat)
    (hprofileLower : profile ≤ CEF)
    (hprofileCashout : 2 * profile + fresh ≤ CE)
    (hshareDeficit : 2 * CEF + fresh ≤ CE + CE_share) :
    2 * CEF + fresh ≤ CE + min CE_share (2 * (CEF - profile)) := by
  have hgap := childRecurrence_deficit_eq_profileGap
    profile CE fresh CEF hprofileCashout hprofileLower
  by_cases hle : CE_share ≤ 2 * (CEF - profile)
  · rw [min_eq_left hle]
    exact hshareDeficit
  · rw [min_eq_right (by omega)]
    exact hgap

/-- A positive margin survives whenever fresh geometry pays the smaller of
the sharing-gate deficit and twice the uncaptured profile gap.  This hybrid
criterion can close a scale even when neither global route is known sharply. -/
theorem hybridDeficitMargin_gives_childRecurrence
    (profile CE fresh CEF CE_share margin : Nat)
    (hprofileLower : profile ≤ CEF)
    (hprofileCashout : 2 * profile + fresh ≤ CE)
    (hshareDeficit : 2 * CEF + fresh ≤ CE + CE_share)
    (habsorb : min CE_share (2 * (CEF - profile)) + margin ≤ fresh) :
    2 * CEF + margin ≤ CE := by
  have hmin := childRecurrence_deficit_le_min_share_profileGap
    profile CE fresh CEF CE_share hprofileLower hprofileCashout hshareDeficit
  omega

/-- **Hybrid multiscale amplifier.**  At every scale it is enough for fresh
geometry to absorb whichever certified deficit is smaller—share-gate count or
uncaptured SAT profile complexity—while leaving a positive linear margin. -/
theorem hybridShareProfileMargin_amplifies
    (freshRate marginRate : Nat)
    (T profile CE_share : Nat → Nat)
    (hprofileLower : ∀ k, profile k ≤ T k)
    (hprofileCashout : ∀ k,
      2 * profile k + freshRate * 2 ^ (k + 1) ≤ T (k + 1))
    (hshareDeficit : ∀ k,
      2 * T k + freshRate * 2 ^ (k + 1) ≤ T (k + 1) + CE_share k)
    (habsorb : ∀ k,
      min (CE_share k) (2 * (T k - profile k)) +
          marginRate * 2 ^ (k + 1) ≤ freshRate * 2 ^ (k + 1)) :
    ∀ b, marginRate * (b * 2 ^ b) ≤ T b := by
  apply NFrameConeAmplify.coneExcess_amplify marginRate T
  intro k
  exact hybridDeficitMargin_gives_childRecurrence
    (profile k) (T (k + 1)) (freshRate * 2 ^ (k + 1))
    (T k) (CE_share k) (marginRate * 2 ^ (k + 1))
    (hprofileLower k) (hprofileCashout k) (hshareDeficit k) (habsorb k)

/-- **Exact hybrid escape signature.**  If the target recurrence fails, then
fresh geometry is insufficient to pay even the smaller certified deficit
(share-gate count versus twice the uncaptured SAT profile gap) together with
the requested margin. -/
theorem childRecurrence_failure_forces_hybridBudgetOverrun
    (profile CE fresh CEF CE_share margin : Nat)
    (hprofileLower : profile ≤ CEF)
    (hprofileCashout : 2 * profile + fresh ≤ CE)
    (hshareDeficit : 2 * CEF + fresh ≤ CE + CE_share)
    (hfail : CE < 2 * CEF + margin) :
    fresh < min CE_share (2 * (CEF - profile)) + margin := by
  by_contra h
  have habsorb : min CE_share (2 * (CEF - profile)) + margin ≤ fresh := by
    omega
  have := hybridDeficitMargin_gives_childRecurrence
    profile CE fresh CEF CE_share margin hprofileLower
    hprofileCashout hshareDeficit habsorb
  omega

/-- **Unconditional hybrid local frontier.**  Every scale either pays the
doubling-plus-margin recurrence or exhibits the exact hybrid budget overrun.
There is no third accounting case. -/
theorem childRecurrence_or_hybridBudgetOverrun
    (profile CE fresh CEF CE_share margin : Nat)
    (hprofileLower : profile ≤ CEF)
    (hprofileCashout : 2 * profile + fresh ≤ CE)
    (hshareDeficit : 2 * CEF + fresh ≤ CE + CE_share) :
    2 * CEF + margin ≤ CE ∨
      fresh < min CE_share (2 * (CEF - profile)) + margin := by
  by_cases hrec : 2 * CEF + margin ≤ CE
  · exact Or.inl hrec
  · exact Or.inr (childRecurrence_failure_forces_hybridBudgetOverrun
      profile CE fresh CEF CE_share margin hprofileLower
      hprofileCashout hshareDeficit (by omega))

/-- **All-scale hybrid frontier.**  Either every recursive scale satisfies the
margin recurrence, or one concrete scale simultaneously defeats both the
sharing-count and aggregate-profile deficit certificates relative to fresh
geometry. -/
theorem allScalesHybridRecurrence_or_exists_budgetOverrun
    (freshRate marginRate : Nat)
    (T profile CE_share : Nat → Nat)
    (hprofileLower : ∀ k, profile k ≤ T k)
    (hprofileCashout : ∀ k,
      2 * profile k + freshRate * 2 ^ (k + 1) ≤ T (k + 1))
    (hshareDeficit : ∀ k,
      2 * T k + freshRate * 2 ^ (k + 1) ≤ T (k + 1) + CE_share k) :
    (∀ k, 2 * T k + marginRate * 2 ^ (k + 1) ≤ T (k + 1)) ∨
      ∃ k, freshRate * 2 ^ (k + 1) <
        min (CE_share k) (2 * (T k - profile k)) +
          marginRate * 2 ^ (k + 1) := by
  by_cases hall : ∀ k,
      2 * T k + marginRate * 2 ^ (k + 1) ≤ T (k + 1)
  · exact Or.inl hall
  · right
    push_neg at hall
    obtain ⟨k, hk⟩ := hall
    exact ⟨k, childRecurrence_failure_forces_hybridBudgetOverrun
      (profile k) (T (k + 1)) (freshRate * 2 ^ (k + 1))
      (T k) (CE_share k) (marginRate * 2 ^ (k + 1))
      (hprofileLower k) (hprofileCashout k) (hshareDeficit k) hk⟩

/-- The hybrid `min` overrun is exactly simultaneous failure of both
certificates: fresh geometry loses to the sharing count plus margin and also
to twice the uncaptured profile gap plus margin. -/
theorem hybridBudgetOverrun_iff_simultaneous
    (fresh CE_share profileGap margin : Nat) :
    fresh < min CE_share (2 * profileGap) + margin ↔
      fresh < CE_share + margin ∧
      fresh < 2 * profileGap + margin := by
  constructor
  · intro h
    constructor
    · exact lt_of_lt_of_le h (Nat.add_le_add_right (min_le_left _ _) _)
    · exact lt_of_lt_of_le h (Nat.add_le_add_right (min_le_right _ _) _)
  · rintro ⟨hshare, hgap⟩
    by_cases hle : CE_share ≤ 2 * profileGap
    · rw [min_eq_left hle]
      exact hshare
    · rw [min_eq_right (by omega)]
      exact hgap

/-- Named semantic form of the sole remaining local adversary. -/
structure SimultaneousHybridEscape
    (fresh CE_share profileGap margin : Nat) : Prop where
  share_overruns_fresh : fresh < CE_share + margin
  profileGap_overruns_fresh : fresh < 2 * profileGap + margin

/-- Failure of the desired recurrence produces the simultaneous sharing and
profile-gap escape signature, not merely one of its components. -/
theorem childRecurrence_failure_has_simultaneousHybridEscape
    (profile CE fresh CEF CE_share margin : Nat)
    (hprofileLower : profile ≤ CEF)
    (hprofileCashout : 2 * profile + fresh ≤ CE)
    (hshareDeficit : 2 * CEF + fresh ≤ CE + CE_share)
    (hfail : CE < 2 * CEF + margin) :
    SimultaneousHybridEscape fresh CE_share (CEF - profile) margin := by
  have hover := childRecurrence_failure_forces_hybridBudgetOverrun
    profile CE fresh CEF CE_share margin hprofileLower
    hprofileCashout hshareDeficit hfail
  obtain ⟨hshare, hgap⟩ := (hybridBudgetOverrun_iff_simultaneous
    fresh CE_share (CEF - profile) margin).mp hover
  exact ⟨hshare, hgap⟩

/-- Conversely, excluding the simultaneous escape signature forces the
doubling-plus-margin recurrence. -/
theorem childRecurrence_of_no_simultaneousHybridEscape
    (profile CE fresh CEF CE_share margin : Nat)
    (hprofileLower : profile ≤ CEF)
    (hprofileCashout : 2 * profile + fresh ≤ CE)
    (hshareDeficit : 2 * CEF + fresh ≤ CE + CE_share)
    (hno : ¬ SimultaneousHybridEscape
      fresh CE_share (CEF - profile) margin) :
    2 * CEF + margin ≤ CE := by
  by_contra hfail
  apply hno
  exact childRecurrence_failure_has_simultaneousHybridEscape
    profile CE fresh CEF CE_share margin hprofileLower
    hprofileCashout hshareDeficit (by omega)

/-- **Semantic prohibition cashes out to `N log N`.**  If the simultaneous
hybrid escape is excluded at every recursive scale, the local recurrence
holds everywhere and the existing amplifier supplies the full margin lower
bound. -/
theorem noSimultaneousHybridEscape_amplifies
    (freshRate marginRate : Nat)
    (T profile CE_share : Nat → Nat)
    (hprofileLower : ∀ k, profile k ≤ T k)
    (hprofileCashout : ∀ k,
      2 * profile k + freshRate * 2 ^ (k + 1) ≤ T (k + 1))
    (hshareDeficit : ∀ k,
      2 * T k + freshRate * 2 ^ (k + 1) ≤ T (k + 1) + CE_share k)
    (hno : ∀ k, ¬ SimultaneousHybridEscape
      (freshRate * 2 ^ (k + 1)) (CE_share k)
      (T k - profile k) (marginRate * 2 ^ (k + 1))) :
    ∀ b, marginRate * (b * 2 ^ b) ≤ T b := by
  apply NFrameConeAmplify.coneExcess_amplify marginRate T
  intro k
  exact childRecurrence_of_no_simultaneousHybridEscape
    (profile k) (T (k + 1)) (freshRate * 2 ^ (k + 1))
    (T k) (CE_share k) (marginRate * 2 ^ (k + 1))
    (hprofileLower k) (hprofileCashout k) (hshareDeficit k) (hno k)

/-- **The simultaneous escape is arithmetically consistent.**  Concrete
parameters satisfy both certified deficit bounds and the full simultaneous
escape signature while the target recurrence fails.  Therefore generic
ledger arithmetic cannot exclude the adversary; a SAT-specific structural
theorem is indispensable. -/
theorem simultaneousHybridEscape_is_arithmetically_consistent :
    ∃ (profile CE fresh CEF CE_share margin : Nat),
      profile ≤ CEF ∧
      2 * profile + fresh ≤ CE ∧
      2 * CEF + fresh ≤ CE + CE_share ∧
      SimultaneousHybridEscape fresh CE_share (CEF - profile) margin ∧
      CE < 2 * CEF + margin := by
  refine ⟨0, 1, 1, 2, 4, 1, ?_⟩
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · exact ⟨by omega, by omega⟩
  · omega

/-! ## Restricted semantic regimes bypass the hybrid escape

The simultaneous hybrid signature is only a necessary consequence of a bad
general nonlinear recurrence; it is not itself incompatible with a good
recurrence.  Consequently, the honest restricted-model cash-out is to derive
the recurrence directly from the stronger semantic theorem available in that
model.  The following lemmas connect the existing formula,
no-cancellation/monotone, and no-net-saving/linear results to the same local
interface used by the hybrid amplifier.
-/

/-- Formula freshness plus a disjoint mixer budget gives the complete local
recurrence.  No profile-gap or sharing-count estimate is needed. -/
theorem formulaFreshness_with_disjointMixer_gives_recurrence
    (CEF coneL coneR coneUnion CE_mix fresh CE : Nat)
    (hchildL : CEF ≤ coneL)
    (hchildR : CEF ≤ coneR)
    (hformula : coneL + coneR = coneUnion)
    (hmix : fresh ≤ CE_mix)
    (hpartition : coneUnion + CE_mix ≤ CE) :
    2 * CEF + fresh ≤ CE := by
  have hfresh : 2 * CEF ≤ coneUnion :=
    NFrameRestrictedFreshness.formula_freshness
      CEF coneL coneR coneUnion coneUnion
      hchildL hchildR hformula (le_refl _)
  omega

/-- In a no-cancellation class (in particular the monotone regime modeled by
the restricted theorem), freshness plus a disjoint mixer budget gives the
complete local recurrence directly. -/
theorem noCancellationFreshness_with_disjointMixer_gives_recurrence
    (CEF coneL coneR coneUnion beneficialInter CE_mix fresh CE : Nat)
    (hchildL : CEF ≤ coneL)
    (hchildR : CEF ≤ coneR)
    (hunion : coneL + coneR = coneUnion + beneficialInter)
    (hnocancel : beneficialInter = 0)
    (hmix : fresh ≤ CE_mix)
    (hpartition : coneUnion + CE_mix ≤ CE) :
    2 * CEF + fresh ≤ CE := by
  have hfresh : 2 * CEF ≤ coneUnion :=
    NFrameRestrictedFreshness.no_cancellation_freshness
      CEF coneL coneR coneUnion coneUnion beneficialInter
      hchildL hchildR hunion (le_refl _) hnocancel
  omega

/-- The already-proved no-net-saving condition, satisfied by the repository's
linear/rank-nullity regime, also closes the complete local recurrence without
using the hybrid escape prohibition. -/
theorem noNetSaving_gives_hybridRecurrence
    (CE CE_L CE_R CE_mix CE_share shareLeft shareRight CEF fresh : Nat)
    (hpartition : CE_L + CE_R + CE_mix + CE_share ≤ CE)
    (hmix : fresh ≤ CE_mix)
    (hleft : CEF ≤ CE_L + shareLeft)
    (hright : CEF ≤ CE_R + shareRight)
    (hnosaving : shareLeft + shareRight ≤ CE_share) :
    2 * CEF + fresh ≤ CE := by
  exact NFrameNonlinearShare.direct_sum_from_no_net_saving
    CE CE_L CE_R CE_mix CE_share shareLeft shareRight CEF fresh
    hpartition hmix hleft hright hnosaving

/-- The concrete semantic signature left after all three proved restricted
safeguards fail.  There is real cone overlap, that overlap is beneficial
(hence cancellation-capable), and the mixed bank produces more usable
one-sided content than its own gate count. -/
structure GenuineNonlinearCancellationEscape
    (coneL coneR coneUnion beneficialInter CE_share
      shareLeft shareRight : Nat) : Prop where
  cone_overlap : coneUnion < coneL + coneR
  beneficial_intersection_pos : 0 < beneficialInter
  nonlinear_net_saving : CE_share < shareLeft + shareRight

/-- **Failure of the local recurrence forces genuinely nonlinear
cancellation-sharing.**  Under the concrete cone and gate ledgers, a bad
recurrence cannot be explained by formula fanout, no-cancellation semantics,
or linear no-net-saving.  It must violate all three safeguards at once. -/
theorem childRecurrence_failure_forces_genuineNonlinearCancellation
    (CEF coneL coneR coneUnion beneficialInter
      CE_L CE_R CE_mix CE_share shareLeft shareRight fresh CE : Nat)
    (hchildConeL : CEF ≤ coneL)
    (hchildConeR : CEF ≤ coneR)
    (hconeUnion : coneL + coneR = coneUnion + beneficialInter)
    (hconePartition : coneUnion + CE_mix ≤ CE)
    (hgatePartition : CE_L + CE_R + CE_mix + CE_share ≤ CE)
    (hmix : fresh ≤ CE_mix)
    (hleft : CEF ≤ CE_L + shareLeft)
    (hright : CEF ≤ CE_R + shareRight)
    (hfail : CE < 2 * CEF + fresh) :
    GenuineNonlinearCancellationEscape coneL coneR coneUnion
      beneficialInter CE_share shareLeft shareRight := by
  have hinter : 0 < beneficialInter := by
    by_contra hzero
    have hrec := noCancellationFreshness_with_disjointMixer_gives_recurrence
      CEF coneL coneR coneUnion beneficialInter CE_mix fresh CE
      hchildConeL hchildConeR hconeUnion (by omega) hmix hconePartition
    omega
  have hnet : CE_share < shareLeft + shareRight := by
    by_contra hnosaving
    have hrec := noNetSaving_gives_hybridRecurrence
      CE CE_L CE_R CE_mix CE_share shareLeft shareRight CEF fresh
      hgatePartition hmix hleft hright (by omega)
    omega
  exact ⟨by omega, hinter, hnet⟩

/-- There is no fourth local case: under both honest ledgers, either the full
recurrence holds or the circuit exhibits the genuine nonlinear cancellation
signature. -/
theorem childRecurrence_or_genuineNonlinearCancellation
    (CEF coneL coneR coneUnion beneficialInter
      CE_L CE_R CE_mix CE_share shareLeft shareRight fresh CE : Nat)
    (hchildConeL : CEF ≤ coneL)
    (hchildConeR : CEF ≤ coneR)
    (hconeUnion : coneL + coneR = coneUnion + beneficialInter)
    (hconePartition : coneUnion + CE_mix ≤ CE)
    (hgatePartition : CE_L + CE_R + CE_mix + CE_share ≤ CE)
    (hmix : fresh ≤ CE_mix)
    (hleft : CEF ≤ CE_L + shareLeft)
    (hright : CEF ≤ CE_R + shareRight) :
    2 * CEF + fresh ≤ CE ∨
      GenuineNonlinearCancellationEscape coneL coneR coneUnion
        beneficialInter CE_share shareLeft shareRight := by
  by_cases hrec : 2 * CEF + fresh ≤ CE
  · exact Or.inl hrec
  · exact Or.inr
      (childRecurrence_failure_forces_genuineNonlinearCancellation
        CEF coneL coneR coneUnion beneficialInter CE_L CE_R CE_mix
        CE_share shareLeft shareRight fresh CE hchildConeL hchildConeR
        hconeUnion hconePartition hgatePartition hmix hleft hright (by omega))

/-- The recurrence deficit is bounded independently by beneficial cone
intersection and by the mixed bank's nonlinear net-saving excess.  Hence the
certified loss is their minimum. -/
theorem childRecurrence_deficit_le_min_cancellationExcess
    (CEF coneL coneR coneUnion beneficialInter
      CE_L CE_R CE_mix CE_share shareLeft shareRight fresh CE : Nat)
    (hchildConeL : CEF ≤ coneL)
    (hchildConeR : CEF ≤ coneR)
    (hconeUnion : coneL + coneR = coneUnion + beneficialInter)
    (hconePartition : coneUnion + CE_mix ≤ CE)
    (hgatePartition : CE_L + CE_R + CE_mix + CE_share ≤ CE)
    (hmix : fresh ≤ CE_mix)
    (hleft : CEF ≤ CE_L + shareLeft)
    (hright : CEF ≤ CE_R + shareRight) :
    2 * CEF + fresh ≤ CE +
      min beneficialInter (shareLeft + shareRight - CE_share) := by
  have hcone : 2 * CEF + fresh ≤ CE + beneficialInter := by
    omega
  have hshare : 2 * CEF + fresh ≤
      CE + (shareLeft + shareRight - CE_share) := by
    omega
  by_cases hle : beneficialInter ≤ shareLeft + shareRight - CE_share
  · rw [min_eq_left hle]
    exact hcone
  · rw [min_eq_right (by omega)]
    exact hshare

/-- If fresh geometry pays the smaller of the two genuine cancellation
excesses and leaves `margin`, the desired doubling-plus-margin recurrence
follows. -/
theorem cancellationExcessMargin_gives_childRecurrence
    (CEF coneL coneR coneUnion beneficialInter
      CE_L CE_R CE_mix CE_share shareLeft shareRight fresh margin CE : Nat)
    (hchildConeL : CEF ≤ coneL)
    (hchildConeR : CEF ≤ coneR)
    (hconeUnion : coneL + coneR = coneUnion + beneficialInter)
    (hconePartition : coneUnion + CE_mix ≤ CE)
    (hgatePartition : CE_L + CE_R + CE_mix + CE_share ≤ CE)
    (hmix : fresh ≤ CE_mix)
    (hleft : CEF ≤ CE_L + shareLeft)
    (hright : CEF ≤ CE_R + shareRight)
    (hbudget : min beneficialInter
      (shareLeft + shareRight - CE_share) + margin ≤ fresh) :
    2 * CEF + margin ≤ CE := by
  have hdeficit := childRecurrence_deficit_le_min_cancellationExcess
    CEF coneL coneR coneUnion beneficialInter CE_L CE_R CE_mix CE_share
    shareLeft shareRight fresh CE hchildConeL hchildConeR hconeUnion
    hconePartition hgatePartition hmix hleft hright
  omega

/-- Conversely, failure of doubling plus margin means fresh geometry cannot
pay even the smaller of the beneficial-intersection and nonlinear-net-saving
excesses. -/
theorem childRecurrence_failure_forces_cancellationBudgetOverrun
    (CEF coneL coneR coneUnion beneficialInter
      CE_L CE_R CE_mix CE_share shareLeft shareRight fresh margin CE : Nat)
    (hchildConeL : CEF ≤ coneL)
    (hchildConeR : CEF ≤ coneR)
    (hconeUnion : coneL + coneR = coneUnion + beneficialInter)
    (hconePartition : coneUnion + CE_mix ≤ CE)
    (hgatePartition : CE_L + CE_R + CE_mix + CE_share ≤ CE)
    (hmix : fresh ≤ CE_mix)
    (hleft : CEF ≤ CE_L + shareLeft)
    (hright : CEF ≤ CE_R + shareRight)
    (hfail : CE < 2 * CEF + margin) :
    fresh < min beneficialInter
      (shareLeft + shareRight - CE_share) + margin := by
  by_contra hbudget
  have hrec := cancellationExcessMargin_gives_childRecurrence
    CEF coneL coneR coneUnion beneficialInter CE_L CE_R CE_mix CE_share
    shareLeft shareRight fresh margin CE hchildConeL hchildConeR hconeUnion
    hconePartition hgatePartition hmix hleft hright (by omega)
  omega

/-- **Cancellation-excess multiscale amplifier.**  If at every recursive
scale fresh geometry absorbs the smaller of beneficial cone intersection and
nonlinear net-saving excess, while leaving a fixed positive margin, the
existing recurrence amplifier yields the full `N log N` lower bound. -/
theorem cancellationExcessMargin_amplifies
    (freshRate marginRate : Nat)
    (T coneL coneR coneUnion beneficialInter CE_L CE_R CE_mix CE_share
      shareLeft shareRight : Nat → Nat)
    (hchildConeL : ∀ k, T k ≤ coneL k)
    (hchildConeR : ∀ k, T k ≤ coneR k)
    (hconeUnion : ∀ k,
      coneL k + coneR k = coneUnion k + beneficialInter k)
    (hconePartition : ∀ k,
      coneUnion k + CE_mix k ≤ T (k + 1))
    (hgatePartition : ∀ k,
      CE_L k + CE_R k + CE_mix k + CE_share k ≤ T (k + 1))
    (hmix : ∀ k, freshRate * 2 ^ (k + 1) ≤ CE_mix k)
    (hleft : ∀ k, T k ≤ CE_L k + shareLeft k)
    (hright : ∀ k, T k ≤ CE_R k + shareRight k)
    (habsorb : ∀ k,
      min (beneficialInter k)
          (shareLeft k + shareRight k - CE_share k) +
        marginRate * 2 ^ (k + 1) ≤ freshRate * 2 ^ (k + 1)) :
    ∀ b, marginRate * (b * 2 ^ b) ≤ T b := by
  apply NFrameConeAmplify.coneExcess_amplify marginRate T
  intro k
  exact cancellationExcessMargin_gives_childRecurrence
    (T k) (coneL k) (coneR k) (coneUnion k) (beneficialInter k)
    (CE_L k) (CE_R k) (CE_mix k) (CE_share k)
    (shareLeft k) (shareRight k) (freshRate * 2 ^ (k + 1))
    (marginRate * 2 ^ (k + 1)) (T (k + 1))
    (hchildConeL k) (hchildConeR k) (hconeUnion k)
    (hconePartition k) (hgatePartition k) (hmix k)
    (hleft k) (hright k) (habsorb k)

/-- **All-scale cancellation frontier.**  Either every scale pays the
doubling-plus-margin recurrence, or a concrete scale is returned where fresh
geometry cannot cover even the smaller genuine cancellation excess plus the
requested margin. -/
theorem allScalesCancellationRecurrence_or_exists_budgetOverrun
    (freshRate marginRate : Nat)
    (T coneL coneR coneUnion beneficialInter CE_L CE_R CE_mix CE_share
      shareLeft shareRight : Nat → Nat)
    (hchildConeL : ∀ k, T k ≤ coneL k)
    (hchildConeR : ∀ k, T k ≤ coneR k)
    (hconeUnion : ∀ k,
      coneL k + coneR k = coneUnion k + beneficialInter k)
    (hconePartition : ∀ k,
      coneUnion k + CE_mix k ≤ T (k + 1))
    (hgatePartition : ∀ k,
      CE_L k + CE_R k + CE_mix k + CE_share k ≤ T (k + 1))
    (hmix : ∀ k, freshRate * 2 ^ (k + 1) ≤ CE_mix k)
    (hleft : ∀ k, T k ≤ CE_L k + shareLeft k)
    (hright : ∀ k, T k ≤ CE_R k + shareRight k) :
    (∀ k, 2 * T k + marginRate * 2 ^ (k + 1) ≤ T (k + 1)) ∨
      ∃ k, freshRate * 2 ^ (k + 1) <
        min (beneficialInter k)
            (shareLeft k + shareRight k - CE_share k) +
          marginRate * 2 ^ (k + 1) := by
  by_cases hall : ∀ k,
      2 * T k + marginRate * 2 ^ (k + 1) ≤ T (k + 1)
  · exact Or.inl hall
  · right
    push_neg at hall
    obtain ⟨k, hk⟩ := hall
    exact ⟨k, childRecurrence_failure_forces_cancellationBudgetOverrun
      (T k) (coneL k) (coneR k) (coneUnion k) (beneficialInter k)
      (CE_L k) (CE_R k) (CE_mix k) (CE_share k)
      (shareLeft k) (shareRight k) (freshRate * 2 ^ (k + 1))
      (marginRate * 2 ^ (k + 1)) (T (k + 1))
      (hchildConeL k) (hchildConeR k) (hconeUnion k)
      (hconePartition k) (hgatePartition k) (hmix k)
      (hleft k) (hright k) hk⟩

/-- **Three-way SAT/cancellation deficit bound.**  Combining the concrete
cancellation ledgers with the independent aggregate SAT restriction-profile
cash-out bounds recurrence loss by the smallest of three quantities:
beneficial cone intersection, nonlinear net-saving excess, and twice the
uncaptured profile gap. -/
theorem childRecurrence_deficit_le_min_cancellation_profileGap
    (profile CEF coneL coneR coneUnion beneficialInter
      CE_L CE_R CE_mix CE_share shareLeft shareRight fresh CE : Nat)
    (hprofileLower : profile ≤ CEF)
    (hprofileCashout : 2 * profile + fresh ≤ CE)
    (hchildConeL : CEF ≤ coneL)
    (hchildConeR : CEF ≤ coneR)
    (hconeUnion : coneL + coneR = coneUnion + beneficialInter)
    (hconePartition : coneUnion + CE_mix ≤ CE)
    (hgatePartition : CE_L + CE_R + CE_mix + CE_share ≤ CE)
    (hmix : fresh ≤ CE_mix)
    (hleft : CEF ≤ CE_L + shareLeft)
    (hright : CEF ≤ CE_R + shareRight) :
    2 * CEF + fresh ≤ CE +
      min (min beneficialInter (shareLeft + shareRight - CE_share))
        (2 * (CEF - profile)) := by
  have hcancel := childRecurrence_deficit_le_min_cancellationExcess
    CEF coneL coneR coneUnion beneficialInter CE_L CE_R CE_mix CE_share
    shareLeft shareRight fresh CE hchildConeL hchildConeR hconeUnion
    hconePartition hgatePartition hmix hleft hright
  have hprofile := childRecurrence_deficit_eq_profileGap
    profile CE fresh CEF hprofileCashout hprofileLower
  by_cases hle :
      min beneficialInter (shareLeft + shareRight - CE_share) ≤
        2 * (CEF - profile)
  · rw [min_eq_left hle]
    exact hcancel
  · rw [min_eq_right (by omega)]
    exact hprofile

/-- Paying the smallest of the two cancellation excesses and the independent
SAT profile-gap deficit, while retaining `margin`, closes the local
doubling-plus-margin recurrence. -/
theorem cancellationProfileMargin_gives_childRecurrence
    (profile CEF coneL coneR coneUnion beneficialInter
      CE_L CE_R CE_mix CE_share shareLeft shareRight fresh margin CE : Nat)
    (hprofileLower : profile ≤ CEF)
    (hprofileCashout : 2 * profile + fresh ≤ CE)
    (hchildConeL : CEF ≤ coneL)
    (hchildConeR : CEF ≤ coneR)
    (hconeUnion : coneL + coneR = coneUnion + beneficialInter)
    (hconePartition : coneUnion + CE_mix ≤ CE)
    (hgatePartition : CE_L + CE_R + CE_mix + CE_share ≤ CE)
    (hmix : fresh ≤ CE_mix)
    (hleft : CEF ≤ CE_L + shareLeft)
    (hright : CEF ≤ CE_R + shareRight)
    (habsorb :
      min (min beneficialInter (shareLeft + shareRight - CE_share))
          (2 * (CEF - profile)) + margin ≤ fresh) :
    2 * CEF + margin ≤ CE := by
  have hdeficit := childRecurrence_deficit_le_min_cancellation_profileGap
    profile CEF coneL coneR coneUnion beneficialInter CE_L CE_R CE_mix
    CE_share shareLeft shareRight fresh CE hprofileLower hprofileCashout
    hchildConeL hchildConeR hconeUnion hconePartition hgatePartition
    hmix hleft hright
  omega

/-- **Unified multiscale amplifier.**  The strongest proved criterion permits
each scale to close using whichever is smallest: beneficial cancellation,
nonlinear net saving, or uncaptured SAT profile complexity. -/
theorem cancellationProfileMargin_amplifies
    (freshRate marginRate : Nat)
    (T profile coneL coneR coneUnion beneficialInter CE_L CE_R CE_mix
      CE_share shareLeft shareRight : Nat → Nat)
    (hprofileLower : ∀ k, profile k ≤ T k)
    (hprofileCashout : ∀ k,
      2 * profile k + freshRate * 2 ^ (k + 1) ≤ T (k + 1))
    (hchildConeL : ∀ k, T k ≤ coneL k)
    (hchildConeR : ∀ k, T k ≤ coneR k)
    (hconeUnion : ∀ k,
      coneL k + coneR k = coneUnion k + beneficialInter k)
    (hconePartition : ∀ k,
      coneUnion k + CE_mix k ≤ T (k + 1))
    (hgatePartition : ∀ k,
      CE_L k + CE_R k + CE_mix k + CE_share k ≤ T (k + 1))
    (hmix : ∀ k, freshRate * 2 ^ (k + 1) ≤ CE_mix k)
    (hleft : ∀ k, T k ≤ CE_L k + shareLeft k)
    (hright : ∀ k, T k ≤ CE_R k + shareRight k)
    (habsorb : ∀ k,
      min (min (beneficialInter k)
          (shareLeft k + shareRight k - CE_share k))
          (2 * (T k - profile k)) + marginRate * 2 ^ (k + 1) ≤
        freshRate * 2 ^ (k + 1)) :
    ∀ b, marginRate * (b * 2 ^ b) ≤ T b := by
  apply NFrameConeAmplify.coneExcess_amplify marginRate T
  intro k
  exact cancellationProfileMargin_gives_childRecurrence
    (profile k) (T k) (coneL k) (coneR k) (coneUnion k)
    (beneficialInter k) (CE_L k) (CE_R k) (CE_mix k) (CE_share k)
    (shareLeft k) (shareRight k) (freshRate * 2 ^ (k + 1))
    (marginRate * 2 ^ (k + 1)) (T (k + 1))
    (hprofileLower k) (hprofileCashout k) (hchildConeL k)
    (hchildConeR k) (hconeUnion k) (hconePartition k)
    (hgatePartition k) (hmix k) (hleft k) (hright k) (habsorb k)

/-- Named form of the sole remaining three-way semantic adversary.  Fresh
geometry loses simultaneously to beneficial cancellation, nonlinear
mass-production excess, and uncaptured SAT profile complexity. -/
structure TripleNonlinearSATEscape
    (fresh beneficialInter netSavingExcess profileGap margin : Nat) : Prop where
  beneficial_overrun : fresh < beneficialInter + margin
  netSaving_overrun : fresh < netSavingExcess + margin
  profileGap_overrun : fresh < 2 * profileGap + margin

/-- The nested minimum budget overrun is exactly the conjunction of all three
semantic overruns. -/
theorem tripleBudgetOverrun_iff_escape
    (fresh beneficialInter netSavingExcess profileGap margin : Nat) :
    fresh < min (min beneficialInter netSavingExcess) (2 * profileGap) +
        margin ↔
      TripleNonlinearSATEscape fresh beneficialInter netSavingExcess
        profileGap margin := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact lt_of_lt_of_le h (Nat.add_le_add_right
        (le_trans (min_le_left _ _) (min_le_left _ _)) _)
    · exact lt_of_lt_of_le h (Nat.add_le_add_right
        (le_trans (min_le_left _ _) (min_le_right _ _)) _)
    · exact lt_of_lt_of_le h (Nat.add_le_add_right (min_le_right _ _) _)
  · rintro ⟨hbeneficial, hnet, hprofile⟩
    simp only [min_def]
    split <;> split <;> omega

/-- Failure of the desired recurrence forces all three nonlinear SAT escape
conditions simultaneously. -/
theorem childRecurrence_failure_has_tripleNonlinearSATEscape
    (profile CEF coneL coneR coneUnion beneficialInter
      CE_L CE_R CE_mix CE_share shareLeft shareRight fresh margin CE : Nat)
    (hprofileLower : profile ≤ CEF)
    (hprofileCashout : 2 * profile + fresh ≤ CE)
    (hchildConeL : CEF ≤ coneL)
    (hchildConeR : CEF ≤ coneR)
    (hconeUnion : coneL + coneR = coneUnion + beneficialInter)
    (hconePartition : coneUnion + CE_mix ≤ CE)
    (hgatePartition : CE_L + CE_R + CE_mix + CE_share ≤ CE)
    (hmix : fresh ≤ CE_mix)
    (hleft : CEF ≤ CE_L + shareLeft)
    (hright : CEF ≤ CE_R + shareRight)
    (hfail : CE < 2 * CEF + margin) :
    TripleNonlinearSATEscape fresh beneficialInter
      (shareLeft + shareRight - CE_share) (CEF - profile) margin := by
  apply (tripleBudgetOverrun_iff_escape fresh beneficialInter
    (shareLeft + shareRight - CE_share) (CEF - profile) margin).mp
  by_contra hbudget
  have hrec := cancellationProfileMargin_gives_childRecurrence
    profile CEF coneL coneR coneUnion beneficialInter CE_L CE_R CE_mix
    CE_share shareLeft shareRight fresh margin CE hprofileLower
    hprofileCashout hchildConeL hchildConeR hconeUnion hconePartition
    hgatePartition hmix hleft hright (by omega)
  omega

/-- Excluding the named triple escape is precisely sufficient for the local
doubling-plus-margin recurrence. -/
theorem childRecurrence_of_no_tripleNonlinearSATEscape
    (profile CEF coneL coneR coneUnion beneficialInter
      CE_L CE_R CE_mix CE_share shareLeft shareRight fresh margin CE : Nat)
    (hprofileLower : profile ≤ CEF)
    (hprofileCashout : 2 * profile + fresh ≤ CE)
    (hchildConeL : CEF ≤ coneL)
    (hchildConeR : CEF ≤ coneR)
    (hconeUnion : coneL + coneR = coneUnion + beneficialInter)
    (hconePartition : coneUnion + CE_mix ≤ CE)
    (hgatePartition : CE_L + CE_R + CE_mix + CE_share ≤ CE)
    (hmix : fresh ≤ CE_mix)
    (hleft : CEF ≤ CE_L + shareLeft)
    (hright : CEF ≤ CE_R + shareRight)
    (hno : ¬ TripleNonlinearSATEscape fresh beneficialInter
      (shareLeft + shareRight - CE_share) (CEF - profile) margin) :
    2 * CEF + margin ≤ CE := by
  by_contra hfail
  exact hno (childRecurrence_failure_has_tripleNonlinearSATEscape
    profile CEF coneL coneR coneUnion beneficialInter CE_L CE_R CE_mix
    CE_share shareLeft shareRight fresh margin CE hprofileLower
    hprofileCashout hchildConeL hchildConeR hconeUnion hconePartition
    hgatePartition hmix hleft hright (by omega))

/-- **Named triple-escape prohibition amplifies to `N log N`.**  This is the
final all-scale semantic interface: ruling out the conjunction of the three
nonlinear overruns at every recursive SAT scale feeds the existing amplifier
without any additional accounting premise. -/
theorem noTripleNonlinearSATEscape_amplifies
    (freshRate marginRate : Nat)
    (T profile coneL coneR coneUnion beneficialInter CE_L CE_R CE_mix
      CE_share shareLeft shareRight : Nat → Nat)
    (hprofileLower : ∀ k, profile k ≤ T k)
    (hprofileCashout : ∀ k,
      2 * profile k + freshRate * 2 ^ (k + 1) ≤ T (k + 1))
    (hchildConeL : ∀ k, T k ≤ coneL k)
    (hchildConeR : ∀ k, T k ≤ coneR k)
    (hconeUnion : ∀ k,
      coneL k + coneR k = coneUnion k + beneficialInter k)
    (hconePartition : ∀ k,
      coneUnion k + CE_mix k ≤ T (k + 1))
    (hgatePartition : ∀ k,
      CE_L k + CE_R k + CE_mix k + CE_share k ≤ T (k + 1))
    (hmix : ∀ k, freshRate * 2 ^ (k + 1) ≤ CE_mix k)
    (hleft : ∀ k, T k ≤ CE_L k + shareLeft k)
    (hright : ∀ k, T k ≤ CE_R k + shareRight k)
    (hno : ∀ k, ¬ TripleNonlinearSATEscape
      (freshRate * 2 ^ (k + 1)) (beneficialInter k)
      (shareLeft k + shareRight k - CE_share k)
      (T k - profile k) (marginRate * 2 ^ (k + 1))) :
    ∀ b, marginRate * (b * 2 ^ b) ≤ T b := by
  apply NFrameConeAmplify.coneExcess_amplify marginRate T
  intro k
  exact childRecurrence_of_no_tripleNonlinearSATEscape
    (profile k) (T k) (coneL k) (coneR k) (coneUnion k)
    (beneficialInter k) (CE_L k) (CE_R k) (CE_mix k) (CE_share k)
    (shareLeft k) (shareRight k) (freshRate * 2 ^ (k + 1))
    (marginRate * 2 ^ (k + 1)) (T (k + 1))
    (hprofileLower k) (hprofileCashout k) (hchildConeL k)
    (hchildConeR k) (hconeUnion k) (hconePartition k)
    (hgatePartition k) (hmix k) (hleft k) (hright k) (hno k)

/-- **The triple escape remains arithmetically consistent.**  Concrete
parameters satisfy the profile cash-out, cone ledger, gate ledger, mixer and
restriction bounds, exhibit all three overruns, and fail the target recurrence.
Thus the named prohibition must come from actual SAT/circuit semantics. -/
theorem tripleNonlinearSATEscape_is_arithmetically_consistent :
    ∃ (profile CEF coneL coneR coneUnion beneficialInter
      CE_L CE_R CE_mix CE_share shareLeft shareRight fresh margin CE : Nat),
      profile ≤ CEF ∧
      2 * profile + fresh ≤ CE ∧
      CEF ≤ coneL ∧ CEF ≤ coneR ∧
      coneL + coneR = coneUnion + beneficialInter ∧
      coneUnion + CE_mix ≤ CE ∧
      CE_L + CE_R + CE_mix + CE_share ≤ CE ∧
      fresh ≤ CE_mix ∧
      CEF ≤ CE_L + shareLeft ∧
      CEF ≤ CE_R + shareRight ∧
      TripleNonlinearSATEscape fresh beneficialInter
        (shareLeft + shareRight - CE_share) (CEF - profile) margin ∧
      CE < 2 * CEF + margin := by
  refine ⟨0, 2, 2, 2, 0, 4, 0, 0, 1, 3, 2, 2, 1, 1, 4, ?_⟩
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, ?_, by omega⟩
  exact ⟨by omega, by omega, by omega⟩

/-! ## Dense-grid obstruction to automatic rectangle extraction

The full-mass horn in `sat3_private_band_squeeze` only certifies density of a
selector grid.  Density alone cannot supply the clean rectangle needed by
`sat3_multi_rectangle_census_local`: the off-diagonal relation on three
points already occupies two thirds of the grid but contains no `2 × 2`
complete rectangle.  Consequently the remaining extraction theorem must use
minimal-SAT/circuit semantics, not the full-mass inequality by itself.
-/

/-- The six off-diagonal cells of the `3 × 3` Boolean grid. -/
def offDiagonalThree : Finset (Fin 3 × Fin 3) :=
  Finset.univ.filter (fun ij => ij.1 ≠ ij.2)

/-- The occupied columns in one row of `offDiagonalThree`. -/
def offDiagonalRow (c : Fin 3) : Finset (Fin 3) :=
  Finset.univ.filter (fun w => c ≠ w)

/-- Every row of the obstruction has density `2/3`. -/
theorem offDiagonalRow_card (c : Fin 3) :
    (offDiagonalRow c).card = 2 := by
  fin_cases c <;> decide

/-- Every pair of distinct rows has codegree exactly one.  Thus the
obstruction satisfies a uniform pairwise-spread law while still containing no
`2 × 2` complete rectangle. -/
theorem offDiagonalRow_pair_codegree (c c' : Fin 3) (hne : c ≠ c') :
    (offDiagonalRow c ∩ offDiagonalRow c').card = 1 := by
  fin_cases c <;> fin_cases c' <;> simp_all <;> decide

/-- A pair of row/column sets forms a complete rectangle in `R`. -/
abbrev ContainsCompleteRectangle
    (R : Finset (Fin 3 × Fin 3)) (C W : Finset (Fin 3)) : Prop :=
  ∀ c ∈ C, ∀ w ∈ W, (c, w) ∈ R

/-- **Dense mass does not force even a `2 × 2` rectangle.**  The
off-diagonal `3 × 3` grid has six cells, but every two rows and two columns
meet on a missing diagonal cell.  This is the finite obstruction preventing
the sign-squeeze full-mass horn from closing the rectangle route by generic
density reasoning. -/
theorem offDiagonalThree_dense_without_two_by_two_rectangle :
    offDiagonalThree.card = 6 ∧
    ∀ C W : Finset (Fin 3), C.card = 2 → W.card = 2 →
      ¬ ContainsCompleteRectangle offDiagonalThree C W := by
  constructor
  · rfl
  · intro C W hC hW hrect
    have hU : (C ∪ W).card ≤ 3 := by
      simpa using Finset.card_le_card (Finset.subset_univ (C ∪ W))
    have hI : 0 < (C ∩ W).card := by
      have hsum := Finset.card_union_add_card_inter C W
      omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hI
    obtain ⟨hxC, hxW⟩ := Finset.mem_inter.mp hx
    have hxx := hrect x hxC x hxW
    simp [offDiagonalThree] at hxx

/-! ### An asymptotic affine-incidence obstruction

The finite `3 × 3` example is not a small-size accident.  Lines and points
over any finite field give a family with `q³` occupied cells in a
`q² × q²` grid and no complete `2 × 2` rectangle.  This matches the
pairwise/codegree barrier asymptotically and shows that a higher-order or
circuit-shaped invariant is indispensable.
-/

namespace AffineRectangleObstruction

variable {F : Type*} [Field F]

abbrev Line (F : Type*) := F × F
abbrev Point (F : Type*) := F × F

/-- The point `(x,y)` lies on the affine line `(a,b)` when `y = ax+b`. -/
def Incident (l : Line F) (p : Point F) : Prop :=
  p.2 = l.1 * p.1 + l.2

/-- **Affine incidence is rectangle-free.** Two distinct affine lines cannot
both contain two distinct points. -/
theorem no_two_by_two
    (l₁ l₂ : Line F) (p₁ p₂ : Point F)
    (hl : l₁ ≠ l₂) (hp : p₁ ≠ p₂)
    (h₁₁ : Incident l₁ p₁) (h₁₂ : Incident l₁ p₂)
    (h₂₁ : Incident l₂ p₁) : ¬ Incident l₂ p₂ := by
  intro h₂₂
  rcases l₁ with ⟨a₁, b₁⟩
  rcases l₂ with ⟨a₂, b₂⟩
  rcases p₁ with ⟨x₁, y₁⟩
  rcases p₂ with ⟨x₂, y₂⟩
  simp only [Incident] at h₁₁ h₁₂ h₂₁ h₂₂
  have hxprod : (a₁ - a₂) * (x₁ - x₂) = 0 := by
    linear_combination -h₁₁ + h₂₁ + h₁₂ - h₂₂
  rcases mul_eq_zero.mp hxprod with ha | hx
  · have hab : b₁ = b₂ := by
      have haa : a₁ = a₂ := sub_eq_zero.mp ha
      rw [haa] at h₁₁
      linear_combination h₂₁ - h₁₁
    apply hl
    exact Prod.ext (sub_eq_zero.mp ha) hab
  · have hxx : x₁ = x₂ := sub_eq_zero.mp hx
    have hyy : y₁ = y₂ := by
      rw [hxx] at h₁₁
      exact h₁₁.trans h₁₂.symm
    apply hp
    exact Prod.ext hxx hyy

/-- Two distinct affine lines have at most one common incident point.  Hence
every intersection of two or more distinct row neighborhoods has cardinality
at most one; passing from pairwise to higher-order incidence counts does not
remove this obstruction. -/
theorem common_point_unique
    (l₁ l₂ : Line F) (hl : l₁ ≠ l₂)
    (p₁ p₂ : Point F)
    (h₁₁ : Incident l₁ p₁) (h₂₁ : Incident l₂ p₁)
    (h₁₂ : Incident l₁ p₂) (h₂₂ : Incident l₂ p₂) :
    p₁ = p₂ := by
  by_contra hp
  exact no_two_by_two l₁ l₂ p₁ p₂ hl hp h₁₁ h₁₂ h₂₁ h₂₂

variable [Fintype F] [DecidableEq F]

/-- Parameterize every incidence by its line and x-coordinate. -/
def incidenceEmbedding : (Line F × F) ↪ (Line F × Point F) where
  toFun lx := (lx.1, (lx.2, lx.1.1 * lx.2 + lx.1.2))
  inj' := by
    intro lx lx' h
    apply Prod.ext
    · exact congrArg (fun z : Line F × Point F => z.1) h
    · exact congrArg (fun z : Line F × Point F => z.2.1) h

/-- The complete affine line-point incidence relation. -/
def incidences : Finset (Line F × Point F) :=
  Finset.univ.map incidenceEmbedding

/-- With `q = |F|`, the affine incidence grid has exactly `q³` occupied
cells inside its `q² × q²` line-point matrix. -/
theorem incidences_card :
    incidences (F := F).card =
      Fintype.card F * Fintype.card F * Fintype.card F := by
  simp [incidences, Fintype.card_prod, Nat.mul_assoc]

/-- Membership in the enumerated relation is exactly affine incidence. -/
theorem mem_incidences_iff (l : Line F) (p : Point F) :
    (l, p) ∈ incidences (F := F) ↔ Incident l p := by
  constructor
  · intro h
    simp [incidences, incidenceEmbedding] at h
    obtain ⟨x, rfl⟩ := h
    rfl
  · intro h
    apply Finset.mem_map.mpr
    refine ⟨(l, p.1), Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · rfl
    · exact Prod.ext rfl h.symm

end AffineRectangleObstruction

/-! ## Exhaustive accounting verdict

The three physically distinct charging interpretations are now summarized in
one proposition and one kernel theorem:

* separate runs retain a factor `K` and are automatically capacitated;
* one run with no reuse is equivalent to `K <= T`;
* one run with reuse `r` is equivalent to `K <= T*r`.

This is an exhaustive verdict about the accounting mechanisms formalized in
this file.  None supplies an independent SAT lower bound.
-/

/-- The complete numerical content of the many-run, one-run non-amortized,
and one-run bounded-reuse charging interpretations for fixed parameters. -/
def TransitionChargingAuditVerdict
    {M : TuringMachine.DTM} (n K T r : Nat)
    (hn : 1 ≤ n) (input : Fin n → Bool) : Prop :=
  (1 ≤ T → K ≤ K * T) ∧
  (Nonempty (SingleRunNonAmortizedObligationSchedule M n K T) ↔ K ≤ T) ∧
  (Nonempty (SingleRunBoundedReuseObligationSchedule M n K T r) ↔
    K ≤ T * r)

/-- **Exhaustive transition-charging audit.**  All three interpretations have
exactly the numerical content stated above; no machine or SAT semantics enters
the proof. -/
theorem transitionChargingAuditVerdict
    {M : TuringMachine.DTM} (n K T r : Nat)
    (hn : 1 ≤ n) (input : Fin n → Bool) :
    TransitionChargingAuditVerdict (M := M) n K T r hn input := by
  refine ⟨obligations_le_runLocalEvents_of_positiveHorizon K T, ?_, ?_⟩
  · exact nonempty_singleRunSchedule_iff hn input
  · exact nonempty_singleRunBoundedReuseSchedule_iff hn input

/-- N-frame specialization of the exhaustive verdict at the DTM's declared
runtime. -/
theorem nframeTransitionChargingAuditVerdict
    {M : TuringMachine.DTM} {n r : Nat}
    (hn : 1 ≤ n) (input : Fin n → Bool) :
    TransitionChargingAuditVerdict (M := M) n
      (Nat.choose (n / 3) (Nat.log 2 n))
      (TuringMachine.timeSteps M n) r hn input :=
  transitionChargingAuditVerdict _ _ _ _ hn input

#print axioms liveRank_le_action
#print axioms GroundedTrajectoryNFrameActionCertificate.toActionCertificate
#print axioms groundedCertificateOfFoolingSet
#print axioms TrajectoryNFrameFoolingCertificate.toGrounded
#print axioms continuationGeometryOfSurjectiveResidual
#print axioms hasContinuationGeometry_of_surjectiveResidual
#print axioms binomial_le_runtime_of_canonicalDTMCertificate
#print axioms binomial_le_runtime_of_hasCanonicalDTMCertificate
#print axioms no_DTMDecidesSAT_of_canonicalResidualAction
#print axioms binomial_le_runtime_of_configurationGroundedDTMCertificate
#print axioms binomial_le_runtime_of_hasConfigurationGroundedDTMCertificate
#print axioms no_DTMDecidesSAT_of_configurationGroundedResidualAction
#print axioms TrajectoryNFrameResidualNoncollapse.toGeometry
#print axioms hasContinuationGeometry_of_residualNoncollapse
#print axioms continuationGeometry_of_residualNoncollapse
#print axioms not_residualNoncollapse_of_zeroBoundaryDecider
#print axioms TrajectoryNFrameContinuationGeometry.freeServicing
#print axioms TrajectoryNFrameObservedServicing.toLocal
#print axioms TrajectoryNFrameContinuationGeometry.withServicing
#print axioms binomial_le_action
#print axioms binomial_le_action_of_grounded
#print axioms hasTrajectoryCertificate_of_grounded
#print axioms hasGroundedCertificate_of_fooling
#print axioms hasFoolingCertificate_of_geometryAndServicing
#print axioms hasGeometryAndServicing_of_continuationGeometry
#print axioms hasGeometryAndServicing_of_observed
#print axioms geometryAndServicing_of_observedProgram
#print axioms not_geometryAndObservedServicing_of_zeroBoundaryDecider
#print axioms nframeActionExtraction_of_grounded
#print axioms groundedExtraction_of_geometryAndServicing
#print axioms action_gt_polynomial_of_certificate
#print axioms operationalSAT_action_lower_of_nframe_extraction
#print axioms rawPairDebt_not_unitLipschitz
#print axioms twoBits_clear_threeWayPairDebt
#print axioms booleanOutputSeparated_card_le_two
#print axioms binaryTranscriptSeparated_card_le_pow
#print axioms obligations_le_transitions_of_nonAmortizedCharge
#print axioms nonAmortizedTransitionCharge_iff
#print axioms obligations_le_transitions_mul_reuse
#print axioms fullTransitionAmortization
#print axioms fullTransitionAmortization_saturates
#print axioms reuse_gt_of_runtime_capacity_gap
#print axioms nontrivial_reuse_of_runtime_lt_obligations
#print axioms nframePolynomialRuntime_forces_superpolynomialReuse
#print axioms nframe_runtime_or_reuse
#print axioms nframe_runtime_lower_of_polynomialReuse
#print axioms nframe_runtime_lower_of_polynomialReuseAt
#print axioms fullAmortization_not_polynomialReuseAt
#print axioms not_allSchedules_polynomialReuseAt
#print axioms CanonicalDTMFirstSeparationData.firstSeparationTime_lt
#print axioms CanonicalDTMFirstSeparationData.separated_at_firstSeparationTime
#print axioms CanonicalDTMFirstSeparationData.toBoundedTransitionReuse
#print axioms CanonicalDTMFirstSeparationData.boundedTransitionReuseOfCanonicalBound
#print axioms CanonicalDTMFirstSeparationData.nframe_runtime_or_canonicalDTMReuse
#print axioms CanonicalDTMFirstSeparationData.nframe_runtime_lower_of_canonicalDTMReuseBound
#print axioms no_DTMDecidesSAT_of_canonicalPairExtraction_and_fiberBound
#print axioms canonicalPairExtraction_of_no_DTMDecidesSAT
#print axioms canonicalFiberBound_of_no_DTMDecidesSAT
#print axioms canonicalPairExtraction_and_fiberBound_iff_no_DTMDecidesSAT
#print axioms duplicateCanonicalDTMFirstSeparationData
#print axioms duplicateCanonicalData_not_pairInjective
#print axioms canonicalPairExtraction_of_injective
#print axioms no_DTMDecidesSAT_of_injectiveCanonicalPairExtraction_and_fiberBound
#print axioms injectiveCanonicalPairExtraction_of_no_DTMDecidesSAT
#print axioms injectiveCanonicalPairExtraction_and_fiberBound_iff_no_DTMDecidesSAT
#print axioms injectiveCanonicalPairExtraction_of_initiallyMerged
#print axioms no_DTMDecidesSAT_of_initiallyMergedInjectiveExtraction_and_fiberBound
#print axioms initiallyMergedInjectiveExtraction_of_no_DTMDecidesSAT
#print axioms initiallyMergedInjectiveExtraction_and_fiberBound_iff_no_DTMDecidesSAT
#print axioms initiallyMergedInjectiveExtraction_of_SATSemantic
#print axioms no_DTMDecidesSAT_of_SATSemanticExtraction_and_fiberBound
#print axioms SATSemanticExtraction_of_no_DTMDecidesSAT
#print axioms SATSemanticExtraction_and_fiberBound_iff_no_DTMDecidesSAT
#print axioms CanonicalDTMFirstSeparationData.runLocalEventCharge_injective
#print axioms obligations_le_runLocalEvents
#print axioms obligations_le_runLocalEvents_of_positiveHorizon
#print axioms CanonicalDTMFirstSeparationData.runLocalEvent_ne_of_index_ne
#print axioms obligations_le_singleRunTransitions
#print axioms singleRunScheduleOfLe
#print axioms nonempty_singleRunSchedule_iff
#print axioms nframe_singleRunSchedule_iff_runtimeLower
#print axioms obligations_le_singleRunTransitions_mul_reuse
#print axioms singleRunBoundedReuseScheduleOfCapacity
#print axioms nonempty_singleRunBoundedReuseSchedule_iff
#print axioms obligations_le_transitions_mul_thermodynamicEnergy
#print axioms nonempty_freeThermodynamicReuseSchedule_iff
#print axioms freeThermodynamicFullAmortization
#print axioms no_informationBoundedReuseCharge_of_information_lt_reuse
#print axioms thermodynamicReuseCharge_must_exceed_information
#print axioms obligations_le_transitions_mul_hubFanIn
#print axioms obligations_le_transitions_mul_hubReachBudget
#print axioms hubGroundedReuseSchedule_of_freeReach
#print axioms obligations_le_DTM_local_spacetime_capacity
#print axioms no_DTMLocalHubReuseSchedule_of_quadratic_gap
#print axioms DTMLocalHubReuseSchedule_of_capacity
#print axioms timeSteps_mul_succ_le_nextPolynomial
#print axioms no_DTMDecidesSAT_of_singleLocalHubExtraction
#print axioms singleLocalHubExtraction_of_no_DTMDecidesSAT
#print axioms singleLocalHubExtraction_iff_no_DTMDecidesSAT
#print axioms distributedLocalHubEventCharge_injective
#print axioms obligations_le_distributed_local_spacetime
#print axioms distributed_local_spacetime_bound_is_automatic
#print axioms thermodynamicLocalityAuditVerdict
#print axioms thermodynamicObserverFrontier_iff_no_DTMDecidesSAT
#print axioms restrictedCircuitSATSharingBoundary
#print axioms restrictedCircuitSharingDemand_le_linear
#print axioms pointwiseScaleCharge_not_additive
#print axioms failure_of_branch_doubling_forces_share_gt_fresh
#print axioms failure_of_fresh_directSum_forces_nonlinear_net_saving
#print axioms branch_doubling_failure_has_nonlinearThermodynamicEscape
#print axioms branch_doubling_of_no_nonlinearThermodynamicEscape
#print axioms branch_doubling_or_nonlinearThermodynamicEscape
#print axioms nonlinearThermodynamicEscape_does_not_force_doubling_failure
#print axioms finiteFreshnessChecks_do_not_imply_uniformFreshness
#print axioms booleanRestrictionProfile_capacity
#print axioms booleanRestrictionProfile_capacity_of_reconstruction
#print axioms pairedBooleanRestrictionProfile_capacity
#print axioms sat3AggregateRestrictionProfile_capacity
#print axioms siblingBooleanRestrictionProfile_capacity
#print axioms sat3SiblingRestrictionProfile_capacity
#print axioms siblingProfileCapacity_cashout
#print axioms sat3SiblingRestrictionProfile_coneExcess
#print axioms siblingProfileCashout_does_not_force_childDoubling
#print axioms childDoubling_of_coneExcess_le_profileDimension
#print axioms childDoubling_or_profileIncompressibilityGap
#print axioms profileLowerBound_does_not_close_childDoubling
#print axioms childRecurrence_deficit_eq_profileGap
#print axioms profileGap_absorbed_by_fresh_gives_childDoubling
#print axioms childDoubling_failure_forces_profileGap_overrun
#print axioms profileGapAbsorption_gives_allScalesDoubling
#print axioms allScalesDoubling_amplifies_base
#print axioms allScalesDoubling_or_exists_profileGapOverrun
#print axioms profileGapMargin_amplifies
#print axioms recurrenceMargin_failure_forces_profileGapBudgetOverrun
#print axioms allScalesMarginRecurrence_or_exists_budgetOverrun
#print axioms childRecurrence_deficit_le_min_share_profileGap
#print axioms hybridDeficitMargin_gives_childRecurrence
#print axioms hybridShareProfileMargin_amplifies
#print axioms childRecurrence_failure_forces_hybridBudgetOverrun
#print axioms childRecurrence_or_hybridBudgetOverrun
#print axioms allScalesHybridRecurrence_or_exists_budgetOverrun
#print axioms hybridBudgetOverrun_iff_simultaneous
#print axioms childRecurrence_failure_has_simultaneousHybridEscape
#print axioms childRecurrence_of_no_simultaneousHybridEscape
#print axioms noSimultaneousHybridEscape_amplifies
#print axioms simultaneousHybridEscape_is_arithmetically_consistent
#print axioms formulaFreshness_with_disjointMixer_gives_recurrence
#print axioms noCancellationFreshness_with_disjointMixer_gives_recurrence
#print axioms noNetSaving_gives_hybridRecurrence
#print axioms childRecurrence_failure_forces_genuineNonlinearCancellation
#print axioms childRecurrence_or_genuineNonlinearCancellation
#print axioms childRecurrence_deficit_le_min_cancellationExcess
#print axioms cancellationExcessMargin_gives_childRecurrence
#print axioms childRecurrence_failure_forces_cancellationBudgetOverrun
#print axioms cancellationExcessMargin_amplifies
#print axioms allScalesCancellationRecurrence_or_exists_budgetOverrun
#print axioms childRecurrence_deficit_le_min_cancellation_profileGap
#print axioms cancellationProfileMargin_gives_childRecurrence
#print axioms cancellationProfileMargin_amplifies
#print axioms tripleBudgetOverrun_iff_escape
#print axioms childRecurrence_failure_has_tripleNonlinearSATEscape
#print axioms childRecurrence_of_no_tripleNonlinearSATEscape
#print axioms noTripleNonlinearSATEscape_amplifies
#print axioms tripleNonlinearSATEscape_is_arithmetically_consistent
#print axioms offDiagonalRow_card
#print axioms offDiagonalRow_pair_codegree
#print axioms offDiagonalThree_dense_without_two_by_two_rectangle
#print axioms AffineRectangleObstruction.no_two_by_two
#print axioms AffineRectangleObstruction.common_point_unique
#print axioms AffineRectangleObstruction.incidences_card
#print axioms AffineRectangleObstruction.mem_incidences_iff
#print axioms transitionChargingAuditVerdict
#print axioms nframeTransitionChargingAuditVerdict

end PallLean.Paper93.DeepMath.PathB.ObserverCentricNFrameActionBridge
