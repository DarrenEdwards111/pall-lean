import PallLean.Paper93.DeepMath.PathB.ObserverTrajectoryDCEW
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverTimeDebt
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFoolingDebt
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderNoHiding
import PallLean.Paper93.DeepMath.PathB.OperationalZeroBoundaryObstruction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUCRDTseitinBoundedReuse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthThermodynamicObserver

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
#print axioms transitionChargingAuditVerdict
#print axioms nframeTransitionChargingAuditVerdict

end PallLean.Paper93.DeepMath.PathB.ObserverCentricNFrameActionBridge
