import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBranchSpanningDynamicHolonomy
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDynamicSPDPObserverLocalRouteG

/-!
# A dynamic boundary link between the P observer and NP residual observer

This file formalizes the precise version of the two-observer idea that remains
comparable.  The P computation and NP residual computation may be different actual
runs, but their projections land in one finite `BoundaryState` belonging to one
observer frame.  The P-side dynamic profile bounds that carrier.  The NP-side
projection is evaluated across a residual family at a real execution time.

This avoids comparing unrelated ranks.  It also exposes the load-bearing condition:
the NP projection must preserve injective semantic residual labels.  Boolean-only
decision observations cannot do so on two or more branch bits.

The resulting inequality beam is valid, but it does not manufacture the boundary
link from `P = NP`.  Constructing that link and proving residual soundness solely
from a hypothetical polynomial solver remains Route G's frontier.
-/

namespace PallLean.Paper93.DeepMath.PathB.DynamicObserverBoundaryLink

open PvsNPRunIndexedFaithfulTPhi
open PvsNPRunIndexedFaithfulTPhi.ActualDecisionRun
open PvsNPTranscriptObserver
open PvsNPBoundedLocalAccessCompiler
open PvsNPDynamicSPDPGlobalGodMove
open BranchSpanningDynamicHolonomy

variable {PInput PState NPState : Type*}

/-- A shared dynamic observer boundary linking one P-side run to one NP residual
family.  Both projections land in exactly the same finite boundary carrier.

`boundary_card_le_finalP` is the P-side operational accounting theorem.
`npSound` is the separate NP-side semantic obligation; it is deliberately visible. -/
structure DynamicBoundaryLink
    (P : BoundedLocalAccessProfile) (n m : ℕ)
    (pRun : ActualDecisionRun PInput PState)
    (pBound : ProfileBoundedDynamicGodMove P n pRun)
    (npRun : ActualDecisionRun ResidualInstance NPState)
    (fam : FoolingResidualFamily m) where
  BoundaryState : Type
  [boundaryFintype : Fintype BoundaryState]
  [boundaryDecidableEq : DecidableEq BoundaryState]
  pInput : PInput
  pProject : PState → BoundaryState
  npProject : NPState → BoundaryState
  npTime : ℕ
  npTime_le : npTime ≤ npRun.steps
  boundary_card_le_finalP :
    Fintype.card BoundaryState ≤
      pBound.observer.boundaryRank pRun.steps pInput
  npSound : SoundOnFoolingFamily
    (fun inst => npProject (npRun.stateAt npTime inst)) fam

namespace DynamicBoundaryLink

/-- The NP observer's branch-spanning rank is exactly exponential when the shared
boundary link carries the certified residual labels. -/
theorem np_holonomyRank_eq_two_pow
    {P : BoundedLocalAccessProfile} {n m : ℕ}
    {pRun : ActualDecisionRun PInput PState}
    {pBound : ProfileBoundedDynamicGodMove P n pRun}
    {npRun : ActualDecisionRun ResidualInstance NPState}
    {fam : FoolingResidualFamily m}
    (L : DynamicBoundaryLink P n m pRun pBound npRun fam) :
    residualFamilyHolonomyRankAt npRun fam L.npProject L.npTime = 2 ^ m := by
  letI : Fintype L.BoundaryState := L.boundaryFintype
  letI : DecidableEq L.BoundaryState := L.boundaryDecidableEq
  exact residualFamilyHolonomyRankAt_eq_two_pow_of_sound
    npRun fam L.npProject L.npTime L.npSound

/-- Same-frame dynamic observer chain:

`2^m ≤ shared boundary ≤ final P boundary ≤ exposed P rank`.
-/
theorem two_pow_le_exposedRank
    {P : BoundedLocalAccessProfile} {n m : ℕ}
    {pRun : ActualDecisionRun PInput PState}
    {pBound : ProfileBoundedDynamicGodMove P n pRun}
    {npRun : ActualDecisionRun ResidualInstance NPState}
    {fam : FoolingResidualFamily m}
    (L : DynamicBoundaryLink P n m pRun pBound npRun fam) :
    2 ^ m ≤ P.exposedRank n := by
  letI : Fintype L.BoundaryState := L.boundaryFintype
  letI : DecidableEq L.BoundaryState := L.boundaryDecidableEq
  have hnp : 2 ^ m ≤ Fintype.card L.BoundaryState :=
    transcript_boundary_card_ge_exp_of_fooling
      (fun inst => L.npProject (npRun.stateAt L.npTime inst)) fam L.npSound
  exact le_trans hnp <| le_trans L.boundary_card_le_finalP
    (pBound.finalBoundary_le L.pInput)

/-- Above the exposed-rank gap, no such dynamically shared P/NP observer boundary
can exist.  This is an audit theorem, not a construction of the missing link. -/
theorem no_link_above_exposedRank
    {P : BoundedLocalAccessProfile} {n m : ℕ}
    {pRun : ActualDecisionRun PInput PState}
    {pBound : ProfileBoundedDynamicGodMove P n pRun}
    {npRun : ActualDecisionRun ResidualInstance NPState}
    {fam : FoolingResidualFamily m}
    (hgap : P.exposedRank n < 2 ^ m) :
    ¬ Nonempty (DynamicBoundaryLink P n m pRun pBound npRun fam) := by
  rintro ⟨L⟩
  exact (not_lt_of_ge L.two_pow_le_exposedRank) hgap

/-! ## Easy-family / Boolean-observer guardrail -/

/-- If the NP projection on the residual family factors through the final Boolean
answer, its family image rank is at most two. -/
theorem np_family_rank_le_two_of_decision_factored
    {P : BoundedLocalAccessProfile} {n m : ℕ}
    {pRun : ActualDecisionRun PInput PState}
    {pBound : ProfileBoundedDynamicGodMove P n pRun}
    {npRun : ActualDecisionRun ResidualInstance NPState}
    {fam : FoolingResidualFamily m}
    (L : DynamicBoundaryLink P n m pRun pBound npRun fam)
    (post : Bool → L.BoundaryState)
    (hfactor : ∀ inst,
      L.npProject (npRun.stateAt L.npTime inst) = post (npRun.finalAnswer inst)) :
    residualFamilyHolonomyRankAt npRun fam L.npProject L.npTime ≤ 2 := by
  let feature := fun a : Fin m → Bool =>
    L.npProject (npRun.stateAt L.npTime (fam.instanceOf a))
  have hfeature : feature = fun a => post (npRun.finalAnswer (fam.instanceOf a)) := by
    funext a
    exact hfactor (fam.instanceOf a)
  rw [residualFamilyHolonomyRankAt]
  change familyImageRank feature ≤ 2
  rw [hfeature]
  exact le_trans
    (familyImageRank_comp_le
      (fun a => npRun.finalAnswer (fam.instanceOf a)) post)
    (by simpa using familyImageRank_le_domain_card post)

/-- A Boolean-only NP observer cannot also preserve an injective `m`-bit residual
label family once `m ≥ 2`.  This rejects the full-AND-style false positive. -/
theorem not_decision_factored_of_two_le
    {P : BoundedLocalAccessProfile} {n m : ℕ}
    {pRun : ActualDecisionRun PInput PState}
    {pBound : ProfileBoundedDynamicGodMove P n pRun}
    {npRun : ActualDecisionRun ResidualInstance NPState}
    {fam : FoolingResidualFamily m}
    (L : DynamicBoundaryLink P n m pRun pBound npRun fam)
    (hm : 2 ≤ m) :
    ¬ ∃ post : Bool → L.BoundaryState, ∀ inst,
      L.npProject (npRun.stateAt L.npTime inst) = post (npRun.finalAnswer inst) := by
  rintro ⟨post, hfactor⟩
  have hlo : residualFamilyHolonomyRankAt
      npRun fam L.npProject L.npTime ≤ 2 :=
    L.np_family_rank_le_two_of_decision_factored post hfactor
  have hhi := L.np_holonomyRank_eq_two_pow
  have hfour : 4 ≤ 2 ^ m := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) hm
  omega

end DynamicBoundaryLink

/-!
The observer-boundary idea therefore works as a rigorously comparable inequality
beam.  It does not yet close Route G: deriving a `DynamicBoundaryLink` from a
hypothetical P-time solver would have to construct the common carrier and prove
`npSound` without using the exponential lower bound or the desired separation.
-/

end PallLean.Paper93.DeepMath.PathB.DynamicObserverBoundaryLink

#print axioms PallLean.Paper93.DeepMath.PathB.DynamicObserverBoundaryLink.DynamicBoundaryLink.two_pow_le_exposedRank
#print axioms PallLean.Paper93.DeepMath.PathB.DynamicObserverBoundaryLink.DynamicBoundaryLink.no_link_above_exposedRank
#print axioms PallLean.Paper93.DeepMath.PathB.DynamicObserverBoundaryLink.DynamicBoundaryLink.not_decision_factored_of_two_le
