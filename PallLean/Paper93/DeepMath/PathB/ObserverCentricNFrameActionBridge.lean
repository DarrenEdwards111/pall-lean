import PallLean.Paper93.DeepMath.PathB.ObserverTrajectoryDCEW
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverTimeDebt

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

/-- A trajectory has an N-frame action certificate at length `n` when it has a
live minor together with honest observer-time debt servicing data. -/
def HasTrajectoryNFrameActionCertificateAt
    (enc : ThreeCNFEncoding) (T : TrajectoryObserverMachine) (n : Nat) : Prop :=
  ∃ minor : TrajectoryGodMoveBoundaryMinor enc T n,
    Nonempty (TrajectoryNFrameActionCertificate minor)

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
#print axioms binomial_le_action
#print axioms action_gt_polynomial_of_certificate
#print axioms operationalSAT_action_lower_of_nframe_extraction

end PallLean.Paper93.DeepMath.PathB.ObserverCentricNFrameActionBridge
