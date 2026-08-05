import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupLeftBoundaryRoundInvariant
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinInP

/-!
# Charged local lookup: whole-run left-boundary safety

Invariant-level round safety is iterated over `clockSum`, followed by the
terminal branch and preceded by INIT.  The endpoint is the concrete canonical
`MasterLiteralLeftSafe` required by the protected suffix adapter.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryWholeRun

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinRoundInvariant
open PallLean.Paper93.DeepMath.PathB.CookLevinWholeRun
open PallLean.Paper93.DeepMath.PathB.CookLevinInP
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryInit
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryRoundInvariant

/-- All live counter-present rounds are safe, at the exact accumulated clock. -/
theorem clockSum_leftSafe (v : Nat) : ∀ (T : List Bool) (D : Nat),
    v ≤ D → RoundInv T v D →
    LeftSafeRun masterM ⟨(1, 0, false, false), 2 * v + 2, T⟩
      (clockSum v D) := by
  induction v with
  | zero =>
      intro T D _ _
      simp [clockSum, LeftSafeRun]
  | succ v ih =>
      intro T D hv h
      have hD : 1 ≤ D := by omega
      have hs := roundInv_step_leftSafe T (v + 1) D (by omega) hD h
      obtain ⟨T1, hrun, hinv, _⟩ :=
        roundInv_round T (v + 1) D (by omega) hD h
      have htail := ih T1 (D - 1) (by omega) hinv
      change LeftSafeRun masterM
        ⟨(1, 0, false, false), 2 * (v + 1) + 2, T⟩
        (roundClock D + clockSum v (D - 1))
      apply leftSafeRun_add
      · simpa [roundClock] using hs
      · rw [show run masterM (roundClock D)
            ⟨(1, 0, false, false), 2 * (v + 1) + 2, T⟩ =
            ⟨(1, 0, false, false), 2 * v + 2, T1⟩ by
          simpa [roundClock] using hrun]
        exact htail

/-- The live rounds followed by the seven-step empty-counter terminal branch
are safe from the round-start configuration. -/
theorem roundStartWholeRun_leftSafe (v : Nat) (T : List Bool) (D : Nat)
    (hv : v ≤ D) (h : RoundInv T v D) :
    LeftSafeRun masterM ⟨(1, 0, false, false), 2 * v + 2, T⟩
      (clockSum v D + 7) := by
  obtain ⟨T', hrun, hinv, _⟩ := rounds v T D hv h
  apply leftSafeRun_add (clockSum_leftSafe v T D hv h)
  rw [hrun]
  exact tailRead_leftSafe (by omega) (by simpa using hinv.lsent)

/-- INIT, all live rounds, and the terminal branch are safe from the forced
initial configuration. -/
theorem fullRun_leftSafe (T : List Bool) (v D : Nat)
    (hv : v ≤ D) (h : RoundInv T v D) :
    LeftSafeRun masterM ⟨(0, 0, false, false), 0, T⟩
      (2 * (v + 1) + 2 + 1 + (clockSum v D + 7)) := by
  apply leftSafeRun_add (a := 2 * (v + 1) + 2 + 1)
    (b := clockSum v D + 7)
  · exact initPhase_leftSafe T v D h
  · rw [init_phase T v D h]
    exact roundStartWholeRun_leftSafe v T D hv h

/-- The canonical signed literal lookup satisfies the sole remaining path
condition required by suffix transport. -/
theorem masterLiteralLeftSafe (w : List Bool) (l : Lit) :
    MasterLiteralLeftSafe w l := by
  let A := signedLookupAssignment w l.1 l.2
  have hlen : A.length = l.1 + 1 := signedLookupAssignment_length _ _ _
  have hv : l.1 ≤ A.length := by omega
  have hInv : RoundInv (literalLookupTape w l) l.1 A.length := by
    simpa [literalLookupTape, A] using encode_roundInv A l.1
  have hsafe := fullRun_leftSafe (literalLookupTape w l) l.1 A.length hv hInv
  simpa [MasterLiteralLeftSafe, literalLookupClock, literalLookupTape,
    master_forced_init, A] using hsafe

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryWholeRun

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryWholeRun.clockSum_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryWholeRun.fullRun_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryWholeRun.masterLiteralLeftSafe
