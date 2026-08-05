import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupLeftBoundaryWholeRun

/-!
# Charged local lookup: unconditional protected suffix execution

The canonical whole-run left-boundary theorem is applied to the suffix
adapter here.  Consequently a marked repeat-controller prefix can protect a
complete `masterM` literal lookup with no remaining path hypothesis.

Besides the Boolean result, the exact configuration and tape transport are
retained.  The final scheduled specialization is the interface needed by a
subsequent return/staging pass: at every live schedule index the adapter
halts, preserves the marked countdown byte-for-byte, and exposes the correct
literal value through its accepting state.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixCanonical

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice (cntT)
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixAdapter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryWholeRun

theorem literalLookupClock_eq_cost (w : List Bool) (l : Lit) :
    literalLookupClock w l = literalLookupCost w l := by
  rfl

/-- Exact body clock after including the protected-prefix scan. -/
def protectedLookupRoundClock (x w : List Bool) (t : Nat) : Nat :=
  2 * (decodedLiterals x).length + 3 + lookupRoundClock x w t

theorem protectedLookupRoundClock_le (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length) :
    protectedLookupRoundClock x w t ≤ 205 * (x.length + 1) ^ 2 := by
  have hB0 := decodedLiterals_length_le x
  have hB : (decodedLiterals x).length ≤ (x.length + 1) ^ 2 := by
    nlinarith [Nat.zero_le x.length]
  have hclk := lookupRoundClock_le x w ht
  simp only [protectedLookupRoundClock]
  nlinarith [Nat.one_le_pow 2 (x.length + 1) (by omega)]

/-- Exact unconditional configuration transport for a canonical protected
literal lookup. -/
theorem suffixAdapter_masterM_run_canonical
    (B j : Nat) (hj : j ≤ B) (w : List Bool) (l : Lit) :
    run (suffixAdapter masterM) (2 * B + 3 + literalLookupClock w l)
        (init (suffixAdapter masterM)
          (cntT B j ++ literalLookupTape w l)) =
      embedSuffix masterM (cntT B j)
        (run masterM (literalLookupClock w l)
          (init masterM (literalLookupTape w l))) := by
  exact suffixAdapter_run_cntT_body masterM B j hj
    (literalLookupTape w l) (literalLookupClock w l)
    ((masterLiteralPrefixSafe_iff_leftSafe w l).2
      (masterLiteralLeftSafe w l))

/-- The complete protected run leaves the controller prefix byte-for-byte
unchanged. -/
theorem suffixAdapter_masterM_tape_canonical
    (B j : Nat) (hj : j ≤ B) (w : List Bool) (l : Lit) :
    (run (suffixAdapter masterM) (2 * B + 3 + literalLookupClock w l)
        (init (suffixAdapter masterM)
          (cntT B j ++ literalLookupTape w l))).tp =
      cntT B j ++
        (run masterM (literalLookupClock w l)
          (init masterM (literalLookupTape w l))).tp := by
  exact suffixAdapter_run_cntT_tape masterM B j hj
    (literalLookupTape w l) (literalLookupClock w l)
    ((masterLiteralPrefixSafe_iff_leftSafe w l).2
      (masterLiteralLeftSafe w l))

/-- The former conditional suffix theorem, now discharged for every canonical
literal lookup. -/
theorem suffixAdapter_masterM_reads_literal_canonical
    (B j : Nat) (hj : j ≤ B) (w : List Bool) (l : Lit) :
    HaltsBy (suffixAdapter masterM)
        (cntT B j ++ literalLookupTape w l)
        (2 * B + 3 + literalLookupClock w l) ∧
      decideOut (suffixAdapter masterM)
        (cntT B j ++ literalLookupTape w l)
        (2 * B + 3 + literalLookupClock w l) =
          evalLit (fun k => w.getD k false) l := by
  exact suffixAdapter_masterM_reads_literal_of_leftSafe B j hj w l
    (masterLiteralLeftSafe w l)

/-- Every live decoded-literal schedule index has an unconditional protected
lookup run at the exact runtime-indexed clock. -/
theorem scheduled_suffixAdapter_reads_literal (x w : List Bool) (t : Nat)
    (ht : t < (decodedLiterals x).length) :
    HaltsBy (suffixAdapter masterM)
        (cntT (decodedLiterals x).length (t + 1) ++
          literalLookupTape w (scheduledLiteral x t))
        (protectedLookupRoundClock x w t) ∧
      decideOut (suffixAdapter masterM)
        (cntT (decodedLiterals x).length (t + 1) ++
          literalLookupTape w (scheduledLiteral x t))
        (protectedLookupRoundClock x w t) =
          evalLit (fun k => w.getD k false) (scheduledLiteral x t) := by
  simpa only [protectedLookupRoundClock, lookupRoundClock,
    literalLookupClock_eq_cost] using
    suffixAdapter_masterM_reads_literal_canonical
      (decodedLiterals x).length (t + 1) (by omega) w
      (scheduledLiteral x t)

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixCanonical

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixCanonical.suffixAdapter_masterM_run_canonical
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixCanonical.suffixAdapter_masterM_tape_canonical
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixCanonical.suffixAdapter_masterM_reads_literal_canonical
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixCanonical.protectedLookupRoundClock_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixCanonical.scheduled_suffixAdapter_reads_literal
