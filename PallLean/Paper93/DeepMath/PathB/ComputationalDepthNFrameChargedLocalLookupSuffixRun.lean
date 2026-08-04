import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupSuffixAdapter

/-!
# Charged local lookup: complete suffix-run transport

The suffix adapter's local theorem is lifted here to an arbitrary finite body
run.  The only hypothesis is an explicit path predicate saying that every
executed body step is nonhalting, reset-free, does not move left from relative
head zero, and writes only at an existing body-tape cell.

The result is then specialized to the repository's canonical literal lookup.
Once the canonical `masterM` path satisfies this predicate, the adapter runs
the complete lookup behind every marked repeat-controller countdown, preserves
that prefix, halts, and returns the proved literal truth value.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinInP
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinWholeRun
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice (cntT)
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixAdapter

/-! ## Exact path discipline -/

/-- The local conditions needed to translate one body step past a protected
prefix.  Each field corresponds exactly to a hypothesis of
`suffixAdapter_step_body`. -/
structure PrefixSafeStep (M : Machine) (c : Cfg M) : Prop where
  notHalted : M.halt c.st = false
  noReset : (M.δ c.st (c.tp.getD c.hd false)).2.2 ≠ 3
  leftInside : (M.δ c.st (c.tp.getD c.hd false)).2.2 = 0 → 0 < c.hd
  writeInside : (M.δ c.st (c.tp.getD c.hd false)).2.1 ≠ none →
    c.hd < c.tp.length

/-- Every actually executed step among the first `n` body transitions is
prefix-safe. -/
def PrefixSafeRun (M : Machine) (c : Cfg M) (n : Nat) : Prop :=
  ∀ i, i < n → PrefixSafeStep M (run M i c)

theorem prefixSafeRun_mono {M : Machine} {c : Cfg M} {m n : Nat}
    (h : PrefixSafeRun M c n) (hmn : m ≤ n) :
    PrefixSafeRun M c m := by
  intro i hi
  exact h i (by omega)

/-! ## Whole-run transport -/

/-- A complete prefix-safe body run commutes with suffix embedding. -/
theorem suffixAdapter_run_body (M : Machine) (pre : List Bool)
    (c : Cfg M) (n : Nat) (hsafe : PrefixSafeRun M c n) :
    run (suffixAdapter M) n (embedSuffix M pre c) =
      embedSuffix M pre (run M n c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [run_succ, ih (prefixSafeRun_mono hsafe (by omega))]
      have hs := hsafe n (by omega)
      simpa only [run_succ] using
        suffixAdapter_step_body M pre (run M n c)
          hs.notHalted hs.noReset hs.leftInside hs.writeInside

/-- Scan a marked controller countdown and then execute the complete protected
body run on its suffix. -/
theorem suffixAdapter_run_cntT_body (M : Machine) (B j : Nat)
    (hj : j ≤ B) (tail : List Bool) (n : Nat)
    (hsafe : PrefixSafeRun M (init M tail) n) :
    run (suffixAdapter M) (2 * B + 3 + n)
        (init (suffixAdapter M) (cntT B j ++ tail)) =
      embedSuffix M (cntT B j) (run M n (init M tail)) := by
  rw [run_add, suffixAdapter_enter_cntT M B j hj tail]
  change run (suffixAdapter M) n
      (embedSuffix M (cntT B j) (init M tail)) = _
  exact suffixAdapter_run_body M (cntT B j) (init M tail) n hsafe

/-- In particular, the final adapter tape is the untouched controller prefix
followed by the exact body machine's final tape. -/
theorem suffixAdapter_run_cntT_tape (M : Machine) (B j : Nat)
    (hj : j ≤ B) (tail : List Bool) (n : Nat)
    (hsafe : PrefixSafeRun M (init M tail) n) :
    (run (suffixAdapter M) (2 * B + 3 + n)
        (init (suffixAdapter M) (cntT B j ++ tail))).tp =
      cntT B j ++ (run M n (init M tail)).tp := by
  rw [suffixAdapter_run_cntT_body M B j hj tail n hsafe]
  rfl

/-! ## Canonical literal lookup specialization -/

def literalLookupClock (w : List Bool) (l : Lit) : Nat :=
  2 * (l.1 + 1) + 2 + 1 +
    (clockSum l.1 (signedLookupAssignment w l.1 l.2).length + 7)

/-- The single remaining operational property of the already-verified
canonical lookup execution. -/
def MasterLiteralPrefixSafe (w : List Bool) (l : Lit) : Prop :=
  PrefixSafeRun masterM (init masterM (literalLookupTape w l))
    (literalLookupClock w l)

/-- Under the exact canonical-path safety property, the protected adapter
performs the entire literal lookup behind any marked controller prefix, halts,
and returns the correct signed literal value. -/
theorem suffixAdapter_masterM_reads_literal (B j : Nat) (hj : j ≤ B)
    (w : List Bool) (l : Lit) (hsafe : MasterLiteralPrefixSafe w l) :
    HaltsBy (suffixAdapter masterM)
        (cntT B j ++ literalLookupTape w l)
        (2 * B + 3 + literalLookupClock w l) ∧
      decideOut (suffixAdapter masterM)
        (cntT B j ++ literalLookupTape w l)
        (2 * B + 3 + literalLookupClock w l) =
          evalLit (fun k => w.getD k false) l := by
  have hrun := suffixAdapter_run_cntT_body masterM B j hj
    (literalLookupTape w l) (literalLookupClock w l) hsafe
  have hmaster := masterM_reads_literal w l
  change
    (suffixAdapter masterM).halt
        (run (suffixAdapter masterM) (2 * B + 3 + literalLookupClock w l)
          (init (suffixAdapter masterM)
            (cntT B j ++ literalLookupTape w l))).st = true ∧
      (suffixAdapter masterM).accept
        (run (suffixAdapter masterM) (2 * B + 3 + literalLookupClock w l)
          (init (suffixAdapter masterM)
            (cntT B j ++ literalLookupTape w l))).st =
          evalLit (fun k => w.getD k false) l
  rw [hrun]
  change
    masterM.halt
        (run masterM (literalLookupClock w l)
          (init masterM (literalLookupTape w l))).st = true ∧
      masterM.accept
        (run masterM (literalLookupClock w l)
          (init masterM (literalLookupTape w l))).st =
          evalLit (fun k => w.getD k false) l
  simpa only [literalLookupClock] using hmaster

/-- `masterM`'s reset obligation is already unconditional; canonical path
safety consists only of the nonhalting-prefix, left-boundary, and write-range
facts. -/
theorem masterLiteral_noReset (w : List Bool) (l : Lit) (i : Nat) :
    (masterM.δ
      (run masterM i (init masterM (literalLookupTape w l))).st
      ((run masterM i (init masterM (literalLookupTape w l))).tp.getD
        (run masterM i (init masterM (literalLookupTape w l))).hd false)).2.2 ≠ 3 :=
  masterM_reset_free _ _

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun.prefixSafeRun_mono
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun.suffixAdapter_run_body
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun.suffixAdapter_run_cntT_body
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun.suffixAdapter_run_cntT_tape
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun.suffixAdapter_masterM_reads_literal
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun.masterLiteral_noReset
