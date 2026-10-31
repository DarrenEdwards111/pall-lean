import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupSuffixCanonical

/-!
# Charged local lookup: materialize the returned truth bit

`returnBitMachine M` executes `M`, then performs one finite-control handoff
that writes `M`'s accepting bit at the halted head position.  The wrapper
itself halts with that same bit in its state and accepting output.

The exact-clock theorem does not assume that the supplied body clock is the
first halting time.  As with the repository's sequence and repeat
combinators, a least-halt argument executes the handoff at the first halt and
uses halted-step freezing to absorb the remaining budget.

Specializing to the protected canonical lookup turns the formerly
state-internal literal value into an actual tape bit for every live decoded
schedule index.  Moving that bit into a reserved doubled output region and
staging the next lookup remain separate local passes.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupReturnBit

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice (cntT)
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixAdapter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixCanonical

/-! ## Generic accepting-bit return wrapper -/

/-- Run `M`; at its first halt, write its accepting bit under the current
head and halt with that bit retained in finite control. -/
def returnBitMachine (M : Machine) : Machine where
  State := M.State ⊕ Bool
  fin := inferInstance
  dec := inferInstance
  start := Sum.inl M.start
  halt := fun s => match s with
    | .inl _ => false
    | .inr _ => true
  δ := fun s b => match s with
    | .inl sm =>
        if M.halt sm then
          (Sum.inr (M.accept sm), some (M.accept sm), 2)
        else
          let tr := M.δ sm b
          (Sum.inl tr.1, tr.2.1, tr.2.2)
    | .inr bv => (Sum.inr bv, none, 2)
  accept := fun s => match s with
    | .inl sm => M.accept sm
    | .inr bv => bv

def embedReturnBody (M : Machine) (c : Cfg M) : Cfg (returnBitMachine M) :=
  ⟨Sum.inl c.st, c.hd, c.tp⟩

@[simp] theorem returnBit_halt_done (M : Machine) (bv : Bool) :
    (returnBitMachine M).halt (Sum.inr bv) = true := rfl

theorem returnBit_step_body (M : Machine) (c : Cfg M)
    (hh : M.halt c.st = false) :
    step (returnBitMachine M) (embedReturnBody M c) =
      embedReturnBody M (step M c) := by
  simp only [step, returnBitMachine, embedReturnBody, hh,
    Bool.false_eq_true, ↓reduceIte]

theorem returnBit_step_capture (M : Machine) (c : Cfg M)
    (hh : M.halt c.st = true) :
    step (returnBitMachine M) (embedReturnBody M c) =
      ⟨Sum.inr (M.accept c.st), c.hd,
        writeAt c.tp c.hd (M.accept c.st)⟩ := by
  simp [step, returnBitMachine, embedReturnBody, hh, moveHead]

theorem returnBit_run_body (M : Machine) (c : Cfg M) (n : Nat)
    (hactive : ∀ i, i < n → M.halt (run M i c).st = false) :
    run (returnBitMachine M) n (embedReturnBody M c) =
      embedReturnBody M (run M n c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [run_succ, ih (fun i hi => hactive i (by omega)),
        returnBit_step_body M _ (hactive n (by omega)), ← run_succ]

/-- At any valid halting budget, the wrapper materializes the body's accepting
bit in one additional step.  Earlier body halting is absorbed exactly. -/
theorem returnBit_run (M : Machine) (T : List Bool) (n : Nat)
    (hh : M.halt (run M n (init M T)).st = true) :
    run (returnBitMachine M) (n + 1) (init (returnBitMachine M) T) =
      ⟨Sum.inr (M.accept (run M n (init M T)).st),
        (run M n (init M T)).hd,
        writeAt (run M n (init M T)).tp
          (run M n (init M T)).hd
          (M.accept (run M n (init M T)).st)⟩ := by
  let c0 := init M T
  let cf := run M n c0
  have hex : ∃ i, M.halt (run M i c0).st = true := ⟨n, hh⟩
  have hfirst : M.halt (run M (Nat.find hex) c0).st = true :=
    Nat.find_spec hex
  have hfirst_le : Nat.find hex ≤ n := Nat.find_le hh
  have hfrozen : run M (Nat.find hex) c0 = cf := by
    dsimp only [cf, c0]
    rw [← run_stable M T hfirst_le hfirst]
  have hactive : ∀ i, i < Nat.find hex →
      M.halt (run M i c0).st = false := by
    intro i hi
    simpa using Nat.find_min hex hi
  have hbody := returnBit_run_body M c0 (Nat.find hex) hactive
  rw [hfrozen] at hbody
  have hcapture := returnBit_step_capture M cf (by simpa [cf] using hh)
  change run (returnBitMachine M) (n + 1)
      (embedReturnBody M c0) = _
  rw [show n + 1 = Nat.find hex + (1 + (n - Nat.find hex)) by omega,
    run_add, hbody, run_add, run_succ, run_zero, hcapture,
    run_of_halted (returnBitMachine M) (returnBit_halt_done M _)]

/-! ## Canonical protected lookup specialization -/

/-- Exact protected lookup plus accepting-bit materialization clock. -/
def returnedLookupRoundClock (x w : List Bool) (t : Nat) : Nat :=
  protectedLookupRoundClock x w t + 1

theorem returnedLookupRoundClock_le (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length) :
    returnedLookupRoundClock x w t ≤ 206 * (x.length + 1) ^ 2 := by
  have h := protectedLookupRoundClock_le x w ht
  simp only [returnedLookupRoundClock]
  nlinarith [Nat.one_le_pow 2 (x.length + 1) (by omega)]

/-- A protected lookup followed by the return handoff halts with the correct
literal value both in finite control and written at the protected lookup's
final head position. -/
theorem returnBit_scheduled_lookup (x w : List Bool) (t : Nat)
    (ht : t < (decodedLiterals x).length) :
    let T := cntT (decodedLiterals x).length (t + 1) ++
      literalLookupTape w (scheduledLiteral x t)
    let n := protectedLookupRoundClock x w t
    let cf := run (suffixAdapter masterM) n
      (init (suffixAdapter masterM) T)
    run (returnBitMachine (suffixAdapter masterM)) (n + 1)
        (init (returnBitMachine (suffixAdapter masterM)) T) =
      ⟨Sum.inr (evalLit (fun k => w.getD k false)
          (scheduledLiteral x t)),
        cf.hd,
        writeAt cf.tp cf.hd
          (evalLit (fun k => w.getD k false) (scheduledLiteral x t))⟩ := by
  dsimp only
  have hs := scheduled_suffixAdapter_reads_literal x w t ht
  have hr := returnBit_run (suffixAdapter masterM)
    (cntT (decodedLiterals x).length (t + 1) ++
      literalLookupTape w (scheduledLiteral x t))
    (protectedLookupRoundClock x w t) hs.1
  have hout := hs.2
  change (suffixAdapter masterM).accept
      (run (suffixAdapter masterM) (protectedLookupRoundClock x w t)
        (init (suffixAdapter masterM)
          (cntT (decodedLiterals x).length (t + 1) ++
            literalLookupTape w (scheduledLiteral x t)))).st = _ at hout
  rw [← hout]
  exact hr

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupReturnBit

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupReturnBit.returnBit_run_body
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupReturnBit.returnBit_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupReturnBit.returnedLookupRoundClock_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupReturnBit.returnBit_scheduled_lookup
