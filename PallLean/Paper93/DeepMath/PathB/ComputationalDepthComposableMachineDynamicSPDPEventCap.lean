import PallLean.Paper93.DeepMath.PathB.ComputationalDepthComposableMachine
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDynamicSPDPEmissionBudget

/-!
# Physical one-step event cap for composable machines

`ComposableMachine.step` performs one finite-control transition and contains at
most one optional tape write.  This file turns a real run of such a machine into
an `ActualDecisionRun`, defines the corresponding write-local positive dynamic
SPDP event stream, and proves its exact event and accumulation caps.

The scope is deliberately precise.  We do not claim that every conceivable
algebraic SPDP event is write-local.  Instead, `WriteLocalDynamicSPDP` records the
extra operational theorem a proposed event semantics must satisfy.  Any stream
satisfying it has event rank at most one and global additive rank at most the
number of machine steps.  Therefore it cannot supply an exponential Route G minor
on a subexponential run.
-/

namespace PallLean.Paper93.DeepMath.PathB.ComposableMachineDynamicSPDPEventCap

open ComposableMachine
open PvsNPRunIndexedFaithfulTPhi
open PvsNPDynamicSPDPGlobalGodMove
open DynamicSPDPEmissionBudget

/-- A real composable-machine computation as the repository's generic actual-run
object. -/
def machineActualRun (M : Machine) (clock : ℕ) :
    ActualDecisionRun (List Bool) (Cfg M) where
  encode := init M
  step := fun _ => step M
  steps := clock
  observe := fun c => M.accept c.st

/-- The machine semantics itself exposes the locality fact: one step either leaves
the tape unchanged or applies exactly one `writeAt` at the current head. -/
theorem step_tape_eq_or_single_write (M : Machine) (c : Cfg M) :
    (step M c).tp = c.tp ∨
      ∃ w : Bool, (step M c).tp = writeAt c.tp c.hd w := by
  unfold step
  by_cases hhalt : M.halt c.st = true
  · simp [hhalt]
  · have hhalt' : M.halt c.st = false := Bool.eq_false_of_not_eq_true hhalt
    rw [hhalt']
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize htr : M.δ c.st (c.tp.getD c.hd false) = tr
    rcases tr with ⟨next, write, move⟩
    cases write with
    | none => exact Or.inl rfl
    | some w => exact Or.inr ⟨w, rfl⟩

/-- The physical write charge of one configuration transition.  A halted step or
`none` write has charge zero; one optional write has charge one. -/
def physicalWriteEventRank (M : Machine) (c : Cfg M) : ℕ :=
  if M.halt c.st then 0
  else
    match (M.δ c.st (c.tp.getD c.hd false)).2.1 with
    | none => 0
    | some _ => 1

/-- Every physical finite-control transition has write charge at most one. -/
theorem physicalWriteEventRank_le_one (M : Machine) (c : Cfg M) :
    physicalWriteEventRank M c ≤ 1 := by
  unfold physicalWriteEventRank
  split
  · omega
  · split <;> omega

/-- The canonical write-local positive dynamic-SPDP stream of the real run. -/
def physicalWriteSPDP (M : Machine) (clock : ℕ) :
    DynamicPositiveSPDP (machineActualRun M clock) where
  eventRank t x :=
    physicalWriteEventRank M ((machineActualRun M clock).stateAt t x)

/-- The canonical physical write stream is uniformly one-bounded. -/
theorem physicalWriteSPDP_eventsBounded
    (M : Machine) (clock time : ℕ) (x : List Bool) :
    EventsBoundedBefore (physicalWriteSPDP M clock) time 1 x := by
  intro t _ht
  exact physicalWriteEventRank_le_one M _

/-- Exact complete-run cap: additive rank of physical writes is at most the
machine clock. -/
theorem physicalWriteSPDP_global_le_clock
    (M : Machine) (clock : ℕ) (x : List Bool) :
    (physicalWriteSPDP M clock).globalGodMoveRank x ≤ clock := by
  have h := globalGodMoveRank_le_steps_mul_cap
    (physicalWriteSPDP M clock) 1 x
    (physicalWriteSPDP_eventsBounded M clock clock x)
  simpa [machineActualRun] using h

/-- A proposed dynamic-SPDP semantics is write-local when every event rank is
dominated by the actual optional-write charge of the same physical transition. -/
structure WriteLocalDynamicSPDP (M : Machine) (clock : ℕ) where
  spdp : DynamicPositiveSPDP (machineActualRun M clock)
  eventRank_le_write : ∀ t x,
    spdp.eventRank t x ≤
      physicalWriteEventRank M ((machineActualRun M clock).stateAt t x)

namespace WriteLocalDynamicSPDP

/-- Every write-local dynamic-SPDP event is at most one. -/
theorem eventRank_le_one {M : Machine} {clock : ℕ}
    (S : WriteLocalDynamicSPDP M clock) (t : ℕ) (x : List Bool) :
    S.spdp.eventRank t x ≤ 1 :=
  le_trans (S.eventRank_le_write t x)
    (physicalWriteEventRank_le_one M _)

/-- Write-local event streams satisfy the uniform local budget. -/
theorem eventsBounded {M : Machine} {clock : ℕ}
    (S : WriteLocalDynamicSPDP M clock) (time : ℕ) (x : List Bool) :
    EventsBoundedBefore S.spdp time 1 x := by
  intro t _ht
  exact S.eventRank_le_one t x

/-- The additive global rank of every write-local stream is at most the clock. -/
theorem globalGodMoveRank_le_clock {M : Machine} {clock : ℕ}
    (S : WriteLocalDynamicSPDP M clock) (x : List Bool) :
    S.spdp.globalGodMoveRank x ≤ clock := by
  have h := DynamicSPDPEmissionBudget.globalGodMoveRank_le_steps_mul_cap
    S.spdp 1 x (S.eventsBounded clock x)
  simpa [machineActualRun] using h

/-- A subexponential-clock physical run with write-local events cannot contain the
exponential additive Route G minor. -/
theorem no_exponential_minor_of_clock_lt
    {M : Machine} {clock n : ℕ}
    (S : WriteLocalDynamicSPDP M clock) (x : List Bool)
    (hclock : clock < 2 ^ n) :
    ¬ 2 ^ n ≤ S.spdp.globalGodMoveRank x := by
  intro hminor
  have hupper := S.globalGodMoveRank_le_clock x
  omega

end WriteLocalDynamicSPDP

end PallLean.Paper93.DeepMath.PathB.ComposableMachineDynamicSPDPEventCap

#print axioms PallLean.Paper93.DeepMath.PathB.ComposableMachineDynamicSPDPEventCap.physicalWriteEventRank_le_one
#print axioms PallLean.Paper93.DeepMath.PathB.ComposableMachineDynamicSPDPEventCap.step_tape_eq_or_single_write
#print axioms PallLean.Paper93.DeepMath.PathB.ComposableMachineDynamicSPDPEventCap.physicalWriteSPDP_global_le_clock
#print axioms PallLean.Paper93.DeepMath.PathB.ComposableMachineDynamicSPDPEventCap.WriteLocalDynamicSPDP.globalGodMoveRank_le_clock
#print axioms PallLean.Paper93.DeepMath.PathB.ComposableMachineDynamicSPDPEventCap.WriteLocalDynamicSPDP.no_exponential_minor_of_clock_lt
