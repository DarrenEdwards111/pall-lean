import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPComparatorBridgeCombinedMachine

/-!
# MCSP verifier: physical staging of the duplicated power bridge

The comparator bridge needs two adjacent copies of `unaryD (2^n)` while the
already materialized table-length counter and the later table-copy scratch
remain live.  This file instantiates the proved suffix-safe local copy machine
on exactly that integrated tape.

The operational output contains the copy machine's required `00` local-home
delimiter between the table counter and the duplicated power bridge.  We make
that gap explicit rather than silently deleting it with a list equation.  The
final theorems identify its exact cells, show that every other block is already
in the required order, and prove that removing precisely those two cells gives
the existing bridge-copy input descriptor.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPPowerBridgeStageMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.MCSPCounterCopyScratchMachine
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyLift
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyFinish
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyLayout

/-- The already live prefix and table-length counter.  This becomes the local
home prefix for the physical power-counter copy. -/
def powerStagePrefix (pre : List Bool) (a : ℕ) : List Bool :=
  pre ++ unaryD a

/-- Scratch needed later by the table bridge-copy, followed by its payload. -/
def tableCopyScratch (a : ℕ) (payload : List Bool) : List Bool :=
  List.replicate (2 * a + 2) false ++ payload

/-- Exact input of the real local copy machine used to duplicate `2^n`. -/
def powerStageInput (pre : List Bool) (n a : ℕ)
    (payload : List Bool) : List Bool :=
  localTape (powerStagePrefix pre a)
    (cpyS (2 ^ n) 0 0 (tableCopyScratch a payload))

/-- Physical output.  The `00` is the local-copy home delimiter; it is live
machine structure and is therefore recorded explicitly. -/
def gappedBridgeCore (n a : ℕ) (payload : List Bool) : List Bool :=
  unaryD a ++ [false, false] ++ powBridge n ++
    tableCopyScratch a payload

def powerStageOutput (pre : List Bool) (n a : ℕ)
    (payload : List Bool) : List Bool :=
  pre ++ gappedBridgeCore n a payload

theorem powerStageInput_eq (pre : List Bool) (n a : ℕ)
    (payload : List Bool) :
    powerStageInput pre n a payload =
      pre ++ unaryD a ++ [false, false] ++ unaryD (2 ^ n) ++
        List.replicate (2 * (2 ^ n) + 2) false ++
          tableCopyScratch a payload := by
  rw [powerStageInput, cpyS_zero]
  simp [localTape, homePrefix, powerStagePrefix, List.append_assoc]

theorem powerStageOutput_eq (pre : List Bool) (n a : ℕ)
    (payload : List Bool) :
    localTape (powerStagePrefix pre a)
        (unaryD (2 ^ n) ++ unaryD (2 ^ n) ++
          tableCopyScratch a payload) =
      powerStageOutput pre n a payload := by
  simp [localTape, homePrefix, powerStagePrefix, powerStageOutput,
    gappedBridgeCore, powBridge, List.append_assoc]

/-- One genuine run of the fixed local-copy machine physically creates both
power counters while preserving the live table counter, table scratch, and
payload byte-for-byte. -/
theorem run_powerStage (pre : List Bool) (n a : ℕ)
    (payload : List Bool) (s : Bool) :
    run localCopyMachine (localCopyClock (2 ^ n))
      (liftCopyCfg (powerStagePrefix pre a)
        ⟨(0, s), 0, cpyS (2 ^ n) 0 0 (tableCopyScratch a payload)⟩) =
      ⟨.copy (10, false),
        localOffset (powerStagePrefix pre a) + (4 * (2 ^ n) + 3),
        powerStageOutput pre n a payload⟩ := by
  rw [run_localCopy_complete]
  unfold liftCopyCfg
  rw [powerStageOutput_eq]

theorem powerStage_halts (pre : List Bool) (n a : ℕ)
    (payload : List Bool) (s : Bool) :
    localCopyMachine.halt
      (run localCopyMachine (localCopyClock (2 ^ n))
        (liftCopyCfg (powerStagePrefix pre a)
          ⟨(0, s), 0,
            cpyS (2 ^ n) 0 0 (tableCopyScratch a payload)⟩)).st = true := by
  exact localCopy_complete_halts (powerStagePrefix pre a)
    (tableCopyScratch a payload) (2 ^ n) s

theorem powerStage_clock_eq (n : ℕ) :
    localCopyClock (2 ^ n) =
      6 * (2 ^ n) * (2 ^ n) + 20 * (2 ^ n) + 12 := by
  exact localCopyClock_eq (2 ^ n)

/-- The two delimiter cells are exactly `00`. -/
theorem gappedBridgeCore_getD_home_lo (n a : ℕ)
    (payload : List Bool) :
    (gappedBridgeCore n a payload).getD (unaryD a).length false = false := by
  simp [gappedBridgeCore]

theorem gappedBridgeCore_getD_home_hi (n a : ℕ)
    (payload : List Bool) :
    (gappedBridgeCore n a payload).getD ((unaryD a).length + 1) false = false := by
  simp [gappedBridgeCore]

/-- Logical deletion used only to state the exact remaining routing task.  No
machine theorem below claims this deletion happens for free. -/
def erasePowerHome (a : ℕ) (T : List Bool) : List Bool :=
  T.take (unaryD a).length ++ T.drop ((unaryD a).length + 2)

theorem erasePowerHome_gappedBridgeCore (n a : ℕ)
    (payload : List Bool) :
    erasePowerHome a (gappedBridgeCore n a payload) =
      bridgeCpyS n a 0 0 payload := by
  rw [bridgeCpyS_zero]
  simp [erasePowerHome, gappedBridgeCore, tableCopyScratch,
    List.append_assoc]

theorem gappedBridgeCore_length (n a : ℕ) (payload : List Bool) :
    (gappedBridgeCore n a payload).length =
      (bridgeCpyS n a 0 0 payload).length + 2 := by
  rw [bridgeCpyS_length n a 0 0 payload (by omega) (by omega)]
  simp [gappedBridgeCore, tableCopyScratch, powBridge_length, unaryD_length]
  omega

end PallLean.Paper93.DeepMath.PathB.MCSPPowerBridgeStageMachine

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerBridgeStageMachine.run_powerStage
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerBridgeStageMachine.powerStage_halts
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerBridgeStageMachine.erasePowerHome_gappedBridgeCore
