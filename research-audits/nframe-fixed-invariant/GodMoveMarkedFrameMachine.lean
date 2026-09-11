import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitAppendBlock
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPDoubledCodec
import GodMoveSATPaddingInvariance

/-!
# A concrete machine primitive for appending to marked Boolean frames

This module reuses the existing doubled-bit codec and physical fixed-block
append machine. A data bit is stored as `bb`; `01` terminates its frame. The
machine scans that detectable marker and performs four local writes to append
one Boolean value. The exact clock is twice the old payload length plus six.

The canonical contract preserves every bit of an arbitrary prefix workspace;
the frame follows that prefix and occupies the final nonblank region. It does
not promise preservation of an arbitrary suffix after the frame. Extra trailing
false padding is handled by an explicit observational-equivalence theorem.

This is a finite-control `ComposableMachine` primitive, with 28 states
independent of payload length. The Boolean to append selects one of two fixed
machines. A full stored-program evaluator, branch/lookup controller and circuit
generator are separate work. No raw tape-length observation, tape shrinking,
or SAT rank bound is assumed.
-/

namespace GodMoveMarkedFrameMachine

open PallLean.Paper93.DeepMath.PathB
open ComposableMachine CookLevinDoubled CookLevinEmitAppendBlock
open MCSPDoubledCodec CellSpread

/-- Existing self-delimiting frame; no new representation is introduced. -/
abbrev frame := encodeD

/-- Decode one marked region at a supplied physical offset. The second result
is the exact remaining suffix after its terminator. -/
def decodeFrameAt (tape : List Bool) (offset : ℕ) : List Bool × List Bool :=
  decodeDPrefix (tape.drop offset)

theorem decodeFrameAt_frame (pre payload suffix : List Bool) :
    decodeFrameAt (pre ++ frame payload ++ suffix) pre.length = (payload, suffix) := by
  simp [decodeFrameAt, List.append_assoc]

theorem frame_length (payload : List Bool) : (frame payload).length = 2 * payload.length + 2 :=
  encodeD_length payload

/-- A specialization of the already proved local append controller. Its ROM
contains just one Boolean bit, independent of the input's width or length. -/
def appendMarkedBit (b : Bool) : Machine := appendMachine [b]

theorem appendMarkedBit_state_card (b : Bool) :
    Fintype.card (appendMarkedBit b).State = 28 := by
  simp [appendMarkedBit, appendMachine]

def appendClock (payload : List Bool) : ℕ := 2 * payload.length + 6

theorem appendClock_eq_frame_length_add_four (payload : List Bool) :
    appendClock payload = (frame payload).length + 4 := by
  rw [frame_length]
  rfl

/-- Exact local-machine run from the beginning of the final marked region.
The prefix is arbitrary workspace and is preserved bit for bit. -/
theorem appendMarkedBit_run (b : Bool) (pre payload : List Bool) :
    run (appendMarkedBit b) (appendClock payload)
      ⟨(appendMarkedBit b).start, pre.length, pre ++ frame payload⟩ =
      ⟨(6, 0, false), pre.length + 2 * (payload.length + 1) + 1,
        pre ++ frame (payload ++ [b])⟩ := by
  simpa only [appendMarkedBit, appendClock, List.length_singleton,
    show 2 * payload.length + 2 + 4 * 1 = 2 * payload.length + 6 by omega] using
    append_run [b] pre payload pre.length rfl (by simp) false

/-- The machine halts and the final region decodes to the appended payload.
This contract keeps workspace on tape instead of demanding physical truncation. -/
theorem appendMarkedBit_region_correct (b : Bool) (pre payload : List Bool) :
    let c := run (appendMarkedBit b) (appendClock payload)
      ⟨(appendMarkedBit b).start, pre.length, pre ++ frame payload⟩
    (appendMarkedBit b).halt c.st = true ∧
      c.tp.take pre.length = pre ∧
      decodeFrameAt c.tp pre.length = (payload ++ [b], []) := by
  dsimp only
  rw [appendMarkedBit_run]
  refine ⟨rfl, ?_, ?_⟩
  · simp
  · simpa only [List.append_nil] using decodeFrameAt_frame pre (payload ++ [b]) []

/-- Standalone forced-initialization endpoint with clock `input.length + 4`
on valid framed inputs. No total claim is made for arbitrary unmarked tapes. -/
theorem appendMarkedBit_correct_on_frame (b : Bool) (payload : List Bool) :
    HaltsBy (appendMarkedBit b) (frame payload) ((frame payload).length + 4) ∧
      transOut (appendMarkedBit b) (frame payload) ((frame payload).length + 4) =
        frame (payload ++ [b]) := by
  rw [← appendClock_eq_frame_length_add_four]
  have h := appendMarkedBit_run b [] payload
  simp only [List.length_nil, List.nil_append, Nat.zero_add] at h
  constructor
  · unfold HaltsBy
    rw [show init (appendMarkedBit b) (frame payload) =
      ⟨(appendMarkedBit b).start, 0, frame payload⟩ from rfl, h]
    rfl
  · unfold transOut
    rw [show init (appendMarkedBit b) (frame payload) =
      ⟨(appendMarkedBit b).start, 0, frame payload⟩ from rfl, h]

/-- Trailing false padding cannot change the executed state, head, or any
observable output bit. This does not assert equality of physical tape lengths. -/
theorem appendMarkedBit_padded_run (b : Bool) (pre payload : List Bool) (padding : ℕ) :
    Congr
      (run (appendMarkedBit b) (appendClock payload)
        ⟨(appendMarkedBit b).start, pre.length,
          (pre ++ frame payload) ++ List.replicate padding false⟩)
      ⟨(6, 0, false), pre.length + 2 * (payload.length + 1) + 1,
        pre ++ frame (payload ++ [b])⟩ := by
  have h : Congr
      (⟨(appendMarkedBit b).start, pre.length,
        (pre ++ frame payload) ++ List.replicate padding false⟩ : Cfg (appendMarkedBit b))
      ⟨(appendMarkedBit b).start, pre.length, pre ++ frame payload⟩ :=
    ⟨rfl, rfl, append_replicate_getD _ _⟩
  have hr := GodMoveSATPaddingInvariance.run_congr (appendMarkedBit b) (appendClock payload) h
  rw [appendMarkedBit_run] at hr
  exact hr

end GodMoveMarkedFrameMachine

#print axioms GodMoveMarkedFrameMachine.decodeFrameAt_frame
#print axioms GodMoveMarkedFrameMachine.appendMarkedBit_state_card
#print axioms GodMoveMarkedFrameMachine.appendMarkedBit_run
#print axioms GodMoveMarkedFrameMachine.appendMarkedBit_region_correct
#print axioms GodMoveMarkedFrameMachine.appendMarkedBit_correct_on_frame
#print axioms GodMoveMarkedFrameMachine.appendMarkedBit_padded_run
