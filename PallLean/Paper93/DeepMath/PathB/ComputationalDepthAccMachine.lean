import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUnaryHealMachine
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitSeq

/-!
# The shared-layout foundation: the accumulator and `addBlock`

The primitives so far *consumed* their operands (leaving marked debris) and buried their
results, so chaining them needed repositioning adapters.  The shared-layout redesign fixes
this at the interface: a **canonical accumulator tape**

  `accLive a v rest = [T,T]^a [F,F] 1^v 0 rest`

carries a persistent live source block `[T,T]^a` (the operand, count `a`) and a unary
accumulator `1^v`.  The keystone operation `addBlock` adds the source's count into the
accumulator **and heals the source back to live**, so the same source can be added
repeatedly:

  `addBlock :  accLive a v (0^a rest)  ↦  accLive a (v+a) rest`.

It is `copyMachine ⨟ healMachine`, composed by `seq_run` from the proved `copyM_rounds`
(deposit `a` into the run, marking the source) and `healM_run` (unmark the source).  Every
downstream operation — multiply (repeat `addBlock`), triple, `+tag` — is a loop of this one
clean primitive on the canonical tape; no debris, no repositioning.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.AccMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq (seqMachine seq_run)
open PallLean.Paper93.DeepMath.PathB.DIndexMachine (flat2 flat2_append)
open PallLean.Paper93.DeepMath.PathB.UnaryCopyMachine (copyMachine copyTape copyM_rounds)
open PallLean.Paper93.DeepMath.PathB.UnaryHealMachine (healMachine healM_run)

/-- The canonical accumulator tape: a live source block `[T,T]^a`, its terminator, and the
unary accumulator `1^v`. -/
def accLive (a v : ℕ) (rest : List Bool) : List Bool :=
  flat2 (List.replicate a true) ++ false :: false :: (List.replicate v true ++ false :: rest)

/-- The accumulator with `a` scratch zeros is exactly the copy machine's input. -/
theorem accLive_copy_in (a s : ℕ) (rest : List Bool) :
    accLive a s (List.replicate a false ++ rest) = copyTape 0 a s rest := by
  unfold accLive copyTape
  simp [flat2, List.replicate_succ]

/-- The copy machine's output, in heal-ready form. -/
theorem copy_out_heal (a s : ℕ) (rest : List Bool) :
    copyTape a 0 s rest
      = flat2 (List.replicate a false)
          ++ false :: (false :: (List.replicate (s + a) true ++ false :: rest)) := by
  unfold copyTape
  simp [flat2, List.replicate]

/-- The heal machine's output is the accumulator with the source live again. -/
theorem heal_out_accLive (a s : ℕ) (rest : List Bool) :
    flat2 (List.replicate a true)
        ++ false :: (false :: (List.replicate (s + a) true ++ false :: rest))
      = accLive a (s + a) rest := by
  unfold accLive
  simp

/-- The add-block machine: add the source's count into the accumulator, healing the
source. -/
def addBlockMachine : Machine := seqMachine copyMachine healMachine

/-- **The keystone shared-layout operation.**  `addBlock` grows the accumulator by the
source count and leaves the source live and reusable, consuming `a` scratch zeros. -/
theorem addBlockM_run (a s : ℕ) (rest : List Bool) :
    ∃ t, run addBlockMachine t
        (init addBlockMachine (accLive a s (List.replicate a false ++ rest)))
      = ⟨Sum.inr ((2 : Fin 3), false), 2 * a, accLive a (s + a) rest⟩ := by
  obtain ⟨t1, _, hcopy⟩ := copyM_rounds a 0 s rest false
  rw [show (0 : ℕ) + a = a from by omega] at hcopy
  obtain ⟨t2, _, hheal⟩ :=
    healM_run a (false :: (List.replicate (s + a) true ++ false :: rest)) false
  have hh1 : copyMachine.halt ((6 : Fin 7), false) = true := rfl
  have hh2 : healMachine.halt ((2 : Fin 3), false) = true := rfl
  refine ⟨t1 + 1 + t2, ?_⟩
  rw [accLive_copy_in]
  -- align heal's input with copy's output, and heal's output with the accumulator
  rw [← copy_out_heal a s rest, heal_out_accLive] at hheal
  show run (seqMachine copyMachine healMachine) (t1 + 1 + t2)
      (init (seqMachine copyMachine healMachine) (copyTape 0 a s rest)) = _
  exact seq_run copyMachine healMachine (copyTape 0 a s rest)
    (copyTape a 0 s rest) (accLive a (s + a) rest) t1 t2
    ((6 : Fin 7), false) (2 * a) ((2 : Fin 3), false) (2 * a)
    hcopy hh1 hheal hh2

/-- The add-block machine halts (so it chains). -/
theorem addBlock_halt (s : Fin 3) (b : Bool) (h : healMachine.halt (s, b) = true) :
    addBlockMachine.halt (Sum.inr (s, b)) = true := h

end PallLean.Paper93.DeepMath.PathB.AccMachine
