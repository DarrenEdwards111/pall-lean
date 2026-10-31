import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineMarkerShift

/-!
# Rule-lookup, brick 13: the unary counter atom (decrement + zero-test)

The remaining phase of `uStepOnTape` is the rule-lookup: match the current simulated state (an unbounded
`ℕ`, stored *unary* on the tape) and the read symbol against the transition table.  Matching the symbol
is a bounded bit compare; matching the *state* is the hard part, because the state is unbounded — it
needs a data-dependent counter/comparison loop over unary blocks.

The atom of every such loop is **decrement-and-test-zero**: read the cell at the block head; if it is a
`true`, consume one unit (write `false`) and report *positive*; if it is a `false`, report *zero*
without writing.  This brick builds that atom, `decUnary`, and ties it to the unary encoding.

## What is proved

* **`decUnary`** — a three-state machine (`read → pos | zero`): read the head cell; `true` ⇒ write
  `false`, halt `pos`; `false` ⇒ halt `zero`.
* **`decUnary_pos_run` / `decUnary_zero_run`** — the two one-step outcomes.
* **`decUnary_consumes`** — in the positive case the head cell is now `false` (one unit consumed).
* **`decUnary_preserves`** — every other cell is unchanged.
* **`decUnary_accept_pos` / `decUnary_accept_zero`** — the decision reports positive vs zero.
* **`decUnary_detects_positive`** — on a unary block `encNat n ++ post`, the decision is `decide (0 < n)`
  — the atom detects whether the unary value is nonzero.

## Honest scope

`decUnary` is the counter atom, not the lookup.  What remains for `uStepOnTape`: the comparison **loop**
(repeat decrement across two unary blocks — the current state and each rule key — until one empties;
shuttling between them; this is the substantial, loop-based core), then wiring the matched rule's output
through the built read/write/move primitives, and the reset-to-0 wrapper; then the lazy-delay diagonal.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineDecUnary

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.UniversalMachineSerial (encNat)
open PallLean.Paper93.DeepMath.PathB.UniversalMachineReadWrite (writeAt_getD_self)
open PallLean.Paper93.DeepMath.PathB.UniversalMachineMarkerShift (writeAt_getD_of_ne)

/-- Control states of `decUnary`: about to read; read a `true` (positive); read a `false` (zero). -/
inductive Dec where
  | read : Dec
  | pos : Dec
  | zero : Dec
  deriving DecidableEq

instance : Fintype Dec := ⟨{.read, .pos, .zero}, fun x => by cases x <;> decide⟩

/-- **The counter atom.**  Read the cell at the head: `true` ⇒ consume it (write `false`) and halt
`pos`; `false` ⇒ halt `zero` (no write).  The decision reports which. -/
def decUnary : Machine where
  State := Dec
  fin := inferInstance
  dec := inferInstance
  start := Dec.read
  halt := fun s => match s with | .read => false | _ => true
  δ := fun s b => match s with
    | .read => if b then (Dec.pos, some false, (2 : Move)) else (Dec.zero, none, (2 : Move))
    | .pos => (Dec.pos, none, (2 : Move))
    | .zero => (Dec.zero, none, (2 : Move))
  accept := fun s => match s with | .pos => true | _ => false

theorem decUnary_step_active {c : Cfg decUnary} (hne : decUnary.halt c.st = false) :
    step decUnary c = ⟨(decUnary.δ c.st (c.tp.getD c.hd false)).1,
                    moveHead c.hd (decUnary.δ c.st (c.tp.getD c.hd false)).2.2,
                    (match (decUnary.δ c.st (c.tp.getD c.hd false)).2.1 with
                      | none => c.tp | some w => writeAt c.tp c.hd w)⟩ := by
  unfold step; rw [hne]; rfl

theorem decUnary_step_pos {c : Cfg decUnary} (hs : c.st = Dec.read)
    (hb : c.tp.getD c.hd false = true) : step decUnary c = ⟨Dec.pos, c.hd, writeAt c.tp c.hd false⟩ := by
  rw [decUnary_step_active (by rw [hs]; rfl), hs, hb]; rfl

theorem decUnary_step_zero {c : Cfg decUnary} (hs : c.st = Dec.read)
    (hb : c.tp.getD c.hd false = false) : step decUnary c = ⟨Dec.zero, c.hd, c.tp⟩ := by
  rw [decUnary_step_active (by rw [hs]; rfl), hs, hb]; rfl

/-- **Positive case (proved).**  Reading a `true`, one step consumes it and halts `pos`. -/
theorem decUnary_pos_run (c : Cfg decUnary) (hs : c.st = Dec.read)
    (hb : c.tp.getD c.hd false = true) :
    run decUnary 1 c = ⟨Dec.pos, c.hd, writeAt c.tp c.hd false⟩ := by
  rw [show run decUnary 1 c = step decUnary c from rfl, decUnary_step_pos hs hb]

/-- **Zero case (proved).**  Reading a `false`, one step halts `zero`, tape unchanged. -/
theorem decUnary_zero_run (c : Cfg decUnary) (hs : c.st = Dec.read)
    (hb : c.tp.getD c.hd false = false) : run decUnary 1 c = ⟨Dec.zero, c.hd, c.tp⟩ := by
  rw [show run decUnary 1 c = step decUnary c from rfl, decUnary_step_zero hs hb]

/-- **The unit is consumed (proved).**  After a positive decrement the head cell is `false`. -/
theorem decUnary_consumes (c : Cfg decUnary) (hs : c.st = Dec.read)
    (hb : c.tp.getD c.hd false = true) : (run decUnary 1 c).tp.getD c.hd false = false := by
  rw [decUnary_pos_run c hs hb]; exact writeAt_getD_self c.tp c.hd false

/-- **The rest is untouched (proved).**  Every other cell is unchanged by the decrement. -/
theorem decUnary_preserves (c : Cfg decUnary) (hs : c.st = Dec.read)
    (hb : c.tp.getD c.hd false = true) (q : ℕ) (hq : q ≠ c.hd) :
    (run decUnary 1 c).tp.getD q false = c.tp.getD q false := by
  rw [decUnary_pos_run c hs hb, writeAt_getD_of_ne c.tp c.hd q false (by omega)]

/-- **Decision reports positive (proved).** -/
theorem decUnary_accept_pos (c : Cfg decUnary) (hs : c.st = Dec.read)
    (hb : c.tp.getD c.hd false = true) : decUnary.accept (run decUnary 1 c).st = true := by
  rw [decUnary_pos_run c hs hb]; rfl

/-- **Decision reports zero (proved).** -/
theorem decUnary_accept_zero (c : Cfg decUnary) (hs : c.st = Dec.read)
    (hb : c.tp.getD c.hd false = false) : decUnary.accept (run decUnary 1 c).st = false := by
  rw [decUnary_zero_run c hs hb]; rfl

/-- **The atom detects a nonzero unary value (proved).**  On a unary block `encNat n ++ post`, the
decision is `decide (0 < n)`. -/
theorem decUnary_detects_positive (n : ℕ) (post : List Bool) :
    decUnary.accept (run decUnary 1 ⟨Dec.read, 0, encNat n ++ post⟩).st = decide (0 < n) := by
  cases n with
  | zero => rw [decUnary_accept_zero ⟨Dec.read, 0, encNat 0 ++ post⟩ rfl rfl]; rfl
  | succ n => rw [decUnary_accept_pos ⟨Dec.read, 0, encNat (n + 1) ++ post⟩ rfl rfl]; rfl

end PallLean.Paper93.DeepMath.PathB.UniversalMachineDecUnary

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineDecUnary.decUnary_consumes
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineDecUnary.decUnary_detects_positive
