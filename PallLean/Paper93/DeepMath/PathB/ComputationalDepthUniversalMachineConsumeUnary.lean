import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineMarkerShift

/-!
# Rule-lookup, brick 14: the counter loop (consume a unary block to zero)

`decUnary` (brick 13) is one decrement.  The lookup needs the *loop*: run a unary block all the way to
zero — the counter's value drives how many times a table pointer advances.  `consumeUnary` is that loop:
from the block start, consume each `true` (write `false`, step right) until the terminating `false`,
halting there.  A length-`n` block takes exactly `n + 1` steps — the loop reads the counter value `n`.

This is the first genuine LOOP in the construction, and the first with an **evolving tape** (each
iteration writes).  The crux is that every write lands *behind* the head, so reads ahead stay correct;
this is captured by the invariant that the tape at positions `≥ head` is unchanged.

## What is proved

* **`consumeUnary`** — a two-state machine (`going → halted`): read the head cell; `true` ⇒ consume it
  (write `false`), step right, keep going; `false` ⇒ halt.
* **`consumeUnary_partial`** — the loop invariant: for `i ≤ n`, after `i` steps the head is at
  `c.hd + i`, still `going`, and the tape *ahead of the head* is unchanged.
* **`consumeUnary_run`** — a length-`n` block is consumed in `n + 1` steps, halting at the terminator
  `c.hd + n`.  The loop runs exactly `n` iterations — the counter value is read.

## Honest scope

`consumeUnary` is the counter loop over ONE block.  The full state-match still needs to drive a table
pointer from this counter (advance one rule per consumed unit) and handle the read symbol; then wire the
matched rule's output through the built read/write/move primitives, and the reset-to-0 wrapper; then the
lazy-delay diagonal.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineConsumeUnary

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.UniversalMachineMarkerShift (writeAt_getD_of_ne)

/-- Control states of `consumeUnary`: consuming, or halted. -/
inductive Con where
  | going : Con
  | halted : Con
  deriving DecidableEq

instance : Fintype Con := ⟨{.going, .halted}, fun x => by cases x <;> decide⟩

/-- **The counter loop.**  Consume each `true` (write `false`, step right); halt on the first `false`. -/
def consumeUnary : Machine where
  State := Con
  fin := inferInstance
  dec := inferInstance
  start := Con.going
  halt := fun s => match s with | .halted => true | .going => false
  δ := fun s b => match s with
    | .going => if b then (Con.going, some false, (1 : Move)) else (Con.halted, none, (2 : Move))
    | .halted => (Con.halted, none, (2 : Move))
  accept := fun _ => false

theorem consumeUnary_step_active {c : Cfg consumeUnary} (hne : consumeUnary.halt c.st = false) :
    step consumeUnary c = ⟨(consumeUnary.δ c.st (c.tp.getD c.hd false)).1,
                    moveHead c.hd (consumeUnary.δ c.st (c.tp.getD c.hd false)).2.2,
                    (match (consumeUnary.δ c.st (c.tp.getD c.hd false)).2.1 with
                      | none => c.tp | some w => writeAt c.tp c.hd w)⟩ := by
  unfold step; rw [hne]; rfl

theorem consumeUnary_step_consume {c : Cfg consumeUnary} (hs : c.st = Con.going)
    (hb : c.tp.getD c.hd false = true) :
    step consumeUnary c = ⟨Con.going, c.hd + 1, writeAt c.tp c.hd false⟩ := by
  rw [consumeUnary_step_active (by rw [hs]; rfl), hs, hb]; rfl

theorem consumeUnary_step_halt {c : Cfg consumeUnary} (hs : c.st = Con.going)
    (hb : c.tp.getD c.hd false = false) : step consumeUnary c = ⟨Con.halted, c.hd, c.tp⟩ := by
  rw [consumeUnary_step_active (by rw [hs]; rfl), hs, hb]; rfl

/-- **The loop invariant (proved).**  For `i ≤ n`, after `i` steps the head has advanced by `i`, the
machine is still `going`, and the tape at positions `≥ c.hd + i` is unchanged (writes stay behind the
head). -/
theorem consumeUnary_partial (n : ℕ) (c : Cfg consumeUnary) (hstart : c.st = Con.going)
    (htrue : ∀ i, i < n → c.tp.getD (c.hd + i) false = true) :
    ∀ i, i ≤ n → ∃ t, run consumeUnary i c = ⟨Con.going, c.hd + i, t⟩ ∧
      ∀ p, c.hd + i ≤ p → t.getD p false = c.tp.getD p false := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨c.tp, ?_, fun p _ => rfl⟩
    show run consumeUnary 0 c = ⟨Con.going, c.hd + 0, c.tp⟩
    obtain ⟨st, hd, tp⟩ := c
    subst hstart
    rfl
  | succ i ih =>
    intro hle
    obtain ⟨t, ht, hahead⟩ := ih (by omega)
    have hread : t.getD (c.hd + i) false = true := by
      rw [hahead (c.hd + i) (le_refl _)]; exact htrue i (by omega)
    refine ⟨writeAt t (c.hd + i) false, ?_, ?_⟩
    · rw [run_succ, ht, consumeUnary_step_consume (c := ⟨Con.going, c.hd + i, t⟩) rfl hread]
      show (⟨Con.going, c.hd + i + 1, writeAt t (c.hd + i) false⟩ : Cfg consumeUnary)
          = ⟨Con.going, c.hd + (i + 1), writeAt t (c.hd + i) false⟩
      rw [show c.hd + i + 1 = c.hd + (i + 1) from by omega]
    · intro p hp
      rw [writeAt_getD_of_ne t (c.hd + i) p false (by omega)]
      exact hahead p (by omega)

/-- **The counter loop runs (proved).**  A length-`n` unary block is consumed in `n + 1` steps, halting
at the terminator `c.hd + n`.  The loop runs exactly `n` iterations — the counter value is read. -/
theorem consumeUnary_run (n : ℕ) (c : Cfg consumeUnary) (hstart : c.st = Con.going)
    (htrue : ∀ i, i < n → c.tp.getD (c.hd + i) false = true)
    (hfalse : c.tp.getD (c.hd + n) false = false) :
    ∃ t, run consumeUnary (n + 1) c = ⟨Con.halted, c.hd + n, t⟩ := by
  obtain ⟨t, ht, hahead⟩ := consumeUnary_partial n c hstart htrue n (le_refl n)
  refine ⟨t, ?_⟩
  rw [run_succ, ht,
    consumeUnary_step_halt (c := ⟨Con.going, c.hd + n, t⟩) rfl
      (by rw [hahead (c.hd + n) (le_refl _)]; exact hfalse)]

end PallLean.Paper93.DeepMath.PathB.UniversalMachineConsumeUnary

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineConsumeUnary.consumeUnary_partial
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineConsumeUnary.consumeUnary_run
