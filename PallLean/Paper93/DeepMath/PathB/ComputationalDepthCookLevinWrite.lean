import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinDynamics

/-!
# Cook–Levin M2 — the tape-write clause (with soundness)

The δ-dynamics clause fixes the next *state and head*.  For the **`⇒` converse** (a satisfying assignment
reconstructs the run) we also need the head cell's new value pinned: the tape cell *under the head* at time `t+1`
is the bit `δ` writes (or the read bit, if `δ` writes `none`; or the read bit, if halted).  The cell-copy clause
(`cellCopyClause`) only handles cells *away from* the head; this file supplies the missing head-cell write.

* `writtenBit M s b` — the bit left under the head: `b` if halted or `δ` writes `none`, else the written bit.
* `step_tape_getD_head` — one step leaves exactly `writtenBit` under the (old) head.
* `writeClause` / `writeClause_sound` — "state `q` ∧ head `p` ∧ cell `= b` at `t` ⇒ cell `p` at `t+1` is
  `writtenBit`", sound against the real run.

With this, the tape at `t+1` is fully determined from row `t`: `cellCopyClause` for `p ≠ head`, `writeClause` for
`p = head`.  That is exactly what the converse's cell-matching induction needs.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinWrite

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinShiftLoop (writeAt_getD_self)
open PallLean.Paper93.DeepMath.PathB.CookLevinTransition (step_of_halt)
open PallLean.Paper93.DeepMath.PathB.CookLevinOneHotWindow
open PallLean.Paper93.DeepMath.PathB.CookLevinDynamics

/-- The bit left under the head after one step, as a function of the local window `(state, head-cell)`: the read
bit `b` if halted or if `δ` writes `none`, else the bit `δ` writes. -/
def writtenBit (M : Machine) (s : M.State) (b : Bool) : Bool :=
  if M.halt s then b else ((M.δ s b).2.1).getD b

/-- **One step leaves `writtenBit` under the old head.** -/
theorem step_tape_getD_head (M : Machine) (c : Cfg M) :
    (step M c).tp.getD c.hd false = writtenBit M c.st (c.tp.getD c.hd false) := by
  unfold writtenBit
  by_cases hh : M.halt c.st = true
  · rw [if_pos hh, step_of_halt M c hh]
  · have hf : M.halt c.st = false := by simpa using hh
    rw [if_neg hh]
    simp only [step, hf, Bool.false_eq_true, if_false]
    cases hw : (M.δ c.st (c.tp.getD c.hd false)).2.1 with
    | none => simp only [hw, Option.getD_none]
    | some w => simp only [hw, Option.getD_some]; exact writeAt_getD_self c.tp c.hd w

/-- The tape-write clause for the window "state `q`, head `p`, cell `= b` at time `t`": the cell at `p` at time
`t+1` is `writtenBit`. -/
noncomputable def writeClause (M : Machine) (t : ℕ) (q : Fin (Fintype.card M.State)) (p : ℕ) (b : Bool) :
    Formula :=
  [implClause (stateVar t q.val, true) (headVar t p, true) (cellVar t p, b)
      (cellVar (t + 1) p, writtenBit M ((Fintype.equivFin M.State).symm q) b)]

/-- **Soundness of the tape-write clause.**  The real-run assignment satisfies it: whenever the window matches at
time `t`, the run's cell at `p` at `t+1` is exactly the encoded `writtenBit`. -/
theorem writeClause_sound (M : Machine) (x : List Bool) (t : ℕ) (q : Fin (Fintype.card M.State)) (p : ℕ)
    (b : Bool) : evalFormula (fullAssign M x) (writeClause M t q p b) = true := by
  have key : (fullAssign M x (stateVar t q.val) = true ∧ fullAssign M x (headVar t p) = true
        ∧ fullAssign M x (cellVar t p) = b) →
      (run M (t + 1) (init M x)).tp.getD p false = writtenBit M ((Fintype.equivFin M.State).symm q) b := by
    rintro ⟨hs, hh, hb⟩
    rw [fullAssign_state, stateBit, dif_pos q.isLt, decide_eq_true_eq, Fin.eta] at hs
    rw [fullAssign_head, decide_eq_true_eq] at hh
    rw [fullAssign_cell, ← hh] at hb
    rw [run_succ, ← hh, step_tape_getD_head, hs, hb]
  rw [writeClause, evalFormula_cons, evalFormula, List.all_nil, Bool.and_true, implClause_iff]
  intro hg
  simp only [evalLit, beq_iff_eq] at hg ⊢
  rw [fullAssign_cell]
  exact key hg

end PallLean.Paper93.DeepMath.PathB.CookLevinWrite
