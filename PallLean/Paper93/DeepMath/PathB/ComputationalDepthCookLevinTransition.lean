import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinVarIndex
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinTableau

/-!
# Cook–Levin M2 — the tape transition-window clause (the crux, tape part)

The transition clauses relate row `t+1` to row `t` by one machine step.  The full window (state one-hot + head
one-hot + δ-table for an arbitrary `State`) is research-scale and deferred; its cleanest self-contained piece — and
the one the scope calls "the crux" — is the **tape** constraint: by transition locality (`step_tape_getD_ne`), cell
`p` is unchanged unless the head sits at `p`.  This file builds that clause, `cellCopyClause`, with

* **syntactic correctness** — an assignment satisfies it iff `head[t][p] off ⇒ cell[t+1][p] = cell[t][p]`; and
* **soundness against the computation** — the assignment that reads the *real run* off the tape satisfies it (this
  is where `step_tape_getD_ne` is cashed in).

It uses a general `guardedIff` CNF primitive (`¬guard ⇒ (v ↔ w)`) and the `cellVar`/`headVar` scheme.  Per
`SCOPE_COOKLEVIN.md` the full formula assembly + poly emitter remain deferred; this is one more genuine brick.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinTransition

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinTableau

/-! ## The guarded-biconditional CNF primitive -/

/-- `¬guard → (v ↔ w)`, as two clauses.  (For the tape clause `guard = head[t][p]`, `v = cell[t+1][p]`,
`w = cell[t][p]`.) -/
def guardedIff (guard v w : ℕ) : Formula :=
  [[(guard, true), (v, false), (w, true)], [(guard, true), (v, true), (w, false)]]

/-- **Correctness of the guarded biconditional.** -/
theorem guardedIff_iff (a : ℕ → Bool) (guard v w : ℕ) :
    evalFormula a (guardedIff guard v w) = true ↔ (a guard = false → a v = a w) := by
  simp only [guardedIff, evalFormula, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    evalClause, List.any_cons, List.any_nil, Bool.or_false, evalLit, Bool.or_eq_true, beq_iff_eq]
  cases a guard <;> cases a v <;> cases a w <;> simp

/-! ## Tape locality including the halted case -/

/-- A halted step is the identity. -/
theorem step_of_halt (M : Machine) (c : Cfg M) (hh : M.halt c.st = true) : step M c = c := by
  unfold step; rw [if_pos hh]

/-- **Full tape locality.**  Regardless of whether the machine has halted, one step leaves every cell except the
head cell unchanged (halted ⇒ the whole config is fixed). -/
theorem step_tape_getD_ne_all (M : Machine) (c : Cfg M) (p : ℕ) (hp : p ≠ c.hd) :
    (step M c).tp.getD p false = c.tp.getD p false := by
  by_cases hh : M.halt c.st = true
  · rw [step_of_halt M c hh]
  · exact step_tape_getD_ne M c p hp (by simpa using hh)

/-! ## The cell-copy transition clause -/

/-- The tape transition clause for cell `p` between rows `t` and `t+1`: `head[t][p] off ⇒ cell[t+1][p] = cell[t][p]`. -/
def cellCopyClause (t p : ℕ) : Formula := guardedIff (headVar t p) (cellVar (t + 1) p) (cellVar t p)

/-- **Syntactic correctness.** -/
theorem cellCopyClause_iff (a : ℕ → Bool) (t p : ℕ) :
    evalFormula a (cellCopyClause t p) = true
      ↔ (a (headVar t p) = false → a (cellVar (t + 1) p) = a (cellVar t p)) :=
  guardedIff_iff a _ _ _

/-! ## The trace-encoding assignment and clause soundness -/

/-- Read the real computation off the tableau variables: cell `c[t][p]` = the tape cell, head `h[t][p]` = "head
sits at `p`".  (State bits are stubbed `false`; they belong to the deferred state/head window.) -/
def traceAssign (M : Machine) (x : List Bool) (v : ℕ) : Bool :=
  if v % 3 = 0 then (run M (Nat.unpair (v / 3)).1 (init M x)).tp.getD (Nat.unpair (v / 3)).2 false
  else if v % 3 = 1 then decide ((run M (Nat.unpair (v / 3)).1 (init M x)).hd = (Nat.unpair (v / 3)).2)
  else false

theorem traceAssign_cell (M : Machine) (x : List Bool) (t p : ℕ) :
    traceAssign M x (cellVar t p) = (run M t (init M x)).tp.getD p false := by
  unfold traceAssign cellVar
  rw [show 3 * Nat.pair t p % 3 = 0 from by omega, show 3 * Nat.pair t p / 3 = Nat.pair t p from by omega,
    Nat.unpair_pair]
  simp

theorem traceAssign_head (M : Machine) (x : List Bool) (t p : ℕ) :
    traceAssign M x (headVar t p) = decide ((run M t (init M x)).hd = p) := by
  unfold traceAssign headVar
  rw [show (3 * Nat.pair t p + 1) % 3 = 1 from by omega, show (3 * Nat.pair t p + 1) / 3 = Nat.pair t p from by omega,
    Nat.unpair_pair]
  simp

/-- **Soundness of the cell-copy clause.**  The assignment that reads the real run off the tape satisfies the
cell-copy clause — this is exactly where transition locality (`step_tape_getD_ne`) is used: when the head is not at
`p` at time `t`, the cell is unchanged from `t` to `t+1`. -/
theorem cellCopyClause_sound (M : Machine) (x : List Bool) (t p : ℕ) :
    evalFormula (traceAssign M x) (cellCopyClause t p) = true := by
  rw [cellCopyClause_iff]
  intro hh
  rw [traceAssign_head] at hh
  rw [traceAssign_cell, traceAssign_cell, run_succ]
  exact step_tape_getD_ne_all M (run M t (init M x)) p (Ne.symm (of_decide_eq_false hh))

end PallLean.Paper93.DeepMath.PathB.CookLevinTransition
