import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinOneHotWindow

/-!
# Cook–Levin M2 — the δ-dynamics transition clause (with soundness)

The last transition-window piece: the state and head at time `t+1` are determined by `δ` applied to the state and
the cell under the head at time `t` (with a self-loop once halted, since a halted step is the identity).  This file
builds that clause and proves it **sound** against the real computation.

* A generic **implication clause** `implClause` — `guard₁ ∧ guard₂ ∧ guard₃ → concl` as one clause — with correctness.
* `stepStateHead` — the state/head transition as a function of the *local window* `(state, head, head-cell)`,
  unifying the halted (identity) and running (`δ`) cases; `step_via_stepStateHead` pins one machine step to it.
* `dynamicsClause M t q p b` — "state `q` ∧ head `p` ∧ cell `= b` at `t` ⇒ the `δ`/self-loop next state and head at
  `t+1`", and `dynamicsClause_sound`: the trace assignment of the real run satisfies it (cashing in
  `step_via_stepStateHead` and the `Fin`-encoding round-trip).

Per `SCOPE_COOKLEVIN.md` the remaining M2 (init/accept assembly, whole-formula `Satisfiable ⟺ accepting`, poly
emitter) is deferred; this completes the *clause-level* soundness bricks.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinDynamics

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinTableau
open PallLean.Paper93.DeepMath.PathB.CookLevinTransition
open PallLean.Paper93.DeepMath.PathB.CookLevinOneHotWindow

/-- Read the cell bit off the run (companion of `fullAssign_head`/`_state`). -/
theorem fullAssign_cell (M : Machine) (x : List Bool) (t p : ℕ) :
    fullAssign M x (cellVar t p) = (run M t (init M x)).tp.getD p false := by
  unfold fullAssign cellVar
  rw [show 3 * Nat.pair t p % 3 = 0 from by omega, show 3 * Nat.pair t p / 3 = Nat.pair t p from by omega,
    Nat.unpair_pair]
  simp

/-! ## The implication clause primitive -/

/-- `g₁ ∧ g₂ ∧ g₃ → concl`, as a single clause (negate each guard, keep the conclusion). -/
def implClause (g1 g2 g3 concl : Lit) : Clause :=
  [(g1.1, !g1.2), (g2.1, !g2.2), (g3.1, !g3.2), concl]

/-- **Correctness of the implication clause.** -/
theorem implClause_iff (a : ℕ → Bool) (g1 g2 g3 concl : Lit) :
    evalClause a (implClause g1 g2 g3 concl) = true
      ↔ ((evalLit a g1 = true ∧ evalLit a g2 = true ∧ evalLit a g3 = true) → evalLit a concl = true) := by
  simp only [implClause, evalClause, List.any_cons, List.any_nil, Bool.or_false, evalLit,
    show ∀ (v : ℕ) (s : Bool), (a v == !s) = !(a v == s) from fun v s => by cases a v <;> cases s <;> rfl]
  cases a g1.1 == g1.2 <;> cases a g2.1 == g2.2 <;> cases a g3.1 == g3.2 <;> cases a concl.1 == concl.2 <;> simp

/-! ## The local-window state/head step -/

/-- The next `(state, head)` as a function of the local window `(state, head, head-cell)`: identity once halted,
else `δ` and `moveHead`. -/
def stepStateHead (M : Machine) (s : M.State) (p : ℕ) (b : Bool) : M.State × ℕ :=
  if M.halt s then (s, p) else ((M.δ s b).1, moveHead p (M.δ s b).2.2)

/-- **One step equals the local-window step.**  Unifies `step_st_hd` (running) and `step_of_halt` (halted). -/
theorem step_via_stepStateHead (M : Machine) (c : Cfg M) :
    (step M c).st = (stepStateHead M c.st c.hd (c.tp.getD c.hd false)).1
    ∧ (step M c).hd = (stepStateHead M c.st c.hd (c.tp.getD c.hd false)).2 := by
  unfold stepStateHead
  by_cases hh : M.halt c.st = true
  · rw [step_of_halt M c hh, if_pos hh]; exact ⟨rfl, rfl⟩
  · rw [if_neg hh]; exact step_st_hd M c (by simpa using hh)

/-! ## The δ-dynamics clause -/

/-- Next-state index under the local window `(q, p, b)`. -/
noncomputable def nextStateIdx (M : Machine) (q : Fin (Fintype.card M.State)) (p : ℕ) (b : Bool) : ℕ :=
  (Fintype.equivFin M.State (stepStateHead M ((Fintype.equivFin M.State).symm q) p b).1).val

/-- Next head under the local window `(q, p, b)`. -/
noncomputable def nextHead (M : Machine) (q : Fin (Fintype.card M.State)) (p : ℕ) (b : Bool) : ℕ :=
  (stepStateHead M ((Fintype.equivFin M.State).symm q) p b).2

/-- The δ-dynamics clauses for the window "state `q`, head `p`, cell `= b` at time `t`": the next state and next
head at `t+1` are the `δ`/self-loop values. -/
noncomputable def dynamicsClause (M : Machine) (t : ℕ) (q : Fin (Fintype.card M.State)) (p : ℕ) (b : Bool) :
    Formula :=
  [implClause (stateVar t q.val, true) (headVar t p, true) (cellVar t p, b)
      (stateVar (t + 1) (nextStateIdx M q p b), true),
   implClause (stateVar t q.val, true) (headVar t p, true) (cellVar t p, b)
      (headVar (t + 1) (nextHead M q p b), true)]

/-- **Soundness of the δ-dynamics clause.**  The trace assignment of the real run satisfies it: whenever the window
matches at time `t`, the run's next state and head are exactly the `δ`/self-loop values encoded. -/
theorem dynamicsClause_sound (M : Machine) (x : List Bool) (t : ℕ) (q : Fin (Fintype.card M.State)) (p : ℕ)
    (b : Bool) : evalFormula (fullAssign M x) (dynamicsClause M t q p b) = true := by
  -- the shared consequent proof: from the window matching, the run's next config matches the local-window step
  have key : (fullAssign M x (stateVar t q.val) = true ∧ fullAssign M x (headVar t p) = true
        ∧ fullAssign M x (cellVar t p) = b) →
      (run M (t + 1) (init M x)).st = (stepStateHead M ((Fintype.equivFin M.State).symm q) p b).1
      ∧ (run M (t + 1) (init M x)).hd = (stepStateHead M ((Fintype.equivFin M.State).symm q) p b).2 := by
    rintro ⟨hs, hh, hb⟩
    rw [fullAssign_state, stateBit, dif_pos q.isLt, decide_eq_true_eq, Fin.eta] at hs
    rw [fullAssign_head, decide_eq_true_eq] at hh
    rw [fullAssign_cell] at hb
    obtain ⟨hst, hhd⟩ := step_via_stepStateHead M (run M t (init M x))
    rw [run_succ, hst, hhd, hs, hh, hb]
    exact ⟨rfl, rfl⟩
  rw [dynamicsClause, evalFormula_cons, evalFormula_cons, evalFormula, List.all_nil, Bool.and_true,
    Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [implClause_iff]
    intro hg
    simp only [evalLit, beq_iff_eq] at hg ⊢
    rw [fullAssign_state, stateBit,
      dif_pos (show nextStateIdx M q p b < Fintype.card M.State from by unfold nextStateIdx; exact Fin.isLt _),
      decide_eq_true_eq, (key hg).1]
    unfold nextStateIdx
    rw [Fin.eta, Equiv.symm_apply_apply]
  · rw [implClause_iff]
    intro hg
    simp only [evalLit, beq_iff_eq] at hg ⊢
    rw [fullAssign_head, decide_eq_true_eq, (key hg).2]
    rfl
end PallLean.Paper93.DeepMath.PathB.CookLevinDynamics
