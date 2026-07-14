import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinReduction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinShiftLoop

/-!
# Cook–Levin M2 — the tableau's semantic backbone (bricks, NOT the theorem)

Per `SCOPE_COOKLEVIN.md`, the full `CookLevin` reduction (M2: emit `Mᵥ`'s bounded computation as a CNF by a poly
transducer and prove `Satisfiable ⟺ accepting run`) is a research-scale formalization, not a session — comparable
faithful efforts are multi-person, multi-month.  This file does **not** claim `CookLevin`; it adds the two genuine,
non-circular, hardness-free bricks the tableau's *correctness* rests on, on top of `run_eq_of_localCheck`:

* **Transition locality** (`step_tape_getD_ne`) — a tape cell away from the head is unchanged by one step.  This is
  the exact reason the row-to-row transition compiles to **per-cell clauses** (each cell's next value depends only
  on a bounded local window: itself and the head/state), the "crux" the scope flags.

* **Abstract tableau soundness** (`tableau_accepts_iff`) — a valid accepting *trace* (`init`, step-consistent,
  accepting final state) exists **iff** the machine halts-accepting.  The tableau CNF encodes exactly "a valid
  accepting trace exists" (init ∧ transition ∧ accept clauses); its satisfiability is this `∃`, so this lemma is
  the reduction's semantic heart — modulo the (deferred, large) CNF encoding of `ValidTrace` as bit-clauses.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinTableau

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction (run_eq_of_localCheck)
open PallLean.Paper93.DeepMath.PathB.CookLevinShiftLoop (writeAt_getD_ne)

/-! ## Transition locality — the per-cell window -/

/-- **Tape locality.**  One step leaves every tape cell except the head cell unchanged.  Hence in the tableau the
next row's cell `p` is determined by a *bounded local window* — cell `p` and (whether the head sits at) `p` — which
is what lets the transition relation be written as per-cell CNF clauses. -/
theorem step_tape_getD_ne (M : Machine) (c : Cfg M) (p : ℕ) (hp : p ≠ c.hd)
    (hh : M.halt c.st = false) : (step M c).tp.getD p false = c.tp.getD p false := by
  simp only [step, hh, Bool.false_eq_true, if_false]
  cases hw : (M.δ c.st (c.tp.getD c.hd false)).2.1 with
  | none => simp only [hw]
  | some w => simp only [hw]; exact writeAt_getD_ne hp

/-- **State/head are a function of the local window.**  Off a halted state, the next state and head depend only on
the current state, head, and the single cell under the head — the other local part of the transition window. -/
theorem step_st_hd (M : Machine) (c : Cfg M) (hh : M.halt c.st = false) :
    (step M c).st = (M.δ c.st (c.tp.getD c.hd false)).1
    ∧ (step M c).hd = moveHead c.hd (M.δ c.st (c.tp.getD c.hd false)).2.2 := by
  unfold step
  rw [if_neg (by rw [hh]; decide)]
  exact ⟨rfl, rfl⟩

/-! ## The abstract tableau: valid traces -/

/-- A **valid trace** of length `T`: it starts at the forced initial config and each successor (up to `T`) is one
machine step.  These are exactly the constraints the tableau's init and transition clauses encode. -/
def ValidTrace (M : Machine) (x : List Bool) (cs : ℕ → Cfg M) (T : ℕ) : Prop :=
  cs 0 = init M x ∧ ∀ i, i < T → cs (i + 1) = step M (cs i)

/-- The real computation is a valid trace. -/
theorem run_isValidTrace (M : Machine) (x : List Bool) (T : ℕ) :
    ValidTrace M x (fun i => run M i (init M x)) T :=
  ⟨run_zero M _, fun i _ => run_succ M i _⟩

/-- **A valid trace is the real computation.**  Every valid trace agrees with the run on `[0, T]` (from
`run_eq_of_localCheck`): the transition constraints pin the *unique* trace, and it is the actual run. -/
theorem tableau_trace_eq (M : Machine) (x : List Bool) (cs : ℕ → Cfg M) (T : ℕ)
    (hv : ValidTrace M x cs T) : ∀ i, i ≤ T → cs i = run M i (init M x) := by
  intro i hi
  induction i with
  | zero => rw [hv.1, run_zero]
  | succ i ih => rw [hv.2 i (by omega), ih (by omega), run_succ]

/-- **Abstract tableau soundness.**  A valid accepting trace of length `T` exists **iff** the machine halts and
accepts by step `T` — i.e. iff `HaltsBy ∧ decideOut = true`.  The tableau CNF is satisfiable exactly when such a
trace exists, so this is the `Satisfiable ⟺ accepting run` equivalence at the (pre-encoding) trace level. -/
theorem tableau_accepts_iff (M : Machine) (x : List Bool) (T : ℕ) :
    (∃ cs, ValidTrace M x cs T ∧ M.halt (cs T).st = true ∧ M.accept (cs T).st = true)
    ↔ (HaltsBy M x T ∧ decideOut M x T = true) := by
  constructor
  · rintro ⟨cs, hv, hhalt, hacc⟩
    rw [tableau_trace_eq M x cs T hv T (le_refl T)] at hhalt hacc
    exact ⟨hhalt, hacc⟩
  · rintro ⟨hhalt, hacc⟩
    exact ⟨fun i => run M i (init M x), run_isValidTrace M x T, hhalt, hacc⟩

end PallLean.Paper93.DeepMath.PathB.CookLevinTableau
