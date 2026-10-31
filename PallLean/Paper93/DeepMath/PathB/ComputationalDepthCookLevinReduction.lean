import PallLean.Paper93.DeepMath.PathB.ComputationalDepthComposableMachine

/-!
# Cook–Levin over `ComposableMachine` — honest foundations (NOT the theorem)

`CookLevin SATV := ∀ L, NPLang L → PolyReduces L (acceptBool SATV)` is the genuine NP-hardness half of
Cook–Levin: every NP language many-one reduces to a **concrete** SAT verifier's boundary.  Per `SCOPE_COOKLEVIN.md`
the faithful construction has two constructive-but-large sub-mountains — (M1) a CNF-evaluator `ComposableMachine`
so `SATV.verify ∈ P`, and (M2) the tableau reduction (encode `Mᵥ`'s bounded-witness computation as a CNF, emit it
by a poly transducer, prove satisfiable ⟺ accepting run).  Neither is hardness-strength (they are theorems of ZFC),
but a full sorry-free proof is a research-scale formalization, not a session; **this file does not claim
`CookLevin`** and contains no `sorry`, no axiom, no hardness socket.

What it builds are the two honest foundations every tableau rests on:

* **CNF/SAT semantics** (`Formula`, `evalFormula`, `Satisfiable`) — the object M2 emits and M1 evaluates.
* **Local checkability** (`run_eq_of_localCheck`) — any config sequence starting at `init` whose every successor is
  `step` **is** the run.  This is the precise reason "`Mᵥ` accepts" is a *local* (per-step) constraint, hence
  compilable to a CNF: the transition clauses pin a unique trace, and it is the real computation.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinReduction

open PallLean.Paper93.DeepMath.PathB.ComposableMachine (Machine Cfg init step run run_zero run_succ)

/-! ## CNF / SAT semantics -/

/-- A literal: a variable index with the polarity (value) that satisfies it. -/
abbrev Lit := ℕ × Bool

/-- A clause is a disjunction of literals. -/
abbrev Clause := List Lit

/-- A formula (CNF) is a conjunction of clauses. -/
abbrev Formula := List Clause

/-- A literal `(v, s)` is satisfied by `a` when `a v = s`. -/
def evalLit (a : ℕ → Bool) (l : Lit) : Bool := a l.1 == l.2

/-- A clause is satisfied when some literal is. -/
def evalClause (a : ℕ → Bool) (c : Clause) : Bool := c.any (evalLit a)

/-- A formula is satisfied when every clause is. -/
def evalFormula (a : ℕ → Bool) (φ : Formula) : Bool := φ.all (evalClause a)

/-- Satisfiability: some assignment satisfies every clause. -/
def Satisfiable (φ : Formula) : Prop := ∃ a : ℕ → Bool, evalFormula a φ = true

/-- The empty formula is satisfiable (vacuously). -/
theorem satisfiable_nil : Satisfiable [] := ⟨fun _ => false, rfl⟩

/-- A formula containing the empty clause is unsatisfiable — the semantics are non-trivial. -/
theorem not_sat_of_mem_empty_clause {φ : Formula} (h : [] ∈ φ) : ¬ Satisfiable φ := by
  rintro ⟨a, ha⟩
  rw [evalFormula, List.all_eq_true] at ha
  have h2 := ha [] h
  rw [evalClause] at h2
  simp at h2

/-- Adding a clause only restricts satisfiability (monotonicity). -/
theorem satisfiable_of_cons {c : Clause} {φ : Formula} (h : Satisfiable (c :: φ)) : Satisfiable φ := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  simp only [evalFormula, List.all_cons, Bool.and_eq_true] at ha
  exact ha.2

/-! ## Local checkability of `ComposableMachine` runs — the tableau backbone -/

/-- **Local checkability.**  Any configuration sequence `cs` that starts at `init M x` and whose every successor is
`step M` of its predecessor **is** the actual run: `cs i = run M i (init M x)`.  This is the exact fact that makes
"`M` accepts" a *local* constraint — the transition relation, checked between consecutive configs, forces a unique
trace equal to the real computation.  The tableau's transition clauses are the CNF encoding of the hypotheses. -/
theorem run_eq_of_localCheck (M : Machine) (x : List Bool) (cs : ℕ → Cfg M)
    (h0 : cs 0 = init M x) (hstep : ∀ i, cs (i + 1) = step M (cs i)) :
    ∀ i, cs i = run M i (init M x) := by
  intro i
  induction i with
  | zero => rw [h0, run_zero]
  | succ i ih => rw [hstep i, ih, run_succ]

/-- The run itself satisfies the local constraints at step `0`. -/
theorem run_localCheck_zero (M : Machine) (x : List Bool) :
    run M 0 (init M x) = init M x := run_zero M _

/-- The run itself satisfies the local (transition) constraint at every step. -/
theorem run_localCheck_step (M : Machine) (x : List Bool) (i : ℕ) :
    run M (i + 1) (init M x) = step M (run M i (init M x)) := run_succ M i _

/-- **Consequence: a locally-valid trace decides acceptance.**  If `cs` is any locally-valid trace of length
`> t`, then its `t`-th config carries the machine's state at time `t` — so reading `M.accept` and `M.halt` off
`cs t` is exactly the real decision.  (This is the acceptance clause's soundness in the tableau: the accept check
on the final tableau row equals the real computation's decision.) -/
theorem localCheck_decides (M : Machine) (x : List Bool) (cs : ℕ → Cfg M)
    (h0 : cs 0 = init M x) (hstep : ∀ i, cs (i + 1) = step M (cs i)) (t : ℕ) :
    M.accept (cs t).st = M.accept (run M t (init M x)).st := by
  rw [run_eq_of_localCheck M x cs h0 hstep t]

end PallLean.Paper93.DeepMath.PathB.CookLevinReduction
