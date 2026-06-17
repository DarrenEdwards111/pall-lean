import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ConcreteNTM
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NTM

/-!
# Physical TM transition tables — the clocked multi-step run from a deterministic table (proved)

The machine-cost sockets across the arc — the lazy-diagonalization *simulation* (entry 219), `ProvidesFastVerifiers`
(entry 201), `ClockedInclusion`/`ConcreteHierarchy` — all rest on a concrete *time-bounded* computation model: a
transition table driving a well-defined `t`-step computation.  Entry 205 proved a worked *one-step* run; this file
proves the **clocked multi-step run** from a **deterministic transition table** — and that it is a valid `reachIn` run
in the abstract `NTM` model.

The construction.  A deterministic table is a total function `δ : (state, read) → (state, write, move)`.  Its functional
step `detStep δ c := applyTrans c ((c.1, readSym c), δ (c.1, readSym c))` and `t`-step run `detRun δ t := (detStep δ)^[t]`
are well-defined; the run is **clocked-additive** (`detRun δ (a+b) = detRun δ b ∘ detRun δ a`); and crucially, the
functional run **is** a valid `t`-step reachability in the corresponding `NTM` (`detRun_reachIn`) — so a physical
deterministic transition table realises a genuine time-bounded computation in the model the cost-sockets reference.

## What is proved (clean axioms, no `sorry`)

* **`detStep`** / **`detRun`** — the functional step and `t`-step run of a deterministic transition table.
* **`detRun_add`** — clocked additivity: `detRun δ (a+b) c = detRun δ b (detRun δ a c)` (`Function.iterate_add_apply`).
* **`detNTM`** — the deterministic table as an abstract `NTM` (step `d = detStep δ c`).
* **`detRun_reachIn`** — the functional `t`-step run is a valid `reachIn` run: `reachIn (detNTM δ) t c (detRun δ t c)`
  (induction via `Function.iterate_succ_apply`).

## Honest scope

This proves the **physical transition-table → clocked computation** realisation: a deterministic table drives a
well-defined `t`-step run, clocked-additive, and that run is a genuine `reachIn` computation in the `NTM` model — the
time-bounded-computation substrate the machine-cost sockets (lazy-diagonalization simulation, `ProvidesFastVerifiers`,
clocked inclusion/hierarchy) reference.  Built on the entry-205/`…ACC0ConcreteNTM` transition-table apparatus
(`applyTrans`, `readSym`, `CConfig`).  What this does **not** do: the *clocking/time-bound counting* (relating
`detRun δ t` to a step-budget `≤ f(|x|)` and hence to the `NTIME(f)` classes), the *universal* table-driven simulation
of one machine by another (the universal-machine cost), or nondeterministic branching cost — those are the further
machine-cost content the `NTIME`-level sockets still need.  This proves the deterministic clocked run and its `reachIn`
validity, not the time-class accounting.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TransitionTable

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (NTM reachIn)

/-- **The functional step of a deterministic transition table.**  A total table `δ : (state, read) → (state, write,
move)` drives the step `applyTrans c ((c.1, readSym c), δ (c.1, readSym c))` — look up the rule for the current
`(state, read)` and apply it. -/
def detStep (δ : ℕ × Bool → ℕ × Bool × Move) (c : CConfig) : CConfig :=
  applyTrans c ((c.1, readSym c), δ (c.1, readSym c))

/-- **The clocked `t`-step run** of a deterministic transition table (`t`-fold iteration of `detStep`). -/
def detRun (δ : ℕ × Bool → ℕ × Bool × Move) (t : ℕ) (c : CConfig) : CConfig :=
  (detStep δ)^[t] c

/-- **Clocked additivity (PROVED).**  `detRun δ (a+b) c = detRun δ b (detRun δ a c)` — running `a` steps then `b` more
equals running `a+b` steps (`Function.iterate_add_apply`). -/
theorem detRun_add (δ : ℕ × Bool → ℕ × Bool × Move) (a b : ℕ) (c : CConfig) :
    detRun δ (a + b) c = detRun δ b (detRun δ a c) := by
  unfold detRun
  rw [show a + b = b + a from Nat.add_comm a b, Function.iterate_add_apply]

/-- **The deterministic table as an abstract `NTM`.**  Step relation `d = detStep δ c` (deterministic), start state `0`,
tape `= input`, accept iff state `1` — the bridge to the `…ACC0NTM` reachability model. -/
def detNTM (δ : ℕ × Bool → ℕ × Bool × Move) : NTM where
  Config := CConfig
  step := fun c d => d = detStep δ c
  init := fun x => (0, 0, x)
  accept := fun c => c.1 = 1

/-- **The clocked run is a valid `reachIn` run (PROVED).**  The functional `t`-step run `detRun δ t c` is reachable from
`c` in exactly `t` steps of the `NTM` `detNTM δ`: `reachIn (detNTM δ) t c (detRun δ t c)`.  Induction on `t` via
`Function.iterate_succ_apply` — so a physical deterministic transition table realises a genuine `t`-step computation in
the model. -/
theorem detRun_reachIn (δ : ℕ × Bool → ℕ × Bool × Move) (t : ℕ) (c : CConfig) :
    reachIn (detNTM δ) t c (detRun δ t c) := by
  induction t generalizing c with
  | zero => simp [reachIn, detRun]
  | succ m ih =>
      rw [reachIn]
      refine ⟨detStep δ c, rfl, ?_⟩
      rw [show detRun δ (m + 1) c = detRun δ m (detStep δ c) from by
        unfold detRun; rw [Function.iterate_succ_apply]]
      exact ih (detStep δ c)

end PallLean.Paper93.DeepMath.PathB.ACC0TransitionTable

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TransitionTable.detRun_add
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TransitionTable.detRun_reachIn
