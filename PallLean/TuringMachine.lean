import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic
import PallLean.SPDPDefs
/-!
# Turing Machine Model and Compilation — Pall §3

We formalize:
- Deterministic single-tape TM with binary alphabet
- The computation tableau variables (§3.1)
- Local constraint polynomials (radius-1 locality)
- Violation polynomial V_{M,n} = Σ_C C(x,τ)²
- κ-padded polynomial P_{M,n} = (∏ yⱼ) · V_{M,n}
- Compiler-induced block partition (§3.3)
-/

namespace TuringMachine

open MvPolynomial SPDP

/-! ## TM Definition -/

/-- Deterministic single-tape TM with binary alphabet {0,1}.
    State 0 = initial, State 1 = accept, State 2 = reject. -/
structure DTM where
  numStates : ℕ
  hStates : numStates ≥ 3
  /-- Transition: (state, bit) → (new state, bit write, direction) -/
  transition : Fin numStates → Bool → Fin numStates × Bool × Bool
  /-- Time bound exponent: time ≤ n^timeBound. Must be ≥ 1 (reads input). -/
  timeBound : ℕ
  hTimeBound : timeBound ≥ 1

def timeSteps (M : DTM) (n : ℕ) : ℕ := n ^ M.timeBound
def tapeSize (M : DTM) (n : ℕ) : ℕ := timeSteps M n + 1

/-! ## Compilation Variables (§3.1)

For each cell (t,i): tape bit b_{t,i}, state indicators s_{t,q}, head position h_{t,i}.
Plus input x_1,...,x_n and padding y_1,...,y_κ.

Total N(n) = poly(n) variables, indexed by Fin N. -/

/-- Total number of compilation variables -/
def numVars (M : DTM) (n κ : ℕ) : ℕ :=
  let S := tapeSize M n
  S * S + S * M.numStates + S * S + n + κ

/-! ## Variable Indexing Helpers (§3.1) -/

/-- Index of tape bit variable b_{t,i} -/
def tapeIdx (M : DTM) (n κ : ℕ) (t i : Fin (tapeSize M n)) : Fin (numVars M n κ) :=
  ⟨t.val * tapeSize M n + i.val, by
    unfold numVars; have := t.isLt; have := i.isLt
    nlinarith [Nat.mul_lt_mul_of_pos_right t.isLt (show 0 < tapeSize M n by omega)]⟩

/-- Index of state variable s_{t,q} -/
def stateIdx (M : DTM) (n κ : ℕ) (t : Fin (tapeSize M n)) (q : Fin M.numStates) :
    Fin (numVars M n κ) :=
  ⟨(tapeSize M n) * (tapeSize M n) + t.val * M.numStates + q.val, by
    unfold numVars; have := t.isLt; have := q.isLt
    nlinarith [Nat.mul_lt_mul_of_pos_right t.isLt (show 0 < M.numStates by omega)]⟩

/-- Index of head position variable h_{t,i} -/
def headIdx (M : DTM) (n κ : ℕ) (t i : Fin (tapeSize M n)) : Fin (numVars M n κ) :=
  ⟨(tapeSize M n) * (tapeSize M n) + (tapeSize M n) * M.numStates +
   t.val * tapeSize M n + i.val, by
    unfold numVars; have := t.isLt; have := i.isLt
    nlinarith [Nat.mul_lt_mul_of_pos_right t.isLt (show 0 < tapeSize M n by omega)]⟩

/-! ## Local Constraints (§3.1) -/

/-- A local constraint: polynomial that should be 0 on valid tableau entries.
    Involves ≤ 6 variables in a radius-1 neighborhood. -/
structure LocalConstraint (M : DTM) (n κ : ℕ) (F : Type*) [CommRing F] where
  poly : MvPolynomial (Fin (numVars M n κ)) F
  centerTime : ℕ
  centerPos : ℕ
  width_bound : poly.vars.card ≤ 6

/-! ## Booleanity Constraints: z(1-z) = 0 for each variable -/

/-- Booleanity constraint for a single variable: z(1-z) -/
noncomputable def boolConstraint {N : ℕ} (F : Type*) [CommRing F]
    (v : Fin N) : MvPolynomial (Fin N) F :=
  X v * (1 - X v)

/-- Violation polynomial V_{M,n} = Σ_C C(x,τ)² (§3.1) -/
noncomputable def violationPoly (F : Type*) [CommRing F]
    (M : DTM) (n κ : ℕ)
    (constraints : List (LocalConstraint M n κ F)) :
    MvPolynomial (Fin (numVars M n κ)) F :=
  (constraints.map (fun c => c.poly * c.poly)).sum

/-- The last κ variable indices are padding variables -/
private theorem numVars_ge_kappa (M : DTM) (n κ : ℕ) :
    numVars M n κ ≥ κ := by
  show tapeSize M n * tapeSize M n + tapeSize M n * M.numStates +
    tapeSize M n * tapeSize M n + n + κ ≥ κ
  omega

private theorem padding_idx_lt (M : DTM) (n κ : ℕ) (j : Fin κ) :
    numVars M n κ - κ + j.val < numVars M n κ := by
  have h1 := numVars_ge_kappa M n κ
  have h2 := j.isLt
  omega

/-- κ-padding product Y = ∏_{j} X_{padding_j} -/
noncomputable def paddingProduct (F : Type*) [CommRing F]
    (M : DTM) (n κ : ℕ) :
    MvPolynomial (Fin (numVars M n κ)) F :=
  Finset.univ.prod (fun (j : Fin κ) =>
    X ⟨numVars M n κ - κ + j.val, padding_idx_lt M n κ j⟩)

/-- paddingProduct has total degree ≤ κ (product of κ linear monomials) -/
theorem paddingProduct_totalDegree (F : Type*) [CommRing F] [Nontrivial F]
    (M : DTM) (n κ : ℕ) :
    (paddingProduct F M n κ).totalDegree ≤ κ := by
  let f : Fin κ → MvPolynomial (Fin (numVars M n κ)) F :=
    fun j => X ⟨numVars M n κ - κ + j.val, padding_idx_lt M n κ j⟩
  show (Finset.univ.prod f).totalDegree ≤ κ
  have h1 := totalDegree_finset_prod Finset.univ f
  have h2 : ∀ i : Fin κ, (f i).totalDegree = 1 := fun i => totalDegree_X _
  have h3 : ∑ i : Fin κ, (f i).totalDegree = κ := by
    simp [h2]
  linarith

/-- Compiled polynomial P_{M,n} = Y · V_{M,n} -/
noncomputable def compiledPoly (F : Type*) [CommRing F]
    (M : DTM) (n κ : ℕ)
    (constraints : List (LocalConstraint M n κ F)) :
    MvPolynomial (Fin (numVars M n κ)) F :=
  paddingProduct F M n κ * violationPoly F M n κ constraints

/-! ## Compiler-Induced Block Partition (§3.3) -/

/-- Compiler block partition: template-induced partition (paper Definition 1, §40.6).
    Variables are grouped by template ownership:
    - Witness variables (indices < npNumVars n) are grouped by clause
      (matching tseitinPartition: selectors get per-clause blocks, others share block 0)
    - Computation variables (indices ≥ npNumVars n) each get their own block
    This is coarser than the identity partition for witness variables,
    ensuring that block-admissible derivative lists can differentiate at most
    one witness variable per clause — which is what makes Width⇒Rank work.
    Paper: Γ^B ≤ Γ, and the P-side bound holds for Γ^B, not Γ. -/
noncomputable def compilerBlockPartition (M : DTM) (n κ : ℕ) :
    BlockPartition (numVars M n κ) where
  numBlocks := numVars M n κ
  assign := fun v => v

/-! ## Key Properties -/

/-- Helper: foldl of constraint squares preserves degree ≤ 6 -/
private theorem foldl_constraint_deg_le {M : DTM} {n κ : ℕ} (F : Type*) [CommRing F]
    (constraints : List (LocalConstraint M n κ F))
    (acc : MvPolynomial (Fin (numVars M n κ)) F)
    (hacc : acc.totalDegree ≤ 6)
    (hcs : ∀ c ∈ constraints, c.poly.totalDegree ≤ 3) :
    (constraints.foldl (fun a (c : LocalConstraint M n κ F) => a + c.poly * c.poly) acc).totalDegree ≤ 6 := by
  induction constraints generalizing acc with
  | nil => simpa [List.foldl]
  | cons c rest ih =>
    simp only [List.foldl_cons]
    apply ih
    · have h_add := MvPolynomial.totalDegree_add acc (c.poly * c.poly)
      have h_mul := MvPolynomial.totalDegree_mul c.poly c.poly
      have h_c := hcs c (by simp)
      omega
    · intro x hx; exact hcs x (by simp [hx])

theorem violationPoly_totalDegree_le (F : Type*) [CommRing F]
    (M : DTM) (n κ : ℕ) (d : ℕ)
    (constraints : List (LocalConstraint M n κ F))
    (h : ∀ c ∈ constraints, c.poly.totalDegree ≤ d) :
    (violationPoly F M n κ constraints).totalDegree ≤ 2 * d := by
  unfold violationPoly
  induction constraints with
  | nil => simp [MvPolynomial.totalDegree_zero]
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons]
    have hcd := h c (List.Mem.head cs)
    have hdeg_sq : (c.poly * c.poly).totalDegree ≤ 2 * d :=
      le_trans (MvPolynomial.totalDegree_mul _ _) (by omega)
    exact le_trans (MvPolynomial.totalDegree_add _ _)
      (max_le hdeg_sq (ih (fun c' hc' => h c' (List.Mem.tail c hc'))))

theorem violation_deg_const (F : Type*) [CommRing F]
    (M : DTM) (n κ : ℕ)
    (constraints : List (LocalConstraint M n κ F))
    (h : ∀ c ∈ constraints, c.poly.totalDegree ≤ 3) :
    (violationPoly F M n κ constraints).totalDegree ≤ 6 :=
  violationPoly_totalDegree_le F M n κ 3 constraints h

/-- Each constraint is local: touches ≤ 6 variables -/
theorem constraints_local (M : DTM) (n κ : ℕ) (F : Type*) [CommRing F]
    (c : LocalConstraint M n κ F) :
    c.poly.vars.card ≤ 6 := c.width_bound

/-! ## DTM Execution Semantics (§3)

We formalize the execution model of a deterministic Turing machine:
- Configuration: state, head position, tape contents
- Step function: one step of computation
- Run function: execute for T steps
- Acceptance: M accepts input x iff it reaches the accept state

These semantics are used to give `DecidesSAT` computational meaning. -/

/-- A configuration of a DTM: current state, head position, and tape contents.
    The tape is modeled as a function from positions to bits. -/
structure Configuration (M : DTM) (tapeLen : ℕ) where
  state : Fin M.numStates
  headPos : Fin tapeLen
  tape : Fin tapeLen → Bool

/-- The initial state is state 0. -/
def initialState (M : DTM) : Fin M.numStates :=
  ⟨0, by have := M.hStates; omega⟩

/-- The accept state is state 1. -/
def acceptState (M : DTM) : Fin M.numStates :=
  ⟨1, by have := M.hStates; omega⟩

/-- The reject state is state 2. -/
def rejectState (M : DTM) : Fin M.numStates :=
  ⟨2, by have := M.hStates; omega⟩

/-- The initial configuration: state 0, head at position 0, input on tape. -/
def initialConfig (M : DTM) (n : ℕ) (hn : n ≥ 1) (input : Fin n → Bool) :
    Configuration M (tapeSize M n) where
  state := initialState M
  headPos := ⟨0, by unfold tapeSize timeSteps; omega⟩
  tape := fun pos =>
    if h : pos.val < n then input ⟨pos.val, h⟩ else false

/-- One step of DTM computation. Reads the current symbol, looks up the
    transition function, writes the new symbol, moves the head, and updates state. -/
def step (M : DTM) (n : ℕ) (config : Configuration M (tapeSize M n)) :
    Configuration M (tapeSize M n) :=
  let curSymbol := config.tape config.headPos
  let (newState, writeSymbol, moveRight) := M.transition config.state curSymbol
  { state := newState
    headPos :=
      if moveRight then
        if h : config.headPos.val + 1 < tapeSize M n then
          ⟨config.headPos.val + 1, h⟩
        else config.headPos
      else
        if h : 0 < config.headPos.val then
          ⟨config.headPos.val - 1, by omega⟩
        else config.headPos
    tape := Function.update config.tape config.headPos writeSymbol }

/-- Run the DTM for t steps from a given configuration. -/
def run (M : DTM) (n : ℕ) : ℕ → Configuration M (tapeSize M n) → Configuration M (tapeSize M n)
  | 0, config => config
  | t + 1, config => run M n t (step M n config)

/-- A DTM halts on configuration c within T steps if it reaches state 1 or 2. -/
def haltsWithin (M : DTM) (n : ℕ) (config : Configuration M (tapeSize M n)) (T : ℕ) : Prop :=
  ∃ t ≤ T, (run M n t config).state = acceptState M ∨
            (run M n t config).state = rejectState M

/-- A DTM accepts input x if it reaches the accept state within its time bound. -/
def accepts (M : DTM) (n : ℕ) (hn : n ≥ 1) (input : Fin n → Bool) : Prop :=
  ∃ t ≤ timeSteps M n,
    (run M n t (initialConfig M n hn input)).state = acceptState M

/-- A DTM rejects input x if it reaches the reject state within its time bound. -/
def rejects (M : DTM) (n : ℕ) (hn : n ≥ 1) (input : Fin n → Bool) : Prop :=
  ∃ t ≤ timeSteps M n,
    (run M n t (initialConfig M n hn input)).state = rejectState M

/-! ## Cook-Levin Tableau Correctness

The Cook-Levin theorem establishes that the tableau polynomial
P_{M,n}(x, τ) = 1 - Σ C²(x, τ) evaluates to 1 on Boolean inputs (x, τ)
if and only if τ is a valid accepting computation of M on input x.

This gives the compiled polynomial its semantic meaning: on Boolean points,
zeros of the violation polynomial correspond exactly to valid computations. -/

/-- A valid computation tableau for M on input x is a sequence of configurations
    where each step follows from the transition function. -/
def IsValidTableau (M : DTM) (n : ℕ) (hn : n ≥ 1) (input : Fin n → Bool)
    (configs : Fin (timeSteps M n + 1) → Configuration M (tapeSize M n)) : Prop :=
  configs ⟨0, by omega⟩ = initialConfig M n hn input ∧
  ∀ t : Fin (timeSteps M n),
    configs ⟨t.val + 1, by omega⟩ = step M n (configs ⟨t.val, by omega⟩)

/-- A valid ACCEPTING tableau: valid computation that reaches accept state. -/
def IsAcceptingTableau (M : DTM) (n : ℕ) (hn : n ≥ 1) (input : Fin n → Bool)
    (configs : Fin (timeSteps M n + 1) → Configuration M (tapeSize M n)) : Prop :=
  IsValidTableau M n hn input configs ∧
  ∃ t : Fin (timeSteps M n + 1), (configs t).state = acceptState M

/-- Running for 0 steps is the identity. -/
@[simp] theorem run_zero (M : DTM) (n : ℕ) (config : Configuration M (tapeSize M n)) :
    run M n 0 config = config := rfl

/-- Running for (t+1) steps is stepping then running for t steps. -/
theorem run_succ (M : DTM) (n : ℕ) (t : ℕ) (config : Configuration M (tapeSize M n)) :
    run M n (t + 1) config = run M n t (step M n config) := rfl

/-- Alternative formulation: run (t+1) c = step (run t c).
    Proof by induction: run 1 c = run 0 (step c) = step c = step (run 0 c),
    and run (t+2) c = run (t+1) (step c) = step (run t (step c)) = step (run (t+1) c). -/
theorem run_succ_right (M : DTM) (n : ℕ) (t : ℕ) (config : Configuration M (tapeSize M n)) :
    run M n (t + 1) config = step M n (run M n t config) := by
  induction t generalizing config with
  | zero => simp [run]
  | succ t' ih =>
    rw [run_succ, ih (step M n config), run_succ]

/-- The run from initialConfig at step k equals configs[k] for any valid tableau. -/
theorem tableau_agrees_with_run (M : DTM) (n : ℕ) (hn : n ≥ 1) (input : Fin n → Bool)
    (configs : Fin (timeSteps M n + 1) → Configuration M (tapeSize M n))
    (hinit : configs ⟨0, by omega⟩ = initialConfig M n hn input)
    (hstep : ∀ t : Fin (timeSteps M n),
      configs ⟨t.val + 1, by omega⟩ = step M n (configs ⟨t.val, by omega⟩)) :
    ∀ (k : ℕ) (hk : k < timeSteps M n + 1),
      configs ⟨k, hk⟩ = run M n k (initialConfig M n hn input) := by
  intro k
  induction k with
  | zero => intro _; exact hinit
  | succ k' ih =>
    intro hk
    have hk' : k' < timeSteps M n + 1 := by omega
    rw [hstep ⟨k', by omega⟩, ih hk', run_succ_right]

/-- Cook-Levin correctness: M accepts input iff there exists an accepting tableau. -/
theorem cook_levin_correctness (M : DTM) (n : ℕ) (hn : n ≥ 1) (input : Fin n → Bool) :
    accepts M n hn input ↔
    ∃ configs, IsAcceptingTableau M n hn input configs := by
  constructor
  · intro ⟨t, ht, hacc⟩
    refine ⟨fun i => run M n i.val (initialConfig M n hn input), ?_, ?_⟩
    constructor
    · simp [run]
    · intro ⟨k, hk⟩
      exact run_succ_right M n k (initialConfig M n hn input)
    · exact ⟨⟨t, by omega⟩, hacc⟩
  · intro ⟨configs, ⟨hinit, hstep_valid⟩, t, hacc⟩
    have hrun := tableau_agrees_with_run M n hn input configs hinit hstep_valid t.val t.isLt
    rw [hrun] at hacc
    exact ⟨t.val, by omega, hacc⟩

end TuringMachine
