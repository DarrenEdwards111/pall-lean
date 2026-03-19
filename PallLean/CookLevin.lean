/-
  CookLevin.lean — Cook-Levin Decomposition (documentation)

  The compiled_separation_axiom in CompiledSeparation.lean combines
  three sub-claims. This file documents the decomposition for
  transparency, but the main proof uses the combined axiom.

  Sub-claims:
  1. Cook-Levin construction: DTM → width-3 CNF (standard CS)
  2. Profile compression: block-local → rank ≤ √n (§8/§17.3)
  3. Extraction: perm rank ≤ compiled rank (§40/Lemma 206)
-/
import PallLean.CompiledPoly
import PallLean.PermanentLower
import PallLean.TuringMachine
import Mathlib.Tactic

namespace CookLevin

open CompiledPoly TuringMachine

/-- A Cook-Levin CNF encoding package at input size `n`. -/
structure CookLevinEncoding (M : DTM) (n : ℕ) where
  k : ℕ
  cnf : CookLevinCNF (compiledVarCount k n)
  hlp : HasLocalPartition cnf

/-- Natural choice for Cook-Levin exponent: use machine time exponent. -/
def defaultK (M : DTM) : ℕ := M.timeBound

/-- `compiledVarCount` is always at least the input length (for `n ≥ 1`). -/
theorem compiledVarCount_ge_n (k n : ℕ) (hn : n ≥ 1) :
    compiledVarCount k n ≥ n := by
  unfold compiledVarCount
  rw [pow_add, pow_one]
  have hn' : 0 < n := Nat.succ_le_iff.mp hn
  have hpow : n ^ (2 * k) ≥ 1 := by
    have hpos : 0 < n ^ (2 * k) := Nat.pow_pos hn'
    omega
  nlinarith

/-- Global version (handles `n = 0` by triviality). -/
theorem compiledVarCount_ge_n_all (k n : ℕ) :
    compiledVarCount k n ≥ n := by
  cases n with
  | zero => simp [compiledVarCount]
  | succ n' =>
    exact compiledVarCount_ge_n k (Nat.succ n') (by omega)

/-- For DTMs (timeBound ≥ 1), `compiledVarCount` is at least cubic in `n`. -/
theorem compiledVarCount_ge_cubic (M : DTM) (n : ℕ) (hn : n ≥ 1) :
    compiledVarCount M.timeBound n ≥ n ^ 3 := by
  unfold compiledVarCount
  have hk : 2 * M.timeBound + 1 ≥ 3 := by
    have htb : M.timeBound ≥ 1 := M.hTimeBound
    omega
  exact Nat.pow_le_pow_right hn hk

/-- Any variable index from the TM tableau can be embedded into the
    compiled variable index space once a bound is provided. -/
def embedVar {N N' : ℕ} (h : N ≤ N') : Fin N → Fin N' :=
  fun i => ⟨i.1, Nat.lt_of_lt_of_le i.2 h⟩

/-- Identity partition: one block per variable. -/
def identityPartition (N : ℕ) : BlockPartition N where
  numBlocks := N
  blockOf := fun v => v

/-- Any width-3 CNF is local under the identity partition. -/
def identity_local {N : ℕ} (cnf : CookLevinCNF N) :
    HasLocalPartition cnf := by
  refine ⟨identityPartition N, ?_, 1⟩
  intro c hc
  simpa [CLClause.isLocal, identityPartition, CLClause.vars] using c.vars_card_le

/-- Window-style partition scaffold: 3 repeating block labels.
    Think of these as coarse "time-window / role" buckets.
    This is closer in spirit to paper-style grouped blocks than identity. -/
def windowPartition (N : ℕ) : BlockPartition N where
  numBlocks := 3
  blockOf := fun v => ⟨v.1 % 3, Nat.mod_lt _ (by decide)⟩

/-- Time-slice partition scaffold:
    group variable indices by coarse slices (index / chunk), then map slices
    into 3 repeating buckets. This models "time-layer" grouping while keeping
    a fixed 3-block codomain so locality proofs stay simple. -/
def timeSlicePartition (N chunk : ℕ) (_hchunk : chunk > 0) : BlockPartition N where
  numBlocks := 3
  blockOf := fun v => ⟨(v.1 / chunk) % 3, Nat.mod_lt _ (by decide)⟩

/-- Default chunk size for slice-based scaffold. -/
def defaultTimeChunk : ℕ := 2

/-- Default tableau-style partition used in current scaffold. -/
def tableauPartition (N : ℕ) : BlockPartition N :=
  timeSlicePartition N defaultTimeChunk (by decide)

/-- Any clause is local under the 3-block window partition
    (image cardinality cannot exceed number of blocks = 3). -/
def window_local {N : ℕ} (cnf : CookLevinCNF N) :
    HasLocalPartition cnf := by
  refine ⟨windowPartition N, ?_, 3⟩
  intro c hc
  have hcard : (c.vars.image (windowPartition N).blockOf).card ≤ 3 := by
    have h' : (c.vars.image (windowPartition N).blockOf).card ≤ Fintype.card (Fin 3) :=
      Finset.card_le_univ (s := c.vars.image (windowPartition N).blockOf)
    simpa using h'
  simpa [CLClause.isLocal] using hcard

/-- Any clause is local under the tableau slice partition (same 3-block codomain). -/
def tableau_local {N : ℕ} (cnf : CookLevinCNF N) :
    HasLocalPartition cnf := by
  refine ⟨tableauPartition N, ?_, 3⟩
  intro c hc
  have hcard : (c.vars.image (tableauPartition N).blockOf).card ≤ 3 := by
    have h' : (c.vars.image (tableauPartition N).blockOf).card ≤ Fintype.card (Fin 3) :=
      Finset.card_le_univ (s := c.vars.image (tableauPartition N).blockOf)
    simpa using h'
  simpa [CLClause.isLocal] using hcard

/-- List-level locality helper under tableau partition. -/
theorem allClausesLocal_tableau {N : ℕ} (xs : List (CLClause N)) :
    ∀ c ∈ xs, c.isLocal (tableauPartition N) := by
  intro c hc
  have hcard : (c.vars.image (tableauPartition N).blockOf).card ≤ 3 := by
    have h' : (c.vars.image (tableauPartition N).blockOf).card ≤ Fintype.card (Fin 3) :=
      Finset.card_le_univ (s := c.vars.image (tableauPartition N).blockOf)
    simpa using h'
  simpa [CLClause.isLocal] using hcard

/-- Canonical one-block partition (used for coarse baseline estimates). -/
def oneBlockPartition (N : ℕ) : BlockPartition N where
  numBlocks := 1
  blockOf := fun _ => ⟨0, by omega⟩

/-- Every clause is local in the one-block partition. -/
def oneBlock_local {N : ℕ} (cnf : CookLevinCNF N) :
    HasLocalPartition cnf := by
  refine ⟨oneBlockPartition N, ?_, 1⟩
  intro c hc
  have hle1 : (c.vars.image (oneBlockPartition N).blockOf).card ≤ 1 := by
    simpa using (Finset.card_le_univ (s := c.vars.image (oneBlockPartition N).blockOf))
  exact le_trans hle1 (by omega)

/-- Positive literal helper. -/
def posLit {N : ℕ} (v : Fin N) : Fin N × Bool := (v, true)

/-- Negative literal helper. -/
def negLit {N : ℕ} (v : Fin N) : Fin N × Bool := (v, false)

/-- Smart constructor: 1-literal clause. -/
def clause1 {N : ℕ} (ℓ₁ : Fin N × Bool) : CLClause N :=
  ⟨[ℓ₁], by simp⟩

/-- Smart constructor: 2-literal clause. -/
def clause2 {N : ℕ} (ℓ₁ ℓ₂ : Fin N × Bool) : CLClause N :=
  ⟨[ℓ₁, ℓ₂], by simp⟩

/-- Smart constructor: 3-literal clause. -/
def clause3 {N : ℕ} (ℓ₁ ℓ₂ ℓ₃ : Fin N × Bool) : CLClause N :=
  ⟨[ℓ₁, ℓ₂, ℓ₃], by simp⟩

/-- Generic CNF constructor from a list of clauses. -/
def mkCNF {N : ℕ} (clauses : List (CLClause N)) : CookLevinCNF N :=
  ⟨clauses, clauses.length⟩

@[simp] theorem mkCNF_clauses {N : ℕ} (clauses : List (CLClause N)) :
    (mkCNF clauses).clauses = clauses := rfl

@[simp] theorem mkCNF_numClauses {N : ℕ} (clauses : List (CLClause N)) :
    (mkCNF clauses).numClauses = clauses.length := rfl

/-- Append clause families while preserving CNF structure. -/
def appendCNF {N : ℕ} (c₁ c₂ : CookLevinCNF N) : CookLevinCNF N :=
  mkCNF (c₁.clauses ++ c₂.clauses)

/-- If all clauses are local to `bp`, then the assembled CNF is local. -/
def localFromAllClauses {N : ℕ} (cnf : CookLevinCNF N)
    (bp : BlockPartition N)
    (hlocal : ∀ c ∈ cnf.clauses, c.isLocal bp)
    (bnd : ℕ := 1) : HasLocalPartition cnf :=
  ⟨bp, hlocal, bnd⟩

/-- Locality is preserved under clause-list append. -/
theorem allClausesLocal_append {N : ℕ} (bp : BlockPartition N)
    (xs ys : List (CLClause N))
    (hx : ∀ c ∈ xs, c.isLocal bp)
    (hy : ∀ c ∈ ys, c.isLocal bp) :
    ∀ c ∈ (xs ++ ys), c.isLocal bp := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact hx c h
  · exact hy c h

/-! ## First concrete clause family: input well-formedness (scaffold)

  These clauses are a first non-empty family in the Cook-Levin direction.
  For each input variable `xᵢ`, we add the tautology `(xᵢ ∨ ¬xᵢ)` in 2-CNF form.
  This is logically redundant, but gives us:
  - concrete variable embedding `Fin n -> Fin (compiledVarCount ...)`
  - concrete clause generation over `Fin n`
  - immediate width/locality proofs via existing infrastructure.

  Next steps will replace/augment these with real tableau constraints
  (initial-state, transition, head uniqueness, etc.). -/

/-- Embed input-variable index space into compiled-variable space. -/
def inputVar (M : DTM) (n : ℕ) : Fin n → Fin (compiledVarCount (defaultK M) n) :=
  embedVar (compiledVarCount_ge_n_all (defaultK M) n)

/-- Input well-formedness tautology clauses: `(xᵢ ∨ ¬xᵢ)` for each `i`. -/
def inputWellformedClauses (M : DTM) (n : ℕ) : List (CLClause (compiledVarCount (defaultK M) n)) :=
  List.ofFn (fun i : Fin n =>
    clause2 (posLit (inputVar M n i)) (negLit (inputVar M n i)))

/-- CNF built from input well-formedness clauses. -/
def inputWellformedCNF (M : DTM) (n : ℕ) : CookLevinCNF (compiledVarCount (defaultK M) n) :=
  mkCNF (inputWellformedClauses M n)

/-- Locality certificate for input-wellformed CNF under identity partition. -/
def inputWellformed_local (M : DTM) (n : ℕ) :
    HasLocalPartition (inputWellformedCNF M n) :=
  identity_local (inputWellformedCNF M n)

/-! ## First semantic tableau scaffold (initial configuration)

  These clauses start mirroring real Cook-Levin intent:
  - head at start cell
  - machine in start state
  - reject flag off at time 0

  They are still a lightweight scaffold, but now carry semantic meaning
  (unlike tautological input-wellformedness clauses).
-/

/-- For `n ≥ 2`, compiled variable count is at least 3 (enough for 3 fixed slots). -/
theorem compiledVarCount_ge_three (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    compiledVarCount (defaultK M) n ≥ 3 := by
  have hcube : compiledVarCount (defaultK M) n ≥ n ^ 3 :=
    compiledVarCount_ge_cubic M n (by omega)
  have hn3 : n ^ 3 ≥ 8 := by
    have hpow : 2 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hn2 3
    simpa using hpow
  omega

/-- For `n ≥ 2`, compiled variable count is at least 8. -/
theorem compiledVarCount_ge_eight (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    compiledVarCount (defaultK M) n ≥ 8 := by
  have hcube : compiledVarCount (defaultK M) n ≥ n ^ 3 :=
    compiledVarCount_ge_cubic M n (by omega)
  have hn3 : n ^ 3 ≥ 8 := by
    have hpow : 2 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hn2 3
    simpa using hpow
  omega

/-- Pick one of 8 fixed scaffold slots in compiled variable space. -/
def scaffoldVar (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (slot : Fin 8) :
    Fin (compiledVarCount (defaultK M) n) :=
  ⟨slot.1, by
    have h8 : compiledVarCount (defaultK M) n ≥ 8 := compiledVarCount_ge_eight M n hn2
    exact Nat.lt_of_lt_of_le slot.2 h8⟩

/-! ## Indexed time-slot API (scaffold)

  Paper-faithful direction: move from ad-hoc fixed literals to generated
  time/role indexed slots.

  We use a small 2-step × 4-role window scaffold (8 slots total), then
  embed into the compiled variable space via `scaffoldVar`.
-/

abbrev StepIdx := Fin 2
abbrev RoleIdx := Fin 4

def step0 : StepIdx := ⟨0, by decide⟩
def step1 : StepIdx := ⟨1, by decide⟩

/-- Encode `(time, role)` into one of 8 scaffold slots. -/
def timeRoleSlot (t : StepIdx) (r : RoleIdx) : Fin 8 :=
  ⟨t.1 * 4 + r.1, by
    have ht : t.1 < 2 := t.2
    have hr : r.1 < 4 := r.2
    omega⟩

/-- Time/role-indexed variable in compiled space. -/
def timeSlotVar (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (t : StepIdx) (r : RoleIdx) : Fin (compiledVarCount (defaultK M) n) :=
  scaffoldVar M n hn2 (timeRoleSlot t r)

/-- Role tags for the 4-slot scaffold. -/
def roleHead : RoleIdx := ⟨0, by decide⟩
def roleState : RoleIdx := ⟨1, by decide⟩
def roleAccept : RoleIdx := ⟨2, by decide⟩
def roleReject : RoleIdx := ⟨3, by decide⟩

/-- Fixed slot for "head at 0" literal in the scaffold layout. -/
def headInitVar (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    Fin (compiledVarCount (defaultK M) n) :=
  scaffoldVar M n hn2 ⟨0, by decide⟩

/-- Fixed slot for "start state active" literal in the scaffold layout. -/
def stateInitVar (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    Fin (compiledVarCount (defaultK M) n) :=
  scaffoldVar M n hn2 ⟨1, by decide⟩

/-- Fixed slot for "reject flag off" literal in the scaffold layout. -/
def rejectInitVar (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    Fin (compiledVarCount (defaultK M) n) :=
  scaffoldVar M n hn2 ⟨2, by decide⟩

/-- Two scaffold head-position slots at time 0 (starter exact-one gadget). -/
def headPos0Var (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    Fin (compiledVarCount (defaultK M) n) :=
  scaffoldVar M n hn2 ⟨3, by decide⟩

def headPos1Var (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    Fin (compiledVarCount (defaultK M) n) :=
  scaffoldVar M n hn2 ⟨4, by decide⟩

/-- Two scaffold state slots at time 0 (starter exact-one gadget). -/
def state0Var (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    Fin (compiledVarCount (defaultK M) n) :=
  scaffoldVar M n hn2 ⟨5, by decide⟩

def state1Var (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    Fin (compiledVarCount (defaultK M) n) :=
  scaffoldVar M n hn2 ⟨6, by decide⟩

def acceptInitVar (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    Fin (compiledVarCount (defaultK M) n) :=
  scaffoldVar M n hn2 ⟨7, by decide⟩
/-- Initial semantic clauses (scaffold): head@0, start-state, not-reject, not-accept. -/
def initialSemanticClauses (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    List (CLClause (compiledVarCount (defaultK M) n)) :=
  [ clause1 (posLit (headInitVar M n hn2))
  , clause1 (posLit (stateInitVar M n hn2))
  , clause1 (negLit (rejectInitVar M n hn2))
  , clause1 (negLit (acceptInitVar M n hn2))
  ]

/-- Starter head-uniqueness gadget over two head-position slots:
    (h0 ∨ h1) ∧ (¬h0 ∨ ¬h1). -/
def headUniqClauses (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    List (CLClause (compiledVarCount (defaultK M) n)) :=
  [ clause2 (posLit (headPos0Var M n hn2)) (posLit (headPos1Var M n hn2))
  , clause2 (negLit (headPos0Var M n hn2)) (negLit (headPos1Var M n hn2))
  ]

/-- Starter state exclusivity gadget over two state slots:
    (s0 ∨ s1) ∧ (¬s0 ∨ ¬s1). -/
def stateUniqClauses (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    List (CLClause (compiledVarCount (defaultK M) n)) :=
  [ clause2 (posLit (state0Var M n hn2)) (posLit (state1Var M n hn2))
  , clause2 (negLit (state0Var M n hn2)) (negLit (state1Var M n hn2))
  ]

/-- Link start-state literal to first state slot: start → s0 and s0 → start. -/
def stateLinkClauses (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    List (CLClause (compiledVarCount (defaultK M) n)) :=
  [ clause2 (negLit (stateInitVar M n hn2)) (posLit (state0Var M n hn2))
  , clause2 (negLit (state0Var M n hn2)) (posLit (stateInitVar M n hn2))
  ]

/-- Transition-style local gadget (scaffold):
    - state progression: s0 → s1, s1 → accept
    - head progression: h0 → h1

  This is still simplified, but introduces explicit time-step-style
  implication constraints akin to Cook-Levin local transition clauses. -/
def transitionScaffoldClauses (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    List (CLClause (compiledVarCount (defaultK M) n)) :=
  [ clause2 (negLit (state0Var M n hn2)) (posLit (state1Var M n hn2))
  , clause2 (negLit (state1Var M n hn2)) (posLit (acceptInitVar M n hn2))
  , clause2 (negLit (headPos0Var M n hn2)) (posLit (headPos1Var M n hn2))
  ]

/-- Window-local transition template (paper-faithful scaffold):
    each clause depends on a small "time window" of state/head literals,
    mirroring Cook-Levin's radius-1 local update constraints. -/
def transitionWindowClause (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (w : Fin 2) :
    CLClause (compiledVarCount (defaultK M) n) :=
  if h0 : w = ⟨0, by decide⟩ then
    -- window 0: (state0 ∧ head0) → state1
    clause3 (negLit (state0Var M n hn2))
            (negLit (headPos0Var M n hn2))
            (posLit (state1Var M n hn2))
  else
    -- window 1: (state1 ∧ head1) → accept
    clause3 (negLit (state1Var M n hn2))
            (negLit (headPos1Var M n hn2))
            (posLit (acceptInitVar M n hn2))

/-- Two window-local transition clauses generated from the template. -/
def transitionWindowClauses (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    List (CLClause (compiledVarCount (defaultK M) n)) :=
  List.ofFn (fun w : Fin 2 => transitionWindowClause M n hn2 w)

/-- Indexed transition family (paper-faithful scaffold):
    generated from explicit `(time, role)` slots instead of ad-hoc literals.

    Clauses:
    - state(t=0) → state(t=1)
    - head(t=0)  → head(t=1)
    - accept(t=0) → accept(t=1)

  This is the first generated "time-step API" family. -/
def indexedTransitionClauses (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    List (CLClause (compiledVarCount (defaultK M) n)) :=
  [ clause2 (negLit (timeSlotVar M n hn2 step0 roleState))
            (posLit (timeSlotVar M n hn2 step1 roleState))
  , clause2 (negLit (timeSlotVar M n hn2 step0 roleHead))
            (posLit (timeSlotVar M n hn2 step1 roleHead))
  , clause2 (negLit (timeSlotVar M n hn2 step0 roleAccept))
            (posLit (timeSlotVar M n hn2 step1 roleAccept))
  ]

/-- Per-time indexed consistency template (paper-faithful scaffold):
    - accept_t and reject_t are mutually exclusive
    - accept_t implies state_t
    - reject_t implies not state_t -/
def indexedConsistencyClausesAt (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (t : StepIdx) : List (CLClause (compiledVarCount (defaultK M) n)) :=
  [ clause2 (negLit (timeSlotVar M n hn2 t roleAccept))
            (negLit (timeSlotVar M n hn2 t roleReject))
  , clause2 (negLit (timeSlotVar M n hn2 t roleAccept))
            (posLit (timeSlotVar M n hn2 t roleState))
  , clause2 (negLit (timeSlotVar M n hn2 t roleReject))
            (negLit (timeSlotVar M n hn2 t roleState))
  ]

/-- Indexed consistency family across all scaffold time slots. -/
def indexedConsistencyClauses (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    List (CLClause (compiledVarCount (defaultK M) n)) :=
  indexedConsistencyClausesAt M n hn2 step0 ++
  indexedConsistencyClausesAt M n hn2 step1

/-- Backward-compatible alias used by scaffold assembly. -/
def consistencyClauses (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
  List (CLClause (compiledVarCount (defaultK M) n)) :=
  indexedConsistencyClauses M n hn2

/-- Phase-bundled scaffold clauses (paper-faithful organization):
    input + initial + uniqueness + transition + consistency. -/
def scaffoldPhaseClauses (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    List (CLClause (compiledVarCount (defaultK M) n)) :=
  inputWellformedClauses M n ++
  initialSemanticClauses M n hn2 ++
  headUniqClauses M n hn2 ++
  stateUniqClauses M n hn2 ++
  stateLinkClauses M n hn2 ++
  transitionScaffoldClauses M n hn2 ++
  transitionWindowClauses M n hn2 ++
  indexedTransitionClauses M n hn2 ++
  consistencyClauses M n hn2

/-! ## Template metadata (family-by-family organization)

  Paper-faithful direction: track clause families explicitly so locality,
  counting, and eventually profile bounds can be stated per-family and
  then assembled compositionally.
-/

inductive FamilyTag where
  | input
  | init
  | headUniq
  | stateUniq
  | stateLink
  | transitionScaffold
  | transitionWindow
  | transitionIndexed
  | consistency
  deriving DecidableEq, Repr

/-- Clauses belonging to a specific template family. -/
def familyClauses (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    FamilyTag → List (CLClause (compiledVarCount (defaultK M) n))
  | .input => inputWellformedClauses M n
  | .init => initialSemanticClauses M n hn2
  | .headUniq => headUniqClauses M n hn2
  | .stateUniq => stateUniqClauses M n hn2
  | .stateLink => stateLinkClauses M n hn2
  | .transitionScaffold => transitionScaffoldClauses M n hn2
  | .transitionWindow => transitionWindowClauses M n hn2
  | .transitionIndexed => indexedTransitionClauses M n hn2
  | .consistency => consistencyClauses M n hn2

/-- Each template family is local under the tableau partition scaffold. -/
theorem familyClauses_local (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (tag : FamilyTag) :
    ∀ c ∈ familyClauses M n hn2 tag,
      c.isLocal (tableauPartition (compiledVarCount (defaultK M) n)) := by
  simpa [familyClauses] using
    (allClausesLocal_tableau (xs := familyClauses M n hn2 tag))

/-- CNF from one specific template family. -/
def familyCNF (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (tag : FamilyTag) :
    CookLevinCNF (compiledVarCount (defaultK M) n) :=
  mkCNF (familyClauses M n hn2 tag)

/-- Locality certificate for a single family CNF under tableau partition. -/
def family_local (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (tag : FamilyTag) :
    HasLocalPartition (familyCNF M n hn2 tag) :=
  localFromAllClauses (cnf := familyCNF M n hn2 tag)
    (bp := tableauPartition (compiledVarCount (defaultK M) n))
    (hlocal := familyClauses_local M n hn2 tag)
    3

/-! ## Family size bookkeeping (paper-faithful counting scaffold)

  These are lightweight cardinality proxies for later profile/rank bounds:
  - input family scales with `n`
  - each local template family has constant size
  - total scaffold size is linear in `n`
-/

@[simp] theorem length_inputWellformedClauses (M : DTM) (n : ℕ) :
    (inputWellformedClauses M n).length = n := by
  simp [inputWellformedClauses]

@[simp] theorem length_initialSemanticClauses (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    (initialSemanticClauses M n hn2).length = 4 := by simp [initialSemanticClauses]

@[simp] theorem length_headUniqClauses (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    (headUniqClauses M n hn2).length = 2 := by simp [headUniqClauses]

@[simp] theorem length_stateUniqClauses (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    (stateUniqClauses M n hn2).length = 2 := by simp [stateUniqClauses]

@[simp] theorem length_stateLinkClauses (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    (stateLinkClauses M n hn2).length = 2 := by simp [stateLinkClauses]

@[simp] theorem length_transitionScaffoldClauses (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    (transitionScaffoldClauses M n hn2).length = 3 := by simp [transitionScaffoldClauses]

@[simp] theorem length_transitionWindowClauses (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    (transitionWindowClauses M n hn2).length = 2 := by simp [transitionWindowClauses]

@[simp] theorem length_indexedTransitionClauses (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    (indexedTransitionClauses M n hn2).length = 3 := by simp [indexedTransitionClauses]

@[simp] theorem length_indexedConsistencyClausesAt (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (t : StepIdx) :
    (indexedConsistencyClausesAt M n hn2 t).length = 3 := by
  simp [indexedConsistencyClausesAt]

@[simp] theorem length_consistencyClauses (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    (consistencyClauses M n hn2).length = 6 := by
  simp [consistencyClauses, indexedConsistencyClauses]

/-- Total scaffold clause count is linear in input length. -/
theorem length_scaffoldPhaseClauses (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    (scaffoldPhaseClauses M n hn2).length = n + 24 := by
  simp [scaffoldPhaseClauses]

/-! ## Profile proxy layer (paper-faithful bridge)

  In the paper, profile compression bounds rank by controlling the number
  of admissible block-touch profiles. Here we add a lightweight proxy:
  - extract per-clause block-touch profiles under tableauPartition
  - bound profile width (card ≤ 3)
  - bound distinct profile count by family length / total linear size.
-/

/-- Block-touch profile list for one family under tableau partition. -/
def familyProfileList (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (tag : FamilyTag) :
    List (Finset (Fin 3)) :=
  (familyClauses M n hn2 tag).map
    (fun c => c.vars.image (tableauPartition (compiledVarCount (defaultK M) n)).blockOf)

/-- Every family profile touches at most 3 blocks. -/
theorem familyProfile_card_le_three (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (tag : FamilyTag) (p : Finset (Fin 3))
    (hp : p ∈ familyProfileList M n hn2 tag) :
    p.card ≤ 3 := by
  rcases List.mem_map.mp hp with ⟨c, hc, rfl⟩
  exact familyClauses_local M n hn2 tag c hc

/-- Distinct profile count in one family is at most family clause count. -/
theorem familyProfileDistinctCount_le_length (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (tag : FamilyTag) :
    (familyProfileList M n hn2 tag).toFinset.card ≤
      (familyClauses M n hn2 tag).length := by
  calc
    (familyProfileList M n hn2 tag).toFinset.card ≤ (familyProfileList M n hn2 tag).length :=
      List.toFinset_card_le _
    _ = (familyClauses M n hn2 tag).length := by
      simp [familyProfileList]

/-- Block-touch profile list for the full scaffold clause bundle. -/
def scaffoldProfileList (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    List (Finset (Fin 3)) :=
  (scaffoldPhaseClauses M n hn2).map
    (fun c => c.vars.image (tableauPartition (compiledVarCount (defaultK M) n)).blockOf)

/-- Distinct profile count for full scaffold is linear in input length. -/
theorem scaffoldProfileDistinctCount_le_linear (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    (scaffoldProfileList M n hn2).toFinset.card ≤ n + 24 := by
  calc
    (scaffoldProfileList M n hn2).toFinset.card ≤ (scaffoldProfileList M n hn2).length :=
      List.toFinset_card_le _
    _ = (scaffoldPhaseClauses M n hn2).length := by
      simp [scaffoldProfileList]
    _ = n + 24 := length_scaffoldPhaseClauses M n hn2

/-! ## Rank-proxy budget (paper-faithful counting proxy)

  In the paper, rank upper bounds come from counting admissible profiles
  and bounding per-profile contribution dimensions.

  Here we add a conservative finite combinatorial proxy:
  - profile count budget = distinct block-touch profiles
  - shift budget for κ over ≤3 blocks = (κ+1)^3
  - rank proxy budget = product of the two

  This is intentionally a proxy (not yet the final SPDP finrank bound),
  but aligns with the paper's counting architecture. -/

/-- Profile count budget for scaffold clauses. -/
def profileBudget (M : DTM) (n : ℕ) (hn2 : n ≥ 2) : ℕ :=
  (scaffoldProfileList M n hn2).toFinset.card

/-- Coarse per-profile shift budget for degree bound κ on ≤3 blocks. -/
def shiftBudget (κ : ℕ) : ℕ := (κ + 1) ^ 3

/-- Combined rank-count proxy budget. -/
def rankProxyBudget (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (κ : ℕ) : ℕ :=
  profileBudget M n hn2 * shiftBudget κ

theorem profileBudget_le_linear (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    profileBudget M n hn2 ≤ n + 24 :=
  scaffoldProfileDistinctCount_le_linear M n hn2

theorem rankProxyBudget_le_linear_mul_shift
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (κ : ℕ) :
    rankProxyBudget M n hn2 κ ≤ (n + 24) * shiftBudget κ := by
  unfold rankProxyBudget
  exact Nat.mul_le_mul_right (shiftBudget κ) (profileBudget_le_linear M n hn2)

/-- Log-parameterized proxy budget (the paper uses κ = O(log n)). -/
def logRankProxyBudget (M : DTM) (n : ℕ) (hn2 : n ≥ 2) : ℕ :=
  rankProxyBudget M n hn2 (Nat.log 2 n)

theorem logRankProxyBudget_le_explicit
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    logRankProxyBudget M n hn2 ≤
      (n + 24) * ((Nat.log 2 n + 1) ^ 3) := by
  simpa [logRankProxyBudget, shiftBudget] using
    rankProxyBudget_le_linear_mul_shift M n hn2 (Nat.log 2 n)

/-- CNF from initial semantic scaffold clauses. -/
def initialSemanticCNF (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    CookLevinCNF (compiledVarCount (defaultK M) n) :=
  mkCNF (scaffoldPhaseClauses M n hn2)

/-- Locality certificate for semantic scaffold CNF under tableau partition. -/
def initialSemantic_local (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    HasLocalPartition (initialSemanticCNF M n hn2) :=
  tableau_local (initialSemanticCNF M n hn2)

/-- Conservative rank upper bound proxy: the blocked SPDP rank of the
    scaffold CNF is bounded by the finrank of the ambient restrictTotalDegree
    module. This is a paper-faithful "ambient dimension" upper bound used as
    a stepping stone before sharper profile-compression bounds. -/
theorem initialSemantic_rank_le_restrictFinrank
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (κ : ℕ) :
    CompiledPoly.blockedSpdpRankQ κ κ
      (CompiledPoly.compiledPolyQ (initialSemanticCNF M n hn2))
      (initialSemantic_local M n hn2).partition
    ≤ Module.finrank ℚ
        (MvPolynomial.restrictTotalDegree (Fin (compiledVarCount (defaultK M) n)) ℚ
          (κ + (CompiledPoly.compiledPolyQ (initialSemanticCNF M n hn2)).totalDegree)) := by
  let poly := CompiledPoly.compiledPolyQ (initialSemanticCNF M n hn2)
  let bp := (initialSemantic_local M n hn2).partition
  let spdp : Set (MvPolynomial (Fin (compiledVarCount (defaultK M) n)) ℚ) :=
    { q | ∃ (S : List (Fin (compiledVarCount (defaultK M) n)))
            (sh : MvPolynomial (Fin (compiledVarCount (defaultK M) n)) ℚ),
        S.length ≤ κ ∧ sh.totalDegree ≤ κ ∧
        (S.toFinset.image bp.blockOf).card ≤ κ ∧
        (sh.vars.image bp.blockOf).card ≤ κ ∧
        q = sh * SPDP.iterDerivList S poly }
  have h_eq :
      CompiledPoly.blockedSpdpRankQ κ κ poly bp =
      Module.finrank ℚ (Submodule.span ℚ spdp) := by
    rfl
  rw [h_eq]
  have h_le : Submodule.span ℚ spdp ≤
      MvPolynomial.restrictTotalDegree (Fin (compiledVarCount (defaultK M) n)) ℚ
        (κ + poly.totalDegree) := by
    simpa [poly, bp, spdp] using
      (PermanentLower.spdp_span_le_restrictTotalDegree κ κ poly bp)
  have h_fin : Module.Finite ℚ (Submodule.span ℚ spdp) := by
    exact Module.Finite.of_injective
      (Submodule.inclusion h_le)
      (Submodule.inclusion_injective h_le)
  exact Submodule.finrank_mono h_le

/-- Ambient finrank budget used by the conservative SPDP bound. -/
noncomputable def ambientFinrankBudget (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (κ : ℕ) : ℕ :=
  Module.finrank ℚ
    (MvPolynomial.restrictTotalDegree (Fin (compiledVarCount (defaultK M) n)) ℚ
      (κ + (CompiledPoly.compiledPolyQ (initialSemanticCNF M n hn2)).totalDegree))

/-- Combined proxy budget: max(ambient finrank budget, profile-count budget). -/
noncomputable def combinedRankProxyBudget (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (κ : ℕ) : ℕ :=
  max (ambientFinrankBudget M n hn2 κ) (rankProxyBudget M n hn2 κ)

/-- Actual blocked SPDP rank is bounded by the combined proxy budget. -/
theorem initialSemantic_rank_le_combinedProxy
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (κ : ℕ) :
    CompiledPoly.blockedSpdpRankQ κ κ
      (CompiledPoly.compiledPolyQ (initialSemanticCNF M n hn2))
      (initialSemantic_local M n hn2).partition
    ≤ combinedRankProxyBudget M n hn2 κ := by
  unfold combinedRankProxyBudget
  exact le_trans
    (initialSemantic_rank_le_restrictFinrank M n hn2 κ)
    (Nat.le_max_left _ _)

/-- Log-parameterized version of the combined rank proxy bound. -/
theorem initialSemantic_logRank_le_combinedProxy
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    CompiledPoly.blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
      (CompiledPoly.compiledPolyQ (initialSemanticCNF M n hn2))
      (initialSemantic_local M n hn2).partition
    ≤ combinedRankProxyBudget M n hn2 (Nat.log 2 n) := by
  exact initialSemantic_rank_le_combinedProxy M n hn2 (Nat.log 2 n)

/-! ## Theorem-92-shaped bridge (paper-faithful)

  We now isolate the exact remaining inequality needed to finish a
  `≤ √n` upper bound for this scaffold encoding:

  (Missing compression inequality)
    combinedRankProxyBudget(M,n,log n) ≤ √n.

  Once supplied (from profile compression machinery), the SPDP upper
  bound follows immediately by transitivity. -/

/-- Compression target predicate for the scaffold at log parameters. -/
def logCompressionTarget (M : DTM) (n : ℕ) (hn2 : n ≥ 2) : Prop :=
  combinedRankProxyBudget M n hn2 (Nat.log 2 n) ≤ Nat.sqrt n

/-- Sufficient condition: if both components are ≤ √n, then combined target holds. -/
theorem logCompressionTarget_of_component_bounds
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (hAmbient : ambientFinrankBudget M n hn2 (Nat.log 2 n) ≤ Nat.sqrt n)
    (hProxy : rankProxyBudget M n hn2 (Nat.log 2 n) ≤ Nat.sqrt n) :
    logCompressionTarget M n hn2 := by
  unfold logCompressionTarget combinedRankProxyBudget
  exact max_le hAmbient hProxy

/-- Explicit bound for the profile-count proxy component at log parameters. -/
theorem rankProxyLog_component_le_explicit
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    rankProxyBudget M n hn2 (Nat.log 2 n)
      ≤ (n + 24) * ((Nat.log 2 n + 1) ^ 3) := by
  simpa [logRankProxyBudget] using logRankProxyBudget_le_explicit M n hn2

/-- If the compression target holds, we get the Theorem-92-shaped bound. -/
theorem initialSemantic_logRank_le_sqrt_of_target
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (hTarget : logCompressionTarget M n hn2) :
    CompiledPoly.blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
      (CompiledPoly.compiledPolyQ (initialSemanticCNF M n hn2))
      (initialSemantic_local M n hn2).partition
    ≤ Nat.sqrt n := by
  exact le_trans (initialSemantic_logRank_le_combinedProxy M n hn2) hTarget

/-- Explicitly exposes the remaining proof obligation for profile compression. -/
theorem remaining_profile_compression_obligation
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    logCompressionTarget M n hn2 →
    CompiledPoly.blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
      (CompiledPoly.compiledPolyQ (initialSemanticCNF M n hn2))
      (initialSemantic_local M n hn2).partition
    ≤ Nat.sqrt n :=
  initialSemantic_logRank_le_sqrt_of_target M n hn2

/-- First non-empty concrete encoding package (semantic scaffold level). -/
def initialEncoding (M : DTM) (n : ℕ) : CookLevinEncoding M n where
  k := defaultK M
  cnf := if hn2 : n ≥ 2 then initialSemanticCNF M n hn2 else inputWellformedCNF M n
  hlp := by
    by_cases hn2 : n ≥ 2
    · simpa [hn2] using initialSemantic_local M n hn2
    · simpa [hn2] using inputWellformed_local M n

/-- Baseline CNF on the compiled variable space (empty clause list).
    This is a structural placeholder witness used for scaffolding proofs.
    It is *not* the full Cook-Levin encoding. -/
def baselineCNF (M : DTM) (n : ℕ) : CookLevinCNF (compiledVarCount (defaultK M) n) :=
  mkCNF []

/-- Baseline encoding package exists for every machine/input size.
    Useful as a non-axiomatic existence scaffold while building the
    full Cook-Levin construction. -/
def baselineEncoding (M : DTM) (n : ℕ) : CookLevinEncoding M n where
  k := defaultK M
  cnf := baselineCNF M n
  hlp := oneBlock_local (baselineCNF M n)

end CookLevin
