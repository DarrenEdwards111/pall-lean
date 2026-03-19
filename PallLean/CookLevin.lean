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

/-- Consistency-style local gadget (scaffold):
    - accept and reject are mutually exclusive
    - accept implies state1
    - reject implies not state1

  These mirror the "global consistency" flavor in Cook-Levin tableaux,
  while remaining width-2 local clauses. -/
def consistencyClauses (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    List (CLClause (compiledVarCount (defaultK M) n)) :=
  [ clause2 (negLit (acceptInitVar M n hn2)) (negLit (rejectInitVar M n hn2))
  , clause2 (negLit (acceptInitVar M n hn2)) (posLit (state1Var M n hn2))
  , clause2 (negLit (rejectInitVar M n hn2)) (negLit (state1Var M n hn2))
  ]

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
  consistencyClauses M n hn2

/-- CNF from initial semantic scaffold clauses. -/
def initialSemanticCNF (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    CookLevinCNF (compiledVarCount (defaultK M) n) :=
  mkCNF (scaffoldPhaseClauses M n hn2)

/-- Locality certificate for semantic scaffold CNF under identity partition. -/
def initialSemantic_local (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    HasLocalPartition (initialSemanticCNF M n hn2) :=
  identity_local (initialSemanticCNF M n hn2)

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
