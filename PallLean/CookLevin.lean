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
