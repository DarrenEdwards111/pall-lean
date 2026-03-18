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

/-- Canonical one-block partition (used for baseline estimates). -/
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

end CookLevin
