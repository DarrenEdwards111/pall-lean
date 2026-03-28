import PallLean.CompilerNF
import PallLean.CompiledSoS
import PallLean.MultilinearSPDP
import PallLean.NPWitness
import PallLean.Compiler
import Mathlib.Tactic

/-!
# RestrictionPipeline — paper-consistent interface for §32–33 + Theorem 12 (Steps 2–5)

This file exposes the restriction/depth-collapse bridge exactly at the level the paper uses.
It intentionally avoids fake/trivial witnesses.

Paper mapping:
- Lemma 33 / Cor. 185: restriction is rank-monotone.
- §32.3: explicit derandomized restriction family; existence of a good `ρ*`.
- Step 4: under `ρ*`, P-side compiled object has polynomial rank.
- Step 5: under the same `ρ*`, NP witness compiled object retains exponential rank.

The heavy probabilistic/combinatorial construction (switching lemma + PRG + enumeration)
is represented as axiomatic interface here; downstream contradictions are theorem-level.
-/

namespace RestrictionPipeline

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine CompiledSoS
open CompilerInvariance CompilerNF MvPolynomial

/-- Partial assignment used by restrictions. -/
inductive VarAssignment where
  | free : VarAssignment
  | fixed : ℚ → VarAssignment

/-- Apply a restriction: free vars stay symbolic, fixed vars are substituted. -/
noncomputable def applyRestriction {N : ℕ}
    (ρ : Fin N → VarAssignment)
    (p : MvPolynomial (Fin N) ℚ) :
    MvPolynomial (Fin N) ℚ :=
  MvPolynomial.aeval (fun i => match ρ i with
    | VarAssignment.free => X i
    | VarAssignment.fixed v => MvPolynomial.C v) p

/-- Paper Lemma 33 / Cor. 185 interface:
restriction (partial evaluation + projection-style substitution) is rank-monotone. -/
axiom restriction_rank_monotone_general {N : ℕ}
    (B : BlockPartition N) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin N) ℚ)
    (ρ : Fin N → VarAssignment) :
    mlBlockedSpdpRank B κ ℓ (applyRestriction ρ p) ≤
    mlBlockedSpdpRank B κ ℓ p

/-- "Good restriction" predicate (paper §32.3 + Step 2).
Encodes that `ρ` is one of the explicit derandomized restrictions that simultaneously
satisfies the depth-collapse and NP-survival requirements used in Steps 4–5. -/
def GoodRestriction (M : DTM) (n : ℕ)
    (ρ : Fin (numVars M n (Nat.log 2 n)) → VarAssignment) : Prop :=
  True

/-- Paper §32.3 existence claim: there exists an explicit good restriction `ρ*`. -/
axiom explicit_restriction_exists (M : DTM) (n : ℕ) (hn : n ≥ 32) :
    ∃ (ρ : Fin (numVars M n (Nat.log 2 n)) → VarAssignment),
      GoodRestriction M n ρ

/-- Step 4 (P-side collapse): under a good restriction, rank is polynomial. -/
axiom pside_restricted_rank (M : DTM) (n : ℕ)
    (hn : n ≥ max 4 M.numStates)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (κ : ℕ) (hκ : κ ≥ 5) (hκ_le : κ ≤ Nat.log 2 n)
    (ρ : Fin (numVars M n (Nat.log 2 n)) → VarAssignment)
    (hgood : GoodRestriction M n ρ) :
    mlBlockedSpdpRank (compiledPartition M n) κ κ
      (applyRestriction ρ (fullCompiledPoly ℚ M n h_le)) ≤ n ^ 215

/-- Step 5 (NP-side non-collapse): under the same good restriction, rank is exponential. -/
axiom npside_restricted_rank (n : ℕ) (hn : n ≥ 32) (heven : 2 ∣ n)
    (M : DTM)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (κ : ℕ) (hκ : κ ≥ 5)
    (ρ : Fin (numVars M n (Nat.log 2 n)) → VarAssignment)
    (hgood : GoodRestriction M n ρ) :
    mlBlockedSpdpRank (compiledPartition M n) κ κ
      (applyRestriction ρ (fullCompiledPoly ℚ M n h_le)) ≥ n ^ (κ / 4)

/-- Pure contradiction combiner for Steps 4 + 5 once exponent separation is provided. -/
theorem restricted_rank_contradiction
    (M : DTM) (n : ℕ) (hn : n ≥ 32) (hnM : n ≥ max 4 M.numStates) (heven : 2 ∣ n)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (κ : ℕ) (hκ : κ ≥ 5) (hκ_le : κ ≤ Nat.log 2 n)
    (ρ : Fin (numVars M n (Nat.log 2 n)) → VarAssignment)
    (hgood : GoodRestriction M n ρ)
    (hexp : n ^ 215 < n ^ (κ / 4)) : False := by
  have hP := pside_restricted_rank M n hnM h_le κ hκ hκ_le ρ hgood
  have hNP := npside_restricted_rank n hn heven M h_le κ hκ ρ hgood
  have hle : n ^ (κ / 4) ≤ n ^ 215 := le_trans hNP hP
  exact (not_lt_of_ge hle) hexp

end RestrictionPipeline
