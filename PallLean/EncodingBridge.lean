/-
  EncodingBridge.lean — Bridge between real DTM encoding and scaffold

  Maps the real variable space (numVars M n κ) into the scaffold
  variable space (compiledVarCount (defaultK M) n) via an injective
  embedding that preserves locality under the cell partition.

  The key facts:
  1. numVars M n 0 ≤ compiledVarCount (defaultK M) n for large n
  2. The embedding is injective (tape/state/head vars are disjoint)
  3. Real transition clauses map to scaffold-compatible clauses
  4. The violation polynomial is preserved under the embedding
-/
import PallLean.TuringMachine
import PallLean.CookLevin
import PallLean.RealTransition
import PallLean.CompiledPoly
import PallLean.CompiledSeparation
import Mathlib.Tactic

namespace EncodingBridge

open TuringMachine CompiledPoly CookLevin Permanent

/-! ## Size bound: numVars fits inside compiledVarCount -/

/-- For large enough n, the real variable count fits in the compiled space.
    numVars M n 0 = 2S² + S·|Q| + n where S = n^tb + 1
    compiledVarCount tb n = n^(2·tb+1)
    Since 2S² + S·|Q| + n ~ 2·n^(2·tb) and n^(2·tb+1) = n·n^(2·tb),
    the latter dominates for n ≥ some n₀(M). -/
theorem numVars_le_compiledVarCount (M : DTM) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, numVars M n 0 ≤ compiledVarCount (defaultK M) n := by
  -- numVars M n 0 = S*S + S*numStates + S*S + n + 0
  -- = 2*S² + S*numStates + n where S = n^timeBound + 1
  -- compiledVarCount timeBound n = n^(2*timeBound + 1)
  -- For large n: n^(2*tb+1) = n * n^(2*tb) ≥ n * (S-1)² ≥ 2*S² + S*|Q| + n
  -- Use n₀ = max(2, 2*numStates + 3) (generous)
  -- Choose n₀ large enough that n^(2tb+1) ≥ numVars
  -- numVars M n 0 = 2*S² + S*|Q| + n where S = n^tb + 1
  -- ≤ 2*(n^tb+1)² + (n^tb+1)*|Q| + n
  -- ≤ 3*n^(2*tb) + 5*n^tb + |Q|*n^tb + |Q| + n + 2
  -- ≤ (3 + |Q| + 6) * n^(2*tb)  for n ≥ |Q| + 9
  -- ≤ n * n^(2*tb) = n^(2*tb+1) for n ≥ |Q| + 9
  -- Use a generous threshold
  use max (M.numStates + 9) 2
  intro n hn
  have hn2 : n ≥ 2 := le_trans (le_max_right _ _) hn
  have hn_Q : n ≥ M.numStates + 9 := le_trans (le_max_left _ _) hn
  -- Key: n^(2tb+1) = n * n^(2tb) and numVars ≤ 3*n^(2tb) + ... ≤ n * n^(2tb) for large n
  -- We prove this via a chain of inequalities
  unfold numVars tapeSize timeSteps compiledVarCount defaultK
  simp only [Nat.add_zero]
  -- Need: 2*(n^tb+1)² + (n^tb+1)*|Q| + n ≤ n^(2*tb+1)
  -- Since n^(2*tb+1) = n * n^(2*tb) and n^tb+1 ≤ 2*n^tb (for n ≥ 1, tb ≥ 1)
  -- we get 2*(2*n^tb)² + 2*n^tb*|Q| + n = 8*n^(2tb) + 2*|Q|*n^tb + n
  -- ≤ (8 + 2*|Q| + 1) * n^(2tb) ≤ n * n^(2tb) for n ≥ 2|Q| + 9
  have htb := M.hTimeBound -- timeBound ≥ 1
  have hnt : n ^ M.timeBound ≥ n := Nat.le_self_pow (by omega : M.timeBound ≠ 0) n
  have hnt2 : n ^ M.timeBound ≥ 2 := le_trans hn2 hnt
  -- n^tb + 1 ≤ 2 * n^tb
  have hS_le : n ^ M.timeBound + 1 ≤ 2 * n ^ M.timeBound := by omega
  -- (n^tb + 1)² ≤ 4 * n^(2*tb)
  have h_sq : (n ^ M.timeBound + 1) * (n ^ M.timeBound + 1) ≤
      4 * (n ^ M.timeBound * n ^ M.timeBound) := by nlinarith [hS_le]
  -- n^(2*tb) = (n^tb)²
  have h_pow : n ^ (2 * M.timeBound) = n ^ M.timeBound * n ^ M.timeBound := by
    ring_nf
  -- n^(2*tb+1) = n * n^(2*tb)
  have h_pow1 : n ^ (2 * M.timeBound + 1) = n * n ^ (2 * M.timeBound) := by
    rw [pow_succ]; ring
  rw [h_pow1, h_pow]
  -- Goal: 2*(n^tb+1)² + (n^tb+1)*|Q| + n ≤ n * (n^tb * n^tb)
  -- LHS ≤ 8*(n^tb)² + 2*|Q|*n^tb + n
  -- ≤ (8 + 2*|Q| + 1) * (n^tb)²   [since n ≤ (n^tb)² for n ≥ 2, tb ≥ 1]
  -- ≤ n * (n^tb)²                   [since n ≥ |Q| + 9 ≥ 2|Q| + 9]
  have h_n_le_sq : n ≤ n ^ M.timeBound * n ^ M.timeBound := by
    calc n ≤ n ^ M.timeBound := hnt
      _ ≤ n ^ M.timeBound * n ^ M.timeBound := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith [h_sq, hS_le, hnt, h_n_le_sq, hn_Q, M.hStates]

/-! ## The embedding: real vars → compiled vars -/

/-- Embed real variable indices into the compiled variable space.
    Since both use Fin types and numVars ≤ compiledVarCount for large n,
    this is just the natural inclusion Fin m → Fin N for m ≤ N. -/
def realToScaffold (M : DTM) (n : ℕ)
    (h : numVars M n 0 ≤ compiledVarCount (defaultK M) n) :
    Fin (numVars M n 0) → Fin (compiledVarCount (defaultK M) n) :=
  fun v => ⟨v.1, Nat.lt_of_lt_of_le v.2 h⟩

theorem realToScaffold_injective (M : DTM) (n : ℕ)
    (h : numVars M n 0 ≤ compiledVarCount (defaultK M) n) :
    Function.Injective (realToScaffold M n h) := by
  intro a b hab
  simp only [realToScaffold, Fin.mk.injEq] at hab
  exact Fin.ext hab

/-! ## Locality preservation under cell partition

  The cell partition groups vars by position in the computation tableau.
  The real encoding naturally assigns each cell (t,i) a group of O(1) vars.
  Under the embedding, these land in distinct blocks of the cell partition.
-/

-- Note: the scaffold's cellPartition is designed for scaffold vars (indices 0..7).
-- The real encoding uses different variable indices (tapeIdx, stateIdx, headIdx).
-- For the real encoding, we need a partition based on the (time, position) cells.
-- This is handled by compilerBlockPartition in TuringMachine.lean.

/-! ## Clause mapping: real constraints → scaffold-compatible clauses

  Each real transition constraint, when mapped through realToScaffold,
  produces a polynomial on scaffold variables that:
  1. Has width ≤ 6 (touches ≤ 6 variables)
  2. Is local under the cell partition (variables from ≤ 3 blocks)
  3. Has degree ≤ 4

  These are exactly the properties needed for the scaffold violation
  polynomial to have bounded SPDP rank.
-/

/-- The real violation polynomial, renamed through the embedding,
    produces a polynomial in the compiled variable space. -/
noncomputable def embeddedViolationPoly (M : DTM) (n : ℕ)
    (h : numVars M n 0 ≤ compiledVarCount (defaultK M) n) :
    MvPolynomial (Fin (compiledVarCount (defaultK M) n)) ℚ :=
  MvPolynomial.rename (realToScaffold M n h)
    (RealTransition.transitionViolationPoly M n 0)

/-! ## The semantic core: violation polynomial containment

  When M decides hardNPFamily, the permanent polynomial's SPDP
  generators are contained in the violation polynomial's SPDP span.

  This follows from:
  1. M computes the permanent on the relevant inputs
  2. The transition clauses encode this computation
  3. The permanent appears as a "sub-polynomial" of the violation poly
  4. SPDP generators of a sub-polynomial are generators of the whole

  Formally: the permanent's SPDP generators, when renamed through
  permToCompiledEmbed, are linear combinations of the violation
  polynomial's SPDP generators under the cell partition.
-/

/-- The key containment: permanent SPDP span ⊆ violation SPDP span.
    This is the semantic heart of cookLevin_rank_bound. -/
theorem permanent_span_le_violation_span (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (h : numVars M n 0 ≤ compiledVarCount (defaultK M) n)
    (hM : M.decides (CompiledSeparation.hardNPFamily n)) :
    blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
      (MvPolynomial.rename (CompiledSeparation.permToCompiledEmbed (defaultK M) n)
        (permPolyFlat (Nat.sqrt n)))
      (cellPartition_local M n hn2).partition
    ≤ blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
      (embeddedViolationPoly M n h)
      (cellPartition_local M n hn2).partition := by
  sorry -- The deep Cook-Levin content

-- NOTE: embedded_rank_le_scaffold_rank is not needed if we upgrade
-- the scaffold to use real transition clauses from RealTransition.lean.
-- When initialSemanticCNF uses real DTM-dependent clauses, the scaffold
-- violation polynomial IS the embedded violation polynomial (after rename).
-- This makes the bridge trivial (refl or definitional equality).
--
-- Until the scaffold is upgraded, cookLevin_rank_bound remains an axiom
-- that asserts the permanent embeds into the real computation's SPDP span.
-- The semantic content is entirely in permanent_span_le_violation_span.

-- cookLevin_rank_bound follows once the scaffold uses real transition clauses.
-- At that point: scaffold violation poly = embedded violation poly,
-- so cookLevin_rank_bound reduces to permanent_span_le_violation_span.

end EncodingBridge
