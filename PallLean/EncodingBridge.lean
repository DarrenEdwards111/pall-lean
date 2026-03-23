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
  use (2 * M.numStates + 3) ^ 2
  intro n hn
  sorry -- Arithmetic: n^(2*tb+1) ≥ 2*(n^tb+1)² + (n^tb+1)*|Q| + n for large n

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

/-- Tape variables at different cells map to different scaffold blocks. -/
theorem tape_vars_distinct_blocks (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (h : numVars M n 0 ≤ compiledVarCount (defaultK M) n)
    (t₁ t₂ : Fin (tapeSize M n)) (i₁ i₂ : Fin (tapeSize M n))
    (hne : (t₁, i₁) ≠ (t₂, i₂)) :
    (cellPartition M n hn2).blockOf
      (realToScaffold M n h (tapeIdx M n 0 t₁ i₁)) ≠
    (cellPartition M n hn2).blockOf
      (realToScaffold M n h (tapeIdx M n 0 t₂ i₂)) := by
  sorry -- Follows from tapeIdx being injective and cellPartition separating indices

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

/-- Bridge: the embedded violation poly has rank ≤ the scaffold violation poly.
    This follows from the scaffold violation polynomial being the
    multilinearization of the embedded violation polynomial (or equal). -/
theorem embedded_rank_le_scaffold_rank (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (h : numVars M n 0 ≤ compiledVarCount (defaultK M) n) :
    blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
      (embeddedViolationPoly M n h)
      (cellPartition_local M n hn2).partition
    ≤ blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyQ_ml (initialSemanticCNF M n hn2))
      (initialSemantic_local M n hn2).partition := by
  sorry -- Scaffold violation poly contains embedded violation poly

/-- Assembly: cookLevin_rank_bound from the bridge.
    permanent_rank ≤ embedded_violation_rank ≤ scaffold_violation_rank -/
theorem cookLevin_rank_bound_from_bridge (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (h : numVars M n 0 ≤ compiledVarCount (defaultK M) n)
    (hM : M.decides (CompiledSeparation.hardNPFamily n)) :
    blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
      (MvPolynomial.rename (CompiledSeparation.permToCompiledEmbed (defaultK M) n)
        (permPolyFlat (Nat.sqrt n)))
      (cellPartition_local M n hn2).partition
    ≤ blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyQ_ml (initialSemanticCNF M n hn2))
      (initialSemantic_local M n hn2).partition :=
  le_trans (permanent_span_le_violation_span M n hn2 h hM)
    (embedded_rank_le_scaffold_rank M n hn2 h)

end EncodingBridge
