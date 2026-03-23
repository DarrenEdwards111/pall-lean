/-
  CookLevinExtraction.lean — Theorem stack for cookLevin_rank_bound

  The goal: prove that when M decides hardNPFamily,
  rank(rename(perm), partition) ≤ rank(violationPolyQ_ml, partition)

  Decomposition into sub-theorems:

  (A) Variable embedding correctness:
      permToCompiledEmbed lands permanent variables in the right scaffold cells.

  (B) Partition compatibility:
      The pullback partition through permToCompiledEmbed refines the
      permanent-side block structure.

  (C) Extraction containment (the semantic core):
      The renamed permanent polynomial's SPDP generators are contained
      in the violation polynomial's SPDP span.

      This is the real Cook-Levin content. It requires:
      - M decides hardNPFamily → M's computation on permanent inputs
        produces a specific pattern in the violation polynomial
      - The violation polynomial's clause structure encodes M's transitions
      - The permanent's algebraic structure survives through this encoding

  (D) Rank transfer:
      From (C), use Submodule.finrank_mono to get the rank inequality.
-/
import PallLean.CompiledPoly
import PallLean.CookLevin
import PallLean.ExtractionDecomposition
import PallLean.CompiledSeparation
import PallLean.TuringMachine
import Mathlib.Tactic

namespace CookLevinExtraction

open MvPolynomial CompiledPoly CookLevin SPDP

/-! ## (A) Variable embedding correctness -/

-- permToCompiledEmbed maps Fin(√n × √n) → Fin(compiledVarCount k n)
-- via embedVar. We need: the image lands in the input variable region.

theorem permEmbed_range_subset_input (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2) :
    ∀ i : Fin (Nat.sqrt n * Nat.sqrt n),
      (CompiledSeparation.permToCompiledEmbed (defaultK M) n i).1 < n := by
  intro i
  have h_sqrt := Nat.sqrt_le n
  have hi := i.2
  calc (CompiledSeparation.permToCompiledEmbed (defaultK M) n i).1
      = i.1 := rfl
    _ < Nat.sqrt n * Nat.sqrt n := hi
    _ ≤ n := h_sqrt

/-! ## (B) Partition compatibility -/

-- Under cellPartition, input vars get their own blocks (block = var index).
-- So the pullback partition through permEmbed assigns each permanent var
-- to its own block. This matches the permanent's natural block structure.

theorem permEmbed_blockOf (M : TuringMachine.DTM) (n : ℕ) (hn2 : n ≥ 2)
    (i : Fin (Nat.sqrt n * Nat.sqrt n)) :
    (cellPartition M n hn2).blockOf
      (CompiledSeparation.permToCompiledEmbed (defaultK M) n i) =
    ⟨i.1, by
      have := permEmbed_range_subset_input M n hn2 i
      exact Nat.lt_of_lt_of_le this (Nat.le_add_right n 2)⟩ := by
  unfold cellPartition CompiledSeparation.permToCompiledEmbed embedVar
  simp only
  have hi : (i : ℕ) < n := permEmbed_range_subset_input M n hn2 i
  split_ifs with h
  · rfl

/-! ## (C) Extraction containment — the semantic core

  This is the deep theorem. It requires showing that when M decides
  hardNPFamily (which involves the permanent), the violation polynomial's
  SPDP span contains all renamed permanent generators.

  The argument:
  1. M decides hardNPFamily → for each input x of the permanent,
     M's computation trace encodes whether perm(matrix(x)) > 0.
  2. The Cook-Levin encoding turns M's computation trace into clauses.
  3. The violation polynomial Σ clausePoly(c)² encodes all clause violations.
  4. The permanent's algebraic structure appears in the violation polynomial
     because the clauses encode M's transitions on permanent inputs.
  5. Each permanent SPDP generator (partial derivative + shift) maps to
     a combination of violation polynomial generators.

  This is the core content of the paper's §11-13.
  It requires the actual DTM transition structure, not just the scaffold.
-/

-- For now, state the key intermediate:
-- Every renamed permanent generator is in the violation polynomial's span.

-- This would follow from: rename(perm) = restriction of violationPolyQ_ml
-- to the permanent variable indices, after appropriate specialization.

-- The restriction here means: set all non-permanent variables to their
-- values determined by M's computation trace on the given input.

-- PLACEHOLDER: the generatorwise containment theorem
-- theorem permanent_generator_in_violation_span ...

end CookLevinExtraction
