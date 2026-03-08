/-
  ExtractionWiring.lean — Extraction rank monotonicity

  The core bridge theorem: rank(tseitin) ≤ rank(compiled).

  This is the semantic bridge between the NP lower bound (tseitin rank
  grows superpolynomially) and the P upper bound (compiled rank is
  polynomially bounded). It corresponds to Theorem 181 Item 3 of
  arXiv:2512.11820v5.

  The axiom `extraction_rank_le` is the ONE irreducible assumption
  in the formalization. It asserts that the SPDP rank of the Tseitin
  polynomial is at most the SPDP rank of the sheet-coupled compiled
  polynomial. This follows from:
    1. Rename preserves rank (injective embedding)
    2. Restriction is rank-nonincreasing (Lemma 33)
    3. Projection is rank-nonincreasing (Lemma 34)
    4. The extraction equation: restrict∘project on the compiled
       polynomial yields the renamed Tseitin polynomial
  Steps 1-3 are proved in this formalization. Step 4 is the concrete
  compiler-correctness claim about sheetCoupling (Theorem 223).
-/
import PallLean.SPDPDefs
import PallLean.Compiler
import PallLean.NPWitness
import PallLean.SheetCoupling
import Mathlib.Tactic

namespace ExtractionWiring

open MvPolynomial SPDP Compiler NPWitness TuringMachine Extraction

variable {F : Type*} [Field F]

/-! ## Core axiom: extraction rank monotonicity (Theorem 181 Item 3)

    For any DTM M, rank(tseitin) ≤ rank(compiled(M♯)).

    The two polynomial rings have different variable counts:
    - Tseitin: npNumVars n ≈ 5n (edge vars + selectors)
    - Compiled: numVars(M♯) ≈ n^(2·timeBound) (tape + state + head + input + padding)

    The sheet coupling M♯ embeds the Tseitin formula into its constraint
    structure. The extraction map T_Φ = restrict(selectors) ∘ project(verifier)
    applied to the compiled polynomial yields the renamed Tseitin polynomial.
    Since restriction and projection are rank-nonincreasing (proved in
    ExtractionProof.lean), and rename with injective maps preserves rank,
    the rank inequality follows.

    This axiom packages the entire extraction pipeline (variable classification,
    additive separability, extraction equation, rank transfer) into a single
    clean statement at the right level of abstraction. -/
axiom extraction_rank_le (F : Type*) [Field F] (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
      (tseitinPoly F n) ≤
    blockedSpdpRank (compiledPartition (sheetCoupling M) n) (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyOf F (sheetCoupling M) n)

/-- Wrapper matching the signature expected by Extraction.lean. -/
theorem extraction_rank_monotone (M : DTM) (n : ℕ) (hn : n ≥ 2 := by omega) :
    blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
      (tseitinPoly F n) ≤
    blockedSpdpRank (compiledPartition (sheetCoupling M) n)
      (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyOf F (sheetCoupling M) n) :=
  extraction_rank_le F M n hn

end ExtractionWiring
