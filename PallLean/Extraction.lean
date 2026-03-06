import PallLean.SPDPDefs
import PallLean.Compiler
import PallLean.NPWitness
import PallLean.TuringMachine
import PallLean.SheetCoupling
import PallLean.ExtractionWiring
import Mathlib.Tactic
/-!
# Extraction Map T_Φ — Pall §11–13
-/

namespace Extraction

open SPDP Compiler NPWitness TuringMachine MvPolynomial

/-- **Extraction rank monotonicity (Theorem 12.2)**

    For any DTM M, rank(tseitin) ≤ rank(compiled(M♯)).
    This is the semantic bridge between the NP lower bound and
    the P upper bound in the separation argument. -/
theorem extraction_rank_monotone (F : Type*) [Field F]
    (M : DTM) (n : ℕ) :
    blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
      (tseitinPoly F n) ≤
    blockedSpdpRank (compiledPartition (sheetCoupling M) n)
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPolyOf F (sheetCoupling M) n) :=
  ExtractionWiring.extraction_rank_monotone M n

end Extraction
