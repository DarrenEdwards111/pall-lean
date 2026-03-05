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

/-- **Extraction rank monotonicity (Theorem 12.2) — NOW A THEOREM**

    Proved from two structural axioms in ExtractionWiring.lean:
    - `relabel_generators_subset`: rename maps generators into image of generators
    - `extraction_factorization`: tseitinPoly = gauge(relabel(restrict(project(compiledPoly))))

    Plus three proved stage lemmas from ExtractionProof.lean:
    - `project_rank_le`, `restrict_rank_le`, `gauge_scalar_rank_le` -/
theorem extraction_rank_monotone (F : Type*) [Field F]
    (M : DTM) (n : ℕ) :
    blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
      (tseitinPoly F n) ≤
    blockedSpdpRank (compiledPartition (sheetCoupling M) n)
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPolyOf F (sheetCoupling M) n) :=
  ExtractionWiring.extraction_rank_monotone M n

end Extraction
