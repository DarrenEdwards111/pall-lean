import PallLean.SPDPDefs
import PallLean.Compiler
import PallLean.NPWitness
import PallLean.TuringMachine
import Mathlib.Tactic
/-!
# Extraction Map T_Φ — Pall §11–13
-/

namespace Extraction

open SPDP Compiler NPWitness TuringMachine MvPolynomial

/-- M♯ = Sheet(M): main track + auxiliary clause track (Def 11.1) -/
def sheetCoupling (M : DTM) : DTM where
  numStates := M.numStates + 3
  hStates := by omega
  transition := fun q b =>
    if h : q.val < M.numStates then
      let ⟨q', w, d⟩ := M.transition ⟨q.val, h⟩ b
      (⟨q'.val, by omega⟩, w, d)
    else (q, b, true)
  timeBound := M.timeBound + 1

/-- **Extraction rank monotonicity (Theorem 12.2)**

    ΓB(Q×_Φn) ≤ ΓB(p_{M♯,n})

    The extraction pipeline (projection, restriction, relabeling, gauge)
    transforms p_{M♯,n} into Q×_Φn. Each stage is rank-nonincreasing:
    - Projection: subspace containment → finrank ≤
    - Restriction: setting variables → rank monotone
    - Relabeling: injective rename → rank invariant
    - Gauge normalization: rank nonincreasing -/
theorem extraction_rank_monotone (F : Type*) [CommRing F] [Nontrivial F]
    (M : DTM) (n : ℕ) :
    blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
      (tseitinPoly F n) ≤
    blockedSpdpRank (compiledPartition (sheetCoupling M) n)
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPolyOf F (sheetCoupling M) n) := by
  sorry -- Thm 12.2: extraction pipeline, each stage rank-nonincreasing

end Extraction
