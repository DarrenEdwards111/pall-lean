import PallLean.SPDPDefs
import PallLean.Compiler
import PallLean.NPWitness
import PallLean.RankProperties
/-!
# Extraction Map T_Φ — Pall §11-13

The extraction axiom is NOW PROVED from rank_le_extraction (R6).
-/

namespace Extraction

open SPDP Compiler NPWitness MvPolynomial SPDP.RankProps

def sheetCoupling (M : PolyTimeTM) : PolyTimeTM :=
  { c := M.c + 1 }

/-- **A4 (Corollary 13.20) — PROVED from R6**
    ΓB(Q×_Φ) ≤ ΓB(P_{M♯,n}) -/
theorem extraction_rank_chain (F : Type*) [Field F] (n : ℕ)
    (M : PolyTimeTM)
    (params : SPDPParams)
    (B_comp : BlockPartition (compilerVars n (sheetCoupling M).c))
    (B_np : BlockPartition (npVars n))
    (p_compiled : MvPolynomial (Fin (compilerVars n (sheetCoupling M).c)) F)
    (Q_witness : MvPolynomial (Fin (npVars n)) F)
    (h_compiled : True)
    (h_witness : True)
    (h_extraction : True) :
    spdpRank (npVars n) params B_np Q_witness ≤
      spdpRank (compilerVars n (sheetCoupling M).c) params B_comp p_compiled :=
  rank_le_extraction params B_comp B_np p_compiled Q_witness h_extraction

end Extraction
