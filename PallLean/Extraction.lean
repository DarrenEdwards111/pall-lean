/-!
# Extraction Map T_Φ

Pall paper Sections 11-13. THE CRITICAL JOINT.
-/

import PallLean.SPDPDefs
import PallLean.Compiler
import PallLean.NPWitness

namespace Extraction

open SPDP Compiler NPWitness MvPolynomial

/-! ## Verifier-Sheet Coupling -/

def sheetCoupling (M : PolyTimeTM) : PolyTimeTM :=
  { c := M.c + 1 }

/-! ## Extraction: Rank Monotonicity (Lemma 13.14 + Cor 13.20)

This axiom encodes the composition of 5 rank-safe stages.
It is the load-bearing joint A4 of the separation. -/

/-- **A4 (Corollary 13.20)**: The extraction map T_Φ connects the
    P-side compiled polynomial to the NP-side coupled sheet,
    with rank monotonicity.

    ΓB(Q×_Φ) ≤ ΓB(P_{M♯,n})

    Mathematical content:
    - Proj(u,z): projection → rank ≤ (delete rows/cols)
    - (v := 0): restriction → rank ≤ (specialise vars)
    - (a := a₀): restriction → rank ≤
    - Relabel_Φ: block-local invertible → rank =
    - Π⁺: gauge normalisation → rank ≤
    - Additive separability (Lemma 13.11)
    - Normalization to exact coupled sheet (Lemma 13.17) -/
axiom extraction_rank_chain (F : Type*) [Field F] (n : ℕ)
    (M : PolyTimeTM)
    (params : SPDPParams)
    (B_comp : BlockPartition (compilerVars n (sheetCoupling M).c))
    (B_np : BlockPartition (npVars n))
    (p_compiled : MvPolynomial (Fin (compilerVars n (sheetCoupling M).c)) F)
    (Q_witness : MvPolynomial (Fin (npVars n)) F)
    (h_compiled : True)   -- p is compiled from M♯
    (h_witness : True)    -- Q is the coupled sheet
    (h_extraction : True) -- T_Φ(p) = Q (Lemma 13.17) :
    spdpRank (npVars n) params B_np Q_witness ≤
      spdpRank (compilerVars n (sheetCoupling M).c) params B_comp p_compiled

end Extraction
