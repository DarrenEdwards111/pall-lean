/-!
# Extraction Map and Rank Monotonicity

Pall paper Sections 11-13: T_Φ connects P-side objects to NP-side witnesses.

⚠️ THIS IS THE CRITICAL LOAD-BEARING JOINT ⚠️
-/

import PallLean.SPDPDefs
import PallLean.Compiler
import PallLean.NPWitness
import Mathlib.Data.MvPolynomial.Basic

namespace Extraction

open SPDP Compiler NPWitness MvPolynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Verifier-Sheet Coupling (Section 11) -/

/-- M♯ = Sheet(M): a polytime TM augmented with clause gadgets.
    L(M♯) = L(M) and M♯ ∈ DTIME(n^{c'}) -/
def sheetCoupling (M : PolyTimeTM) : PolyTimeTM :=
  { c := M.c + 1 }  -- c' = c + 1 (one extra polynomial factor)

/-! ## Extraction Map T_Φ (Definition 13.13) -/

/-- T_Φ applied to a compiled polynomial yields something in the NP-side space.
    Composed of 5 rank-safe stages:
    Π⁺ ∘ Relabel_Φ ∘ (a := a₀) ∘ (v := 0) ∘ Proj(u,z) -/
noncomputable def extractionMap (n : ℕ) (Φ : TseitinFormula n)
    (params : SPDPParams) :
    MvPolynomial (Fin (compilerVars n (sheetCoupling ⟨0⟩).c)) F →
    MvPolynomial (Fin (npVars n)) F :=
  fun _ => 0 -- placeholder; each stage is rank-safe

/-! ## Rank Safety (Lemma 13.14) -/

/-- Each stage of T_Φ is rank-nonincreasing:
    ΓB(T_Φ(p)) ≤ ΓB(p)

    Stage 1 (Projection): deletes rows/columns → rank ≤
    Stage 2 (Restriction v:=0): specialises variables → rank ≤
    Stage 3 (Pin a:=a₀): specialises variables → rank ≤
    Stage 4 (Relabel): block-local invertible → rank =
    Stage 5 (Gauge Π⁺): block-local linear → rank ≤ -/
theorem extraction_rank_safe (n : ℕ) (Φ : TseitinFormula n) (M : PolyTimeTM)
    (params : SPDPParams)
    (B_comp : BlockPartition (compilerVars n (sheetCoupling M).c))
    (B_np : BlockPartition (npVars n))
    (p : MvPolynomial (Fin (compilerVars n (sheetCoupling M).c)) F) :
    spdpRank (npVars n) params B_np (extractionMap n Φ params p) ≤
      spdpRank (compilerVars n (sheetCoupling M).c) params B_comp p := by
  sorry

/-! ## Extraction Correctness (Lemma 13.17) -/

/-- T_Φ(P_{M♯,n}) = Q×_Φ (up to rank-irrelevant constant when κ ≥ 1) -/
theorem extraction_correct (n : ℕ) (Φ : TseitinFormula n) (M : PolyTimeTM)
    (params : SPDPParams)
    (B_comp : BlockPartition (compilerVars n (sheetCoupling M).c))
    (B_np : BlockPartition (npVars n)) :
    spdpRank (npVars n) params B_np
      (extractionMap n Φ params (compiledPoly n (sheetCoupling M) params B_comp : MvPolynomial _ F)) =
    spdpRank (npVars n) params B_np (coupledSheet n Φ params B_np : MvPolynomial _ F) := by
  sorry

/-! ## Corollary 13.20: The one-line rank chain -/

/-- ΓB(Q×_Φ) ≤ ΓB(P_{M♯,n}) ≤ n^{O(1)} -/
theorem rank_chain (n : ℕ) (Φ : TseitinFormula n) (M : PolyTimeTM)
    (params : SPDPParams)
    (B_comp : BlockPartition (compilerVars n (sheetCoupling M).c))
    (B_np : BlockPartition (npVars n)) :
    spdpRank (npVars n) params B_np (coupledSheet n Φ params B_np : MvPolynomial _ F) ≤
      spdpRank (compilerVars n (sheetCoupling M).c) params B_comp
        (compiledPoly n (sheetCoupling M) params B_comp : MvPolynomial _ F) := by
  calc spdpRank (npVars n) params B_np (coupledSheet n Φ params B_np : MvPolynomial _ F)
      = spdpRank (npVars n) params B_np
          (extractionMap n Φ params (compiledPoly n (sheetCoupling M) params B_comp)) := by
        rw [extraction_correct n Φ M params B_comp B_np]
    _ ≤ spdpRank (compilerVars n (sheetCoupling M).c) params B_comp
          (compiledPoly n (sheetCoupling M) params B_comp) := by
        exact extraction_rank_safe n Φ M params B_comp B_np _

end Extraction
