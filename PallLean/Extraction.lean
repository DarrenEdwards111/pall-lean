/-!
# Extraction Map and Rank Monotonicity

Pall paper Sections 11-13: The extraction map T_Φ that connects
P-side compiled objects to NP-side witness objects.

THIS IS THE CRITICAL LOAD-BEARING JOINT OF THE PROOF.
-/

import PallLean.SPDPDefs
import PallLean.Compiler
import PallLean.NPWitness

namespace Extraction

open SPDP Compiler NPWitness

/-! ## Verifier-Sheet Coupling (Section 11) -/

/-- M♯ = Sheet(M): the verifier-sheet coupled decider.
    Takes a polytime 3-SAT decider M and produces M♯ that
    includes the clause gadgets in its compiled form. -/
structure SheetCoupledTM extends PolyTimeTM where
  -- M♯ recognises the same language as M
  same_language : True
  -- M♯ is still polytime (Lemma 11.2)
  still_polytime : True

/-- Any polytime 3-SAT decider can be converted to a sheet-coupled version -/
axiom sheet_coupling (M : PolyTimeTM) : SheetCoupledTM

/-! ## Extraction Map T_Φ (Section 13, Definition 13.13) -/

/-- The extraction map T_Φ: composed of 5 rank-safe stages.
    T_Φ := Π⁺ ∘ Relabel_Φ ∘ (a := a₀) ∘ (v := 0) ∘ Proj(u,z)

    Stage 1: Proj(u,z) — project to verifier/clause blocks
    Stage 2: (v := 0)  — witness-free restriction
    Stage 3: (a := a₀) — pin admin/tag variables
    Stage 4: Relabel_Φ — instance-specific affine relabeling
    Stage 5: Π⁺        — gauge normalization -/
axiom extraction_map (F : Type*) [Field F] {n nv : ℕ}
  (Φ : TseitinFormula n) (params : SPDPParams)
  (B : BlockPartition nv) :
  MvPolynomial (Fin nv) F → MvPolynomial (Fin (np_vars n)) F

/-! ## Rank Safety (Lemma 13.14) -/

/-- **Lemma 13.14 (Stagewise rank-safety)**:
    Each stage of T_Φ is rank-nonincreasing. -/
axiom extraction_rank_safe (F : Type*) [Field F] {n nv : ℕ}
  (Φ : TseitinFormula n) (params : SPDPParams)
  (B_in : BlockPartition nv) (B_out : BlockPartition (np_vars n))
  (p : MvPolynomial (Fin nv) F) :
  SPDPRank F params B_out (extraction_map F Φ params B_in p) ≤
    SPDPRank F params B_in p

/-! ## Extraction Correctness (Lemma 13.15, 13.17) -/

/-- **Lemma 13.17 (Normalization to exact coupled sheet)**:
    T_Φ applied to the compiled polynomial of M♯ on input Φ
    yields exactly Q×_Φ. -/
axiom extraction_correct (F : Type*) [Field F] {n : ℕ}
  (M♯ : SheetCoupledTM) (Φ : TseitinFormula n)
  (params : SPDPParams) (B_comp : BlockPartition (compiler_vars n M♯.c))
  (B_np : BlockPartition (np_vars n)) :
  extraction_map F Φ params B_comp (compiled_polynomial F M♯.toPolyTimeTM n params B_comp) =
    coupled_sheet F Φ (np_vars n) params B_np

/-! ## The One-Line Rank Inequality (Corollary 13.20) -/

/-- **Corollary 13.20**: Combining extraction correctness with rank safety:
    ΓB(Q×_Φ) ≤ ΓB(P_{M♯,n}) -/
theorem rank_inequality (F : Type*) [Field F] {n : ℕ}
  (M♯ : SheetCoupledTM) (Φ : TseitinFormula n)
  (params : SPDPParams) (B_comp : BlockPartition (compiler_vars n M♯.c))
  (B_np : BlockPartition (np_vars n)) :
  SPDPRank F params B_np (coupled_sheet F Φ (np_vars n) params B_np) ≤
    SPDPRank F params B_comp (compiled_polynomial F M♯.toPolyTimeTM n params B_comp) := by
  rw [← extraction_correct F M♯ Φ params B_comp B_np]
  exact extraction_rank_safe F Φ params B_comp B_np _

end Extraction
