/-
  ExtractionDecomposition.lean — Decomposition of extraction_rank_monotone

  The extraction rank inequality:
    rank(perm, extraction_BP) ≤ rank(V, cell_partition)
  
  decomposes into three independent sub-facts:

  (A) Rename preserves rank: for injective f,
      rank(p, pullback_BP) ≤ rank(rename f p, BP)
      
  (B) Monotonicity in parameters: PROVED (blockedSpdpRankQ_mono_params)

  (C) Cook-Levin extraction: the permanent polynomial can be extracted
      from the violation polynomial via a specific polynomial map.
      This is the core Cook-Levin correctness claim.
      
  Sub-fact (A) is algebraic and should be provable from MvPolynomial.rename.
  Sub-fact (C) is the deep one — it requires the full Cook-Levin theorem.
-/
import PallLean.CompiledPoly
import PallLean.Permanent
import Mathlib.Tactic

namespace ExtractionDecomposition

open MvPolynomial CompiledPoly

/-! ## Sub-fact (A): Rename preserves rank

  If f : Fin m ↪ Fin N is injective, then:
    blockedSpdpRankQ κ ℓ p (pullback f bp) ≤ blockedSpdpRankQ κ ℓ (rename f p) bp
    
  Proof sketch:
  - rename f sends generators m · ∂^S(p) to (rename f m) · ∂^{f(S)}(rename f p)
  - this is injective on the span (since rename f is an algebra embedding)
  - so the rank can only increase when we add more generators in the larger space
  
  This should be formalizable using MvPolynomial.rename_injective and
  the algebra homomorphism properties of rename.
-/

/-- Pullback of a block partition along a function. -/
def CompiledPoly.BlockPartition.pullback {m N : ℕ} (bp : BlockPartition N) (f : Fin m → Fin N) :
    BlockPartition m where
  numBlocks := bp.numBlocks
  blockOf := fun v => bp.blockOf (f v)

/-- iterDerivList commutes with rename (for injective f). -/
theorem iterDerivList_rename {m N : ℕ} {F : Type*} [CommRing F]
    (f : Fin m → Fin N) (hf : Function.Injective f)
    (S : List (Fin m)) (p : MvPolynomial (Fin m) F) :
    SPDP.iterDerivList (S.map f) (rename f p) = rename f (SPDP.iterDerivList S p) := by
  induction S generalizing p with
  | nil => simp [SPDP.iterDerivList]
  | cons i T ih =>
    simp only [SPDP.iterDerivList, List.foldl_cons, List.map_cons]
    rw [pderiv_rename hf]
    exact ih (pderiv i p)

/-- Rename by an injective function preserves (or increases) SPDP rank.
    Proof: rename f maps each generator m·∂^S(p) to (rename f m)·∂^{fS}(rename f p).
    This is an injective map on the span (since rename f is an algebra embedding).
    So the image span ≤ the full span of rename f p's generators. -/
-- Helper: rename preserves the generating set membership
private theorem rename_gen_mem {m N : ℕ} (f : Fin m → Fin N) (hf : Function.Injective f)
    (κ ℓ : ℕ) (p : MvPolynomial (Fin m) ℚ) (bp : BlockPartition N)
    (q : MvPolynomial (Fin m) ℚ)
    (hq : q ∈ { r : MvPolynomial (Fin m) ℚ | ∃ S ms,
      S.length ≤ κ ∧ ms.totalDegree ≤ ℓ ∧
      (S.toFinset.image (CompiledPoly.BlockPartition.pullback bp f).blockOf).card =
        S.toFinset.card ∧
      (∀ v ∈ ms.vars, (CompiledPoly.BlockPartition.pullback bp f).blockOf v ∈
        S.toFinset.image (CompiledPoly.BlockPartition.pullback bp f).blockOf) ∧
      r = ms * SPDP.iterDerivList S p }) :
    rename f q ∈ { r : MvPolynomial (Fin N) ℚ | ∃ S ms,
      S.length ≤ κ ∧ ms.totalDegree ≤ ℓ ∧
      (S.toFinset.image bp.blockOf).card = S.toFinset.card ∧
      (∀ v ∈ ms.vars, bp.blockOf v ∈ S.toFinset.image bp.blockOf) ∧
      r = ms * SPDP.iterDerivList S (rename f p) } := by
  obtain ⟨S, ms, hlen, hdeg, htrans, hcoupl, rfl⟩ := hq
  refine ⟨S.map f, rename f ms, by simp [hlen], ?_, ?_, ?_, ?_⟩
  · -- totalDegree preserved
    exact le_trans (totalDegree_rename_le f ms) hdeg
  · -- Transversal transfers via f injective
    -- (S.map f).toFinset.image bp.blockOf has same card as (S.map f).toFinset
    -- because pullback.blockOf = bp.blockOf ∘ f
    sorry -- Finset card manipulation with injective f
  · -- S-coupling: ∀ v ∈ (rename f ms).vars, bp.blockOf v ∈ (S.map f).toFinset.image bp.blockOf
    -- rename f ms has vars ⊆ f '' ms.vars (by MvPolynomial.vars_rename)
    -- For v ∈ f '' ms.vars: v = f w for some w ∈ ms.vars
    -- bp.blockOf (f w) = (pullback bp f).blockOf w ∈ S.toFinset.image (pullback bp f).blockOf
    -- = (S.map f).toFinset.image bp.blockOf
    sorry -- vars_rename + pullback definition
  · -- Product + iterDerivList commute with rename
    rw [map_mul, iterDerivList_rename f hf]

theorem rename_rank_le {m N : ℕ} (f : Fin m → Fin N) (hf : Function.Injective f)
    (κ ℓ : ℕ) (p : MvPolynomial (Fin m) ℚ) (bp : BlockPartition N) :
    blockedSpdpRankQ κ ℓ p (CompiledPoly.BlockPartition.pullback bp f) ≤
      blockedSpdpRankQ κ ℓ (rename f p) bp := by
  unfold blockedSpdpRankQ
  -- rename f maps LHS span into RHS span, and is injective
  -- So finrank(LHS) ≤ finrank(image of LHS under rename f) ≤ finrank(RHS)
  sorry

/-! ## Sub-fact (C): Cook-Levin extraction

  The permanent polynomial on m = √n variables can be "extracted" from
  the violation polynomial V_{M,n} of the permanent-computing DTM.
  
  Concretely: there exists an injective map f : Fin (m²) → Fin N and
  a block partition bp such that:
    rename f (permPolyFlat m) "appears in" violationPolyQ(CNF)
    
  The rank inequality follows because the permanent's SPDP generators
  are a subset of the violation polynomial's generators (via rename).
  
  This requires:
  1. Constructing the DTM M that computes the permanent
  2. The Cook-Levin encoding of M's computation as a violation polynomial
  3. Showing the permanent embeds into this encoding
  
  This is the full Cook-Levin theorem + extraction map (Paper §11-13).
-/

/-- Cook-Levin extraction: the permanent embeds into the compiled polynomial. -/
axiom cookLevin_extraction (M : TuringMachine.DTM) (n : ℕ) (hn2 : n ≥ 2) :
    True  -- placeholder for the extraction embedding

end ExtractionDecomposition
