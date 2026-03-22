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
  · -- Transversal: card((S.map f).toFinset.image bp.blockOf) = card((S.map f).toFinset)
    -- Key: (S.map f).toFinset.image bp.blockOf = S.toFinset.image (bp.blockOf ∘ f)
    --       = S.toFinset.image (pullback bp f).blockOf
    -- And (S.map f).toFinset.card = S.toFinset.card (f injective)
    -- So the equality follows from htrans.
    have h1 : (S.map f).toFinset = S.toFinset.image f := by
      ext x; simp [List.mem_toFinset, Finset.mem_image, List.mem_map]
    rw [h1, Finset.image_image]
    -- Now goal: card(S.toFinset.image (bp.blockOf ∘ f)) = card(S.toFinset.image f)
    -- LHS = card(S.toFinset.image (pullback bp f).blockOf) = card(S.toFinset) = htrans
    -- RHS = card(S.toFinset) (f injective)
    rw [show bp.blockOf ∘ f = (CompiledPoly.BlockPartition.pullback bp f).blockOf from rfl]
    rw [htrans]
    exact (Finset.card_image_of_injective S.toFinset hf).symm
  · -- S-coupling: ∀ v ∈ (rename f ms).vars, bp.blockOf v ∈ (S.map f).toFinset.image bp.blockOf
    intro v hv
    -- vars(rename f ms) ⊆ f '' vars(ms)
    have hv_range := MvPolynomial.vars_rename f ms hv
    simp only [Finset.mem_image] at hv_range
    obtain ⟨w, hw_mem, rfl⟩ := hv_range
    -- bp.blockOf (f w) = (pullback bp f).blockOf w
    -- ∈ S.toFinset.image (pullback bp f).blockOf (from hcoupl)
    -- = (S.map f).toFinset.image bp.blockOf
    have hw_coupled := hcoupl w hw_mem
    simp only [Finset.mem_image] at hw_coupled ⊢
    simp only [List.mem_toFinset, List.mem_map] at *
    obtain ⟨u, hu_mem, hu_eq⟩ := hw_coupled
    exact ⟨f u, ⟨u, hu_mem, rfl⟩, hu_eq⟩
  · -- Product + iterDerivList commute with rename
    rw [map_mul, iterDerivList_rename f hf]

theorem rename_rank_le {m N : ℕ} (f : Fin m → Fin N) (hf : Function.Injective f)
    (κ ℓ : ℕ) (p : MvPolynomial (Fin m) ℚ) (bp : BlockPartition N) :
    blockedSpdpRankQ κ ℓ p (CompiledPoly.BlockPartition.pullback bp f) ≤
      blockedSpdpRankQ κ ℓ (rename f p) bp := by
  unfold blockedSpdpRankQ
  -- Step 1: rename f maps LHS gens → RHS gens (via rename_gen_mem)
  -- Step 2: So (span LHS).map (rename f) ≤ span RHS
  -- Step 3: finrank(span LHS) ≤ finrank(span RHS) via injection + mono
  
  set pbp := CompiledPoly.BlockPartition.pullback bp f
  set lhs_gens := { q : MvPolynomial (Fin m) ℚ | ∃ S ms,
    S.length ≤ κ ∧ ms.totalDegree ≤ ℓ ∧
    (S.toFinset.image pbp.blockOf).card = S.toFinset.card ∧
    (∀ v ∈ ms.vars, pbp.blockOf v ∈ S.toFinset.image pbp.blockOf) ∧
    q = ms * SPDP.iterDerivList S p }
  set rhs_gens := { q : MvPolynomial (Fin N) ℚ | ∃ S ms,
    S.length ≤ κ ∧ ms.totalDegree ≤ ℓ ∧
    (S.toFinset.image bp.blockOf).card = S.toFinset.card ∧
    (∀ v ∈ ms.vars, bp.blockOf v ∈ S.toFinset.image bp.blockOf) ∧
    q = ms * SPDP.iterDerivList S (rename f p) }
  
  -- rename f maps lhs_gens into rhs_gens
  have h_image : ∀ q ∈ lhs_gens, rename f q ∈ rhs_gens := fun q hq =>
    rename_gen_mem f hf κ ℓ p bp q hq
  
  -- So (span lhs_gens).map (rename f).toLinearMap ≤ span rhs_gens
  have h_map_le : (Submodule.span ℚ lhs_gens).map
      (rename f : MvPolynomial (Fin m) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ).toLinearMap ≤
      Submodule.span ℚ rhs_gens := by
    rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    intro q hq
    exact Submodule.mem_comap.mpr (Submodule.subset_span (h_image q hq))
  
  -- finrank(span lhs) ≤ finrank(image) ≤ finrank(span rhs)
  -- For the first ≤: rename f is injective → ker ∩ span = 0 → finrank preserved
  -- For the second ≤: image ≤ span rhs → finrank_mono
  -- The RHS span is finite-dimensional (inside restrictTotalDegree)
  have hfin_rhs : Module.Finite ℚ ↥(Submodule.span ℚ rhs_gens) := by
    apply Module.Finite.of_injective
      (Submodule.inclusion (CompiledPoly.spdp_span_le_restrictTotalDegree κ ℓ (rename f p) bp))
      (Submodule.inclusion_injective _)
  -- rename f is injective → finrank(span lhs) = finrank(image)
  set ren := (rename f : MvPolynomial (Fin m) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ).toLinearMap
  have hren_inj : Function.Injective ren := MvPolynomial.rename_injective f hf
  have h_eq : Module.finrank ℚ (Submodule.span ℚ lhs_gens) =
      Module.finrank ℚ ((Submodule.span ℚ lhs_gens).map ren) :=
    (Submodule.equivMapOfInjective ren hren_inj (Submodule.span ℚ lhs_gens)).finrank_eq
  -- Chain: finrank(LHS) = finrank(image) ≤ finrank(RHS)
  rw [h_eq]
  exact Submodule.finrank_mono h_map_le

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
