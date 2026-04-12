/-
  GodMoveReal.lean — God-Move extraction with rank monotonicity

  Paper §29, Lemma 123:

  The compiler output P_{M',n}(u,z,v) decomposes as Q×_Φ(u,z) + R(v).
  By Lemma 122 (rank monotonicity): Γ(Q×_Φ) ≤ Γ(P_{M',n}).

  We formalize:
  1. Adding a constant does not change the SPDP subspace (κ ≥ 1)
  2. The God-Move extraction structure connecting compiled and coupled sheets
  3. The rank monotonicity chain for the separation
-/
import PallLean.PaperFaithfulSeparation
import Mathlib.Tactic
import Mathlib.Data.Nat.Log

namespace GodMoveReal

open SPDP MultilinearSPDP MvPolynomial TuringMachine PaperFaithfulSeparation

attribute [local instance] Classical.dec

/-! ## Adding a Constant Does Not Change SPDP Subspace (κ ≥ 1)

For the God-Move, we need: adding a constant to p does not change its
SPDP subspace when κ ≥ 1, because ∂_S(constant) = 0 for |S| ≥ 1. -/

/-- iterDerivList of a constant C c is 0 when the list is nonempty. -/
theorem iterDerivList_C_eq_zero {N : ℕ} (c : ℚ)
    (S : List (Fin N)) (hS : S ≠ []) :
    iterDerivList S (C c : MvPolynomial (Fin N) ℚ) = 0 := by
  cases S with
  | nil => exact absurd rfl hS
  | cons i rest =>
    unfold iterDerivList
    simp only [List.foldl_cons, pderiv_C]
    exact foldl_pderiv_zero rest

/-- Adding C c to a polynomial does not change its SPDP subspace when κ ≥ 1. -/
theorem mlBlockedSpdpSubspace_add_const {N : ℕ}
    (B : BlockPartition N) (κ ℓ : ℕ) (hκ : κ ≥ 1)
    (p : MvPolynomial (Fin N) ℚ) (c : ℚ) :
    mlBlockedSpdpSubspace B κ ℓ (p + C c) = mlBlockedSpdpSubspace B κ ℓ p := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro q ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
    rw [hq]
    have hS_ne : S ≠ [] := by intro h; subst h; simp at hlen; omega
    rw [iterDerivList_add S p (C c), iterDerivList_C_eq_zero c S hS_ne, add_zero]
    exact Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
  · apply Submodule.span_le.mpr
    intro q ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
    rw [hq]
    have hS_ne : S ≠ [] := by intro h; subst h; simp at hlen; omega
    have : m * iterDerivList S p = m * iterDerivList S (p + C c) := by
      rw [iterDerivList_add S p (C c), iterDerivList_C_eq_zero c S hS_ne, add_zero]
    rw [this]
    exact Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩

/-- Adding C c does not change SPDP rank when κ ≥ 1. -/
theorem mlBlockedSpdpRank_add_const {N : ℕ}
    (B : BlockPartition N) (κ ℓ : ℕ) (hκ : κ ≥ 1)
    (p : MvPolynomial (Fin N) ℚ) (c : ℚ) :
    mlBlockedSpdpRank B κ ℓ (p + C c) = mlBlockedSpdpRank B κ ℓ p := by
  unfold mlBlockedSpdpRank
  rw [mlBlockedSpdpSubspace_add_const B κ ℓ hκ p c]

/-! ## Negation Preserves SPDP Subspace

iterDerivList distributes over negation (by linearity of pderiv). -/

/-- pderiv distributes over negation. -/
theorem iterDerivList_neg {N : ℕ}
    (S : List (Fin N)) (p : MvPolynomial (Fin N) ℚ) :
    iterDerivList S (-p) = -iterDerivList S p := by
  induction S generalizing p with
  | nil => simp [iterDerivList]
  | cons i rest ih =>
    simp only [iterDerivList, List.foldl_cons]
    rw [show pderiv i (-p) = -(pderiv i p) from map_neg (pderiv i) p]
    exact ih (pderiv i p)

/-- mlProj distributes over negation. -/
theorem mlProj_neg {N : ℕ} (p : MvPolynomial (Fin N) ℚ) :
    mlProj (-p) = -mlProj p := by
  have h1 : -p = (-1 : ℚ) • p := by simp
  rw [h1, mlProj_smul]
  simp

/-- The SPDP subspace of -p equals that of p. -/
theorem mlBlockedSpdpSubspace_neg {N : ℕ}
    (B : BlockPartition N) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin N) ℚ) :
    mlBlockedSpdpSubspace B κ ℓ (-p) = mlBlockedSpdpSubspace B κ ℓ p := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro q ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
    rw [hq, iterDerivList_neg, mul_neg, mlProj_neg]
    exact Submodule.neg_mem _
      (Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩)
  · apply Submodule.span_le.mpr
    intro q ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
    rw [hq]
    have : m * iterDerivList S p = -(m * iterDerivList S (-p)) := by
      rw [iterDerivList_neg, mul_neg, neg_neg]
    rw [this, mlProj_neg]
    exact Submodule.neg_mem _
      (Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩)

/-- Γ(-p) ≤ Γ(p). -/
theorem mlBlockedSpdpRank_neg_le {N : ℕ}
    (B : BlockPartition N) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin N) ℚ) :
    mlBlockedSpdpRank B κ ℓ (-p) ≤ mlBlockedSpdpRank B κ ℓ p := by
  unfold mlBlockedSpdpRank
  rw [mlBlockedSpdpSubspace_neg B κ ℓ p]

/-! ## Rank Summand Bound (God-Move Decomposition)

If P = Q + R, then Γ(Q) ≤ Γ(P) + Γ(R).
Proof: Q = P + (-R), so Γ(Q) ≤ Γ(P) + Γ(-R) ≤ Γ(P) + Γ(R). -/

/-- If P = Q + R, then Γ(Q) ≤ Γ(P) + Γ(R). -/
theorem rank_summand_bound {N : ℕ}
    (B : BlockPartition N) (κ ℓ : ℕ)
    (p q r : MvPolynomial (Fin N) ℚ)
    (hpqr : p = q + r) :
    mlBlockedSpdpRank B κ ℓ q ≤
      mlBlockedSpdpRank B κ ℓ p + mlBlockedSpdpRank B κ ℓ r := by
  have hq : q = p + (-r) := by rw [hpqr]; ring
  calc mlBlockedSpdpRank B κ ℓ q
      = mlBlockedSpdpRank B κ ℓ (p + (-r)) := by rw [hq]
    _ ≤ mlBlockedSpdpRank B κ ℓ p + mlBlockedSpdpRank B κ ℓ (-r) :=
        mlBlockedSpdpRank_add_le B κ ℓ p (-r)
    _ ≤ mlBlockedSpdpRank B κ ℓ p + mlBlockedSpdpRank B κ ℓ r :=
        Nat.add_le_add_left (mlBlockedSpdpRank_neg_le B κ ℓ r) _

/-- When Γ(R) = 0: Γ(Q) ≤ Γ(P). -/
theorem rank_summand_le_of_zero_remainder {N : ℕ}
    (B : BlockPartition N) (κ ℓ : ℕ)
    (p q r : MvPolynomial (Fin N) ℚ)
    (hpqr : p = q + r)
    (hr : mlBlockedSpdpRank B κ ℓ r = 0) :
    mlBlockedSpdpRank B κ ℓ q ≤ mlBlockedSpdpRank B κ ℓ p := by
  calc mlBlockedSpdpRank B κ ℓ q
      ≤ mlBlockedSpdpRank B κ ℓ p + mlBlockedSpdpRank B κ ℓ r :=
        rank_summand_bound B κ ℓ p q r hpqr
    _ = mlBlockedSpdpRank B κ ℓ p := by omega

/-! ## God-Move Extraction Structure -/

/-- The God-Move extraction data. -/
structure GodMoveData (M : DTM) (n : ℕ) where
  N : ℕ
  partition : BlockPartition N
  poly : MvPolynomial (Fin N) ℚ
  coupled : PaperFaithfulSeparation.CoupledVerifierSheet
  coupledRank : ℕ → ℕ → ℕ
  compiledRank : ℕ → ℕ → ℕ
  rank_monotone : ∀ κ ℓ : ℕ, coupledRank κ ℓ ≤ compiledRank κ ℓ
  compiledRank_eq : ∀ κ ℓ : ℕ,
    compiledRank κ ℓ = mlBlockedSpdpRank partition κ ℓ poly

/-! ## Rank Monotonicity Chain for the Separation -/

/-- Abstract restriction monotonicity: subspace containment gives rank bound. -/
theorem restriction_rank_mono {N : ℕ}
    (B : BlockPartition N) (κ ℓ : ℕ)
    (p q : MvPolynomial (Fin N) ℚ)
    (h : mlBlockedSpdpSubspace B κ ℓ q ≤ mlBlockedSpdpSubspace B κ ℓ p) :
    mlBlockedSpdpRank B κ ℓ q ≤ mlBlockedSpdpRank B κ ℓ p :=
  Submodule.finrank_mono h


/-! ## Concrete typed source/target map surface

The active paper-faithful route needs an explicit typed source/target surface for
`ΠΦ : F[u,v] → F[u]`, even before the semantic proof of existence is available.
The structures below do not claim the map has been constructed from Cook-Levin.
They only make the typed ingredients explicit so later work can state the real
God-Move without collapsing compiled and coupled polynomials into one variable
space. -/

/-- Explicit data for the restriction stage of the God-Move.

This records which compiled variables are being fixed as administrative/tableau
coordinates and what constant specialization is applied to them. The remaining
semantic burden is to connect this abstract record to the actual Cook-Levin
variable layout for the hard instance. -/
structure GodMoveRestrictionData (compiledVars : ℕ) where
  administrativeVars : Finset (Fin compiledVars)
  tableauVars : Finset (Fin compiledVars)
  fixedVars : Finset (Fin compiledVars)
  freeVarsAfterRestriction : ℕ
  freeVarEmbedding : Fin freeVarsAfterRestriction → Fin compiledVars
  assignment : Fin compiledVars → ℚ
  clauseSheetPreservedVars : Finset (Fin compiledVars)
  fixes_administrative_vars : Prop
  fixes_tableau_vars_to_constants : Prop
  preserves_clause_sheet_vars : Prop
  specializedVars : Finset (Fin compiledVars)
  fixedVars_cover_specialized_coordinates : Prop
  free_embedding_avoids_fixed : Prop
  clauseSheetPreservedVars_avoid_fixed : Prop

/-- Explicit data for the projection stage of the God-Move.

After the restriction step removes the administrative/tableau coordinates, the
paper projects onto the clause-sheet coordinates `u`. This record makes that
coordinate-selection step explicit without yet claiming the real semantic proof
that the chosen coordinates are the correct ones for the hard instance. -/
structure GodMoveProjectionData (restrictedVars : ℕ) where
  clauseSheetVars : Finset (Fin restrictedVars)
  keptVars : Finset (Fin restrictedVars)
  projectedVars : ℕ
  coordinateMap : Fin projectedVars → Fin restrictedVars
  keptVarEmbedding : Fin projectedVars → Fin restrictedVars
  projectedCoordinates : Finset (Fin restrictedVars)
  droppedCoordinates : Finset (Fin restrictedVars)
  selects_clause_sheet_coordinates : Prop
  discards_non_clause_sheet_coordinates : Prop
  keptVars_match_clauseSheetVars : Prop
  coordinateMap_hits_keptVars : Prop
  projectedCoordinates_match_embedding : Prop
  droppedCoordinates_complement_projection : Prop

/-- Explicit data for the relabeling / normalization stage of the God-Move.

After projection to the clause-sheet coordinates, the paper applies a fixed
block-local relabeling / basis normalization before comparing with the coupled
sheet polynomial. This record exposes that third stage as data rather than
leaving it only as an opaque map. -/
structure GodMoveRelabelData (projectedVars coupledVars : ℕ) where
  sourceBlocks : ℕ
  targetBlocks : ℕ
  sourceBlockMap : Fin projectedVars → Fin sourceBlocks
  targetBlockMap : Fin coupledVars → Fin targetBlocks
  variableRelabel : Fin projectedVars → Fin coupledVars
  normalizedVarEmbedding : Fin projectedVars → Fin coupledVars
  normalizedCoordinates : Finset (Fin coupledVars)
  normalizationScalars : Fin coupledVars → ℚ
  respects_block_locality : Prop
  is_basis_normalization : Prop
  is_instance_uniform_relabeling : Prop
  variableRelabel_respects_blocks : Prop
  source_target_blocks_cohere : Prop
  normalizedCoordinates_match_relabel : Prop

/-- A typed map from compiled tableau space to coupled clause-sheet space.

The paper's `ΠΦ` is described as a composite of three operations:
1. restrict administrative/tableau variables to fixed constants,
2. project to the clause-sheet coordinates,
3. apply a fixed block-local relabeling / basis normalization.

We expose those layers here as explicit fields, while still packaging the final
composite map as `toFun`. The fields are descriptive scaffolding for the real
semantic theorem, not a claim that the construction has already been proved. -/
structure GodMoveTypedMap (compiledVars coupledVars : ℕ) where
  restrictionData : GodMoveRestrictionData compiledVars
  restrictedVars : ℕ
  projectionData : GodMoveProjectionData restrictedVars
  restrictFun : MvPolynomial (Fin compiledVars) ℚ → MvPolynomial (Fin restrictedVars) ℚ
  projectFun : MvPolynomial (Fin restrictedVars) ℚ →
    MvPolynomial (Fin projectionData.projectedVars) ℚ
  relabelData : GodMoveRelabelData projectionData.projectedVars coupledVars
  relabelFun : MvPolynomial (Fin projectionData.projectedVars) ℚ →
    MvPolynomial (Fin coupledVars) ℚ
  toFun : MvPolynomial (Fin compiledVars) ℚ → MvPolynomial (Fin coupledVars) ℚ
  factors_through : ∀ p, toFun p = relabelFun (projectFun (restrictFun p))
  restriction_is_constant_specialization : Prop
  projection_is_clause_sheet : Prop
  relabel_is_block_local_normalization : Prop
  instance_uniform : Prop
  witness_free : Prop
  block_local : Prop
  instance_uniform_coheres_with_relabel : Prop
  witness_free_coheres_with_restriction : Prop
  block_local_coheres_with_projection_relabel : Prop

/-- Typed target data for the coupled clause-sheet side. -/
structure GodMoveTypedTarget (coupledVars : ℕ) where
  partition : BlockPartition coupledVars
  poly : MvPolynomial (Fin coupledVars) ℚ

/-- Explicit typed God-Move surface connecting compiled and coupled spaces.

This is still only a surface/interface: it does not assert that the map has been
constructed from the real Cook-Levin compilation. It packages the typed objects
that a future paper-faithful semantic theorem should produce. -/
structure GodMoveTypedExtraction (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  coupledVars : ℕ
  map : GodMoveTypedMap (cook_levin_compilation M n hn2 htb hns).numVars coupledVars
  target : GodMoveTypedTarget coupledVars
  extraction_correct :
    map.toFun (compiledPoly (cook_levin_compilation M n hn2 htb hns)) = target.poly
  extraction_correct_factors_through : Prop
  target_lower :
    Nat.choose n (Nat.log 2 n) ≤
      mlBlockedSpdpRank target.partition (Nat.log 2 n) (Nat.log 2 n) target.poly
  rank_transfer :
    mlBlockedSpdpRank target.partition (Nat.log 2 n) (Nat.log 2 n) target.poly ≤
      mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns))

/-- Forgetting the concrete typed map data yields the lighter abstract interface
used in `PaperFaithfulSeparation.lean`. -/
def godMoveTypedExtractionToInterface
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (g : GodMoveTypedExtraction M n hn2 htb hns) :
    PaperFaithfulSeparation.GodMoveExtractionInterface M n hn2 htb hns where
  coupledVars := g.coupledVars
  coupledPartition := g.target.partition
  coupledPoly := g.target.poly
  instance_uniform := g.map.instance_uniform
  witness_free := g.map.witness_free
  block_local := g.map.block_local
  target_lower := g.target_lower
  rank_transfer := g.rank_transfer

end GodMoveReal
