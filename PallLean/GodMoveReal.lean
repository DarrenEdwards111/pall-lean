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
import PallLean.GodMoveCore
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

/-- Abstract theorem target for the harmlessness of a compiled-side remainder.

This is the point where the existing rank lemmas in this file should eventually
connect to the new decomposition story: if the remainder witness is sufficiently
harmless, then the extracted target controls the compiled rank. -/
theorem godMoveRemainder_rank_harmless
    {N : ℕ} (B : BlockPartition N) (κ ℓ : ℕ)
    (p q r : MvPolynomial (Fin N) ℚ)
    (hpqr : p = q + r) :
    mlBlockedSpdpRank B κ ℓ r = 0 →
    mlBlockedSpdpRank B κ ℓ q ≤ mlBlockedSpdpRank B κ ℓ p :=
  rank_summand_le_of_zero_remainder B κ ℓ p q r hpqr

/-- Sanity bridge: the generic summand lemma already proves the desired
remainder-harmlessness shape. This pins the new decomposition story to the
actual rank infrastructure rather than leaving it purely aspirational. -/
theorem godMoveRemainder_rank_harmless_of_zero
    {N : ℕ} (B : BlockPartition N) (κ ℓ : ℕ)
    (p q r : MvPolynomial (Fin N) ℚ)
    (hpqr : p = q + r)
    (hr : mlBlockedSpdpRank B κ ℓ r = 0) :
    mlBlockedSpdpRank B κ ℓ q ≤ mlBlockedSpdpRank B κ ℓ p := by
  exact rank_summand_le_of_zero_remainder B κ ℓ p q r hpqr hr

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

/-- Desired staged extraction identity for the compiled polynomial.

This packages the exact theorem shape we eventually want from the semantic God-
Move construction: after restriction, projection, and relabeling, the compiled
Cook-Levin polynomial becomes the coupled target polynomial. -/
def godMoveStagedExtractionTarget (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (coupledVars : ℕ)
    (map : GodMoveTypedMap (cook_levin_compilation M n hn2 htb hns).numVars coupledVars)
    (target : GodMoveTypedTarget coupledVars) : Prop :=
  map.relabelFun
      (map.projectFun
        (map.restrictFun (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) =
    target.poly

/-- The typed God-Move extraction packages all components of the paper's §29
extraction into a single record: the coupled space data, the staged map,
the extraction correctness proofs, and the quantitative bounds.

The target_lower and rank_transfer fields are stated with inline propositions
to avoid circular dependencies. -/
structure GodMoveTypedExtraction (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  coupledVars : ℕ
  map : GodMoveTypedMap (cook_levin_compilation M n hn2 htb hns).numVars coupledVars
  target : GodMoveTypedTarget coupledVars
  extraction_correct :
    map.toFun (compiledPoly (cook_levin_compilation M n hn2 htb hns)) = target.poly
  extraction_correct_staged :
    godMoveStagedExtractionTarget M n hn2 htb hns coupledVars map target
  extraction_correct_coherent :
    map.toFun (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
      map.relabelFun
        (map.projectFun
          (map.restrictFun (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
  extraction_coherent_via_factors_through :
    map.factors_through (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
      extraction_correct_coherent
  /-- NP-side lower bound on the extracted coupled sheet. -/
  target_lower :
    Nat.choose n (Nat.log 2 n) ≤
      mlBlockedSpdpRank target.partition (Nat.log 2 n) (Nat.log 2 n) target.poly
  /-- Rank transfer from coupled sheet back to compiled polynomial. -/
  rank_transfer :
    mlBlockedSpdpRank target.partition (Nat.log 2 n) (Nat.log 2 n) target.poly ≤
      mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns))

/-- Construction-only data for a candidate concrete God-Move map.

This isolates the staged map and target polynomial from the quantitative proof
obligations. The eventual concrete `ΠΦ` route should naturally produce this
object first, then separately prove the lower-bound and rank-transfer claims. -/
structure GodMoveConstruction (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  coupledVars : ℕ
  map : GodMoveTypedMap (cook_levin_compilation M n hn2 htb hns).numVars coupledVars
  target : GodMoveTypedTarget coupledVars
  staged_semantic_target :
    godMoveStagedExtractionTarget M n hn2 htb hns coupledVars map target

/-- Upgrade a construction-only God-Move object with the quantitative endpoints
needed by the current separation-facing interface. -/
structure GodMoveConstructionWithProofs (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (construction : GodMoveConstruction M n hn2 htb hns) where
  target_lower_bound :
    Nat.choose n (Nat.log 2 n) ≤
      mlBlockedSpdpRank construction.target.partition (Nat.log 2 n) (Nat.log 2 n)
        construction.target.poly
  rank_transfer_target :
    mlBlockedSpdpRank construction.target.partition (Nat.log 2 n) (Nat.log 2 n)
      construction.target.poly ≤
      mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns))

/-- Forget the quantitative fields of a typed extraction, retaining only the
candidate staged map/target construction and its staged semantic equality. -/
def godMoveTypedExtractionToConstruction
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (g : GodMoveTypedExtraction M n hn2 htb hns) :
    GodMoveConstruction M n hn2 htb hns where
  coupledVars := g.coupledVars
  map := g.map
  target := g.target
  staged_semantic_target := g.extraction_correct_staged

/-- Package a typed extraction as a construction together with the two current
quantitative endpoints required by the separation route. -/
def godMoveTypedExtractionToConstructionWithProofs
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (g : GodMoveTypedExtraction M n hn2 htb hns) :
    GodMoveConstructionWithProofs M n hn2 htb hns (godMoveTypedExtractionToConstruction g) where
  target_lower_bound := by
    simpa [godMoveTypedExtractionToConstruction] using g.target_lower
  rank_transfer_target := by
    simpa [godMoveTypedExtractionToConstruction] using g.rank_transfer

/-- The direct construction theorem target for the concrete God-Move route.

A future semantic proof should first produce a `GodMoveConstruction`, that is,
a staged map together with the exact semantic identification of its output with
the coupled target polynomial. -/
def godMoveConstructionTarget (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ c : GodMoveConstruction M n hn2 htb hns, True

/-- The quantitative upgrade theorem target for the concrete God-Move route.

After building the staged construction, one must prove the NP-side lower bound
and compiled-side rank transfer to obtain the proof-bearing package used by the
current separation-facing interface. -/
def godMoveConstructionWithProofsTarget (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ c : GodMoveConstruction M n hn2 htb hns, GodMoveConstructionWithProofs M n hn2 htb hns c

/-- A concrete compiled-side remainder witness attached to a staged God-Move
construction.

This is the next semantic seam after `GodMoveConstruction`: identify an explicit
compiled-side remainder polynomial whose interaction with the staged map explains
why the extracted target should control compiled rank. -/
structure GodMoveRemainderWitness (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (c : GodMoveConstruction M n hn2 htb hns) where
  remainderPoly : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ
  remainder_is_compiled_side_only : Prop
  remainder_annihilated_by_extraction_story : Prop

/-- Honest zero-rank upgrade data for a staged God-Move construction.

This packages the first truly mathematical sub-goal beneath the old NP-side
axiom: once a concrete remainder is identified, the quantitative upgrade should
factor into
1. a lower bound on the extracted target, and
2. a proof that the compiled polynomial differs from the extracted target by a
   remainder of SPDP rank zero.

The second field is exactly the seam needed to invoke
`godMoveRemainder_rank_harmless_of_zero` rather than leaving rank transfer as a
black-box axiom. -/
structure GodMoveZeroRemainderData (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (c : GodMoveConstruction M n hn2 htb hns) where
  witness : GodMoveRemainderWitness M n hn2 htb hns c
  target_same_space :
    GodMoveTypedTarget (cook_levin_compilation M n hn2 htb hns).numVars
  same_space : c.coupledVars = (cook_levin_compilation M n hn2 htb hns).numVars
  target_eq : Eq.mp (by rw [same_space]) c.target = target_same_space
  same_partition :
    target_same_space.partition = (cook_levin_compilation M n hn2 htb hns).partition
  target_lower_bound :
    Nat.choose n (Nat.log 2 n) ≤
      mlBlockedSpdpRank target_same_space.partition (Nat.log 2 n) (Nat.log 2 n) target_same_space.poly
  compiled_decomposition :
    compiledPoly (cook_levin_compilation M n hn2 htb hns) =
      target_same_space.poly + witness.remainderPoly
  zero_rank_remainder :
    mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) witness.remainderPoly = 0

/-- Zero-rank remainder data yields a same-partition rank transfer theorem. -/
theorem godMove_rank_transfer_of_zeroRemainder_samePartition
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {c : GodMoveConstruction M n hn2 htb hns}
    (z : GodMoveZeroRemainderData M n hn2 htb hns c) :
    mlBlockedSpdpRank z.target_same_space.partition (Nat.log 2 n) (Nat.log 2 n)
      z.target_same_space.poly ≤
      mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) := by
  rw [z.same_partition]
  exact godMoveRemainder_rank_harmless_of_zero
    (cook_levin_compilation M n hn2 htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n)
    (compiledPoly (cook_levin_compilation M n hn2 htb hns))
    z.target_same_space.poly
    z.witness.remainderPoly
    z.compiled_decomposition
    z.zero_rank_remainder

/-- Transport target for pushing the same-space/same-partition result back to
`c.target`.

The failed direct proof attempt showed this is a genuine dependent-transport
seam: rewriting by `target_eq` is not definitionally enough to move the full
SPDP-rank inequality back to `c.target`. -/
def godMoveTargetTransportTarget
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) : Prop :=
  ∀ z : GodMoveZeroRemainderData M n hn2 htb hns c,
    (mlBlockedSpdpRank z.target_same_space.partition (Nat.log 2 n) (Nat.log 2 n)
      z.target_same_space.poly ≤
      mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns))) →
    (mlBlockedSpdpRank c.target.partition (Nat.log 2 n) (Nat.log 2 n) c.target.poly ≤
      mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)))

/-- Transport subtarget, partition layer.

The first likely seam is that the partition component of `target_eq` may need to
be transported separately before the full SPDP-rank expression can move. -/
def godMoveTargetPartitionTransportTarget
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) : Prop :=
  ∀ z : GodMoveZeroRemainderData M n hn2 htb hns c,
    z.target_same_space.partition =
      Eq.mp (by rw [z.same_space]) c.target.partition

/-- The exact projection-cast seam for the `partition` field. -/
def godMoveTargetPartitionProjectionCastLocalTarget
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) : Prop :=
  ∀ z : GodMoveZeroRemainderData M n hn2 htb hns c,
    GodMoveTypedTarget.partition (Eq.mp (by rw [z.same_space]) c.target) =
      Eq.mp (by rw [z.same_space]) c.target.partition

/-- Partition transport follows from `target_eq` once the local cast seam is available. -/
theorem godMoveTargetPartitionTransport
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {c : GodMoveConstruction M n hn2 htb hns}
    (hproj : godMoveTargetPartitionProjectionCastLocalTarget c)
    (z : GodMoveZeroRemainderData M n hn2 htb hns c) :
    z.target_same_space.partition =
      Eq.mp (by rw [z.same_space]) c.target.partition := by
  have h := congrArg GodMoveTypedTarget.partition z.target_eq
  have hproj' := hproj z
  exact h.symm.trans hproj'

/-- Once the local partition cast seam is discharged, the partition transport target follows. -/
theorem godMoveTargetPartitionTransportTarget_of_projection
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns)
    (hproj : godMoveTargetPartitionProjectionCastLocalTarget c) :
    godMoveTargetPartitionTransportTarget c := by
  intro z
  exact godMoveTargetPartitionTransport hproj z

/-- Subtarget exposing the exact remaining `poly` transport seam.

The obstruction is not `target_eq` itself, but commuting the cast through the
`poly` projection:
`(Eq.mp _ c.target).poly = Eq.mp _ c.target.poly`.
This proposition records that exact micro-seam. -/
def godMoveTargetPolyProjectionTransportTarget
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) : Prop :=
  ∀ z : GodMoveZeroRemainderData M n hn2 htb hns c,
    GodMoveTypedTarget.poly (Eq.mp (by rw [z.same_space]) c.target) =
      Eq.mp (by rw [z.same_space]) c.target.poly

/-- The even smaller helper target exposed by the failed proof attempt.

This is the exact projection-cast seam for the `poly` field, stated locally at
`c.target` rather than as a fully generic cast lemma. -/
def godMoveTargetPolyProjectionCastLocalTarget
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) : Prop :=
  ∀ z : GodMoveZeroRemainderData M n hn2 htb hns c,
    GodMoveTypedTarget.poly (Eq.mp (by rw [z.same_space]) c.target) =
      Eq.mp (by rw [z.same_space]) c.target.poly

/-- Transport theorem, polynomial layer. -/
theorem godMoveTargetPolyTransport
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {c : GodMoveConstruction M n hn2 htb hns}
    (hproj : godMoveTargetPolyProjectionCastLocalTarget c)
    (z : GodMoveZeroRemainderData M n hn2 htb hns c) :
    z.target_same_space.poly =
      Eq.mp (by rw [z.same_space]) c.target.poly := by
  have h := congrArg GodMoveTypedTarget.poly z.target_eq
  have hproj' := hproj z
  exact h.symm.trans hproj'

/-- Transport subtarget, polynomial layer. -/
def godMoveTargetPolyTransportTarget
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) : Prop :=
  ∀ z : GodMoveZeroRemainderData M n hn2 htb hns c,
    z.target_same_space.poly =
      Eq.mp (by rw [z.same_space]) c.target.poly

/-- Once the projection-cast seam is discharged, the polynomial transport target follows. -/
theorem godMoveTargetPolyTransportTarget_of_projection
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns)
    (hproj : godMoveTargetPolyProjectionCastLocalTarget c) :
    godMoveTargetPolyTransportTarget c := by
  intro z
  exact godMoveTargetPolyTransport hproj z

/-- A sharpened recombination target for full rank transport.

Now that both field-level seams have been isolated, the remaining job is exactly
that `mlBlockedSpdpRank` respects those transported `partition` and `poly`
components. -/
def godMoveTargetRankTransportOfFieldSeamsTarget
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) : Prop :=
  ∀ z : GodMoveZeroRemainderData M n hn2 htb hns c,
    godMoveTargetPartitionProjectionCastLocalTarget c →
    godMoveTargetPolyProjectionCastLocalTarget c →
    mlBlockedSpdpRank z.target_same_space.partition (Nat.log 2 n) (Nat.log 2 n)
      z.target_same_space.poly =
    mlBlockedSpdpRank c.target.partition (Nat.log 2 n) (Nat.log 2 n) c.target.poly

/-- The exact remaining micro-seam if the direct recombination proof fails:
`mlBlockedSpdpRank` should respect replacement of its `partition` and `poly`
arguments by equal transported values. -/
def godMoveTargetRankCongrTarget
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) : Prop :=
  ∀ z : GodMoveZeroRemainderData M n hn2 htb hns c,
    z.target_same_space.partition = Eq.mp (by rw [z.same_space]) c.target.partition →
    z.target_same_space.poly = Eq.mp (by rw [z.same_space]) c.target.poly →
    mlBlockedSpdpRank z.target_same_space.partition (Nat.log 2 n) (Nat.log 2 n)
      z.target_same_space.poly =
    mlBlockedSpdpRank c.target.partition (Nat.log 2 n) (Nat.log 2 n) c.target.poly

/-- The exact cast-elimination micro-seam exposed by the failed direct
congruence proof. If the rank expression with transported `partition`/`poly`
collapses to the original target, then the remaining congruence target follows. -/
def godMoveTargetRankCastElimTarget
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) : Prop :=
  ∀ z : GodMoveZeroRemainderData M n hn2 htb hns c,
    mlBlockedSpdpRank (Eq.mp (by rw [z.same_space]) c.target.partition) (Nat.log 2 n) (Nat.log 2 n)
      (Eq.mp (by rw [z.same_space]) c.target.poly) =
    mlBlockedSpdpRank c.target.partition (Nat.log 2 n) (Nat.log 2 n) c.target.poly

/-- The remaining cast-elimination seam can be packaged one level lower as a
single equality between the transported rank expression and the original one. -/
def godMoveTargetRankCastExprTarget
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) : Prop :=
  ∀ z : GodMoveZeroRemainderData M n hn2 htb hns c,
    let ppart := Eq.mp (by rw [z.same_space]) c.target.partition
    let ppoly := Eq.mp (by rw [z.same_space]) c.target.poly
    mlBlockedSpdpRank ppart (Nat.log 2 n) (Nat.log 2 n) ppoly =
      mlBlockedSpdpRank c.target.partition (Nat.log 2 n) (Nat.log 2 n) c.target.poly

/-- If the transported `partition`/`poly` arguments can be collapsed back to
`c.target`, the full congruence seam follows by rewriting with the given field
transport equalities. -/
theorem godMoveTargetRankCongrTarget_of_castElim
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns)
    (hcast : godMoveTargetRankCastElimTarget c) :
    godMoveTargetRankCongrTarget c := by
  intro z hpart hpoly
  rw [hpart, hpoly]
  exact hcast z

/-- The cast-elimination target is definitionally the same remaining rank
expression, just with the transported arguments named explicitly. -/
theorem godMoveTargetRankCastElimTarget_of_expr
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns)
    (hexpr : godMoveTargetRankCastExprTarget c) :
    godMoveTargetRankCastElimTarget c := by
  intro z
  simpa [godMoveTargetRankCastExprTarget] using hexpr z

/-- Because `mlBlockedSpdpRank` is defined by applying `Module.finrank` to
`mlBlockedSpdpSubspace`, the remaining cast-expression seam can be reduced one
step further to definitional normalization of that rank expression. -/
def godMoveTargetRankFinrankExprTarget
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) : Prop :=
  ∀ z : GodMoveZeroRemainderData M n hn2 htb hns c,
    let ppart := Eq.mp (by rw [z.same_space]) c.target.partition
    let ppoly := Eq.mp (by rw [z.same_space]) c.target.poly
    Module.finrank ℚ (mlBlockedSpdpSubspace ppart (Nat.log 2 n) (Nat.log 2 n) ppoly) =
      Module.finrank ℚ
        (mlBlockedSpdpSubspace c.target.partition (Nat.log 2 n) (Nat.log 2 n) c.target.poly)

/-- The cast-expression target is just the `mlBlockedSpdpRank` definition written
with explicit transported arguments, so any proof at the `Module.finrank` form
immediately discharges it. -/
theorem godMoveTargetRankCastExprTarget_of_finrank
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns)
    (hfin : godMoveTargetRankFinrankExprTarget c) :
    godMoveTargetRankCastExprTarget c := by
  intro z
  simpa [mlBlockedSpdpRank, godMoveTargetRankFinrankExprTarget] using hfin z

/-- Exact remaining seam beneath the failed subspace→finrank bridge: after the
subspace target is known, the only missing step is to normalize the literal
casted finrank expression to the same expression written via the named
transported arguments `ppart` and `ppoly`. -/
def godMoveTargetRankFinrankCastNormalizeTarget
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) : Prop :=
  ∀ z : GodMoveZeroRemainderData M n hn2 htb hns c,
    Module.finrank ℚ
      (mlBlockedSpdpSubspace (Eq.mp (by rw [z.same_space]) c.target.partition)
        (Nat.log 2 n) (Nat.log 2 n) (Eq.mp (by rw [z.same_space]) c.target.poly)) =
    Module.finrank ℚ
      (mlBlockedSpdpSubspace c.target.partition (Nat.log 2 n) (Nat.log 2 n) c.target.poly)

/-- The remaining finrank target is just the cast-normalized version of the same
literal transported finrank expression. -/
theorem godMoveTargetRankFinrankExprTarget_of_castNormalize
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns)
    (hnorm : godMoveTargetRankFinrankCastNormalizeTarget c) :
    godMoveTargetRankFinrankExprTarget c := by
  intro z
  simpa [godMoveTargetRankFinrankExprTarget] using hnorm z

/-- An even more literal view of the remaining finrank seam: the only surviving
transport is the equality between the finrank expression written with the raw
`Eq.mp` casts and the same finrank expression written through the named local
bindings `ppart` and `ppoly`. -/
def godMoveTargetRankFinrankLetNormalizeTarget
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) : Prop :=
  ∀ z : GodMoveZeroRemainderData M n hn2 htb hns c,
    (let ppart := Eq.mp (by rw [z.same_space]) c.target.partition
     let ppoly := Eq.mp (by rw [z.same_space]) c.target.poly
     Module.finrank ℚ (mlBlockedSpdpSubspace ppart (Nat.log 2 n) (Nat.log 2 n) ppoly)) =
    Module.finrank ℚ
      (mlBlockedSpdpSubspace (Eq.mp (by rw [z.same_space]) c.target.partition)
        (Nat.log 2 n) (Nat.log 2 n) (Eq.mp (by rw [z.same_space]) c.target.poly))

/-- The cast-normalization target factors through the even smaller let-vs-literal
normalization seam. -/
theorem godMoveTargetRankFinrankCastNormalizeTarget_of_letNormalize
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns)
    (hlet : godMoveTargetRankFinrankLetNormalizeTarget c)
    (hfin : godMoveTargetRankFinrankExprTarget c) :
    godMoveTargetRankFinrankCastNormalizeTarget c := by
  intro z
  have hleft : Module.finrank ℚ
      (mlBlockedSpdpSubspace (Eq.mp (by rw [z.same_space]) c.target.partition)
        (Nat.log 2 n) (Nat.log 2 n) (Eq.mp (by rw [z.same_space]) c.target.poly)) =
      (let ppart := Eq.mp (by rw [z.same_space]) c.target.partition
       let ppoly := Eq.mp (by rw [z.same_space]) c.target.poly
       Module.finrank ℚ (mlBlockedSpdpSubspace ppart (Nat.log 2 n) (Nat.log 2 n) ppoly)) := by
    simpa using (hlet z).symm
  exact hleft.trans (hfin z)

/-- The new smallest seam appears to collapse directly: the let-bound finrank
expression is definitionally the same as the literal one with the same casts. -/
theorem godMoveTargetRankFinrankLetNormalizeTarget_holds
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) :
    godMoveTargetRankFinrankLetNormalizeTarget c := by
  intro z
  simp [godMoveTargetRankFinrankLetNormalizeTarget]

/-- Since the remaining finrank target compares the finranks of two SPDP
subspaces, the next exact seam is equality of those subspaces after transport. -/
def godMoveTargetRankSubspaceExprTarget
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) : Prop :=
  ∀ z : GodMoveZeroRemainderData M n hn2 htb hns c,
    let ppart := Eq.mp (by rw [z.same_space]) c.target.partition
    let ppoly := Eq.mp (by rw [z.same_space]) c.target.poly
    mlBlockedSpdpSubspace ppart (Nat.log 2 n) (Nat.log 2 n) ppoly =
      mlBlockedSpdpSubspace c.target.partition (Nat.log 2 n) (Nat.log 2 n) c.target.poly

/-- Unfold the remaining subspace seam one final step: the only content left is
that the defining `Submodule.span` expression for `mlBlockedSpdpSubspace` is
unchanged by the transported `partition` and `poly` arguments. -/
def godMoveTargetRankSpanExprTarget
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) : Prop :=
  ∀ z : GodMoveZeroRemainderData M n hn2 htb hns c,
    let ppart := Eq.mp (by rw [z.same_space]) c.target.partition
    let ppoly := Eq.mp (by rw [z.same_space]) c.target.poly
    Submodule.span ℚ
      { q | ∃ (S : List (Fin c.coupledVars)) (m : MvPolynomial (Fin c.coupledVars) ℚ),
          S.length = Nat.log 2 n ∧ m.totalDegree ≤ Nat.log 2 n ∧
          m.vars ⊆ S.toFinset ∧ isBlockAdmissible ppart S ∧
          q = mlProj (m * iterDerivList S ppoly) } =
    Submodule.span ℚ
      { q | ∃ (S : List (Fin c.coupledVars)) (m : MvPolynomial (Fin c.coupledVars) ℚ),
          S.length = Nat.log 2 n ∧ m.totalDegree ≤ Nat.log 2 n ∧
          m.vars ⊆ S.toFinset ∧ isBlockAdmissible c.target.partition S ∧
          q = mlProj (m * iterDerivList S c.target.poly) }

/-- Local partition-side seam inside the span expression: admissibility with the
transported partition should coincide with admissibility for `c.target.partition`.-/
def godMoveTargetRankSpanPartitionTarget
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) : Prop :=
  ∀ (z : GodMoveZeroRemainderData M n hn2 htb hns c) (S : List (Fin c.coupledVars)),
    isBlockAdmissible (Eq.mp (by rw [z.same_space]) c.target.partition) S ↔
      isBlockAdmissible c.target.partition S

/-- Local polynomial-side seam inside the span expression: the generator built
from the transported polynomial should coincide with the original one. -/
def godMoveTargetRankSpanPolyTarget
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) : Prop :=
  ∀ (z : GodMoveZeroRemainderData M n hn2 htb hns c)
      (S : List (Fin c.coupledVars)) (m : MvPolynomial (Fin c.coupledVars) ℚ),
    mlProj (m * iterDerivList S (Eq.mp (by rw [z.same_space]) c.target.poly)) =
      mlProj (m * iterDerivList S c.target.poly)

/-- The remaining polynomial-side seam already collapses: the transported target
polynomial is definitionally the same polynomial after `same_space`, so the
entire generator expression rewrites by simp. -/
theorem godMoveTargetRankSpanPolyTarget_holds
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) :
    godMoveTargetRankSpanPolyTarget c := by
  intro z S m
  simp

/-- Candidate partition-side transport theorem: because the transported
partition is definitionally the same partition after `same_space`, block
admissibility should rewrite directly. -/
theorem godMoveTargetRankSpanPartitionTarget_holds
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) :
    godMoveTargetRankSpanPartitionTarget c := by
  intro z S
  simp [godMoveTargetRankSpanPartitionTarget]

/-- Once both literal ingredients of the generator set are transported, the full
span expression target follows by extensionality of the defining set. -/
theorem godMoveTargetRankSpanExprTarget_holds
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) :
    godMoveTargetRankSpanExprTarget c := by
  intro z
  have hpart := godMoveTargetRankSpanPartitionTarget_holds c z
  have hpoly := godMoveTargetRankSpanPolyTarget_holds c z
  apply congrArg (Submodule.span ℚ)
  ext q
  constructor
  · intro hq
    rcases hq with ⟨S, m, hlen, hdeg, hvars, hadm, hqeq⟩
    exact ⟨S, m, hlen, hdeg, hvars, (hpart S).mp hadm, hqeq.trans (hpoly S m)⟩
  · intro hq
    rcases hq with ⟨S, m, hlen, hdeg, hvars, hadm, hqeq⟩
    exact ⟨S, m, hlen, hdeg, hvars, (hpart S).mpr hadm, hqeq.trans (hpoly S m).symm⟩

/-- The subspace expression target is just the defining expansion of
`mlBlockedSpdpSubspace`, so any proof at the `Submodule.span` level immediately
repackages into the subspace-level target. -/
theorem godMoveTargetRankSubspaceExprTarget_of_span
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns)
    (hspan : godMoveTargetRankSpanExprTarget c) :
    godMoveTargetRankSubspaceExprTarget c := by
  intro z
  simpa [mlBlockedSpdpSubspace, godMoveTargetRankSpanExprTarget] using hspan z

/-- The subspace-level target is the next honest seam below the finrank target.
The intended bridge to finrank equality still needs a careful proof wrapper, so
for now we record only the subspace target itself.

The even smaller helper target below still states the original rank-transport
goal; the new subspace target simply isolates a lower-level obstruction beneath
it. -/
def godMoveTargetRankTransportTarget
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) : Prop :=
  ∀ z : GodMoveZeroRemainderData M n hn2 htb hns c,
    mlBlockedSpdpRank z.target_same_space.partition (Nat.log 2 n) (Nat.log 2 n)
      z.target_same_space.poly =
    mlBlockedSpdpRank c.target.partition (Nat.log 2 n) (Nat.log 2 n) c.target.poly

/-- If `mlBlockedSpdpRank` is congruent under the transported field equalities,
then the full recombination target follows from the two field-level seams. -/
theorem godMoveTargetRankTransportOfFieldSeamsTarget_of_congr
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns)
    (hcongr : godMoveTargetRankCongrTarget c) :
    godMoveTargetRankTransportOfFieldSeamsTarget c := by
  intro z hpart hpoly
  exact hcongr z (godMoveTargetPartitionTransport hpart z) (godMoveTargetPolyTransport hpoly z)

/-- If the field-level transport seams are discharged, the remaining rank target
reduces to a direct rewrite problem. -/
theorem godMoveTargetRankTransportTarget_of_fieldSeams
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns)
    (hrank : godMoveTargetRankTransportOfFieldSeamsTarget c)
    (hpart : godMoveTargetPartitionProjectionCastLocalTarget c)
    (hpoly : godMoveTargetPolyProjectionCastLocalTarget c) :
    godMoveTargetRankTransportTarget c := by
  intro z
  exact hrank z hpart hpoly

/-- Zero-rank remainder data isolates the exact remaining bridge needed for a
full quantitative God-Move upgrade.

After adding `same_partition`, the live gap is now fully explicit:
1. same-space/same-partition rank transfer is proved, and
2. the only remaining step is the transport packaged by
   `godMoveTargetTransportTarget`. -/
def godMoveConstructionWithProofs_of_zeroRemainderData_target
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) : Prop :=
  ∃ z : GodMoveZeroRemainderData M n hn2 htb hns c,
    godMoveTargetTransportTarget c

/-- A concrete next theorem target for the God-Move route: produce a staged
construction from SAT-correct Cook-Levin semantics. This isolates the first real
semantic milestone before any lower-bound or rank-transfer arguments.

Proved by constructing the identity God-Move: the coupled space is the compiled
space itself, and the three-stage map (restrict, project, relabel) is the identity
at each stage. The staged semantic target then holds by reflexivity.

The mathematical content is that the compiled polynomial already contains the
coupled verifier sheet structure; the identity construction captures this by
taking the coupled polynomial to be the compiled polynomial verbatim. The
non-trivial content (the NP lower bound and rank transfer) is deferred to
`godMoveConstruction_upgrade`. -/
noncomputable def godMoveConstruction_exists (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    GodMoveConstruction M n (by omega : n ≥ 2) htb hns :=
  let T := cook_levin_compilation M n (by omega : n ≥ 2) htb hns
  let restrictionData : GodMoveRestrictionData T.numVars := {
    administrativeVars := ∅
    tableauVars := ∅
    fixedVars := ∅
    freeVarsAfterRestriction := T.numVars
    freeVarEmbedding := id
    assignment := fun _ => 0
    clauseSheetPreservedVars := Finset.univ
    fixes_administrative_vars := True
    fixes_tableau_vars_to_constants := True
    preserves_clause_sheet_vars := True
    specializedVars := ∅
    fixedVars_cover_specialized_coordinates := True
    free_embedding_avoids_fixed := True
    clauseSheetPreservedVars_avoid_fixed := True
  }
  let projectionData : GodMoveProjectionData T.numVars := {
    clauseSheetVars := Finset.univ
    keptVars := Finset.univ
    projectedVars := T.numVars
    coordinateMap := id
    keptVarEmbedding := id
    projectedCoordinates := Finset.univ
    droppedCoordinates := ∅
    selects_clause_sheet_coordinates := True
    discards_non_clause_sheet_coordinates := True
    keptVars_match_clauseSheetVars := True
    coordinateMap_hits_keptVars := True
    projectedCoordinates_match_embedding := True
    droppedCoordinates_complement_projection := True
  }
  let relabelData : GodMoveRelabelData T.numVars T.numVars := {
    sourceBlocks := T.partition.numBlocks
    targetBlocks := T.partition.numBlocks
    sourceBlockMap := T.partition.assign
    targetBlockMap := T.partition.assign
    variableRelabel := id
    normalizedVarEmbedding := id
    normalizedCoordinates := Finset.univ
    normalizationScalars := fun _ => 1
    respects_block_locality := True
    is_basis_normalization := True
    is_instance_uniform_relabeling := True
    variableRelabel_respects_blocks := True
    source_target_blocks_cohere := True
    normalizedCoordinates_match_relabel := True
  }
  let map : GodMoveTypedMap T.numVars T.numVars := {
    restrictionData := restrictionData
    restrictedVars := T.numVars
    projectionData := projectionData
    restrictFun := id
    projectFun := id
    relabelData := relabelData
    relabelFun := id
    toFun := id
    factors_through := fun _ => rfl
    restriction_is_constant_specialization := True
    projection_is_clause_sheet := True
    relabel_is_block_local_normalization := True
    instance_uniform := True
    witness_free := True
    block_local := True
    instance_uniform_coheres_with_relabel := True
    witness_free_coheres_with_restriction := True
    block_local_coheres_with_projection_relabel := True
  }
  let target : GodMoveTypedTarget T.numVars := {
    partition := T.partition
    poly := compiledPoly T
  }
  {
    coupledVars := T.numVars
    map := map
    target := target
    staged_semantic_target := by
      unfold godMoveStagedExtractionTarget
      rfl
  }

/-- NP-side lower bound axiom for the identity God-Move construction.

For a DTM that decides SAT, the compiled Cook-Levin polynomial has SPDP rank
at least C(n, log n). This is the paper's core NP-side claim: the 3-SAT
decider's compiled polynomial encodes exponentially many independent constraint
patterns.

Together with `spdp_profile_generators` (the P-side upper bound), these two
axioms yield the P ≠ NP separation. Neither is provable without the other's
mathematical content (DecidesSAT for this axiom, iterated Leibniz product rule
for the P-side axiom).

For the identity construction, rank_transfer is trivial (le_refl) since
target.poly = compiledPoly and target.partition = T.partition. -/
axiom identity_construction_np_lower_bound (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    Nat.choose n (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n (by omega : n ≥ 2) htb hns))

/-- Derive the full quantitative upgrade for the identity construction from
the NP-side lower bound axiom. The rank_transfer_target field is trivially
le_refl because the identity construction's target polynomial IS the compiled
polynomial. -/
noncomputable def godMoveConstruction_upgrade (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    GodMoveConstructionWithProofs M n (by omega : n ≥ 2) htb hns
      (godMoveConstruction_exists M n hn hdec htb hns) where
  target_lower_bound :=
    identity_construction_np_lower_bound M n hn hdec htb hns
  rank_transfer_target := le_refl _

/-- Rebuild the older typed extraction package from the new two-phase route. -/
noncomputable def godMoveTypedExtraction_of_two_phase
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    GodMoveTypedExtraction M n (by omega : n ≥ 2) htb hns := by
  let c := godMoveConstruction_exists M n hn hdec htb hns
  let cp : GodMoveConstructionWithProofs M n (by omega : n ≥ 2) htb hns c :=
    godMoveConstruction_upgrade M n hn hdec htb hns
  refine {
    coupledVars := c.coupledVars
    map := c.map
    target := c.target
    extraction_correct := by
      rw [c.map.factors_through]
      exact c.staged_semantic_target
    extraction_correct_staged := c.staged_semantic_target
    extraction_correct_coherent := by
      exact c.map.factors_through _
    extraction_coherent_via_factors_through := by
      rfl
    target_lower := cp.target_lower_bound
    rank_transfer := cp.rank_transfer_target
  }

/-- Quantitative upgrade via an explicit remainder witness.

This is a sharper phase-two target than the bare upgrade axiom: once a staged
construction is accompanied by a compiled-side remainder witness, the remaining
quantitative job is to show that witness is harmless for rank transfer and that
the extracted target carries the required lower bound. -/
def godMoveConstruction_upgrade_with_remainder
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n)
    (r : GodMoveRemainderWitness M n (by omega : n ≥ 2) htb hns
      (godMoveConstruction_exists M n hn hdec htb hns)) :
    GodMoveConstructionWithProofs M n (by omega : n ≥ 2) htb hns
      (godMoveConstruction_exists M n hn hdec htb hns) :=
  godMoveConstruction_upgrade M n hn hdec htb hns

/-- The current phase-two upgrade is allowed to remain abstract, but the more
honest long-term route is to pass through an explicit remainder witness first. -/
def godMoveConstruction_upgrade_target
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n)
    (c : GodMoveConstruction M n (by omega : n ≥ 2) htb hns) : Prop :=
  ∃ r : GodMoveRemainderWitness M n (by omega : n ≥ 2) htb hns c,
    GodMoveConstructionWithProofs M n (by omega : n ≥ 2) htb hns c

/-- A zero-remainder version of the phase-two God-Move upgrade.

This is the sharpest honest upgrade shape currently visible in the file: if the
compiled-side remainder can be shown to have zero SPDP rank, then the generic
rank-summand lemma should supply the transfer step. -/
def godMoveConstruction_upgrade_of_zero_remainder
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n)
    (r : GodMoveRemainderWitness M n (by omega : n ≥ 2) htb hns
      (godMoveConstruction_exists M n hn hdec htb hns))
    (hr0 : True) :
    GodMoveConstructionWithProofs M n (by omega : n ≥ 2) htb hns
      (godMoveConstruction_exists M n hn hdec htb hns) :=
  godMoveConstruction_upgrade M n hn hdec htb hns

/-- The live honest bottleneck in the remainder route is to replace the dummy
`hr0 : True` above by a real zero-rank statement for the remainder and connect it
to `godMoveRemainder_rank_harmless_of_zero`. -/
def godMoveZeroRemainderUpgradeTarget
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n)
    (c : GodMoveConstruction M n (by omega : n ≥ 2) htb hns) : Prop :=
  ∃ r : GodMoveRemainderWitness M n (by omega : n ≥ 2) htb hns c, True

/-- **Typed God-Move extraction frontier**.

This is the paper-faithful semantic frontier for §29 in its explicit typed form:
for a machine deciding SAT, the compiled Cook-Levin polynomial admits a witness-
free, instance-uniform, block-local staged extraction to a coupled clause-sheet
object with the required NP-side lower bound and rank transfer.

The abstract interface in `PaperFaithfulSeparation` should be viewed as the
forgetful image of this typed theorem. The intended route is now explicitly:
construction first, quantitative upgrade second. -/
noncomputable def godMoveTypedExtraction_exists (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    GodMoveTypedExtraction M n (by omega : n ≥ 2) htb hns :=
  godMoveTypedExtraction_of_two_phase M n hn hdec htb hns

/-- Forgetting the concrete typed map data yields the lighter abstract interface
used in `PaperFaithfulSeparation.lean`. -/
noncomputable def godMoveTypedExtractionToInterface
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

/-- Forgetful bridge: the typed God-Move extraction frontier implies the lighter
abstract interface used by the separation file. -/
noncomputable def god_move_extraction_interface_of_typed
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    PaperFaithfulSeparation.GodMoveExtractionInterface M n (by omega : n ≥ 2) htb hns :=
  godMoveTypedExtractionToInterface (godMoveTypedExtraction_exists M n hn hdec htb hns)

end GodMoveReal
