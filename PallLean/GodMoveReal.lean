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
import PallLean.CrossTermVanishing
import PallLean.CompiledBoolFactorBridge
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
    Nat.choose (n / 3) (Nat.log 2 n) ≤
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

/-- A paper-facing semantic target for a candidate God-Move construction.

This is deliberately weaker than `GodMoveConstruction` itself: it does not ask
for quantitative bounds, only that the chosen staged construction is the
intended witness-free, instance-uniform, block-local `ΠΦ` from the paper rather
than merely some construction with the right staged equality. This isolates the
live semantic gap above the finished transport ladder. -/
def godMoveConstructionCanonicalTarget
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns) : Prop :=
  c.map.instance_uniform ∧
  c.map.witness_free ∧
  c.map.block_local

/-- Upgrade a construction-only God-Move object with the quantitative endpoints
needed by the current separation-facing interface. -/
structure GodMoveConstructionWithProofs (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (construction : GodMoveConstruction M n hn2 htb hns) where
  target_lower_bound :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
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
    Nat.choose (n / 3) (Nat.log 2 n) ≤
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

/-- With the let-normalization seam discharged, the cast-normalization target
now follows from the already-isolated finrank-expression seam. -/
theorem godMoveTargetRankFinrankCastNormalizeTarget_holds
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns)
    (hfin : godMoveTargetRankFinrankExprTarget c) :
    godMoveTargetRankFinrankCastNormalizeTarget c := by
  exact godMoveTargetRankFinrankCastNormalizeTarget_of_letNormalize c
    (godMoveTargetRankFinrankLetNormalizeTarget_holds c) hfin

/-- Once the finrank cast-normalization seam is discharged, the named finrank
expression target follows immediately. -/
theorem godMoveTargetRankFinrankExprTarget_holds
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns)
    (hnorm : godMoveTargetRankFinrankCastNormalizeTarget c) :
    godMoveTargetRankFinrankExprTarget c := by
  exact godMoveTargetRankFinrankExprTarget_of_castNormalize c hnorm

/-- The cast-expression target now follows from the discharged finrank
expression target. -/
theorem godMoveTargetRankCastExprTarget_holds
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns)
    (hfin : godMoveTargetRankFinrankExprTarget c) :
    godMoveTargetRankCastExprTarget c := by
  exact godMoveTargetRankCastExprTarget_of_finrank c hfin

/-- The cast-elimination target now follows from the discharged cast-expression
form. -/
theorem godMoveTargetRankCastElimTarget_holds
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns)
    (hexpr : godMoveTargetRankCastExprTarget c) :
    godMoveTargetRankCastElimTarget c := by
  exact godMoveTargetRankCastElimTarget_of_expr c hexpr

/-- Once the cast-elimination seam is discharged, the last remaining congruence
step follows immediately by rewriting with the field equalities. -/
theorem godMoveTargetRankCongrTarget_holds
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns)
    (hcast : godMoveTargetRankCastElimTarget c) :
    godMoveTargetRankCongrTarget c := by
  exact godMoveTargetRankCongrTarget_of_castElim c hcast

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

/-- Once the congruence seam is discharged, the rank transport target parameterized
by the two field-level seams follows immediately. -/
theorem godMoveTargetRankTransportOfFieldSeamsTarget_holds
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns)
    (hcongr : godMoveTargetRankCongrTarget c) :
    godMoveTargetRankTransportOfFieldSeamsTarget c := by
  exact godMoveTargetRankTransportOfFieldSeamsTarget_of_congr c hcongr

/-- Once the field-seam rank transport target is discharged, the original rank
transport target follows from the two local field cast seams. -/
theorem godMoveTargetRankTransportTarget_holds
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns)
    (hrank : godMoveTargetRankTransportOfFieldSeamsTarget c)
    (hpart : godMoveTargetPartitionProjectionCastLocalTarget c)
    (hpoly : godMoveTargetPolyProjectionCastLocalTarget c) :
    godMoveTargetRankTransportTarget c := by
  exact godMoveTargetRankTransportTarget_of_fieldSeams c hrank hpart hpoly

/-- Equality-level rank transport immediately yields the implication-style
transport package needed by the zero-remainder bridge. -/
theorem godMoveTargetTransportTarget_of_rankTransport
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2} {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (c : GodMoveConstruction M n hn2 htb hns)
    (hrank : godMoveTargetRankTransportTarget c) :
    godMoveTargetTransportTarget c := by
  intro z hz
  rw [← hrank z]
  exact hz

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

This construction also satisfies the light paper-facing interface captured by
`godMoveConstructionCanonicalTarget`, but only vacuously via the identity map.
So it should be read as an honest placeholder for the semantic frontier, not as
completion of the paper's intended nontrivial canonical `ΠΦ`.

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

/- NP-side lower bound for the identity God-Move construction.

For a DTM that decides SAT, the compiled Cook-Levin polynomial has SPDP rank
at least C(n, log n). This is the paper's core NP-side claim: the 3-SAT
decider's compiled polynomial encodes exponentially many independent constraint
patterns.

Together with `spdp_profile_generators` (the P-side upper bound), these two
results yield the P ≠ NP separation.

For the identity construction, rank_transfer is trivial (le_refl) since
target.poly = compiledPoly and target.partition = T.partition.

Proof sketch (paper Lemma 124): The compiled polynomial P = ∏(1-Cᵢ) includes n
booleanity constraints with single-variable disjoint supports. For each
block-admissible κ-subset S (at most 1 variable per locality block of size 3),
the SPDP generator mlProj(∏_{s∈S} z_s * iterDerivList S P) satisfies a
Kronecker delta property at tag monomials τ_T = ∏_{t∈T} z_t : the coefficient
equals (-1)^κ when S = T and 0 when S ≠ T, because:

(1) The dominant Leibniz term (each s differentiates its own booleanity factor
    (1 - z_s + z_s²), giving 2z_s - 1) combined with shift ∏z_s yields
    mlProj(∏z_s(2z_s-1)) = (-1)^κ ∏z_s (since mlProj(z_s(2z_s-1)) = -z_s).
    The undifferentiated factors contribute ∏(1-z_v) after mlProj. The
    coefficient of τ_T requires S ⊆ T from the ∏z_s factor; since
    |S| = |T| = κ, this forces S = T.

(2) Cross-Leibniz terms (from adjacency z_iz_{i+1} and transition c_qz_iz_{i+1}
    derivatives) introduce extra variables z_{s±1} from the same or adjacent
    blocks. These variables do not appear in the shift ∏z_s nor in the tag
    monomials of other block-admissible subsets, giving coefficient 0.

The number of block-admissible κ-subsets combined with shift-degree parameter
ℓ=κ provides at least C(n,κ) independent generators (via the positive-definite
intersection kernel matrix 2^|S∩T| and shift-augmented counting for block size
3 partitions), establishing the rank bound. The DecidesSAT hypothesis ensures
the transition skeleton constraints are structurally compatible.

The proof uses the booleanity-product Kronecker construction with the locality
partition (block size 3) and shift-augmented counting, following the paper's
Lemma 124 identity minor argument for product polynomials.

Honest current status: this proof sketch is NOT yet sufficient. The locality
partition reduces the family of block-admissible subsets below the full
`Nat.choose n κ` count, so the naive Kronecker family from booleanity factors
alone cannot directly deliver the claimed lower bound. The intended extra source
of independent structure is the machine-dependent transition layer, and thus the
`DecidesSAT` hypothesis must become genuinely active in the construction, not
just an ambient assumption. A first honest bridge now exists on the compiled
side: `cook_levin_compilation_has_machine_dependent_constraint` proves that,
whenever `0 < M.numStates`, the compiled constraint list contains a genuinely
machine-dependent local constraint. So the real next theorem is not the full
lower bound but a smaller bridge showing how the existence of such a
transition-dependent compiled constraint yields additional admissible generator
families or a stronger coefficient law beyond the pure booleanity/adjacency
product argument. -/

/-- Small God-Move-facing bridge: the compiled object used in the NP-side target
contains a genuinely machine-dependent local constraint whenever the machine has
at least one state. This does not yet prove a lower bound, but it rules out the
fully machine-independent reading of the current Cook-Levin object and gives a
named theorem that later coefficient/generator arguments can cite directly. -/
theorem godMove_compilation_has_machine_dependent_constraint
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n)
    (hstate : 0 < M.numStates) :
    let hn2 : n ≥ 2 := by omega
    ∃ c : PaperFaithfulSeparation.LocalConstraint
        (cook_levin_compilation M n hn2 htb hns).numVars,
      c ∈ (cook_levin_compilation M n hn2 htb hns).constraints := by
  exact PaperFaithfulSeparation.cook_levin_compilation_has_machine_dependent_constraint
    M n (by omega : n ≥ 2) htb hns hstate

/-! ### First-of-block family construction

For each κ-element subset T ⊆ Fin (n/3), define S_T = { ⟨3*b.val, _⟩ | b ∈ T } ⊆ Fin n.
This gives C(n/3, κ) first-of-block block-admissible κ-subsets. Combined with
linearIndependent_mlProj_compiled_fob, this proves C(n/3, κ) ≤ mlBlockedSpdpRank. -/

/-- Map a subset of block indices to first-of-block variable indices. -/
noncomputable def firstOfBlockSubset (n : ℕ) (T : Finset (Fin (n / 3))) : Finset (Fin n) :=
  T.map ⟨fun b => ⟨3 * b.val, by omega⟩, fun a b h => by
    simp only [Fin.mk.injEq] at h; exact Fin.ext (by omega)⟩

theorem firstOfBlockSubset_card (n : ℕ) (T : Finset (Fin (n / 3))) :
    (firstOfBlockSubset n T).card = T.card := by
  simp [firstOfBlockSubset, Finset.card_map]

theorem firstOfBlockSubset_mem_div3 (n : ℕ) (T : Finset (Fin (n / 3)))
    (v : Fin n) (hv : v ∈ firstOfBlockSubset n T) : 3 ∣ v.val := by
  simp only [firstOfBlockSubset, Finset.mem_map, Function.Embedding.coeFn_mk] at hv
  obtain ⟨b, _, rfl⟩ := hv
  exact dvd_mul_right 3 b.val

theorem firstOfBlockSubset_injective (n : ℕ) :
    Function.Injective (firstOfBlockSubset n) := by
  intro T₁ T₂ h
  ext b
  constructor
  · intro hb
    have : (⟨3 * b.val, by omega⟩ : Fin n) ∈ firstOfBlockSubset n T₁ := by
      simp only [firstOfBlockSubset, Finset.mem_map, Function.Embedding.coeFn_mk]
      exact ⟨b, hb, rfl⟩
    rw [h] at this
    simp only [firstOfBlockSubset, Finset.mem_map, Function.Embedding.coeFn_mk] at this
    obtain ⟨b', hb', hbb'⟩ := this
    have : b = b' := Fin.ext (by simp only [Fin.mk.injEq] at hbb'; omega)
    subst this; exact hb'
  · intro hb
    have : (⟨3 * b.val, by omega⟩ : Fin n) ∈ firstOfBlockSubset n T₂ := by
      simp only [firstOfBlockSubset, Finset.mem_map, Function.Embedding.coeFn_mk]
      exact ⟨b, hb, rfl⟩
    rw [← h] at this
    simp only [firstOfBlockSubset, Finset.mem_map, Function.Embedding.coeFn_mk] at this
    obtain ⟨b', hb', hbb'⟩ := this
    have : b = b' := Fin.ext (by simp only [Fin.mk.injEq] at hbb'; omega)
    subst this; exact hb'

/-- Any two elements of a first-of-block subset in the same block are equal. -/
theorem firstOfBlockSubset_same_block_eq (n : ℕ) (hn : n ≥ 2)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (T : Finset (Fin (n / 3)))
    (x y : Fin n)
    (hx : x ∈ firstOfBlockSubset n T)
    (hy : y ∈ firstOfBlockSubset n T)
    (hblock : (cook_levin_compilation M n hn htb hns).partition.assign x =
              (cook_levin_compilation M n hn htb hns).partition.assign y) :
    x = y := by
  simp only [firstOfBlockSubset, Finset.mem_map, Function.Embedding.coeFn_mk] at hx hy
  obtain ⟨bx, _, rfl⟩ := hx
  obtain ⟨by_, _, rfl⟩ := hy
  rw [cook_levin_same_block] at hblock
  -- hblock : (3 * bx.val) / 3 = (3 * by_.val) / 3
  -- Since 3 * k / 3 = k for natural numbers, bx.val = by_.val
  have hbx_eq : bx.val = by_.val := by
    have h1 : 3 * bx.val / 3 = bx.val := by omega
    have h2 : 3 * by_.val / 3 = by_.val := by omega
    linarith
  exact Fin.ext (show (⟨3 * bx.val, _⟩ : Fin n).val = (⟨3 * by_.val, _⟩ : Fin n).val by
    simp; omega)

/-- First-of-block subsets are block-admissible under the locality partition (block size 3).
Variable i goes to block i/3, and our subset picks variable 3*b from block b,
so at most 1 variable per block. -/
theorem firstOfBlockSubset_blockAdmissible (n : ℕ) (hn : n ≥ 2)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (T : Finset (Fin (n / 3))) :
    isBlockAdmissible (cook_levin_compilation M n hn htb hns).partition
      (firstOfBlockSubset n T).toList := by
  refine ⟨Finset.nodup_toList _, fun b => ?_⟩
  -- Show: the filtered list has length ≤ 1
  -- Strategy: show any two elements in the filtered list are equal,
  -- then use Nodup to conclude length ≤ 1.
  have hnd := Finset.nodup_toList (firstOfBlockSubset n T)
  have hfilt_nd : ((firstOfBlockSubset n T).toList.filter
      (fun i => (cook_levin_compilation M n hn htb hns).partition.assign i = b)).Nodup :=
    List.Nodup.filter _ hnd
  -- If two elements of the filtered list exist, they must be equal (by same_block_eq)
  -- A nodup list with ≥ 2 elements has two distinct elements, contradiction.
  by_contra hbad; push_neg at hbad
  -- Get two distinct elements from the nodup filtered list of length ≥ 2
  have hlen := hbad
  have : ∃ x y, x ∈ ((firstOfBlockSubset n T).toList.filter
      (fun i => (cook_levin_compilation M n hn htb hns).partition.assign i = b)) ∧
      y ∈ ((firstOfBlockSubset n T).toList.filter
      (fun i => (cook_levin_compilation M n hn htb hns).partition.assign i = b)) ∧
      x ≠ y := by
    have h0 : 0 < ((firstOfBlockSubset n T).toList.filter
        (fun i => (cook_levin_compilation M n hn htb hns).partition.assign i = b)).length := by omega
    have h1 : 1 < ((firstOfBlockSubset n T).toList.filter
        (fun i => (cook_levin_compilation M n hn htb hns).partition.assign i = b)).length := by omega
    refine ⟨((firstOfBlockSubset n T).toList.filter
        (fun i => (cook_levin_compilation M n hn htb hns).partition.assign i = b))[0],
      ((firstOfBlockSubset n T).toList.filter
        (fun i => (cook_levin_compilation M n hn htb hns).partition.assign i = b))[1],
      List.getElem_mem h0, List.getElem_mem h1, ?_⟩
    intro heq
    -- The list is nodup, but positions 0 and 1 have the same value
    have h_nd2 := hfilt_nd
    rw [List.nodup_iff_injective_getElem] at h_nd2
    have h_inj := @h_nd2 ⟨0, h0⟩ ⟨1, h1⟩ heq
    simp at h_inj
  obtain ⟨x, y, hx, hy, hne⟩ := this
  simp only [List.mem_filter, decide_eq_true_eq] at hx hy
  have hx_set : x ∈ firstOfBlockSubset n T := Finset.mem_toList.mp hx.1
  have hy_set : y ∈ firstOfBlockSubset n T := Finset.mem_toList.mp hy.1
  exact hne (firstOfBlockSubset_same_block_eq n hn M htb hns T x y hx_set hy_set
    (hx.2.trans hy.2.symm))

/-- The family of all C(n/3, κ) first-of-block κ-subsets. -/
noncomputable def fobFamily (n κ : ℕ) : Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin (n / 3))).powersetCard κ).map
    ⟨firstOfBlockSubset n, firstOfBlockSubset_injective n⟩

theorem fobFamily_card (n κ : ℕ) :
    (fobFamily n κ).card = Nat.choose (n / 3) κ := by
  simp [fobFamily, Finset.card_map, Finset.card_powersetCard, Finset.card_fin]

theorem fobFamily_mem_card (n κ : ℕ) (S : Finset (Fin n)) (hS : S ∈ fobFamily n κ) :
    S.card = κ := by
  simp only [fobFamily, Finset.mem_map, Function.Embedding.coeFn_mk] at hS
  obtain ⟨T, hT, rfl⟩ := hS
  rw [firstOfBlockSubset_card]
  rw [Finset.mem_powersetCard] at hT
  exact hT.2

theorem fobFamily_mem_fob (n κ : ℕ) (S : Finset (Fin n)) (hS : S ∈ fobFamily n κ)
    (v : Fin n) (hv : v ∈ S) : 3 ∣ v.val := by
  simp only [fobFamily, Finset.mem_map, Function.Embedding.coeFn_mk] at hS
  obtain ⟨T, _, rfl⟩ := hS
  exact firstOfBlockSubset_mem_div3 n T v hv

theorem fobFamily_mem_blockAdmissible (n : ℕ) (hn : n ≥ 2) (κ : ℕ)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin n)) (hS : S ∈ fobFamily n κ) :
    isBlockAdmissible (cook_levin_compilation M n hn htb hns).partition S.toList := by
  simp only [fobFamily, Finset.mem_map, Function.Embedding.coeFn_mk] at hS
  obtain ⟨T, _, rfl⟩ := hS
  exact firstOfBlockSubset_blockAdmissible n hn M htb hns T

/-- The NP-side lower bound: C(n/3, log n) ≤ rank(compiledPoly).

Constructed from the family of C(n/3, κ) first-of-block block-admissible κ-subsets,
whose compiled SPDP generators are linearly independent by
CrossTermVanishing.linearIndependent_mlProj_compiled_fob.

**Semantic note (paper-faithfulness audit)**:
This theorem takes `DecidesSAT M` as a hypothesis but does NOT use it in the
proof. The linear independence of first-of-block SPDP generators is proved
purely from the booleanity-factor product structure of `compiledPoly`, which
is independent of whether `M` decides 3-SAT.

In the paper's Route B (Global God-Move), the `DecidesSAT` hypothesis is
load-bearing at a DIFFERENT point: it justifies the God-Move extraction map
`Π_Φ` that sends the compiled polynomial to the coupled verifier sheet on the
hard Tseitin instance. The NP-side lower bound should apply to the COUPLED
sheet (or to the compiled polynomial restricted to the hard instance), not to
the compiled polynomial of an arbitrary DTM.

The current identity-construction route bypasses this by taking the coupled
space = compiled space, making `DecidesSAT` formally present but semantically
inert. A paper-faithful Route B would instead:
1. Use `DecidesSAT` to justify the God-Move extraction
2. Prove the NP lower bound on the extracted coupled sheet
3. Transfer back via restriction monotonicity

See `compiled_np_lower_bound_any_dtm` below for the DecidesSAT-free version. -/
theorem identity_construction_np_lower_bound (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n (by omega : n ≥ 2) htb hns)) := by
  set κ := Nat.log 2 n with hκ_def
  have hκ1 : κ ≥ 1 := by
    simp only [κ, hκ_def]
    have h804 : 2 ^ 804 ≤ n := hn
    have : Nat.log 2 (2 ^ 804) ≤ Nat.log 2 n := Nat.log_mono_right h804
    rw [Nat.log_pow (by norm_num : 1 < 2)] at this
    omega
  set F := fobFamily n κ
  have hFcard : F.card = Nat.choose (n / 3) κ := fobFamily_card n κ
  have hcard : ∀ S ∈ F, S.card = κ := fun S hS => fobFamily_mem_card n κ S hS
  have hfob : ∀ S ∈ F, ∀ v ∈ S, 3 ∣ v.val := fun S hS => fobFamily_mem_fob n κ S hS
  have hadm : ∀ S ∈ F, isBlockAdmissible
      (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).partition S.toList :=
    fun S hS => fobFamily_mem_blockAdmissible n (by omega) κ M htb hns S hS
  have hli : LinearIndependent ℚ (fun S : F =>
      mlProj (iterDerivList (S : Finset (Fin n)).toList
        (compiledPoly (cook_levin_compilation M n (by omega : n ≥ 2) htb hns)))) :=
    CrossTermVanishing.linearIndependent_mlProj_compiled_fob M n (by omega) htb hns κ hκ1 hcard hfob
  exact CompiledBoolFactorBridge.weakened_bound_from_compiled_independence
    M n (by omega) htb hns κ hκ1 rfl F hFcard hcard hadm hli

/-- **DecidesSAT-free variant**: the NP-side lower bound for the compiled
polynomial holds for ANY DTM, not just one that decides 3-SAT.

This makes the semantic situation explicit: the booleanity-factor cross-term
vanishing argument is purely structural and does not depend on the machine's
acceptance semantics. The `DecidesSAT` hypothesis in
`identity_construction_np_lower_bound` is formally unused.

**Paper-faithfulness implication**: In the paper's Route B (Global God-Move),
this bound should NOT apply to the compiled polynomial of an arbitrary DTM.
Instead, the paper uses `DecidesSAT` to justify the God-Move extraction,
and the NP lower bound applies to the extracted coupled verifier sheet.
The current identity-construction route collapses these steps, making the
separation appear to work for all DTMs — which is too strong (and in tension
with the P-side bound `spdp_profile_generators`, since their conjunction
would imply no DTM with bounded parameters exists). -/
theorem compiled_np_lower_bound_any_dtm (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n (by omega : n ≥ 2) htb hns)) := by
  set κ := Nat.log 2 n with hκ_def
  have hκ1 : κ ≥ 1 := by
    simp only [κ, hκ_def]
    have h804 : 2 ^ 804 ≤ n := hn
    have : Nat.log 2 (2 ^ 804) ≤ Nat.log 2 n := Nat.log_mono_right h804
    rw [Nat.log_pow (by norm_num : 1 < 2)] at this
    omega
  set F := fobFamily n κ
  have hFcard : F.card = Nat.choose (n / 3) κ := fobFamily_card n κ
  have hcard : ∀ S ∈ F, S.card = κ := fun S hS => fobFamily_mem_card n κ S hS
  have hfob : ∀ S ∈ F, ∀ v ∈ S, 3 ∣ v.val := fun S hS => fobFamily_mem_fob n κ S hS
  have hadm : ∀ S ∈ F, isBlockAdmissible
      (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).partition S.toList :=
    fun S hS => fobFamily_mem_blockAdmissible n (by omega) κ M htb hns S hS
  have hli : LinearIndependent ℚ (fun S : F =>
      mlProj (iterDerivList (S : Finset (Fin n)).toList
        (compiledPoly (cook_levin_compilation M n (by omega : n ≥ 2) htb hns)))) :=
    CrossTermVanishing.linearIndependent_mlProj_compiled_fob M n (by omega) htb hns κ hκ1 hcard hfob
  exact CompiledBoolFactorBridge.weakened_bound_from_compiled_independence
    M n (by omega) htb hns κ hκ1 rfl F hFcard hcard hadm hli

/-! ## Semantic Gap Analysis: Identity Construction vs Paper Route B

The identity construction (`godMoveConstruction_exists`) takes the coupled
space to be the compiled space itself. This makes the rank transfer trivial
(`le_refl`) but has a semantic consequence:

**The NP lower bound applies to the compiled polynomial of ANY DTM.**

Combined with the P-side axiom `spdp_profile_generators` (which also applies
to any DTM), this would yield `C(n/3, log n) ≤ n^200` for all large n — a
false arithmetic inequality. This tension means at most one of:

1. `compiled_np_lower_bound_any_dtm` (the NP-side)
2. `spdp_profile_generators` (the P-side axiom)

can be correct for the same notion of `mlBlockedSpdpRank` and block partition.

**Resolution path** (paper-faithful Route B):
- The paper resolves this by making `DecidesSAT` load-bearing in the
  God-Move extraction. The NP lower bound applies to the COUPLED SHEET
  (not the compiled polynomial), and rank transfer uses restriction
  monotonicity (not identity). The P-side bound still applies to the
  compiled polynomial. There is no contradiction because the coupled
  sheet is a proper restriction/projection of the compiled polynomial.
- To implement this, the identity construction must be replaced by a
  genuine God-Move extraction that uses `DecidesSAT` to relate the
  compiled polynomial to the hard Tseitin instance.
-/

/- Construction note for the current identity placeholder route.

For `godMoveConstruction_exists`, the ambient-space identification and the
compiled-target lower-bound side should collapse definitionally. So the first
likely genuinely nontrivial content in building `GodMoveZeroRemainderData` is a
compiled-side remainder witness together with a decomposition against that
remainder and a zero-rank proof for it.

This is intentionally left as commentary rather than a brittle proposition until
those field types are re-expressed in a way Lean accepts cleanly without fresh
dependent-transport clutter. -/

/-- Derive the quantitative upgrade currently available for the identity
construction.

This is intentionally weaker than the paper's intended God-Move upgrade: the
rank-transfer field is discharged by reflexivity only because the present
construction is the identity construction, whose target polynomial is literally
the compiled polynomial. So this closes the current typed interface, but it does
not yet realize the paper's nontrivial witness-free extraction/projection map. -/
theorem godMoveConstruction_exists_is_canonical_target
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    godMoveConstructionCanonicalTarget (godMoveConstruction_exists M n hn hdec htb hns) := by
  change
    (godMoveConstruction_exists M n hn hdec htb hns).map.instance_uniform ∧
    (godMoveConstruction_exists M n hn hdec htb hns).map.witness_free ∧
    (godMoveConstruction_exists M n hn hdec htb hns).map.block_local
  simp [godMoveConstruction_exists, godMoveConstructionCanonicalTarget]

/-- The identity construction admits the obvious zero remainder witness.

This does not yet build `GodMoveZeroRemainderData`; it only confirms that the
raw witness object itself is not the hard part. The remaining work is in the
same-space target packaging, decomposition, and zero-rank transport layer. -/
noncomputable def godMoveConstruction_exists_zero_remainder_witness
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    GodMoveRemainderWitness M n (by omega : n ≥ 2) htb hns
      (godMoveConstruction_exists M n hn hdec htb hns) where
  remainderPoly := 0
  remainder_is_compiled_side_only := True
  remainder_annihilated_by_extraction_story := True

/-- Direct zero-remainder data for the identity construction.

With the explicit zero remainder witness in hand and the existing lemma
`mlBlockedSpdpRank_zero`, the identity construction now supports an honest
zero-remainder package. -/
noncomputable def godMoveConstruction_exists_zero_remainder_data
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    GodMoveZeroRemainderData M n (by omega : n ≥ 2) htb hns
      (godMoveConstruction_exists M n hn hdec htb hns) := by
  let hs : (godMoveConstruction_exists M n hn hdec htb hns).coupledVars =
      (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars := by
    simp [godMoveConstruction_exists]
  refine {
    witness := godMoveConstruction_exists_zero_remainder_witness M n hn hdec htb hns
    target_same_space := Eq.mp (by rw [hs]) (godMoveConstruction_exists M n hn hdec htb hns).target
    same_space := hs
    target_eq := by
      subst hs
      rfl
    same_partition := by
      simp [godMoveConstruction_exists]
    target_lower_bound := by
      simpa [godMoveConstruction_exists] using
        identity_construction_np_lower_bound M n hn hdec htb hns
    compiled_decomposition := by
      simp [godMoveConstruction_exists, godMoveConstruction_exists_zero_remainder_witness]
    zero_rank_remainder := by
      simpa [godMoveConstruction_exists_zero_remainder_witness] using
        mlBlockedSpdpRank_zero
          (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
  }

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

/-- Rebuild the older typed extraction package from the new two-phase route.

At present this inherits the identity-based quantitative upgrade above, so it is
best read as the currently available typed package, not yet as the final
paper-faithful God-Move theorem. -/
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
  godMoveConstructionCanonicalTarget c ∧
  ∃ r : GodMoveRemainderWitness M n (by omega : n ≥ 2) htb hns c,
    GodMoveConstructionWithProofs M n (by omega : n ≥ 2) htb hns c

/-- Missing bridge for the current identity placeholder route.

The stronger wrapper theorem for `godMoveConstruction_exists` would need not
just an arbitrary compiled-side remainder witness, but the sharper zero-
remainder package that feeds the already-exposed transport machinery. This is
separate from the already proved canonical-target fact, and keeping it explicit
prevents us from silently pretending that the sharpened upgrade target is
already inhabited. -/
def godMoveConstruction_exists_remainder_target
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) : Prop :=
  ∃ z : GodMoveZeroRemainderData M n (by omega : n ≥ 2) htb hns
      (godMoveConstruction_exists M n hn hdec htb hns),
    godMoveTargetTransportTarget (godMoveConstruction_exists M n hn hdec htb hns)

/- Direct bridge attempt note.

After constructing `godMoveConstruction_exists_zero_remainder_data`, the next
attempt was to discharge `godMoveConstruction_exists_remainder_target`
immediately. Lean showed the exact remaining gap: the existing recombined theorem
`godMoveTargetRankTransportTarget_holds` produces the rank-level target, but the
bridge target isolated earlier asks for the stronger transport package
`godMoveTargetTransportTarget`.

So the zero-remainder data is now genuinely in hand for the identity
construction, and the remaining identity-side blocker has narrowed further to
bridging from the proved rank-transport layer to the still-missing full
`godMoveTargetTransportTarget` packaging. -/

theorem godMoveConstruction_exists_remainder_target_holds
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    godMoveConstruction_exists_remainder_target M n hn hdec htb hns := by
  refine ⟨godMoveConstruction_exists_zero_remainder_data M n hn hdec htb hns, ?_⟩
  let c := godMoveConstruction_exists M n hn hdec htb hns
  let hlet := godMoveTargetRankFinrankLetNormalizeTarget_holds c
  let hnorm := godMoveTargetRankFinrankCastNormalizeTarget_holds c hlet
  let hfin := godMoveTargetRankFinrankExprTarget_holds c hnorm
  let hexpr := godMoveTargetRankCastExprTarget_holds c hfin
  let hcast := godMoveTargetRankCastElimTarget_holds c hexpr
  let hcongr := godMoveTargetRankCongrTarget_holds c hcast
  let hrank0 := godMoveTargetRankTransportOfFieldSeamsTarget_holds c hcongr
  let hrank := godMoveTargetRankTransportTarget_holds
    c
    hrank0
    (by
      intro z
      simp)
    (by
      intro z
      simp)
  exact godMoveTargetTransportTarget_of_rankTransport c hrank

/-- The stronger identity wrapper theorem now really holds: the identity
construction meets the sharpened phase-two upgrade target, not just the older
placeholder packaging. -/
theorem godMoveConstruction_exists_meets_upgrade_target
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    godMoveConstruction_upgrade_target M n hn htb hns
      (godMoveConstruction_exists M n hn hdec htb hns) := by
  refine ⟨godMoveConstruction_exists_is_canonical_target M n hn hdec htb hns, ?_⟩
  refine ⟨godMoveConstruction_exists_zero_remainder_witness M n hn hdec htb hns, ?_⟩
  exact godMoveConstruction_upgrade M n hn hdec htb hns

/-- A zero-remainder version of the phase-two God-Move upgrade.

This placeholder still packages the identity-based upgrade, so it is not yet the
paper-faithful zero-remainder theorem. The real missing content is precisely the
canonical zero-remainder package stated by `GodMoveZeroRemainderUpgradeTarget`
below. -/
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
to `godMoveRemainder_rank_harmless_of_zero`.

A more faithful way to state that bottleneck is to ask directly for zero-remainder
upgrade data, not just an arbitrary remainder witness, while keeping the
paper-facing semantic side visible via `godMoveConstructionCanonicalTarget`.
So the zero-remainder frontier now explicitly asks both for a canonical-style
construction and for the transport witness arising from zero remainder. This
packages exactly the semantic object needed to move from construction to
quantitative upgrade without pretending the upgrade already exists. -/
def godMoveZeroRemainderUpgradeTarget
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n)
    (c : GodMoveConstruction M n (by omega : n ≥ 2) htb hns) : Prop :=
  godMoveConstructionCanonicalTarget c ∧
  ∃ z : GodMoveZeroRemainderData M n (by omega : n ≥ 2) htb hns c,
    godMoveTargetTransportTarget c

/-- Bundled honest frontier for the current identity placeholder route.

This packages exactly what is and is not known for the identity construction in
the same language as the main semantic bottleneck: we already have the
canonical-side construction theorem, and what remains is precisely the sharpened
zero-remainder upgrade target for that same construction. -/
def godMoveConstruction_exists_placeholder_frontier
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) : Prop :=
  godMoveZeroRemainderUpgradeTarget M n hn htb hns
    (godMoveConstruction_exists M n hn hdec htb hns)

/-- Tiny helper packaging for comparing a God-Move target with the compiled
Cook-Levin polynomial in the same ambient variable space.

The first honest non-identity semantic seam is not yet a full theorem about the
paper's canonical `ΠΦ`. It is only the typed comparison package needed to even
state that the transported target polynomial differs from the compiled
polynomial without running into ambient-space mismatches. -/
structure GodMoveTargetCompiledComparison
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (c : GodMoveConstruction M n hn2 htb hns) where
  same_space : c.coupledVars = (cook_levin_compilation M n hn2 htb hns).numVars
  target_same_space :
    GodMoveTypedTarget ((cook_levin_compilation M n hn2 htb hns).numVars)
  target_eq : Eq.mp (by rw [same_space]) c.target = target_same_space

/-- First explicit non-identity semantic seam for the paper's actual `ΠΦ`.

The identity construction is now fully wrapped up through the sharpened upgrade
interface, so the remaining paper-faithful work must distinguish a genuine
canonical God-Move from the identity placeholder. The smallest explicit seam is
that, after transporting to the compiled ambient space, the target polynomial
should no longer be literally the compiled polynomial.

This target still does not claim to construct the real `ΠΦ`; it only packages
the first typed property that any genuine non-identity canonical extraction must
satisfy. -/
def godMoveNonidentityConstructionTarget
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n)
    (c : GodMoveConstruction M n (by omega : n ≥ 2) htb hns) : Prop :=
  godMoveConstructionCanonicalTarget c ∧
  ∃ cmp : GodMoveTargetCompiledComparison M n (by omega : n ≥ 2) htb hns c,
    cmp.target_same_space.poly ≠
      compiledPoly (cook_levin_compilation M n (by omega : n ≥ 2) htb hns)

/-- The current identity construction is canonical, but it is not non-identity:
after transporting to the compiled ambient space, its target polynomial is still
literally the compiled Cook-Levin polynomial. -/
theorem godMoveConstruction_exists_not_nonidentity
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    ¬ godMoveNonidentityConstructionTarget M n hn htb hns
        (godMoveConstruction_exists M n hn hdec htb hns) := by
  intro hnon
  rcases hnon with ⟨_, cmp, hne⟩
  have hpoly := congrArg GodMoveTypedTarget.poly cmp.target_eq
  simp [godMoveConstruction_exists] at hpoly
  exact hne hpoly.symm

/-- Tiny helper packaging for transported staged-map output in the compiled
ambient space.

This isolates the next cast seam above target comparison: not just transporting
`c.target`, but transporting the actual output of the staged map on the compiled
polynomial into the compiled ambient variable space. -/
structure GodMoveTransportedMapOutput
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (c : GodMoveConstruction M n hn2 htb hns) where
  comparison : GodMoveTargetCompiledComparison M n hn2 htb hns c
  map_output_same_space :
    MvPolynomial (Fin ((cook_levin_compilation M n hn2 htb hns).numVars)) ℚ
  map_output_eq :
    Eq.mp (by rw [comparison.same_space])
      (c.map.toFun (compiledPoly (cook_levin_compilation M n hn2 htb hns))) =
      map_output_same_space

/-- First staged-map nontriviality seam for a genuine non-identity `ΠΦ`.

The polynomial-level non-identity target above cleanly separates the current
identity placeholder from any real God-Move candidate. The next stronger seam is
that the staged extraction map itself should not collapse to the identity map on
the compiled polynomial. This is still local and typed: it does not yet claim to
construct the paper's final `ΠΦ`, only to isolate the next semantic property a
real non-identity candidate must satisfy. -/
def godMoveNontrivialStagedMapTarget
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n)
    (c : GodMoveConstruction M n (by omega : n ≥ 2) htb hns) : Prop :=
  godMoveConstructionCanonicalTarget c ∧
  ∃ out : GodMoveTransportedMapOutput M n (by omega : n ≥ 2) htb hns c,
    out.map_output_same_space ≠ out.comparison.target_same_space.poly

/-- The current identity construction also fails the stronger staged-map
nontriviality seam: after transporting to the compiled ambient space, the staged
map output is still literally the compiled Cook-Levin polynomial, matching the
transported target. -/
theorem godMoveConstruction_exists_not_nontrivial_staged_map
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    ¬ godMoveNontrivialStagedMapTarget M n hn htb hns
        (godMoveConstruction_exists M n hn hdec htb hns) := by
  intro hnon
  rcases hnon with ⟨_, out, hne⟩
  have hmap :
      out.map_output_same_space =
        compiledPoly (cook_levin_compilation M n (by omega : n ≥ 2) htb hns) := by
    rw [← out.map_output_eq]
    simp [godMoveConstruction_exists]
  have hpoly := congrArg GodMoveTypedTarget.poly out.comparison.target_eq
  simp [godMoveConstruction_exists] at hpoly
  have hEq : out.map_output_same_space = out.comparison.target_same_space.poly := by
    rw [hmap]
    exact hpoly
  exact hne hEq

/-- Bundled target for a genuine paper-facing `ΠΦ` candidate.

This is the first compact target that really looks like the intended semantic
frontier after the identity route is closed. A genuine candidate should be:
1. canonical in the paper-facing sense,
2. satisfy the staged extraction identity, and
3. be nontrivial at the staged-map level, so it is not just the identity
   placeholder in disguise. -/
def godMoveGenuineCandidateTarget
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n)
    (c : GodMoveConstruction M n (by omega : n ≥ 2) htb hns) : Prop :=
  godMoveConstructionCanonicalTarget c ∧
  godMoveStagedExtractionTarget M n (by omega : n ≥ 2) htb hns
    c.coupledVars c.map c.target ∧
  godMoveNontrivialStagedMapTarget M n hn htb hns c

/-- The identity placeholder construction is not yet a genuine `ΠΦ` candidate:
it is canonical and satisfies the trivial staged extraction identity, but it
fails the required staged-map nontriviality. -/
theorem godMoveConstruction_exists_not_genuine_candidate
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    ¬ godMoveGenuineCandidateTarget M n hn htb hns
        (godMoveConstruction_exists M n hn hdec htb hns) := by
  intro hg
  exact godMoveConstruction_exists_not_nontrivial_staged_map M n hn hdec htb hns hg.2.2

/-- Tiny helper packaging for projection-stage output before relabeling.

This lets us compare a candidate to the identity placeholder at the projection
stage without pretending the full dependent `projectionData` records are already
in a comfortably comparable form. -/
structure GodMoveProjectionOutputComparison
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (c : GodMoveConstruction M n hn2 htb hns) where
  restricted_output : MvPolynomial (Fin c.map.restrictedVars) ℚ
  restricted_output_eq :
    c.map.restrictFun (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
      restricted_output
  projection_output : MvPolynomial (Fin c.map.projectionData.projectedVars) ℚ
  projection_output_eq : c.map.projectFun restricted_output = projection_output

/-- The identity placeholder admits the projection-output comparison package
trivially, since both restriction and projection are literally the identity. -/
noncomputable def godMoveConstruction_exists_projection_output_comparison
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    GodMoveProjectionOutputComparison M n (by omega : n ≥ 2) htb hns
      (godMoveConstruction_exists M n hn hdec htb hns) where
  restricted_output :=
    (godMoveConstruction_exists M n hn hdec htb hns).map.restrictFun
      (compiledPoly (cook_levin_compilation M n (by omega : n ≥ 2) htb hns))
  restricted_output_eq := rfl
  projection_output :=
    (godMoveConstruction_exists M n hn hdec htb hns).map.projectFun
      ((godMoveConstruction_exists M n hn hdec htb hns).map.restrictFun
        (compiledPoly (cook_levin_compilation M n (by omega : n ≥ 2) htb hns)))
  projection_output_eq := rfl

/-- Shared ambient comparison package for projection-stage output.

This is the projection analogue of `GodMoveTargetCompiledComparison`: it gives a
candidate projection output together with an explicit same-space witness to the
identity placeholder's projection ambient space, so the two outputs can be
compared without raw dependent-type mismatches. -/
structure GodMoveProjectionSharedComparison
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (c : GodMoveConstruction M n (by omega : n ≥ 2) htb hns) where
  candidate_output : GodMoveProjectionOutputComparison M n (by omega : n ≥ 2) htb hns c
  same_projected_vars :
    c.map.projectionData.projectedVars =
      (godMoveConstruction_exists M n hn hdec htb hns).map.projectionData.projectedVars
  candidate_output_same_space :
    MvPolynomial (Fin ((godMoveConstruction_exists M n hn hdec htb hns).map.projectionData.projectedVars)) ℚ
  candidate_output_eq :
    Eq.mp (by rw [same_projected_vars]) candidate_output.projection_output =
      candidate_output_same_space

/-- Tiny helper packaging for relabel-stage output.

This extends the staged comparison ladder one level higher: after restriction
and projection, we package the actual relabel output before comparing it to the
identity placeholder or to the final transported target. -/
structure GodMoveRelabelOutputComparison
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (c : GodMoveConstruction M n hn2 htb hns) where
  projection_output : GodMoveProjectionOutputComparison M n hn2 htb hns c
  relabel_output : MvPolynomial (Fin c.coupledVars) ℚ
  relabel_output_eq : c.map.relabelFun projection_output.projection_output = relabel_output

/-- The identity placeholder admits the relabel-output comparison package
trivially, since restriction, projection, and relabeling are all identity maps. -/
noncomputable def godMoveConstruction_exists_relabel_output_comparison
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    GodMoveRelabelOutputComparison M n (by omega : n ≥ 2) htb hns
      (godMoveConstruction_exists M n hn hdec htb hns) where
  projection_output :=
    godMoveConstruction_exists_projection_output_comparison M n hn hdec htb hns
  relabel_output :=
    (godMoveConstruction_exists M n hn hdec htb hns).map.relabelFun
      ((godMoveConstruction_exists_projection_output_comparison M n hn hdec htb hns).projection_output)
  relabel_output_eq := rfl

/-- Shared ambient comparison package for relabel-stage output.

This is the relabel analogue of `GodMoveProjectionSharedComparison`: it packages
candidate relabel output in the identity placeholder's coupled ambient space so
that relabel-stage perturbation can be stated without another raw dependent-type
mismatch. -/
structure GodMoveRelabelSharedComparison
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (c : GodMoveConstruction M n (by omega : n ≥ 2) htb hns) where
  candidate_output : GodMoveRelabelOutputComparison M n (by omega : n ≥ 2) htb hns c
  same_coupled_vars : c.coupledVars = (godMoveConstruction_exists M n hn hdec htb hns).coupledVars
  candidate_output_same_space :
    MvPolynomial (Fin ((godMoveConstruction_exists M n hn hdec htb hns).coupledVars)) ℚ
  candidate_output_eq :
    Eq.mp (by rw [same_coupled_vars]) candidate_output.relabel_output =
      candidate_output_same_space

/-- First construction-level frontier for moving beyond the identity placeholder.

Rather than pretending to have the full paper `ΠΦ`, the next honest step is to
modify at least one semantic stage of the identity construction while keeping
the comparison well-typed. At this level, the two cleanly comparable pieces are:
1. the restriction data, and
2. the transported target polynomial in the compiled ambient space. -/
def godMoveOneStagePerturbationTarget
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n)
    (c : GodMoveConstruction M n (by omega : n ≥ 2) htb hns) : Prop :=
  ∃ cmp : GodMoveTargetCompiledComparison M n (by omega : n ≥ 2) htb hns c,
    ∃ proj : GodMoveProjectionSharedComparison M n hn hdec htb hns c,
      ∃ rel : GodMoveRelabelSharedComparison M n hn hdec htb hns c,
        c.map.restrictionData ≠
            (godMoveConstruction_exists M n hn hdec htb hns).map.restrictionData ∨
          proj.candidate_output_same_space ≠
            (godMoveConstruction_exists_projection_output_comparison M n hn hdec htb hns).projection_output ∨
          rel.candidate_output_same_space ≠
            (godMoveConstruction_exists_relabel_output_comparison M n hn hdec htb hns).relabel_output ∨
          cmp.target_same_space.poly ≠
            compiledPoly (cook_levin_compilation M n (by omega : n ≥ 2) htb hns)

/-- The identity placeholder fails the one-stage perturbation target too:
its restriction data is unchanged, and its transported target polynomial is
still just the compiled Cook-Levin polynomial. -/
theorem godMoveConstruction_exists_not_one_stage_perturbation
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    ¬ godMoveOneStagePerturbationTarget M n hn hdec htb hns
        (godMoveConstruction_exists M n hn hdec htb hns) := by
  intro hp
  rcases hp with ⟨cmp, proj, rel, hpert⟩
  have hpoly := congrArg GodMoveTypedTarget.poly cmp.target_eq
  simp [godMoveConstruction_exists] at hpoly
  have hproj_id :
      (godMoveConstruction_exists_projection_output_comparison M n hn hdec htb hns).projection_output =
        compiledPoly (cook_levin_compilation M n (by omega : n ≥ 2) htb hns) := by
    simp [godMoveConstruction_exists_projection_output_comparison, godMoveConstruction_exists]
  have hproj :
      proj.candidate_output_same_space =
        (godMoveConstruction_exists_projection_output_comparison M n hn hdec htb hns).projection_output := by
    rw [hproj_id]
    rw [← proj.candidate_output_eq]
    rw [← proj.candidate_output.projection_output_eq, ← proj.candidate_output.restricted_output_eq]
    simp [godMoveConstruction_exists]
  have hrel_id :
      (godMoveConstruction_exists_relabel_output_comparison M n hn hdec htb hns).relabel_output =
        compiledPoly (cook_levin_compilation M n (by omega : n ≥ 2) htb hns) := by
    simp [godMoveConstruction_exists_relabel_output_comparison,
      godMoveConstruction_exists_projection_output_comparison, godMoveConstruction_exists]
  have hrel :
      rel.candidate_output_same_space =
        (godMoveConstruction_exists_relabel_output_comparison M n hn hdec htb hns).relabel_output := by
    rw [hrel_id]
    rw [← rel.candidate_output_eq]
    rw [← rel.candidate_output.relabel_output_eq]
    rw [← rel.candidate_output.projection_output.projection_output_eq,
      ← rel.candidate_output.projection_output.restricted_output_eq]
    simp [godMoveConstruction_exists]
  rcases hpert with hrest | hproj_ne | hrel_ne | htarget
  · simp [godMoveConstruction_exists] at hrest
  · exact hproj_ne hproj
  · exact hrel_ne hrel
  · exact htarget hpoly.symm

/-- The next honest existence frontier after closing the identity route.

This does not pretend to construct the paper's non-identity `ΠΦ`. It only says
what the next real success would look like: some God-Move construction that is a
genuine candidate and also perturbs at least one explicit stage of the identity
placeholder chain. -/
def godMoveNonidentityCandidateExistsTarget
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) : Prop :=
  ∃ c : GodMoveConstruction M n (by omega : n ≥ 2) htb hns,
    godMoveGenuineCandidateTarget M n hn htb hns c ∧
    godMoveOneStagePerturbationTarget M n hn hdec htb hns c

/-- The current identity placeholder does not inhabit the new non-identity
existence target. This theorem does not rule out other constructions; it only
records that the old identity route is definitively not the answer. -/
theorem godMoveConstruction_exists_not_nonidentity_candidate_witness
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    ¬ (godMoveGenuineCandidateTarget M n hn htb hns
          (godMoveConstruction_exists M n hn hdec htb hns) ∧
        godMoveOneStagePerturbationTarget M n hn hdec htb hns
          (godMoveConstruction_exists M n hn hdec htb hns)) := by
  intro h
  exact godMoveConstruction_exists_not_genuine_candidate M n hn hdec htb hns h.1

/-- Smallest constructive subtarget of the post-identity frontier.

Before constructing a full non-identity God-Move candidate, the first concrete
success could simply be a construction whose restriction stage is genuinely
non-identity while the rest of the staged comparison framework remains in place.
This isolates that minimal witness shape. -/
def godMoveRestrictionPerturbationWitnessTarget
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) : Prop :=
  ∃ c : GodMoveConstruction M n (by omega : n ≥ 2) htb hns,
    godMoveConstructionCanonicalTarget c ∧
    c.map.restrictionData ≠
      (godMoveConstruction_exists M n hn hdec htb hns).map.restrictionData

/-- The identity placeholder does not witness even the weakest constructive
restriction-perturbation target. -/
theorem godMoveConstruction_exists_not_restriction_perturbation_witness
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    ¬ (godMoveConstructionCanonicalTarget
          (godMoveConstruction_exists M n hn hdec htb hns) ∧
        (godMoveConstruction_exists M n hn hdec htb hns).map.restrictionData ≠
          (godMoveConstruction_exists M n hn hdec htb hns).map.restrictionData) := by
  intro h
  exact h.2 rfl

/-- Smallest explicit candidate shape for a restriction-stage perturbation.

This still does not claim to realize the paper's true `ΠΦ`. It only packages
what a first constructive attempt should minimally provide: a God-Move
construction together with a proof that its restriction data differs from the
identity placeholder's restriction stage. -/
def godMoveRestrictionPerturbationCandidateTarget
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n)
    (c : GodMoveConstruction M n (by omega : n ≥ 2) htb hns) : Prop :=
  godMoveConstructionCanonicalTarget c ∧
  c.map.restrictionData ≠
    (godMoveConstruction_exists M n hn hdec htb hns).map.restrictionData

/-- The weakest constructive restriction witness target is exactly the
existential packaging of a restriction-perturbation candidate. -/
theorem godMoveRestrictionPerturbationWitnessTarget_iff
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    godMoveRestrictionPerturbationWitnessTarget M n hn hdec htb hns ↔
      ∃ c : GodMoveConstruction M n (by omega : n ≥ 2) htb hns,
        godMoveRestrictionPerturbationCandidateTarget M n hn hdec htb hns c := by
  rfl

/-- The identity placeholder still fails the candidate-level restriction
perturbation target. -/
theorem godMoveConstruction_exists_not_restriction_perturbation_candidate
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    ¬ godMoveRestrictionPerturbationCandidateTarget M n hn hdec htb hns
        (godMoveConstruction_exists M n hn hdec htb hns) := by
  intro h
  exact h.2 rfl

/-- Smallest object-level target for a non-identity restriction stage.

This is one level below a full `GodMoveConstruction`: before building a whole
candidate, we can ask just for a restriction-data record over the compiled
variable space that differs from the identity placeholder's restriction stage. -/
def godMoveRestrictionDataPerturbationTarget
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) : Prop :=
  ∃ r : GodMoveRestrictionData ((cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars),
    r ≠ (godMoveConstruction_exists M n hn hdec htb hns).map.restrictionData

/-- Even at raw restriction-data level, the identity placeholder's own record is
not a perturbation witness. -/
theorem godMoveConstruction_exists_not_restriction_data_perturbation_self
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    ¬ ((godMoveConstruction_exists M n hn hdec htb hns).map.restrictionData ≠
      (godMoveConstruction_exists M n hn hdec htb hns).map.restrictionData) := by
  intro h
  exact h rfl

/-- Tiny positivity lemma for the compiled Cook-Levin variable count.

This isolates the object-level blocker for the first explicit restriction-data
perturbation witness: we only need a small positive `Fin` index in the compiled
ambient space, and `cook_levin_compilation` literally sets `numVars := n`. -/
theorem cookLevin_numVars_pos
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    0 < (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars := by
  have hn2 : 2 ≤ n := by
    omega
  have hn0 : 0 < n := by
    omega
  simpa [cook_levin_compilation] using hn0

/-- A first explicit non-identity restriction-data candidate.

This is intentionally tiny and local: single out one compiled variable as fixed,
mark it administrative/tableau, remove it from the preserved clause-sheet set,
and keep the rest of the record as close as possible to the identity
placeholder. The point is not that this is the right paper construction, only
that it is an actual concrete perturbation of the identity restriction record. -/
noncomputable def godMoveRestrictionData_firstPerturbation
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    GodMoveRestrictionData ((cook_levin_compilation M n (by
      have hn2 : n ≥ 2 := by omega
      exact hn2) htb hns).numVars) :=
  let hn2 : n ≥ 2 := by omega
  let T := cook_levin_compilation M n hn2 htb hns
  let v0 : Fin T.numVars := ⟨0, cookLevin_numVars_pos M n hn htb hns⟩
  {
    administrativeVars := {v0}
    tableauVars := {v0}
    fixedVars := {v0}
    freeVarsAfterRestriction := T.numVars
    freeVarEmbedding := id
    assignment := fun _ => 0
    clauseSheetPreservedVars := Finset.univ.erase v0
    fixes_administrative_vars := True
    fixes_tableau_vars_to_constants := True
    preserves_clause_sheet_vars := True
    specializedVars := {v0}
    fixedVars_cover_specialized_coordinates := True
    free_embedding_avoids_fixed := True
    clauseSheetPreservedVars_avoid_fixed := True
  }

/-- The first explicit restriction-data candidate is genuinely different from
the identity placeholder's restriction stage. -/
theorem godMoveRestrictionData_firstPerturbation_ne_identity
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    godMoveRestrictionData_firstPerturbation M n hn hdec htb hns ≠
      (godMoveConstruction_exists M n hn hdec htb hns).map.restrictionData := by
  intro h
  have hadmin := congrArg GodMoveRestrictionData.administrativeVars h
  simp [godMoveRestrictionData_firstPerturbation, godMoveConstruction_exists] at hadmin

/-- Smallest typed-map level target above the explicit restriction-data witness.

This is the next honest lift: not yet a full `GodMoveConstruction`, but a typed
map whose restriction stage is the concrete perturbed record we just built. -/
def godMoveRestrictionPerturbedTypedMapTarget
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n)
    (coupledVars : ℕ)
    (map : GodMoveTypedMap (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars coupledVars) : Prop :=
  map.restrictionData = godMoveRestrictionData_firstPerturbation M n hn hdec htb hns

/-- The current identity placeholder typed map does not satisfy the new
restriction-perturbed typed-map target. -/
theorem godMoveConstruction_exists_map_not_restriction_perturbed
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    ¬ godMoveRestrictionPerturbedTypedMapTarget M n hn hdec htb hns
        (godMoveConstruction_exists M n hn hdec htb hns).coupledVars
        (godMoveConstruction_exists M n hn hdec htb hns).map := by
  intro h
  exact godMoveRestrictionData_firstPerturbation_ne_identity M n hn hdec htb hns h.symm

/-- First explicit typed-map candidate with a perturbed restriction stage.

This is the minimal typed lift of the concrete restriction-data witness: keep
projection, relabeling, and all function-level maps equal to the current
identity placeholder, and replace only `restrictionData`. -/
noncomputable def godMoveTypedMap_firstRestrictionPerturbation
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    GodMoveTypedMap
      (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars
      (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars :=
  let T := cook_levin_compilation M n (by omega : n ≥ 2) htb hns
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
  {
    restrictionData := godMoveRestrictionData_firstPerturbation M n hn hdec htb hns
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

/-- The first explicit typed-map candidate really satisfies the restriction
perturbation typed-map target. -/
theorem godMoveTypedMap_firstRestrictionPerturbation_is_target
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    godMoveRestrictionPerturbedTypedMapTarget M n hn hdec htb hns
      (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars
      (godMoveTypedMap_firstRestrictionPerturbation M n hn hdec htb hns) := by
  rfl

/-- Local semantic honesty target for the first perturbed typed map.

Once `restrictionData` is changed, keeping `restrictFun := id` may no longer be
an honest realization of the staged map semantics. This target isolates the next
real theorem question: does the first perturbed typed map still satisfy the
staged extraction identity, or does the metadata/function mismatch force
failure? -/
def godMoveFirstRestrictionPerturbationStagedTarget
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) : Prop :=
  godMoveStagedExtractionTarget M n (by omega : n ≥ 2) htb hns
    (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars
    (godMoveTypedMap_firstRestrictionPerturbation M n hn hdec htb hns)
    { partition := (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).partition
      poly := compiledPoly (cook_levin_compilation M n (by omega : n ≥ 2) htb hns) }

/-- The first perturbed typed map still satisfies the raw staged extraction
identity definitionally, because its function-level maps remain identity. This
shows the real semantic gap is not the bare staged equality itself, but the lack
of coherence between perturbed restriction metadata and the still-identity
`restrictFun`. -/
theorem godMoveFirstRestrictionPerturbationStagedTarget_holds
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    godMoveFirstRestrictionPerturbationStagedTarget M n hn hdec htb hns := by
  unfold godMoveFirstRestrictionPerturbationStagedTarget
  unfold godMoveStagedExtractionTarget
  simp [godMoveTypedMap_firstRestrictionPerturbation]

/-- First metadata/function coherence target for the restriction stage.

The staged extraction identity alone is too weak, because a metadata-only
perturbation can still satisfy it when `restrictFun := id`. The next semantic
frontier is to require that the restriction function genuinely reflects the
restriction metadata, at least enough to distinguish the identity map from a map
that claims some variable is fixed/specialized. -/
def godMoveRestrictionCoherenceTarget
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n)
    (compiledVars coupledVars : ℕ)
    (map : GodMoveTypedMap compiledVars coupledVars) : Prop :=
  map.restrictionData.fixedVars ≠ ∅ →
    map.restrictFun 1 ≠ (1 : MvPolynomial (Fin map.restrictedVars) ℚ)

/-- The first perturbed typed map fails the restriction coherence target.

Its metadata says some variable is fixed, but the actual restriction function is
still the identity map, so constants like `1` are left unchanged. This is the
first clean proof that metadata-only perturbation is semantically fake. -/
theorem godMoveTypedMap_firstRestrictionPerturbation_not_coherent
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    ¬ godMoveRestrictionCoherenceTarget M n hn hdec htb hns
        (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars
        (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars
        (godMoveTypedMap_firstRestrictionPerturbation M n hn hdec htb hns) := by
  intro hcoh
  have hfixed :
      (godMoveTypedMap_firstRestrictionPerturbation M n hn hdec htb hns).restrictionData.fixedVars ≠ ∅ := by
    simp [godMoveTypedMap_firstRestrictionPerturbation, godMoveRestrictionData_firstPerturbation]
  have hneq := hcoh hfixed
  have hone :
      (godMoveTypedMap_firstRestrictionPerturbation M n hn hdec htb hns).restrictFun 1 =
        (1 : MvPolynomial (Fin (godMoveTypedMap_firstRestrictionPerturbation M n hn hdec htb hns).restrictedVars) ℚ) := by
    simp [godMoveTypedMap_firstRestrictionPerturbation]
  exact hneq hone

/-- Smallest behavior-level target for a genuinely perturbed restriction map.

After proving metadata-only perturbation is incoherent, the next construction
must change the actual restriction function. This target isolates the minimal
behavioral requirement: on the compiled polynomial `1`, the restriction function
must genuinely differ from the identity behavior. -/
def godMoveRestrictionFunctionPerturbationTarget
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n)
    (compiledVars coupledVars : ℕ)
    (map : GodMoveTypedMap compiledVars coupledVars) : Prop :=
  ∃ p : MvPolynomial (Fin compiledVars) ℚ,
    map.restrictFun p ≠ map.restrictFun 0

/- After broadening `godMoveRestrictionFunctionPerturbationTarget` to avoid the
ambient-space mismatch, the old negative theorem for the metadata-only perturbed
map is no longer the right statement. An identity map certainly can separate
some polynomial from `0`; the real semantic issue is coherence with the claimed
restriction metadata, already captured by `godMoveRestrictionCoherenceTarget`. -/

/-- Stronger behavior-level seam: the restriction function itself must differ
from the identity on some compiled polynomial, after identifying the restricted
ambient space with the compiled one.

This is the honest successor to the metadata-only perturbation target above.
Unlike `godMoveRestrictionFunctionPerturbationTarget`, it actually separates a
genuine restriction-stage perturbation from the identity placeholder. -/
def godMoveRestrictionFunctionNonidentityTarget
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n)
    (compiledVars coupledVars : ℕ)
    (map : GodMoveTypedMap compiledVars coupledVars) : Prop :=
  ∃ hsame : map.restrictedVars = compiledVars,
    ∃ p : MvPolynomial (Fin compiledVars) ℚ,
      map.restrictFun p ≠ Eq.mp (by rw [hsame]) p

/-- Variable assignment for the first genuinely perturbed restriction function.

This is the minimal substitution pattern suggested by the restriction metadata:
send the singled-out fixed variable to `0`, and leave all other variables as
formal variables. The resulting map is intended for `MvPolynomial.aeval`. -/
noncomputable def godMoveRestrictionFirstPerturbationSubst
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    Fin ((cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars) →
      MvPolynomial (Fin ((cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars)) ℚ :=
  let T := cook_levin_compilation M n (by omega : n ≥ 2) htb hns
  let v0 : Fin T.numVars := ⟨0, cookLevin_numVars_pos M n hn htb hns⟩
  fun i => if i = v0 then 0 else X i

/-- First genuinely non-identity restriction function candidate, now using the
correct substitution primitive (`MvPolynomial.aeval`) rather than `rename`. -/
noncomputable def godMoveRestrictFun_firstPerturbation
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    MvPolynomial (Fin ((cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars)) ℚ →
      MvPolynomial (Fin ((cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars)) ℚ :=
  fun p => MvPolynomial.aeval (godMoveRestrictionFirstPerturbationSubst M n hn hdec htb hns) p

/-- The first perturbed restriction function is genuinely non-identity on a very
simple test polynomial, namely the singled-out variable itself. -/
theorem godMoveRestrictFun_firstPerturbation_nontrivial
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    let T := cook_levin_compilation M n (by omega : n ≥ 2) htb hns
    let v0 : Fin T.numVars := ⟨0, cookLevin_numVars_pos M n hn htb hns⟩
    godMoveRestrictFun_firstPerturbation M n hn hdec htb hns (X v0) ≠ X v0 := by
  intro T v0 h
  have hcoeff := congrArg (fun p => MvPolynomial.coeff (Finsupp.single v0 1) p) h
  simp [godMoveRestrictFun_firstPerturbation, godMoveRestrictionFirstPerturbationSubst, v0,
    MvPolynomial.coeff_X] at hcoeff

/-- The identity placeholder restriction stage is not a genuine behavior-level
perturbation: its restriction function is literally the identity. -/
theorem godMoveConstruction_exists_map_not_restriction_function_nonidentity
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    ¬ godMoveRestrictionFunctionNonidentityTarget M n hn hdec htb hns
        (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars
        (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars
        (godMoveConstruction_exists M n hn hdec htb hns).map := by
  intro h
  rcases h with ⟨hsame, p, hp⟩
  cases hsame
  exact hp (by simp [godMoveConstruction_exists])

/-- First typed map with genuinely perturbed restriction behavior.

This is the behavior-level successor to the earlier metadata-only perturbation:
we keep the projection/relabel stages identity-like, but now the restriction
function itself actually performs the intended substitution. -/
noncomputable def godMoveTypedMap_firstBehaviorPerturbation
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    GodMoveTypedMap
      (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars
      (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars :=
  let T := cook_levin_compilation M n (by omega : n ≥ 2) htb hns
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
  {
    restrictionData := godMoveRestrictionData_firstPerturbation M n hn hdec htb hns
    restrictedVars := T.numVars
    projectionData := projectionData
    restrictFun := godMoveRestrictFun_firstPerturbation M n hn hdec htb hns
    projectFun := id
    relabelData := relabelData
    relabelFun := id
    toFun := fun p => godMoveRestrictFun_firstPerturbation M n hn hdec htb hns p
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

/-- The first behavior-perturbed typed map satisfies the broad function
perturbation target. -/
theorem godMoveTypedMap_firstBehaviorPerturbation_is_function_perturbed
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    godMoveRestrictionFunctionPerturbationTarget M n hn hdec htb hns
      (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars
      (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars
      (godMoveTypedMap_firstBehaviorPerturbation M n hn hdec htb hns) := by
  refine ⟨1, ?_⟩
  simp [godMoveTypedMap_firstBehaviorPerturbation, godMoveRestrictFun_firstPerturbation]

/-- The first behavior-perturbed typed map also satisfies the stronger
nonidentity target: its restriction function no longer agrees with the identity
map on the distinguished fixed variable. -/
theorem godMoveTypedMap_firstBehaviorPerturbation_is_nonidentity
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    godMoveRestrictionFunctionNonidentityTarget M n hn hdec htb hns
      (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars
      (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars
      (godMoveTypedMap_firstBehaviorPerturbation M n hn hdec htb hns) := by
  let T := cook_levin_compilation M n (by omega : n ≥ 2) htb hns
  let v0 : Fin T.numVars := ⟨0, cookLevin_numVars_pos M n hn htb hns⟩
  refine ⟨rfl, X v0, ?_⟩
  simpa [godMoveTypedMap_firstBehaviorPerturbation] using
    godMoveRestrictFun_firstPerturbation_nontrivial M n hn hdec htb hns

/-- Existential packaging of the first honest behavior-level success beyond the
metadata-only perturbation story.

This does not yet construct a full paper-faithful `GodMoveConstruction`, but it
does exhibit an explicit typed map whose restriction stage is genuinely
non-identity as a function, not just in its metadata. -/
def godMoveRestrictionFunctionNonidentityWitnessTarget
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) : Prop :=
  ∃ coupledVars :
      ℕ,
    ∃ map : GodMoveTypedMap
      (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars
      coupledVars,
      godMoveRestrictionFunctionNonidentityTarget M n hn hdec htb hns
        (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars
        coupledVars map

/-- The first behavior-perturbed typed map witnesses the new behavior-level
nonidentity target. This is the cleanest current constructive milestone on the
post-identity Route B thread. -/
theorem godMoveRestrictionFunctionNonidentityWitnessTarget_holds
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    godMoveRestrictionFunctionNonidentityWitnessTarget M n hn hdec htb hns := by
  refine ⟨(cook_levin_compilation M n (by omega : n ≥ 2) htb hns).numVars,
    godMoveTypedMap_firstBehaviorPerturbation M n hn hdec htb hns, ?_⟩
  exact godMoveTypedMap_firstBehaviorPerturbation_is_nonidentity M n hn hdec htb hns

/- The first behavior-perturbed typed map should now witness the corrected
function-perturbation target. The remaining bridge is still genuinely tiny, but
it should be finished with cleanly typed polynomial equalities rather than a
rushed contradiction proof. The needed ingredients are already in hand:

  1. `godMoveRestrictFun_firstPerturbation_nontrivial`
  2. `godMoveRestrictFun_firstPerturbation ... 0 = 0`
  3. `MvPolynomial.X_ne_zero v0`

The next turn can close this by writing that bridge carefully. -/

/- First explicit full `GodMoveConstruction` attempt from the perturbed typed map.

The raw data all lines up: we can build the perturbed restriction-data witness
and the corresponding typed map while keeping projection/relabel/target
identity-like. The next real blocker is exactly the staged semantic target for
that map:

  map.relabelFun (map.projectFun (map.restrictFun compiledPoly)) = target.poly

This no longer closes by definitional simplification once the restriction stage
is perturbed, even though the function-level maps are still identity. So the
next honest lift is not more record assembly, but a small theorem explaining why
the staged extraction identity still holds (or fails) for the first perturbed
typed map. -/

/-- The already-proved canonical theorem supplies the canonical half of the
bundled identity placeholder frontier. What remains open is exactly the
zero-remainder/transport existential half. -/
theorem godMoveConstruction_exists_placeholder_frontier_canonical
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    godMoveConstructionCanonicalTarget
      (godMoveConstruction_exists M n hn hdec htb hns) :=
  godMoveConstruction_exists_is_canonical_target M n hn hdec htb hns

/-- The bundled identity placeholder frontier is definitionally exactly the
canonical half together with the still-open zero-remainder/transport
existential half. -/
theorem godMoveConstruction_exists_placeholder_frontier_iff
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    godMoveConstruction_exists_placeholder_frontier M n hn hdec htb hns ↔
      (godMoveConstructionCanonicalTarget
          (godMoveConstruction_exists M n hn hdec htb hns) ∧
        ∃ z : GodMoveZeroRemainderData M n (by omega : n ≥ 2) htb hns
            (godMoveConstruction_exists M n hn hdec htb hns),
          godMoveTargetTransportTarget
            (godMoveConstruction_exists M n hn hdec htb hns)) := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Since the canonical half is already known, any proof of the bundled
identity placeholder frontier yields exactly the still-missing
zero-remainder/transport existential package. -/
theorem godMoveConstruction_exists_placeholder_frontier_missing
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n)
    (hfront : godMoveConstruction_exists_placeholder_frontier M n hn hdec htb hns) :
    ∃ z : GodMoveZeroRemainderData M n (by omega : n ≥ 2) htb hns
        (godMoveConstruction_exists M n hn hdec htb hns),
      godMoveTargetTransportTarget
        (godMoveConstruction_exists M n hn hdec htb hns) := by
  rcases (godMoveConstruction_exists_placeholder_frontier_iff M n hn hdec htb hns).mp hfront with
    ⟨hcanon, hz⟩
  exact hz

/-- Conversely, once the missing zero-remainder/transport package is available,
the bundled identity placeholder frontier follows immediately because the
canonical half is already proved. -/
theorem godMoveConstruction_exists_placeholder_frontier_of_missing
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n)
    (hz : ∃ z : GodMoveZeroRemainderData M n (by omega : n ≥ 2) htb hns
        (godMoveConstruction_exists M n hn hdec htb hns),
      godMoveTargetTransportTarget
        (godMoveConstruction_exists M n hn hdec htb hns)) :
    godMoveConstruction_exists_placeholder_frontier M n hn hdec htb hns := by
  exact ⟨godMoveConstruction_exists_placeholder_frontier_canonical M n hn hdec htb hns, hz⟩

/-- Because the canonical half is already settled, the bundled identity
placeholder frontier is equivalent to the explicit zero-remainder/transport
existential bridge. This is the final honest packaging statement before trying
to construct that bridge. -/
theorem godMoveConstruction_exists_placeholder_frontier_iff_missing
    (M : DTM) (n : ℕ)
    (hn : n ≥ 2 ^ 804)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) :
    godMoveConstruction_exists_placeholder_frontier M n hn hdec htb hns ↔
      (∃ z : GodMoveZeroRemainderData M n (by omega : n ≥ 2) htb hns
          (godMoveConstruction_exists M n hn hdec htb hns),
        godMoveTargetTransportTarget
          (godMoveConstruction_exists M n hn hdec htb hns)) := by
  constructor
  · exact godMoveConstruction_exists_placeholder_frontier_missing M n hn hdec htb hns
  · exact godMoveConstruction_exists_placeholder_frontier_of_missing M n hn hdec htb hns

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
