import PallLean.CompiledGeneratorVerifierImage

/-!
# CompiledGeneratorPipeline

Assemble the verifier-side transport packaging with the compiled decomposition
(`fullCompiledPoly = verifierSheet + violationPoly`) at the subspace level.
-/

namespace CompiledGeneratorTransportFrontier

open CompiledAssemblyRoadmap
open LatentFullBridge LatentCompiler MultilinearSPDP NPWitness Compiler TuringMachine
open MvPolynomial SPDP

/-- Critical remaining obligation (isolated): raw rename/map transport inequality
for the violation branch. Once this is proved, `hViolMatches` rewrites the target
to `latentCompiledPoly` via `mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches`.
-/
axiom violation_branch_rename_transport_target
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyOf ℚ M n)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n)))


/-- Renamed-Tseitin branch transport into the latent map-image under the chosen
bridge map. (Current project staging keeps this as a target obligation while the
generator-to-subspace lift is under construction.) -/
axiom rename_branch_transport_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n))

/-- Bridge-direction recast: use `U : compiled → latent` first, proving renamed
witness/Tseitin generators land directly in the latent SPDP subspace. -/
def RenameBranchGlobalDomStyleU
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (U : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (latentNumVars M n)) ℚ) : Prop :=
  ∀ (S : List (Fin (npNumVars n)))
    (m : MvPolynomial (Fin (npNumVars n)) ℚ),
    S.length = Nat.log 2 n →
    m.totalDegree ≤ Nat.log 2 n →
    m.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le)) S →
    U ((MvPolynomial.rename (witnessInclusion M n h_le))
      (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n))))
      ∈ mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)

/-- Specialized target for the concrete bridge-direction map
`U = (mapFullToLatentPoly M n B).toLinearMap`.

This is the next semantic proof obligation requested in the chain. -/
axiom rename_branch_globalDomStyleU_for_bridgeMap
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) :
    RenameBranchGlobalDomStyleU M n h_le
      (mapFullToLatentPoly M n B).toLinearMap

/-- Separate transfer-back hypothesis: `T` is a right-inverse of `U` on the
latent SPDP subspace image used by the rename branch. -/
def HasTransferBackOnLatentSubspace
    (M : DTM) (n : ℕ)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (U : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (latentNumVars M n)) ℚ) : Prop :=
  ∀ r,
    r ∈ mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly M n) →
    U (T r) = r

/-- Sufficient condition for transfer-back on the latent branch subspace:
if `U ∘ T = id` globally on latent polynomials, then it holds in particular on
`mlBlockedSpdpSubspace ... (latentCompiledPoly)`. -/
theorem hasTransferBackOnLatentSubspace_of_leftInverse
    (M : DTM) (n : ℕ)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (U : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (latentNumVars M n)) ℚ)
    (hLeftInv : Function.LeftInverse U T) :
    HasTransferBackOnLatentSubspace M n T U := by
  intro r hr
  exact hLeftInv r

/-- Bridge-map specialization: if `T` is a global right-inverse of
`(mapFullToLatentPoly M n B).toLinearMap`, then the transfer-back condition used
by the rename-branch pipeline holds. -/
theorem hasTransferBackOnLatentSubspace_bridgeMap_of_leftInverse
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hLeftInv : Function.LeftInverse (mapFullToLatentPoly M n B).toLinearMap T) :
    HasTransferBackOnLatentSubspace M n T (mapFullToLatentPoly M n B).toLinearMap :=
  hasTransferBackOnLatentSubspace_of_leftInverse M n T
    (mapFullToLatentPoly M n B).toLinearMap hLeftInv

/-- Next crisp algebraic bridge target: prove global left-inverse for the
chosen reconstruction map `T` against the bridge map `mapFullToLatentPoly`. -/
axiom bridgeMap_leftInverse_target
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) :
    Function.LeftInverse (mapFullToLatentPoly M n B).toLinearMap T

/-- Concrete sufficient condition for the left-inverse target:
if `U.comp T = LinearMap.id`, then `U` is a left inverse of `T`. -/
theorem bridgeMap_leftInverse_of_comp_id
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hComp : (mapFullToLatentPoly M n B).toLinearMap.comp T = LinearMap.id) :
    Function.LeftInverse (mapFullToLatentPoly M n B).toLinearMap T := by
  intro r
  have := LinearMap.congr_fun hComp r
  simpa using this

/-- Next closure reduction: if the bridge-map composition identity holds,
then the staged bridge-map left-inverse target follows immediately. -/
theorem bridgeMap_leftInverse_target_of_comp_id
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hComp : (mapFullToLatentPoly M n B).toLinearMap.comp T = LinearMap.id) :
    Function.LeftInverse (mapFullToLatentPoly M n B).toLinearMap T :=
  bridgeMap_leftInverse_of_comp_id M n B T hComp

/-- Next algebraic target (fully explicit): prove the bridge composition
identity for the chosen reconstruction map `T`. -/
axiom bridgeMap_comp_id_target
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) :
    (mapFullToLatentPoly M n B).toLinearMap.comp T = LinearMap.id

/-- Intended concrete reconstruction map for the bridge route.
This is the `T` that should ultimately replace the abstract parameter in the
pipeline once constructed/proved from LatentFullBridge-side machinery.

Design skeleton: extend a latent polynomial back to full coordinates by choosing
a preimage on the bridge-image variables and sending off-image latent variables
to `0` at the full level. This remains staged until the concrete
inverse-on-image variable map is defined constructively in `LatentFullBridge`. -/
axiom bridgeReconstructionVarMap
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n) :
    Fin (latentNumVars M n) → MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ

axiom bridgeReconstructionMap
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n) :
    MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ

/-- Expected construction theorem: `bridgeReconstructionMap` is the `aeval`
linear map induced by the variable-level reconstruction assignment. -/
axiom bridgeReconstructionMap_def
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n) :
    bridgeReconstructionMap M n B =
      (MvPolynomial.aeval (bridgeReconstructionVarMap M n B)).toLinearMap

/-- Expected inverse-on-image behavior for reconstructed variables: after mapping
back down with `mapFullToLatentPoly`, bridge-image latent variables are fixed. -/
axiom bridgeReconstructionVarMap_retracts_on_image
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n) :
    ∀ i : Fin (latentNumVars M n),
      (mapFullToLatentPoly M n B).toLinearMap ((bridgeReconstructionVarMap M n B) i) =
        MvPolynomial.X i

/-- Expected global consequence on the bridge-image-generated latent algebra:
this is the theorem family from which generator retraction should be proved by
induction / `aeval` extensionality. -/
axiom bridgeReconstructionMap_retracts_on_generated_algebra
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n) :
    ∀ p : MvPolynomial (Fin (latentNumVars M n)) ℚ,
      (mapFullToLatentPoly M n B).toLinearMap ((bridgeReconstructionMap M n B) p) = p

/-- Corrected missing bridge theorem statement for the intended concrete `T`:
retraction identity on the relevant latent SPDP subspace (not globally). -/
axiom bridgeMap_retract_on_latentSubspace_for_bridgeReconstructionMap
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n) :
    HasTransferBackOnLatentSubspace M n (bridgeReconstructionMap M n B)
      (mapFullToLatentPoly M n B).toLinearMap

/-- Generator-level retraction target for the concrete reconstruction map:
prove `U(T(g)) = g` first on latent SPDP generators, then lift by span. -/
axiom bridgeReconstructionMap_retracts_latent_generator_target
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n) :
    ∀ (S : List (Fin (latentNumVars M n)))
      (m : MvPolynomial (Fin (latentNumVars M n)) ℚ),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible (latentPartition M n) S →
      (mapFullToLatentPoly M n B).toLinearMap
        ((bridgeReconstructionMap M n B)
          (mlProj (m * SPDP.iterDerivList S (latentCompiledPoly M n))))
      = mlProj (m * SPDP.iterDerivList S (latentCompiledPoly M n))

/-- Planned lift template: once generator-level retraction is proved for the
concrete reconstruction map, the restricted transfer-back law follows on the
entire latent SPDP subspace by `Submodule.span_le`. -/
axiom bridgeMap_retract_on_latentSubspace_for_bridgeReconstructionMap_of_generators
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n) :
    HasTransferBackOnLatentSubspace M n (bridgeReconstructionMap M n B)
      (mapFullToLatentPoly M n B).toLinearMap

/-- Immediate closure from the composition-identity target to the staged
left-inverse bridge target. -/
theorem bridgeMap_leftInverse_target_of_comp_id_target
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) :
    Function.LeftInverse (mapFullToLatentPoly M n B).toLinearMap T :=
  bridgeMap_leftInverse_target_of_comp_id M n B T
    (bridgeMap_comp_id_target M n B T)

/-- Concrete transfer-back for the intended reconstruction map (restricted
retraction form; this is the corrected target replacing global comp-id). -/
theorem hasTransferBack_for_bridgeReconstructionMap
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n) :
    HasTransferBackOnLatentSubspace M n (bridgeReconstructionMap M n B)
      (mapFullToLatentPoly M n B).toLinearMap :=
  bridgeMap_retract_on_latentSubspace_for_bridgeReconstructionMap M n B

axiom mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_leftInverse
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hLeftInv : Function.LeftInverse (mapFullToLatentPoly M n B).toLinearMap T)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n))

/-- Collapsed endpoint for the concrete reconstruction map, using the corrected
restricted transfer-back route. -/
axiom mlBlockedSpdpSubspace_fullCompiled_le_map_for_bridgeReconstructionMap
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map (bridgeReconstructionMap M n B)
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n))

/-- Closure endpoint instantiated from the isolated left-inverse target. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_leftInverse M n h_le B T
    (bridgeMap_leftInverse_target M n B T) hViolMatches

/-- Transfer-back lemma: once branch transport is proved in bridge direction
(`U`), and `T` is a right-inverse on the latent branch subspace, recover the
original `map T` branch target. -/
axiom rename_branch_transport_target_of_U
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (U : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (latentNumVars M n)) ℚ)
    (hU : RenameBranchGlobalDomStyleU M n h_le U)
    (hBack : HasTransferBackOnLatentSubspace M n T U) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n))

/-- Immediate bridge-map closure: once transfer-back holds for `(T,U)` with
`U = mapFullToLatentPoly.toLinearMap`, the rename-branch subspace transport
follows. -/
theorem rename_branch_transport_target_via_bridgeMapU
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hBack : HasTransferBackOnLatentSubspace M n T
      (mapFullToLatentPoly M n B).toLinearMap) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_of_U M n h_le T
    (mapFullToLatentPoly M n B).toLinearMap
    (rename_branch_globalDomStyleU_for_bridgeMap M n h_le B)
    hBack

/-- End-to-end staged closure through the bridge-direction `U` route:
if transfer-back holds on latent branch subspace and `hViolMatches` is given,
then full compiled subspace transport follows. -/
axiom mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hBack : HasTransferBackOnLatentSubspace M n T
      (mapFullToLatentPoly M n B).toLinearMap)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n))

/-- Semantic generator transport hypothesis package for the renamed
witness/Tseitin branch under a chosen bridge map `T`.

This is the concrete bridge property that must be proved to remove
`rename_branch_transport_target` as an axiom. -/
def RenameBranchSemanticTransport
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) : Prop :=
  ∀ (S : List (Fin (npNumVars n)))
    (m : MvPolynomial (Fin (npNumVars n)) ℚ),
    S.length = Nat.log 2 n →
    m.totalDegree ≤ Nat.log 2 n →
    m.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le)) S →
    (MvPolynomial.rename (witnessInclusion M n h_le))
      (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)))
      ∈ Submodule.map T
          (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
            (latentCompiledPoly M n))

/-- Specialized global-domination style hypothesis for a chosen bridge map `T`:
mapped rename-witness/Tseitin generators land in the latent mapped SPDP image. -/
def RenameBranchGlobalDomStyle
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) : Prop :=
  ∀ (S : List (Fin (npNumVars n)))
    (m : MvPolynomial (Fin (npNumVars n)) ℚ),
    S.length = Nat.log 2 n →
    m.totalDegree ≤ Nat.log 2 n →
    m.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le)) S →
    (MvPolynomial.rename (witnessInclusion M n h_le))
      (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)))
      ∈ Submodule.map T
          (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
            (latentCompiledPoly M n))

/-- Bridge-facing semantic lemma skeleton to prove next (independent of the
staged subspace target axiom), stated in the global-domination style. -/
axiom rename_branch_generator_transport_semantic
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) :
    RenameBranchGlobalDomStyle M n h_le T

/-- Convert the global-domination style statement into the semantic transport
package consumed by the branch pipeline. -/
theorem rename_branch_semantic_of_globalDomStyle
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hDom : RenameBranchGlobalDomStyle M n h_le T) :
    RenameBranchSemanticTransport M n h_le T := hDom

theorem rename_branch_generator_transport_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) :
    ∀ (S : List (Fin (npNumVars n)))
      (m : MvPolynomial (Fin (npNumVars n)) ℚ),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le)) S →
      (MvPolynomial.rename (witnessInclusion M n h_le))
        (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)))
        ∈ Submodule.map T
            (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
              (latentCompiledPoly M n)) := by
  intro S m hlen hdeg hvars hadm
  have hgen :
      mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)) ∈
        mlBlockedSpdpSubspace
          (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
          (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n) :=
    Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
  have hmap :
      (MvPolynomial.rename (witnessInclusion M n h_le))
        (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)))
      ∈ Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
          (mlBlockedSpdpSubspace
            (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
            (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n)) :=
    ⟨_, hgen, rfl⟩
  exact rename_branch_transport_target M n h_le T hmap

/-- Explicit missing-piece theorem shape (rename-witness branch transport).
Currently instantiated from the isolated target obligation above. -/
theorem map_rename_witness_tseitin_subspace_le_map_latent_subspace
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target M n h_le T

/-- Subspace-level decomposition through the compiled polynomial split, with the
verifier side already reduced to renamed Tseitin generators. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_rename_tseitin_sup_violation
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le) ≤
      Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
        (mlBlockedSpdpSubspace
          (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
          (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
      ⊔
      mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (violationPolyOf ℚ M n) := by
  -- First split fullCompiled into verifier + violation at subspace level.
  have hAdd :
      mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n h_le) ≤
      mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (verifierSheetOf ℚ M n h_le)
      ⊔
      mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (violationPolyOf ℚ M n) := by
    simpa [fullCompiledPoly] using
      (mlBlockedSpdpSubspace_add_le (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (verifierSheetOf ℚ M n h_le) (violationPolyOf ℚ M n))
  -- Then replace verifier subspace by the renamed Tseitin-side bound.
  have hVer :
      mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (verifierSheetOf ℚ M n h_le) ≤
      Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
        (mlBlockedSpdpSubspace
          (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
          (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n)) :=
    mlBlockedSpdpSubspace_verifier_le_rename_tseitin M n h_le
  have hSup :
      mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (verifierSheetOf ℚ M n h_le)
      ⊔
      mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (violationPolyOf ℚ M n) ≤
      Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
        (mlBlockedSpdpSubspace
          (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
          (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
      ⊔
      mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (violationPolyOf ℚ M n) := by
    exact sup_le (le_trans hVer le_sup_left) le_sup_right
  exact le_trans hAdd hSup

/-- Final branch-combination step: once
(1) renamed-Tseitin branch transports into the latent map-image and
(2) violation branch transports into the same latent map-image,
then the full compiled SPDP subspace transports into that latent map-image. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_of_branch_transports
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hRenameBranch :
      Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
        (mlBlockedSpdpSubspace
          (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
          (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
      ≤ Submodule.map T
          (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
            (latentCompiledPoly M n)))
    (hViolationBranch :
      mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (violationPolyOf ℚ M n)
      ≤ Submodule.map T
          (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
            (latentCompiledPoly M n))) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  have hSplit := mlBlockedSpdpSubspace_fullCompiled_le_rename_tseitin_sup_violation M n h_le
  have hSupToMap :
      Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
        (mlBlockedSpdpSubspace
          (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
          (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
      ⊔
      mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (violationPolyOf ℚ M n)
      ≤ Submodule.map T
          (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
            (latentCompiledPoly M n)) :=
    sup_le hRenameBranch hViolationBranch
  exact le_trans hSplit hSupToMap

/-- Violation-branch transport packaged in the bridge-facing form:
if a rename-transport lemma is available for the violation polynomial under the
chosen bridge map, then `hViolMatches` rewrites the target to
`latentCompiledPoly`. -/
theorem mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hRenameTransport :
      mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (violationPolyOf ℚ M n)
      ≤ Submodule.map T
          (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
            (MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n)))) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyOf ℚ M n)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  simpa [hViolMatches] using hRenameTransport

/-- Canonical packaged version using the isolated raw target axiom. -/
theorem mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches_target
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyOf ℚ M n)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches M n B T hViolMatches
    (violation_branch_rename_transport_target M n B T)

/-- Immediate post-target wiring: once the renamed-Tseitin branch transport is
supplied, the violation branch closes from `hViolMatches` + isolated target, and
therefore full compiled subspace transport follows. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_of_targets
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hRenameBranch :
      Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
        (mlBlockedSpdpSubspace
          (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
          (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
      ≤ Submodule.map T
          (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
            (latentCompiledPoly M n))) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  refine mlBlockedSpdpSubspace_fullCompiled_le_map_of_branch_transports M n h_le T hRenameBranch ?_
  exact mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches_target M n B T hViolMatches

/-- Fully staged closure: both branch transports are consumed from isolated
target obligations (`rename_branch_transport_target` and
`violation_branch_rename_transport_target` + `hViolMatches`). -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_of_staged_targets
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_fullCompiled_le_map_of_targets M n h_le B T hViolMatches
    (rename_branch_transport_target M n h_le T)

end CompiledGeneratorTransportFrontier
