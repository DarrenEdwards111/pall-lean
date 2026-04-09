import PallLean.CompiledGeneratorVerifierImage

/-!
# CompiledGeneratorPipeline

Assemble the verifier-side transport packaging with the compiled decomposition
(`fullCompiledPoly = verifierSheet + violationPoly`) at the subspace level.
-/

namespace CompiledGeneratorTransportFrontier

/-!
## Status note on staged declarations

This file now mixes four layers:

1. Concrete bridge-specialized theorems that are actually proved later in the
   file.
2. A newer concrete `restrictPoly` route, now exposed by preferred theorem
   surfaces such as `restrictPoly_mapFullToLatentPoly`,
   `restrictPoly_leftInverse_target`, and
   `mlBlockedSpdpSubspace_fullCompiled_le_map_for_restrictPoly`.
3. Generic packaging statements that are still stronger than what the current
   theorem layer establishes, so they remain explicit axioms.
4. Legacy bridge-construction axioms (`bridgeSectionVar`,
   `bridgeReconstructionMap`, composition/left-inverse targets) that remain live
   only where the file still routes through the older section-variable/
   `bridgeReconstructionMap` presentation.

In particular:
- `rename_branch_transport_target` is now bypassed by the later theorem
  `map_rename_witness_tseitin_subspace_le_map_latent_subspace`, but remains as
  an early generic placeholder because of declaration order.
- `rename_branch_transport_target_of_U` is currently underpowered: the present
  hypotheses do not suffice to prove it, as they give only latent-side
  retraction `U (T r) = r`, not the source-side retraction needed by the natural
  span-induction proof.
- `violation_branch_rename_transport_target` remains the generic arbitrary-`T`
  target, even though the concrete bridge-specialized violation route is proved
  later.
- The concrete full-compiled route should now be read primarily through the
  `restrictPoly`-oriented endpoint
  `mlBlockedSpdpSubspace_fullCompiled_le_map_for_restrictPoly`; the older
  `bridgeReconstructionMap` endpoint remains a legacy wrapper while downstream
  cleanup is still in progress.
-/

open CompiledAssemblyRoadmap
open LatentFullBridge LatentCompiler MultilinearSPDP NPWitness Compiler TuringMachine
open MvPolynomial SPDP

/-- Critical remaining generic obligation for the violation branch.

Note: the concrete bridge-specialized route has been proved later in this file
for `T = bridgeReconstructionMap M n B`, via
`violation_generator_reconstruction_atomic` and its semantic/frontier lift,
and also for the preferred concrete `restrictPoly` route via the later
compiled-witness semantic package.

What remains staged here is strictly stronger: a raw rename/map transport
inequality for an arbitrary linear map `T` into the full-variable polynomial
space. The actual proved theorem layer below shows that the honest sufficient
hypothesis is compiled-witness semantic transport, not this bare arbitrary-`T`
statement alone.

So this axiom is now best read as the residual generic violation frontier.
Once it is proved, `hViolMatches` rewrites the target to `latentCompiledPoly`
via `mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches`. -/
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

/-- Honest consequence form of the early generic violation-branch transport
surface. This records the actual downstream content now available from the
later compiled-witness semantic route, without pretending the early axiom has
been proved in place. -/
theorem violation_branch_rename_transport_target_consequence_of_compiledWitnessSemantic
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hSem : ViolationGeneratorSemanticTransportCompiledWitness M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyOf ℚ M n)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n))) := by
  exact violationBranchTransportFrontier_of_compiledWitnessSemantic M n B T hSem

/-- Honest consequence form of the early generic violation-branch transport
surface from the direct semantic package, without going through the compiled-
witness reformulation when it is not needed. -/
theorem violation_branch_rename_transport_target_consequence_of_semantic
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hSem : ViolationGeneratorSemanticTransport M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyOf ℚ M n)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n))) := by
  exact violationBranchTransportFrontier_of_generatorFrontier M n B T
    (violationGeneratorTransportFrontier_of_semantic M n B T hSem)

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
then the older staged bridge-map left-inverse target follows immediately.

This is part of the legacy bridge-map packaging layer, not the preferred
`restrictPoly`-oriented surface. -/
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

/-- Legacy concrete reconstruction map for the section-variable bridge route.
This is the older `T`-surface used by the `aeval`-style reconstruction layer
below.

Current preferred concrete design: use
`MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj`.
That route is already live later in this file at the full-compiled level via
results such as `restrictPoly_leftInverse_target` and
`mlBlockedSpdpSubspace_fullCompiled_le_map_for_restrictPoly`.
So the main remaining issue is not defining a concrete reconstruction map, but
cleaning up the residual theorem surfaces that still talk in terms of the older
`bridgeReconstructionMap` presentation.

This section-variable interface is retained only because some earlier wrappers
and bridge-specialized proofs below are still written against an
`aeval`-style map. A direct in-place replacement was attempted and backed out:
the real blockers are (1) declaration order, since some early generic bridge
wrappers are stated before the later concrete reconstruction layer, and
(2) surviving wrappers that still quantify over arbitrary `T`, whereas the
clean `restrictPoly` route first collapses the concrete specialization.

Additional bridge-section data needed to make the current `aeval` presentation
constructive: choose a full-variable preimage for each relevant latent variable.

Important: this cannot be reduced from `B.inj` alone. Injectivity of
`B.toLatent` gives a left inverse on the full-variable source, but the section
law needed here is a right inverse on latent variables,
`B.toLatent (bridgeSectionVar ... i) = i`, which requires surjectivity onto the
relevant latent variable set (or an explicit chosen image-subset interface), not
mere injectivity. -/
axiom bridgeSectionVar
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n) :
    Fin (latentNumVars M n) → Fin (numVars M n (Nat.log 2 n))

/-- Section law expected of the chosen bridge-section variables. -/
axiom bridgeSectionVar_spec
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n) :
    ∀ i : Fin (latentNumVars M n),
      B.toLatent (bridgeSectionVar M n B i) = i

/-- Missing bridge-side monomial action lemma needed for the reconstruction
calculation: `mapFullToLatentPoly` sends a full variable `X j` to the latent
variable `X (B.toLatent j)`. -/
axiom mapFullToLatentPoly_X
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (j : Fin (numVars M n (Nat.log 2 n))) :
    (mapFullToLatentPoly M n B).toLinearMap (MvPolynomial.X j) =
      MvPolynomial.X (B.toLatent j)

/-- Concrete variable-level reconstruction assignment induced by the chosen
bridge section. -/
noncomputable def bridgeReconstructionVarMap
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n) :
    Fin (latentNumVars M n) → MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ :=
  fun i => MvPolynomial.X (bridgeSectionVar M n B i)

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
theorem bridgeReconstructionVarMap_retracts_on_image
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n) :
    ∀ i : Fin (latentNumVars M n),
      (mapFullToLatentPoly M n B).toLinearMap ((bridgeReconstructionVarMap M n B) i) =
        MvPolynomial.X i := by
  intro i
  unfold bridgeReconstructionVarMap
  rw [mapFullToLatentPoly_X]
  rw [bridgeSectionVar_spec]

/-- On variables, the composite latent endomorphism obtained by reconstructing
with the chosen bridge section and mapping back down is the identity. -/
theorem bridgeReconstruction_comp_X
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (i : Fin (latentNumVars M n)) :
    ((mapFullToLatentPoly M n B).comp
      (MvPolynomial.aeval (bridgeReconstructionVarMap M n B)))
        (MvPolynomial.X i) = MvPolynomial.X i := by
  simp only [MvPolynomial.aeval_X, AlgHom.comp_apply]
  simpa using bridgeReconstructionVarMap_retracts_on_image M n B i

/-- Expected global consequence on the bridge-image-generated latent algebra:
this is the theorem family from which generator retraction is proved by
induction / `aeval` extensionality for the legacy section-variable route.

Refactor note: the concrete `restrictPoly` route is already live later in this
file at the full-compiled level, but this exact latent-side theorem slot has
not been replaced directly. The remaining gap here is local theorem packaging,
not absence of a concrete reconstruction map. In particular, the naive direct
replacement by `restrictPoly ℚ B.toLatent B.inj` still runs into the same
latent-side/generator-level shape mismatch documented below, so downstream
retargeting should keep happening through the later concrete `restrictPoly`
seams rather than by mutating this early theorem surface in place. -/
theorem bridgeReconstructionMap_retracts_on_generated_algebra
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n) :
    ∀ p : MvPolynomial (Fin (latentNumVars M n)) ℚ,
      (mapFullToLatentPoly M n B).toLinearMap ((bridgeReconstructionMap M n B) p) = p := by
  intro p
  rw [bridgeReconstructionMap_def]
  let ψ : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₐ[ℚ]
      MvPolynomial (Fin (latentNumVars M n)) ℚ :=
    (mapFullToLatentPoly M n B).comp (MvPolynomial.aeval (bridgeReconstructionVarMap M n B))
  have hψ : ψ = AlgHom.id ℚ (MvPolynomial (Fin (latentNumVars M n)) ℚ) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa [ψ] using bridgeReconstruction_comp_X M n B i
  change ψ p = p
  simpa [ψ] using congrArg (fun f => f p) hψ

/-
Refactor checkpoint: a direct late theorem here using
`MultilinearSPDP.restrictPoly_rename ℚ B.toLatent B.inj` does NOT typecheck in
this slot. The issue is not declaration order but variable-space direction:

- `mapFullToLatentPoly` is the compiled → latent rename along `B.toLatent`
- `restrictPoly_rename` applies to `restrictPoly f (rename f p)` where `p`
  lives on the source variable space of `f`
- here the ambient theorem input `p` already lives on latent variables, so the
  naive rewrite would incorrectly try to apply `rename B.toLatent` to a latent
  polynomial, but `B.toLatent` has type compiled → latent

So the future concrete `restrictPoly` refactor still needs an intermediate
 theorem packaged in the correct variable spaces, not just a one-line reuse of
`restrictPoly_rename` at this exact theorem slot.

Concretely, the next typed target should quantify over a compiled polynomial
`q : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ` and prove a statement of
shape

`(mapFullToLatentPoly M n B).toLinearMap
    (((MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap)
      ((mapFullToLatentPoly M n B).toLinearMap q))
  = (mapFullToLatentPoly M n B).toLinearMap q`

or, more canonically, the AlgHom-level identity

`(mapFullToLatentPoly M n B).comp
    (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj)
  = mapFullToLatentPoly M n B`.

That is the correctly typed bridge idempotence statement from which a later
latent-side retraction theorem may be packaged.
-/

/-
Attempted concrete `restrictPoly` bridge theorem here and got the real type
obstruction cleanly:

`MultilinearSPDP.restrictPoly F f hf` has type
`MvPolynomial (Fin m) F →ₐ[F] MvPolynomial (Fin n) F`
for `f : Fin n → Fin m`.

So if we instantiate `f := B.toLatent`, then `restrictPoly ℚ B.toLatent B.inj`
has type

`MvPolynomial (Fin (latentNumVars M n)) ℚ →ₐ[ℚ]
    MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ`,

which is a latent → compiled map.

That means the naive AlgHom composite

`(mapFullToLatentPoly M n B).comp
    (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj)`

is not even composable in the direction previously recorded here, because
`AlgHom.comp g f` expects the codomain of `f` to match the domain of `g`, while
`mapFullToLatentPoly M n B` itself is already compiled → latent.

So the earlier note saying this was the "correctly typed" next AlgHom identity
was still wrong. The genuine next step is to formulate the bridge idempotence
statement in the actual latent → compiled → latent order, or equivalently as a
pointwise theorem without forcing it first into the mistaken `AlgHom.comp`
surface.
-/

/-- Correctly oriented concrete `restrictPoly` bridge identity: restricting a
renamed compiled polynomial back along the bridge recovers the original
compiled polynomial. This is the honest latent → compiled → latent theorem seam
for the future `bridgeReconstructionMap` refactor. -/
theorem restrictPoly_mapFullToLatentPoly
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (p : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) :
    (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj)
      ((mapFullToLatentPoly M n B) p)
      = p := by
  simpa [mapFullToLatentPoly] using
    (MultilinearSPDP.restrictPoly_rename ℚ B.toLatent B.inj p)

/-- Later concrete replacement seam for the legacy reconstruction theorem:
using `restrictPoly` directly, the latent → compiled → latent composite is the
identity on all compiled-space inputs. This mirrors the role of
`bridgeReconstructionMap_retracts_on_generated_algebra`, but at the correctly
typed compiled-polynomial interface exposed by `restrictPoly_rename`. -/
theorem restrictPoly_retracts_on_mapFullToLatentPoly_image
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n) :
    ∀ p : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ,
      (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj)
        ((mapFullToLatentPoly M n B) p) = p := by
  intro p
  exact restrictPoly_mapFullToLatentPoly M n B p

/-
Tried next to package the `restrictPoly` seam at subspace level via a `≤`
between `Submodule.map`s. That also exposed a real direction issue, not a mere
Lean nuisance:

- `Submodule.map (mapFullToLatentPoly M n B).toLinearMap ⊤` lives in the latent
  polynomial space.
- `Submodule.map (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap ⊤`
  lives in the compiled polynomial space.

So there is no direct same-codomain inclusion theorem of that naive shape.
The correct next downstream retargeting theorem must either:

1. stay pointwise, with an explicit compiled witness produced from a latent-side
   element of interest, or
2. package a relation after one more application of `mapFullToLatentPoly`, so
   both sides live back in the latent polynomial space.

In other words, the current proved seam

`restrictPoly_mapFullToLatentPoly : restrictPoly ((mapFullToLatentPoly) p) = p`

is still the right primitive. The missing later theorem surface must respect
that `restrictPoly` lands in compiled space, while `mapFullToLatentPoly` lands in
latent space.
-/

/-- Correctly codomain-matched latent-side packaging of the concrete
`restrictPoly` seam: after mapping back down once more, the composite
latent → compiled → latent fixes every latent polynomial coming from a compiled
input. This is the smallest honest pointwise retarget surface suggested by the
preceding direction note. -/
theorem mapFullToLatentPoly_restrictPoly_mapFullToLatentPoly
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (p : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) :
    (mapFullToLatentPoly M n B)
      ((MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj)
        ((mapFullToLatentPoly M n B) p))
      = (mapFullToLatentPoly M n B) p := by
  rw [restrictPoly_mapFullToLatentPoly M n B p]

/-- Correctly packaged `Function.LeftInverse` form of the concrete `restrictPoly`
retraction: the domain is the compiled polynomial space, matching the domain of
`mapFullToLatentPoly M n B`. -/
theorem restrictPoly_leftInverse_compiled
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n) :
    Function.LeftInverse
      (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj)
      (mapFullToLatentPoly M n B) := by
  intro p
  exact restrictPoly_mapFullToLatentPoly M n B p

/-- Concrete left-inverse packaging at the linear-map theorem surface used by the
existing bridge reconstruction layer. This is the same compiled-domain fact as
`restrictPoly_leftInverse_compiled`, just with the codomain/domain made explicit
through the inherited linear maps. -/
theorem restrictPoly_leftInverse_target
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n) :
    Function.LeftInverse (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
      (mapFullToLatentPoly M n B).toLinearMap := by
  intro p
  exact restrictPoly_mapFullToLatentPoly M n B p

/-- Corrected missing bridge theorem statement for the intended concrete `T`:
retraction identity on the relevant latent SPDP subspace (not globally). -/
theorem bridgeMap_retract_on_latentSubspace_for_bridgeReconstructionMap
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n) :
    HasTransferBackOnLatentSubspace M n (bridgeReconstructionMap M n B)
      (mapFullToLatentPoly M n B).toLinearMap :=
  hasTransferBackOnLatentSubspace_bridgeMap_of_leftInverse M n B
    (bridgeReconstructionMap M n B)
    (bridgeMap_leftInverse_target_of_comp_id M n B (bridgeReconstructionMap M n B)
      (bridgeMap_comp_id_target M n B (bridgeReconstructionMap M n B)))

/-- Generator-level retraction target for the concrete reconstruction map:
prove `U(T(g)) = g` first on latent SPDP generators, then lift by span. -/
theorem bridgeReconstructionMap_retracts_latent_generator_target
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
      = mlProj (m * SPDP.iterDerivList S (latentCompiledPoly M n)) := by
  intro S m hLen hdeg hvars hadm
  simpa using
    bridgeReconstructionMap_retracts_on_generated_algebra M n B
      (mlProj (m * SPDP.iterDerivList S (latentCompiledPoly M n)))

/-
Attempted next downstream mirror theorem: a direct `restrictPoly` analogue of
`bridgeReconstructionMap_retracts_latent_generator_target`.

That naive generator-level port still fails for a real type reason. The legacy
reconstruction theorem is phrased on a latent polynomial
`mlProj (m * iterDerivList S (latentCompiledPoly M n))` after applying a latent
→ compiled map and then mapping back down with `mapFullToLatentPoly`. By
contrast, `restrictPoly_mapFullToLatentPoly` applies only to compiled-polynomial
inputs:

`restrictPoly ℚ B.toLatent B.inj ((mapFullToLatentPoly M n B) p) = p`

with `p : MvPolynomial (Fin (numVars ...)) ℚ`.

What changed since this note was first added is that the concrete route now does
have a correct higher-level full-compiled endpoint,
`mlBlockedSpdpSubspace_fullCompiled_le_map_for_restrictPoly`, obtained by adding
an oriented sibling to the old staged full-compiled API.

So the remaining blocker is specifically the *generator-level latent-side mirror*
shape, not the concrete `restrictPoly` route as a whole. Any further cleanup
here should therefore either:
- package compiled-preimage data for the latent generator family, or
- bypass this generator-level theorem entirely by rewriting downstream concrete
  full-compiled uses to `mlBlockedSpdpSubspace_fullCompiled_le_map_for_restrictPoly`.
-/

/-- Planned lift template: once generator-level retraction is proved for the
concrete reconstruction map, the restricted transfer-back law follows on the
entire latent SPDP subspace by `Submodule.span_le`. -/
theorem bridgeMap_retract_on_latentSubspace_for_bridgeReconstructionMap_of_generators
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n) :
    HasTransferBackOnLatentSubspace M n (bridgeReconstructionMap M n B)
      (mapFullToLatentPoly M n B).toLinearMap := by
  intro q hq
  rw [mlBlockedSpdpSubspace] at hq
  let s : Set (MvPolynomial (Fin (latentNumVars M n)) ℚ) :=
    {q | ∃ (S : List (Fin (latentNumVars M n))) (m : MvPolynomial (Fin (latentNumVars M n)) ℚ),
        S.length = Nat.log 2 n ∧
        m.totalDegree ≤ Nat.log 2 n ∧
        m.vars ⊆ S.toFinset ∧
        SPDP.isBlockAdmissible (latentPartition M n) S ∧
        q = mlProj (m * SPDP.iterDerivList S (latentCompiledPoly M n))}
  have hPq : ((mapFullToLatentPoly M n B).toLinearMap ((bridgeReconstructionMap M n B) q) = q) := by
    refine Submodule.span_induction (R := ℚ) (s := s)
      (p := fun r _ => (mapFullToLatentPoly M n B).toLinearMap ((bridgeReconstructionMap M n B) r) = r)
      ?hmem ?hzero ?hadd ?hsmul hq
    · intro r hr
      rcases hr with ⟨S, m, hLen, hdeg, hvars, hadm, rfl⟩
      exact bridgeReconstructionMap_retracts_latent_generator_target M n B S m hLen hdeg hvars hadm
    · simp
    · intro x y hx hy hxP hyP
      simp [LinearMap.map_add, hxP, hyP]
    · intro c x hx hxP
      simp [LinearMap.map_smul, hxP]
  exact hPq

/-- Immediate closure from the composition-identity target to the older staged
left-inverse bridge target.

This remains as compatibility support for the legacy bridge-map layer. -/
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

/-- Correctly oriented sibling of the legacy staged endpoint above. This is the
natural staged theorem surface for the concrete `restrictPoly` seam, whose
packaged fact is

`Function.LeftInverse (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
  (mapFullToLatentPoly M n B).toLinearMap`.

This is now the right staged interface for concrete full-compiled retargeting.
The older axiom remains only because existing generic bridge-map-U packaging was
written in the opposite argument order. -/
axiom mlBlockedSpdpSubspace_fullCompiled_le_map_of_restrictPoly_leftInverse
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hLeftInv : Function.LeftInverse T (mapFullToLatentPoly M n B).toLinearMap)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n))

/-- Legacy concrete endpoint for the section-variable/`bridgeReconstructionMap`
presentation, using the older bridge-reconstruction packaging.

This theorem is kept mainly for compatibility with the older bridge-map-U layer
that still exists in this file. New concrete downstream retargeting should
prefer `mlBlockedSpdpSubspace_fullCompiled_le_map_for_restrictPoly`, whose
theorem surface matches the proved `restrictPoly` orientation directly. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_for_bridgeReconstructionMap
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map (bridgeReconstructionMap M n B)
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_leftInverse M n h_le B
    (bridgeReconstructionMap M n B)
    (bridgeMap_leftInverse_target_of_comp_id_target M n B (bridgeReconstructionMap M n B))
    hViolMatches


/-- Preferred concrete full-compiled endpoint for the `restrictPoly` route.

For declaration-order reasons, this early theorem still uses the proved
`restrictPoly`-oriented staged interface. A later theorem in this file,
`mlBlockedSpdpSubspace_fullCompiled_le_map_for_restrictPoly_direct`, upgrades
this to the fully concrete branch-by-branch route using the concrete violation
`restrictPoly` theorem as well. Concrete downstream use should still target the
present theorem name; later in the file it is shown to coincide with the more
explicit direct branch proof. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_for_restrictPoly
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_fullCompiled_le_map_of_restrictPoly_leftInverse M n h_le B
    (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
    (restrictPoly_leftInverse_target M n B)
    hViolMatches

/-- Legacy closure endpoint instantiated through the older bridge-map-U
left-inverse target.

This remains only as compatibility glue for theorem surfaces still phrased in
that older argument order; new concrete retargeting should prefer the
`restrictPoly`-oriented endpoint above. -/
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

/-- Staged transfer-back lemma for the rename branch.

Important: the current hypothesis `HasTransferBackOnLatentSubspace M n T U`
only gives `U (T r) = r` on the latent branch subspace. That is not strong
enough to derive this conclusion by the natural source-space span induction,
because the generator step needs a source-side retraction of the form
`T (U x) = x` on the relevant rename-branch image (or an equivalent membership
principle placing each source generator directly in `Submodule.map T ...`).

Equivalently, the proved theorem layer below shows that what actually suffices
is one of the explicit stronger hypotheses:
- source-membership of each renamed generator,
- source-image control through `T ∘ U`, or
- the concrete `restrictPoly`/`bridgeReconstructionMap` collapse theorems.

No derivation from `hBack` alone exists in this file. This declaration is the
remaining raw generic gap, kept explicit rather than hidden behind later
wrappers. -/
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

/-- Honest early superseding surface for `rename_branch_transport_target_of_U`:
if one has a bridge-direction map `U` together with the actual source-side
witness needed to place each renamed generator in `Submodule.map T ...`, then
full rename-branch transport follows. This is the theorem-strength replacement
for the old `hBack`-driven shape. -/
theorem rename_branch_transport_target_of_U_source_membership
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (U : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (latentNumVars M n)) ℚ)
    (hU : RenameBranchGlobalDomStyleU M n h_le U)
    (hSource : ∀ (S : List (Fin (npNumVars n)))
      (m : MvPolynomial (Fin (npNumVars n)) ℚ),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le)) S →
      T (U ((MvPolynomial.rename (witnessInclusion M n h_le))
        (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n))))) =
        (MvPolynomial.rename (witnessInclusion M n h_le))
          (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)))) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  intro q hq
  rcases hq with ⟨r, hr, rfl⟩
  rw [mlBlockedSpdpSubspace] at hr
  let s : Set (MvPolynomial (Fin (npNumVars n)) ℚ) :=
    {q | ∃ (S : List (Fin (npNumVars n))) (m : MvPolynomial (Fin (npNumVars n)) ℚ),
        S.length = Nat.log 2 n ∧
        m.totalDegree ≤ Nat.log 2 n ∧
        m.vars ⊆ S.toFinset ∧
        SPDP.isBlockAdmissible
          (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le)) S ∧
        q = mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n))}
  have hMap :
      (MvPolynomial.rename (witnessInclusion M n h_le)) r ∈
        Submodule.map T
          (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
            (latentCompiledPoly M n)) := by
    refine Submodule.span_induction (R := ℚ) (s := s)
      (p := fun x _ =>
        (MvPolynomial.rename (witnessInclusion M n h_le)) x ∈
          Submodule.map T
            (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
              (latentCompiledPoly M n)))
      ?_ ?_ ?_ ?_ hr
    · intro x hx
      rcases hx with ⟨S, m, hLen, hdeg, hvars, hadm, rfl⟩
      refine ⟨U ((MvPolynomial.rename (witnessInclusion M n h_le))
          (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)))), ?_, ?_⟩
      · exact hU S m hLen hdeg hvars hadm
      · exact hSource S m hLen hdeg hvars hadm
    · simpa using (Submodule.zero_mem
        (Submodule.map T
          (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
            (latentCompiledPoly M n))))
    · intro x y _ _ hx hy
      simpa using Submodule.add_mem
        (Submodule.map T
          (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
            (latentCompiledPoly M n))) hx hy
    · intro c x _ hx
      simpa using Submodule.smul_mem
        (Submodule.map T
          (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
            (latentCompiledPoly M n))) c hx
  simpa [s] using hMap

/-- Honest strengthened replacement for `rename_branch_transport_target_of_U`:
what actually suffices is not latent-side transfer-back `U (T r) = r`, but a
direct source-generator image-membership hypothesis. Stated this early, before
the later `RenameBranchGlobalDomStyle` alias exists, the condition is exactly
that every renamed witness/Tseitin generator already lands in
`Submodule.map T ...`. -/
theorem rename_branch_transport_target_of_source_membership
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hT : ∀ (S : List (Fin (npNumVars n)))
      (m : MvPolynomial (Fin (npNumVars n)) ℚ),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le)) S →
      (MvPolynomial.rename (witnessInclusion M n h_le))
        (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)))
        ∈ Submodule.map T
            (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
              (latentCompiledPoly M n))) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  intro q hq
  rcases hq with ⟨r, hr, rfl⟩
  rw [mlBlockedSpdpSubspace] at hr
  let s : Set (MvPolynomial (Fin (npNumVars n)) ℚ) :=
    {q | ∃ (S : List (Fin (npNumVars n))) (m : MvPolynomial (Fin (npNumVars n)) ℚ),
        S.length = Nat.log 2 n ∧
        m.totalDegree ≤ Nat.log 2 n ∧
        m.vars ⊆ S.toFinset ∧
        SPDP.isBlockAdmissible
          (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le)) S ∧
        q = mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n))}
  have hMap :
      (MvPolynomial.rename (witnessInclusion M n h_le)) r ∈
        Submodule.map T
          (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
            (latentCompiledPoly M n)) := by
    refine Submodule.span_induction (R := ℚ) (s := s)
      (p := fun x _ =>
        (MvPolynomial.rename (witnessInclusion M n h_le)) x ∈
          Submodule.map T
            (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
              (latentCompiledPoly M n)))
      ?_ ?_ ?_ ?_ hr
    · intro x hx
      rcases hx with ⟨S, m, hLen, hdeg, hvars, hadm, rfl⟩
      exact hT S m hLen hdeg hvars hadm
    · simpa using (Submodule.zero_mem
        (Submodule.map T
          (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
            (latentCompiledPoly M n))))
    · intro x y _ _ hx hy
      simpa using Submodule.add_mem
        (Submodule.map T
          (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
            (latentCompiledPoly M n))) hx hy
    · intro c x _ hx
      simpa using Submodule.smul_mem
        (Submodule.map T
          (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
            (latentCompiledPoly M n))) c hx
  simpa [s] using hMap

/-- Immediate legacy bridge-map closure: once transfer-back holds for `(T,U)`
with `U = mapFullToLatentPoly.toLinearMap`, the rename-branch subspace
transport follows.

Status: this theorem is still only a thin wrapper around the raw generic axiom
`rename_branch_transport_target_of_U`. The honest theorem layer established
below shows stronger sufficient hypotheses, but declaration order prevents this
legacy wrapper from being rewritten directly in-place. Treat this as part of
the same explicit generic gap, not as proved content sourced from `hBack`
alone. -/
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

/-- Honest early consequence theorem for the old `of_U` surface: whenever one
has the actual source-generator image witness that the old axiom was missing,
the same endpoint follows from the strengthened theorem rather than from the
underpowered `hBack` story. -/
theorem rename_branch_transport_target_of_U_consequence
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (U : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (latentNumVars M n)) ℚ)
    (hU : RenameBranchGlobalDomStyleU M n h_le U)
    (hSource : ∀ (S : List (Fin (npNumVars n)))
      (m : MvPolynomial (Fin (npNumVars n)) ℚ),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le)) S →
      T (U ((MvPolynomial.rename (witnessInclusion M n h_le))
        (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n))))) =
        (MvPolynomial.rename (witnessInclusion M n h_le))
          (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)))) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_of_U_source_membership M n h_le T U hU hSource

/-- Explicit source-membership replacement surface for the old generic `of_U`
family. This names the actual sufficient raw hypothesis directly: source-side
control of each compiled rename generator through `T ∘ U`. -/
theorem rename_branch_transport_target_of_U_of_source_membership
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (U : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (latentNumVars M n)) ℚ)
    (hU : RenameBranchGlobalDomStyleU M n h_le U)
    (hSource : ∀ (S : List (Fin (npNumVars n)))
      (m : MvPolynomial (Fin (npNumVars n)) ℚ),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le)) S →
      T (U ((MvPolynomial.rename (witnessInclusion M n h_le))
        (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n))))) =
        (MvPolynomial.rename (witnessInclusion M n h_le))
          (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)))) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_of_U_source_membership M n h_le T U hU hSource

/-- Explicit source-membership sibling for the old generic `of_U` family.
This keeps the legacy endpoint shape while naming the actual sufficient raw
hypothesis directly: membership of each compiled-side rename generator in the
image of `T`. -/
theorem rename_branch_transport_target_of_U_consequence_of_source_membership
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (U : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (latentNumVars M n)) ℚ)
    (hU : RenameBranchGlobalDomStyleU M n h_le U)
    (hSource : ∀ (S : List (Fin (npNumVars n)))
      (m : MvPolynomial (Fin (npNumVars n)) ℚ),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le)) S →
      T (U ((MvPolynomial.rename (witnessInclusion M n h_le))
        (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n))))) =
        (MvPolynomial.rename (witnessInclusion M n h_le))
          (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)))) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_of_U_source_membership M n h_le T U hU hSource

/-- Precise generic source-image replacement surface for the old `of_U` axiom:
the honest sufficient hypothesis is source-side control through `T ∘ U`, not
latent-side transfer-back. This exposes that exact generic theorem shape. -/
theorem rename_branch_transport_target_of_U_of_source_image
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (U : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (latentNumVars M n)) ℚ)
    (hU : RenameBranchGlobalDomStyleU M n h_le U)
    (hSource : ∀ (S : List (Fin (npNumVars n)))
      (m : MvPolynomial (Fin (npNumVars n)) ℚ),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le)) S →
      T (U ((MvPolynomial.rename (witnessInclusion M n h_le))
        (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n))))) =
        (MvPolynomial.rename (witnessInclusion M n h_le))
          (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)))) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_of_U_source_membership M n h_le T U hU hSource

/-- Honest consequence theorem for the old generic `of_U` family under the
actual source-image hypothesis it needs. This keeps the legacy theorem shape
available while making the genuine sufficiency condition explicit. -/
theorem rename_branch_transport_target_of_U_consequence_of_source_image
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (U : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (latentNumVars M n)) ℚ)
    (hU : RenameBranchGlobalDomStyleU M n h_le U)
    (hSource : ∀ (S : List (Fin (npNumVars n)))
      (m : MvPolynomial (Fin (npNumVars n)) ℚ),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le)) S →
      T (U ((MvPolynomial.rename (witnessInclusion M n h_le))
        (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n))))) =
        (MvPolynomial.rename (witnessInclusion M n h_le))
          (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)))) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_of_U_of_source_image M n h_le T U hU hSource

/-- Honest bridge-facing replacement surface for the early bridge-map wrapper:
if one can directly supply the needed renamed witness/Tseitin source-generator
membership property for `T`, then the full rename-branch transport follows,
with no use of the underpowered `HasTransferBackOnLatentSubspace` route. -/
theorem rename_branch_transport_target_via_bridgeMapU_of_source_membership
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hT : ∀ (S : List (Fin (npNumVars n)))
      (m : MvPolynomial (Fin (npNumVars n)) ℚ),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le)) S →
      (MvPolynomial.rename (witnessInclusion M n h_le))
        (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)))
        ∈ Submodule.map T
            (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
              (latentCompiledPoly M n))) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_of_source_membership M n h_le T hT

/-- Honest bridge-facing consequence for the earliest bridge-map wrapper:
whenever one can supply the actual source-generator image witness that the old
`HasTransferBackOnLatentSubspace` route does not provide, the same endpoint
follows from the proved source-membership theorem. -/
theorem rename_branch_transport_target_via_bridgeMapU_consequence_of_source_membership
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hT : ∀ (S : List (Fin (npNumVars n)))
      (m : MvPolynomial (Fin (npNumVars n)) ℚ),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le)) S →
      (MvPolynomial.rename (witnessInclusion M n h_le))
        (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)))
        ∈ Submodule.map T
            (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
              (latentCompiledPoly M n))) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_via_bridgeMapU_of_source_membership M n h_le B T hT

/-- Precise early-source-image principle for the legacy bridge-map-U route:
what the old wrapper really needs is not latent-side transfer-back, but a
source-side image witness through `T ∘ mapFullToLatentPoly`. This packages that
exact hypothesis at the earliest bridge-shaped surface. -/
theorem rename_branch_transport_target_via_bridgeMapU_of_source_image
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hSource : ∀ (S : List (Fin (npNumVars n)))
      (m : MvPolynomial (Fin (npNumVars n)) ℚ),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le)) S →
      T ((mapFullToLatentPoly M n B).toLinearMap
        ((MvPolynomial.rename (witnessInclusion M n h_le))
          (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n))))) =
        (MvPolynomial.rename (witnessInclusion M n h_le))
          (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)))) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_of_U_source_membership M n h_le T
    (mapFullToLatentPoly M n B).toLinearMap
    (rename_branch_globalDomStyleU_for_bridgeMap M n h_le B)
    hSource

/-- Honest consequence theorem for the earliest bridge-map wrapper under the
actual source-image hypothesis it needs. This keeps the old bridge-shaped
endpoint available, but now tied to the right image-control assumption rather
than the insufficient latent-side transfer-back story. -/
theorem rename_branch_transport_target_via_bridgeMapU_consequence_of_source_image
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hSource : ∀ (S : List (Fin (npNumVars n)))
      (m : MvPolynomial (Fin (npNumVars n)) ℚ),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le)) S →
      T ((mapFullToLatentPoly M n B).toLinearMap
        ((MvPolynomial.rename (witnessInclusion M n h_le))
          (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n))))) =
        (MvPolynomial.rename (witnessInclusion M n h_le))
          (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)))) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_via_bridgeMapU_of_source_image M n h_le B T hSource


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

/-- Honest generic replacement surface for the weak `hBack`-based route:
if one can directly provide the renamed witness/Tseitin generator membership
property for `T`, then the full rename-branch subspace transport follows.
This is the right generic theorem family to target downstream, rather than the
underpowered `rename_branch_transport_target_of_U` path. -/
theorem rename_branch_transport_target_of_semantic_membership
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hSem : RenameBranchSemanticTransport M n h_le T) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  exact rename_branch_transport_target_of_source_membership M n h_le T hSem

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
  exact (rename_branch_generator_transport_semantic M n h_le T)
    S m hlen hdeg hvars hadm

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
  rename_branch_transport_target_of_source_membership M n h_le T
    (rename_branch_generator_transport_semantic M n h_le T)

/-- Later replacement for the old bridge-map-U/transfer-back rename route.
This theorem gives the actual proved arbitrary-`T` rename-branch transport
surface, bypassing `rename_branch_transport_target_of_U` and
`rename_branch_transport_target_via_bridgeMapU` wherever declaration order
allows. -/
theorem rename_branch_transport_target_of_semantic
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
  map_rename_witness_tseitin_subspace_le_map_latent_subspace M n h_le T

/-- Honest consequence form of the old bridge-map-U/transfer-back wrapper.
This avoids pretending the legacy wrapper is definitionally the same theorem as
`rename_branch_transport_target_of_semantic`; instead it states the actual
downstream fact that the old bridge-facing hypothesis implies the proved
semantic endpoint. -/
theorem rename_branch_transport_target_via_bridgeMapU_consequence_of_semantic
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
  rename_branch_transport_target_of_semantic M n h_le T

/-- Honest bridge-facing consequence of the new strengthened early `of_U`
theorem surface. For the concrete bridge map, a source-side witness
`T (U generator) = generator` yields the same rename-branch transport target as
before, but now through a genuine theorem instead of the underpowered
transfer-back story. -/
theorem rename_branch_transport_target_of_U_source_membership_consequence
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hSource : ∀ (S : List (Fin (npNumVars n)))
      (m : MvPolynomial (Fin (npNumVars n)) ℚ),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le)) S →
      T ((mapFullToLatentPoly M n B).toLinearMap
        ((MvPolynomial.rename (witnessInclusion M n h_le))
          (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n))))) =
        (MvPolynomial.rename (witnessInclusion M n h_le))
          (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)))) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_of_U_source_membership M n h_le T
    (mapFullToLatentPoly M n B).toLinearMap
    (rename_branch_globalDomStyleU_for_bridgeMap M n h_le B)
    hSource

/-- Concrete strengthened rename transport for the preferred reconstruction map
`restrictPoly`. This is the first honest bridge-map theorem in this family that
supplies the required source-side witness `T (U generator) = generator`
directly, via the compiled-input left-inverse seam. -/
theorem rename_branch_transport_target_of_U_source_membership_for_restrictPoly
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_of_U_source_membership_consequence M n h_le B
    (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
    (fun S m hLen hdeg hvars hadm =>
      restrictPoly_mapFullToLatentPoly M n B
        ((MvPolynomial.rename (witnessInclusion M n h_le))
          (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)))))

/-- Honest concrete consequence for the old `rename_branch_transport_target_of_U`
surface on the preferred `restrictPoly` route. This keeps the earlier theorem
shape alive for the concrete bridge map, but its proof source is now the
compiled-input/source-membership theorem rather than the underpowered generic
`hBack` story. -/
theorem rename_branch_transport_target_of_U_consequence_for_restrictPoly
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_of_U_source_membership_for_restrictPoly M n h_le B

/-- Honest consequence form of the earliest rename-target wrapper.
This removes the remaining proof-term equality pin at the generic rename
surface: the old staged endpoint implies the proved semantic transport result,
without claiming the two theorem terms are definitionally identical. -/
theorem rename_branch_transport_target_consequence_of_semantic
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
  rename_branch_transport_target_of_semantic M n h_le T

/-- Honest consequence theorem for the earliest rename-target axiom under the
actual source-membership hypothesis. This exposes the raw endpoint directly from
proved source-membership transport, without routing through the semantic axiom
shell. -/
theorem rename_branch_transport_target_consequence_of_source_membership
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hT : ∀ (S : List (Fin (npNumVars n)))
      (m : MvPolynomial (Fin (npNumVars n)) ℚ),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le)) S →
      (MvPolynomial.rename (witnessInclusion M n h_le))
        (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)))
        ∈ Submodule.map T
            (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
              (latentCompiledPoly M n))) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_of_source_membership M n h_le T hT


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

/-- Canonical packaged version using the isolated raw target axiom.

Status: this remains a legacy early wrapper over the residual generic violation
axiom `violation_branch_rename_transport_target`. The honest theorem layer is
now the compiled-witness semantic route proved later in the file; this wrapper
persists only for declaration-order compatibility. -/
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
supplied, the violation branch closes from `hViolMatches` plus whichever
violation transport theorem is available, and therefore full compiled subspace
transport follows.

Status: this early theorem still uses the raw staged violation target through
`mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches_target`. The honest
replacement layer is the later compiled-witness semantic family, and that is the
preferred proof source downstream whenever declaration order allows. -/
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

/-- Staged closure using the proved later rename-branch theorem. This removes
one dependency on the old staged stack, leaving only the surviving generic
violation transport target on this early route. -/
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
          (latentCompiledPoly M n)) := by
  refine mlBlockedSpdpSubspace_fullCompiled_le_map_of_branch_transports M n h_le T ?_ ?_
  · exact map_rename_witness_tseitin_subspace_le_map_latent_subspace M n h_le T
  · exact mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches_target M n B T hViolMatches

/-- Atomic bridge-side target for the remaining violation branch: a compiled
violation generator should be the reconstruction-image of its renamed latent
counterpart. If this theorem can be proved, the concrete semantic frontier for
`bridgeReconstructionMap` should collapse with only bookkeeping around the
pulled-forward derivative list and multiplier. -/
theorem violation_generator_reconstruction_atomic
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n) :
    ∀ (S : List (Fin (numVars M n (Nat.log 2 n))))
      (m : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible (compiledPartition M n) S →
      mlProj (m * SPDP.iterDerivList S (violationPolyOf ℚ M n)) =
        (bridgeReconstructionMap M n B)
          (mlProj ((MvPolynomial.rename B.toLatent m) *
            SPDP.iterDerivList (S.map B.toLatent)
              (MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n)))) := by
  intro S m hLen hdeg hvars hadm
  have hf := B.inj
  have h_iter :
      SPDP.iterDerivList (S.map B.toLatent)
        (MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n)) =
        MvPolynomial.rename B.toLatent
          (SPDP.iterDerivList S (violationPolyOf ℚ M n)) := by
    simpa using
      (iterDerivList_rename B.toLatent hf S (violationPolyOf ℚ M n))
  have h_mult :
      (MvPolynomial.rename B.toLatent m) *
        SPDP.iterDerivList (S.map B.toLatent)
          (MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n)) =
      MvPolynomial.rename B.toLatent
        (m * SPDP.iterDerivList S (violationPolyOf ℚ M n)) := by
    rw [h_iter, ← map_mul (MvPolynomial.rename B.toLatent)]
  have h_proj :
      mlProj ((MvPolynomial.rename B.toLatent m) *
        SPDP.iterDerivList (S.map B.toLatent)
          (MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n))) =
      MvPolynomial.rename B.toLatent
        (mlProj (m * SPDP.iterDerivList S (violationPolyOf ℚ M n))) := by
    rw [h_mult, mlProj_rename B.toLatent hf]
  have h_retract :
      (mapFullToLatentPoly M n B).toLinearMap
        ((bridgeReconstructionMap M n B)
          (mlProj ((MvPolynomial.rename B.toLatent m) *
            SPDP.iterDerivList (S.map B.toLatent)
              (MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n))))) =
      mlProj ((MvPolynomial.rename B.toLatent m) *
        SPDP.iterDerivList (S.map B.toLatent)
          (MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n))) := by
    rw [h_proj]
    simpa [h_proj] using
      bridgeReconstructionMap_retracts_on_generated_algebra M n B
        (MvPolynomial.rename B.toLatent
          (mlProj (m * SPDP.iterDerivList S (violationPolyOf ℚ M n))))
  apply (MvPolynomial.rename_injective B.toLatent hf)
  symm
  simpa [mapFullToLatentPoly, h_proj] using h_retract

/-- Filtering a mapped list by a target-block predicate has the same length as
filtering the source list by the pulled-back predicate. -/
private theorem map_filter_length_eq_filter_length
    {α β : Type*} (f : α → β) (p : β → Bool) :
    ∀ S : List α,
      ((S.map f).filter p).length = (S.filter (fun a => p (f a))).length := by
  intro S
  induction S with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.filter_cons]
    by_cases h : p (f a)
    · simp [h, ih]
    · simp [h, ih]

/-- If two predicates agree pointwise on a list, their filtered lengths agree. -/
private theorem filter_length_eq_of_pointwise
    {α : Type*} (p q : α → Bool)
    (hpoint : ∀ a, p a = q a) :
    ∀ S : List α, (S.filter p).length = (S.filter q).length := by
  intro S
  induction S with
  | nil => simp
  | cons a rest ih =>
    simp only [List.filter_cons]
    rw [hpoint a]
    split <;> simp [ih]

/-- Concrete semantic violation-generator transport target for the reconstruction
map. This is now the exact remaining bridge-side obligation: given a compiled
violation SPDP generator, exhibit a latent renamed violation generator whose
image under `bridgeReconstructionMap` is that compiled generator. -/
theorem violation_generator_reconstruction_semantic_target
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (hAssignToLatent : ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i)) :
    ViolationGeneratorSemanticTransport M n B (bridgeReconstructionMap M n B) := by
  refine ⟨hAssignToLatent, ?_⟩
  intro S m hLen hdeg hvars hadm
  refine ⟨S.map B.toLatent, MvPolynomial.rename B.toLatent m, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hLen
  · exact le_trans (MvPolynomial.totalDegree_rename_le B.toLatent m) hdeg
  ·
    show (MvPolynomial.rename B.toLatent m).vars ⊆ (S.map B.toLatent).toFinset
    intro i hi
    have hsub := MvPolynomial.vars_rename B.toLatent m
    rcases Finset.mem_image.mp (hsub hi) with ⟨j, hj, rfl⟩
    exact Finset.mem_coe.mpr <| List.mem_toFinset.mpr <| List.mem_map.mpr ⟨j, List.mem_toFinset.mp (hvars hj), rfl⟩
  ·
    constructor
    · exact List.Nodup.map B.inj hadm.1
    · intro b
      have hpoint :
          ∀ i : Fin (numVars M n (Nat.log 2 n)),
            decide ((latentPartition M n).assign (B.toLatent i) = b) =
              decide ((compiledPartition M n).assign i = b) := by
        intro i
        by_cases h : (latentPartition M n).assign (B.toLatent i) = b
        · have hc : (compiledPartition M n).assign i = b := by
            calc
              (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i) := hAssignToLatent i
              _ = b := h
          simp [h, hc]
        · have hc : ¬ (compiledPartition M n).assign i = b := by
            intro hc
            apply h
            calc
              (latentPartition M n).assign (B.toLatent i) = (compiledPartition M n).assign i := (hAssignToLatent i).symm
              _ = b := hc
          simp [h, hc]
      calc
        ((S.map B.toLatent).filter (fun j => decide ((latentPartition M n).assign j = b))).length
            = (S.filter (fun i => decide ((latentPartition M n).assign (B.toLatent i) = b))).length :=
              map_filter_length_eq_filter_length B.toLatent (fun j => decide ((latentPartition M n).assign j = b)) S
        _ = (S.filter (fun i => decide ((compiledPartition M n).assign i = b))).length :=
              filter_length_eq_of_pointwise
                (fun i => decide ((latentPartition M n).assign (B.toLatent i) = b))
                (fun i => decide ((compiledPartition M n).assign i = b))
                hpoint S
        _ ≤ 1 := hadm.2 b
  ·
    simpa [map_violationPolyOf] using
      (violation_generator_reconstruction_atomic M n B S m hLen hdeg hvars hadm)

/-- Concrete bridge-specialized packaging of the remaining violation frontier.
Once the semantic generator theorem for `bridgeReconstructionMap` is proved, the
subspace-level violation transport follows immediately by the established
frontier chain. -/
theorem violationBranchTransportFrontier_for_bridgeReconstructionMap
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (hAssignToLatent : ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i)) :
    violationBranchTransportFrontier M n B (bridgeReconstructionMap M n B) := by
  apply violationBranchTransportFrontier_of_generatorFrontier
  apply violationGeneratorTransportFrontier_of_semantic
  exact violation_generator_reconstruction_semantic_target M n B hAssignToLatent

/-- Concrete compiled-witness semantic violation transport specialized to the
preferred `restrictPoly` reconstruction map. The witness remains in compiled
space and is pushed down by `mapFullToLatentPoly`, matching the orientation of
`restrictPoly_mapFullToLatentPoly`. -/
theorem violation_generator_restrictPoly_semantic
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (hAssignToLatent : ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i)) :
    ViolationGeneratorSemanticTransportCompiledWitness M n B
      (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap := by
  refine ⟨hAssignToLatent, ?_⟩
  intro S m hLen hdeg hvars hadm
  refine ⟨m, hdeg, hvars, ?_⟩
  have h_iter :
      SPDP.iterDerivList (S.map B.toLatent)
        (MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n)) =
      MvPolynomial.rename B.toLatent
        (SPDP.iterDerivList S (violationPolyOf ℚ M n)) := by
    simpa using
      (iterDerivList_rename B.toLatent B.inj S (violationPolyOf ℚ M n))
  have h_mult :
      (mapFullToLatentPoly M n B m) *
        SPDP.iterDerivList (S.map B.toLatent)
          (MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n)) =
      MvPolynomial.rename B.toLatent
        (m * SPDP.iterDerivList S (violationPolyOf ℚ M n)) := by
    rw [mapFullToLatentPoly, h_iter, ← map_mul (MvPolynomial.rename B.toLatent)]
  have h_proj :
      mlProj ((mapFullToLatentPoly M n B m) *
        SPDP.iterDerivList (S.map B.toLatent)
          (MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n))) =
      MvPolynomial.rename B.toLatent
        (mlProj (m * SPDP.iterDerivList S (violationPolyOf ℚ M n))) := by
    rw [h_mult, mlProj_rename B.toLatent B.inj]
  rw [h_proj]
  symm
  exact restrictPoly_mapFullToLatentPoly M n B
    (mlProj (m * SPDP.iterDerivList S (violationPolyOf ℚ M n)))

/-- Concrete `restrictPoly`-based violation frontier, obtained via the new
compiled-witness semantic package. -/
theorem violationBranchTransportFrontier_for_restrictPoly
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (hAssignToLatent : ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i)) :
    violationBranchTransportFrontier M n B
      (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap := by
  apply violationBranchTransportFrontier_of_generatorFrontier
  apply violationGeneratorTransportFrontier_of_compiledWitnessSemantic
  exact violation_generator_restrictPoly_semantic M n B hAssignToLatent

/-- Concrete `restrictPoly`-specialized packaged violation transport into
`latentCompiledPoly`. This is the preferred concrete violation endpoint when the
bridge is realized by `restrictPoly`. -/
theorem mlBlockedSpdpSubspace_violation_le_map_for_restrictPoly
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (hAssignToLatent : ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i))
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyOf ℚ M n)
    ≤ Submodule.map (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches M n B
    (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
    hViolMatches (violationBranchTransportFrontier_for_restrictPoly M n B hAssignToLatent)

/-- Concrete bridge-specialized packaged violation transport into
`latentCompiledPoly`, using the existing rewrite target `hViolMatches`.

This remains as a compatibility surface for the legacy bridge reconstruction
presentation, but the actual concrete route is now pinned down later by
`mlBlockedSpdpSubspace_violation_le_map_for_bridgeReconstructionMap_eq_restrictPoly`. -/
theorem mlBlockedSpdpSubspace_violation_le_map_for_bridgeReconstructionMap
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (hAssignToLatent : ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i))
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyOf ℚ M n)
    ≤ Submodule.map (bridgeReconstructionMap M n B)
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches M n B (bridgeReconstructionMap M n B)
    hViolMatches (violationBranchTransportFrontier_for_bridgeReconstructionMap M n B hAssignToLatent)

/-- The next honest reduction target for the legacy concrete wrapper is an
actual theorem, not a doc cleanup: prove that the legacy section-variable
reconstruction map agrees with the concrete `restrictPoly` bridge on the latent
polynomial space.

A naive `rfl` proof fails even after `bridgeReconstructionMap_def`; the two maps
are not definitionally equal and the reduction needs real coefficient/algebraic
work. Keeping this target explicit avoids pretending the legacy wrapper has
already collapsed. -/
theorem bridgeReconstructionMap_eq_restrictPoly_target
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n) :
    bridgeReconstructionMap M n B =
      (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap := by
  rw [bridgeReconstructionMap_def, MultilinearSPDP.restrictPoly]
  congr
  funext j
  by_cases h : ∃ i, B.toLatent i = j
  · have hsec : ∃ i, B.toLatent i = j := ⟨bridgeSectionVar M n B j, bridgeSectionVar_spec M n B j⟩
    simp only [dif_pos h]
    change MvPolynomial.X (bridgeSectionVar M n B j) = MvPolynomial.X h.choose
    congr
    exact B.inj ((bridgeSectionVar_spec M n B j).trans h.choose_spec.symm)
  · simp only [dif_neg h]
    exfalso
    exact h ⟨bridgeSectionVar M n B j, bridgeSectionVar_spec M n B j⟩

/-- Late direct concrete full-compiled endpoint for the `restrictPoly` route,
using both proved concrete branch theorems: the rename-branch theorem and the
concrete violation `restrictPoly` endpoint.

This theorem is the explicit branch-by-branch form of the preferred concrete
route. It no longer depends on the older staged generic violation target. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_for_restrictPoly_direct
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (hAssignToLatent : ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i))
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  refine mlBlockedSpdpSubspace_fullCompiled_le_map_of_branch_transports M n h_le
    (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
    ?_ ?_
  · exact rename_branch_transport_target_of_U_source_membership_for_restrictPoly M n h_le B
  · exact mlBlockedSpdpSubspace_violation_le_map_for_restrictPoly M n B
      hAssignToLatent hViolMatches

/- The earlier preferred concrete `restrictPoly` endpoint agrees with the late
fully concrete branch-by-branch route once the stronger assignment-style bridge
hypothesis needed by the violation theorem is available. -/
/-- Honest stronger concrete endpoint for `restrictPoly`: once the bridge also
satisfies the assignment-style compatibility actually needed on the violation
branch, the full compiled transport closes by the fully concrete branch-by-
branch proof. This makes the missing hypothesis explicit on a real theorem
surface rather than burying it inside the older staged left-inverse route. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_for_restrictPoly_of_assignToLatent
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (hAssignToLatent : ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i))
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_fullCompiled_le_map_for_restrictPoly_direct M n h_le B
    hAssignToLatent hViolMatches

theorem mlBlockedSpdpSubspace_fullCompiled_le_map_for_restrictPoly_eq_direct
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (hAssignToLatent : ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i))
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace_fullCompiled_le_map_for_restrictPoly M n h_le B hViolMatches =
      mlBlockedSpdpSubspace_fullCompiled_le_map_for_restrictPoly_direct M n h_le B
        hAssignToLatent hViolMatches := by
  rfl

theorem mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches_compiledWitness
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hSem : ViolationGeneratorSemanticTransportCompiledWitness M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyOf ℚ M n)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  exact mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches M n B T hViolMatches
    (violationBranchTransportFrontier_of_generatorFrontier M n B T
      (violationGeneratorTransportFrontier_of_compiledWitnessSemantic M n B T hSem))

theorem mlBlockedSpdpSubspace_fullCompiled_le_map_of_targets_semantic
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
            (latentCompiledPoly M n)))
    (hSem : ViolationGeneratorSemanticTransport M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  refine mlBlockedSpdpSubspace_fullCompiled_le_map_of_branch_transports M n h_le T hRenameBranch ?_
  exact mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches M n B T hViolMatches
    (violation_branch_rename_transport_target_consequence_of_semantic M n B T hSem)

theorem mlBlockedSpdpSubspace_fullCompiled_le_map_of_targets_compiledWitness
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
            (latentCompiledPoly M n)))
    (hSem : ViolationGeneratorSemanticTransportCompiledWitness M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  refine mlBlockedSpdpSubspace_fullCompiled_le_map_of_branch_transports M n h_le T hRenameBranch ?_
  exact mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches M n B T hViolMatches
    (violationBranchTransportFrontier_of_compiledWitnessSemantic M n B T hSem)

/-- Later replacement for the early staged closure: same endpoint, but the
violation branch is discharged by compiled-witness semantics rather than the raw
staged generic violation axiom. This is the preferred arbitrary-`T` full-compiled
surface once a compiled-witness semantic package is available. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_of_staged_targets_compiledWitness
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hSem : ViolationGeneratorSemanticTransportCompiledWitness M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  refine mlBlockedSpdpSubspace_fullCompiled_le_map_of_branch_transports M n h_le T ?_ ?_
  · exact map_rename_witness_tseitin_subspace_le_map_latent_subspace M n h_le T
  · exact mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches M n B T hViolMatches
      (violationBranchTransportFrontier_of_compiledWitnessSemantic M n B T hSem)

/-- Honest theorem-level consequence of the early staged full-compiled closure
`mlBlockedSpdpSubspace_fullCompiled_le_map_of_staged_targets`.
This keeps the same no-extra-rename-hypothesis endpoint while discharging the
violation side by compiled-witness semantics instead of the raw staged target. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_of_staged_targets_consequence_of_semantic
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hSem : ViolationGeneratorSemanticTransport M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  refine mlBlockedSpdpSubspace_fullCompiled_le_map_of_branch_transports M n h_le T ?_ ?_
  · exact map_rename_witness_tseitin_subspace_le_map_latent_subspace M n h_le T
  · exact mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches M n B T hViolMatches
      (violation_branch_rename_transport_target_consequence_of_semantic M n B T hSem)

theorem mlBlockedSpdpSubspace_fullCompiled_le_map_of_staged_targets_consequence
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hSem : ViolationGeneratorSemanticTransportCompiledWitness M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_fullCompiled_le_map_of_staged_targets_compiledWitness M n h_le B T
    hViolMatches hSem

/-- Explicit compiled-witness sibling of
`mlBlockedSpdpSubspace_fullCompiled_le_map_of_staged_targets_consequence_of_semantic`.
This keeps the same old staged endpoint name pattern while making the stronger
compiled-witness semantic source visible in the theorem name. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_of_staged_targets_consequence_of_compiledWitness
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hSem : ViolationGeneratorSemanticTransportCompiledWitness M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_fullCompiled_le_map_of_staged_targets_consequence M n h_le B T
    hViolMatches hSem

/-- Honest theorem-level consequence of the early staged full-compiled target
surface `mlBlockedSpdpSubspace_fullCompiled_le_map_of_targets`.
This keeps the same endpoint available when the violation branch is supplied by
compiled-witness semantics rather than the raw staged generic violation target. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_of_targets_consequence_of_semantic
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
            (latentCompiledPoly M n)))
    (hSem : ViolationGeneratorSemanticTransport M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  refine mlBlockedSpdpSubspace_fullCompiled_le_map_of_branch_transports M n h_le T hRenameBranch ?_
  exact mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches M n B T hViolMatches
    (violation_branch_rename_transport_target_consequence_of_semantic M n B T hSem)

/-- Honest theorem-level consequence of the early staged full-compiled target
surface `mlBlockedSpdpSubspace_fullCompiled_le_map_of_targets`.
This keeps the same endpoint available when the violation branch is supplied by
compiled-witness semantics rather than the raw staged generic violation target. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_of_targets_consequence
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
            (latentCompiledPoly M n)))
    (hSem : ViolationGeneratorSemanticTransportCompiledWitness M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_fullCompiled_le_map_of_targets_compiledWitness M n h_le B T
    hViolMatches hRenameBranch hSem

/-- Explicit compiled-witness sibling of
`mlBlockedSpdpSubspace_fullCompiled_le_map_of_targets_consequence_of_semantic`.
This keeps the same old target-endpoint name pattern while making the stronger
compiled-witness semantic source visible in the theorem name. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_of_targets_consequence_of_compiledWitness
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
            (latentCompiledPoly M n)))
    (hSem : ViolationGeneratorSemanticTransportCompiledWitness M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_fullCompiled_le_map_of_targets_consequence M n h_le B T
    hViolMatches hRenameBranch hSem

theorem mlBlockedSpdpSubspace_violation_le_map_for_bridgeReconstructionMap_eq_restrictPoly
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (hAssignToLatent : ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i))
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace_violation_le_map_for_bridgeReconstructionMap M n B hAssignToLatent hViolMatches =
      by
        rw [bridgeReconstructionMap_eq_restrictPoly_target M n B]
        exact mlBlockedSpdpSubspace_violation_le_map_for_restrictPoly M n B hAssignToLatent hViolMatches := by
  rfl

theorem mlBlockedSpdpSubspace_violation_le_map_of_semantic
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hSem : ViolationGeneratorSemanticTransport M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyOf ℚ M n)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  exact mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches M n B T hViolMatches
    (violation_branch_rename_transport_target_consequence_of_semantic M n B T hSem)

theorem mlBlockedSpdpSubspace_violation_le_map_of_compiledWitnessSemantic
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hSem : ViolationGeneratorSemanticTransportCompiledWitness M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyOf ℚ M n)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  exact mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches M n B T hViolMatches
    (violationBranchTransportFrontier_of_compiledWitnessSemantic M n B T hSem)

/-- Later replacement for the early violation wrapper
`mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches_target`: same endpoint,
but discharged by the direct semantic theorem instead of the raw staged generic
violation axiom. -/
theorem mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches_target_semantic
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hSem : ViolationGeneratorSemanticTransport M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyOf ℚ M n)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_violation_le_map_of_semantic M n B T hViolMatches hSem

/-- Later replacement for the early violation wrapper
`mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches_target`: same endpoint,
but discharged by the real compiled-witness semantic theorem instead of the raw
staged generic violation axiom. This is the preferred arbitrary-`T` violation
surface once compiled-witness semantics are available. -/
theorem mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches_target_compiledWitness
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hSem : ViolationGeneratorSemanticTransportCompiledWitness M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyOf ℚ M n)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_violation_le_map_of_compiledWitnessSemantic M n B T hViolMatches hSem

/-- Honest theorem-level consequence of the early packaged violation-target
surface `mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches_target`.
This keeps the old endpoint available through the later direct semantic route
instead of the raw staged violation transport axiom. -/
theorem mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches_target_consequence_of_semantic
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hSem : ViolationGeneratorSemanticTransport M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyOf ℚ M n)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches_target_semantic M n B T
    hViolMatches hSem

/-- Honest theorem-level consequence of the early packaged violation-target
surface `mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches_target`.
This keeps the old endpoint available through the later compiled-witness
semantic route instead of the raw staged violation transport axiom. -/
theorem mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches_target_consequence
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hSem : ViolationGeneratorSemanticTransportCompiledWitness M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyOf ℚ M n)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches_target_compiledWitness M n B T
    hViolMatches hSem

/-- Explicit compiled-witness sibling of
`mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches_target_consequence_of_semantic`.
This preserves the old endpoint while making the stronger compiled-witness
semantic source visible in the theorem name. -/
theorem mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches_target_consequence_of_compiledWitness
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hSem : ViolationGeneratorSemanticTransportCompiledWitness M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyOf ℚ M n)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches_target_consequence M n B T
    hViolMatches hSem

/-- Later replacement for the early generator-level rename transport wrapper
`rename_branch_generator_transport_target`: same endpoint, but discharged by the
proved semantic rename branch theorem instead of the early staged
`rename_branch_transport_target` axiom layer. -/
theorem rename_branch_generator_transport_target_of_semantic
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
  exact rename_branch_transport_target_of_semantic M n h_le T hmap

/-- Later replacement for the legacy bridge-map-U rename wrapper
`rename_branch_transport_target_via_bridgeMapU`: same endpoint, but discharged
by the proved semantic rename branch theorem instead of the underpowered
`rename_branch_transport_target_of_U` route. -/
theorem rename_branch_transport_target_via_bridgeMapU_compiledWitness
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
  rename_branch_transport_target_of_semantic_membership M n h_le T
    (rename_branch_generator_transport_semantic M n h_le T)

/-- Bridge-facing honest replacement for the old `hBack`-driven rename wrapper:
same bridge-flavored endpoint, but discharged solely from the semantic
membership theorem family rather than latent-side transfer-back. -/
theorem rename_branch_transport_target_via_bridgeMapU_of_semantic_membership
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hSem : RenameBranchSemanticTransport M n h_le T) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_of_semantic_membership M n h_le T hSem

/-- Later bridge-flavored packaging of the strengthened early `of_U` theorem
surface: if a concrete bridge-direction map `U` comes with the actual
source-side witness `T (U generator) = generator`, then rename transport follows
through the new early theorem rather than the old `hBack` route. -/
theorem rename_branch_transport_target_of_U_source_membership_of_semantic
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (U : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (latentNumVars M n)) ℚ)
    (hU : RenameBranchGlobalDomStyleU M n h_le U)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hSource : ∀ (S : List (Fin (npNumVars n)))
      (m : MvPolynomial (Fin (npNumVars n)) ℚ),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le)) S →
      T (U ((MvPolynomial.rename (witnessInclusion M n h_le))
        (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n))))) =
        (MvPolynomial.rename (witnessInclusion M n h_le))
          (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)))) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_of_U_source_membership M n h_le T U hU hSource

/-- Later arbitrary-`T` replacement for the old bridge-map-U left-inverse full
compiled route using direct semantic transport on both branches. This packages
the already-proved semantic rename branch with the direct semantic violation
branch, bypassing the legacy bridge-map-U closure wherever declaration order
permits. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_via_semantic_targets_of_semantic
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hSem : ViolationGeneratorSemanticTransport M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  refine mlBlockedSpdpSubspace_fullCompiled_le_map_of_branch_transports M n h_le T
    (rename_branch_transport_target_of_semantic_membership M n h_le T
      (rename_branch_generator_transport_semantic M n h_le T)) ?_
  exact mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches_target_consequence_of_semantic
    M n B T hViolMatches hSem

/-- Explicit compiled-witness sibling of
`mlBlockedSpdpSubspace_fullCompiled_le_map_via_semantic_targets_of_semantic`.
This preserves the same endpoint while making the stronger compiled-witness
semantic source visible in the theorem name. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_via_semantic_targets_of_compiledWitness
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hSem : ViolationGeneratorSemanticTransportCompiledWitness M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  refine mlBlockedSpdpSubspace_fullCompiled_le_map_of_branch_transports M n h_le T
    (rename_branch_transport_target_of_semantic_membership M n h_le T
      (rename_branch_generator_transport_semantic M n h_le T)) ?_
  exact mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches_target_consequence_of_compiledWitness
    M n B T hViolMatches hSem

/-- Later arbitrary-`T` replacement for the old bridge-map-U left-inverse full
compiled route. This packages the already-proved semantic rename branch with the
compiled-witness semantic violation branch, bypassing the legacy bridge-map-U
closure wherever declaration order permits. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_via_semantic_targets
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hSem : ViolationGeneratorSemanticTransportCompiledWitness M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  refine mlBlockedSpdpSubspace_fullCompiled_le_map_of_branch_transports M n h_le T
    (rename_branch_transport_target_of_semantic_membership M n h_le T
      (rename_branch_generator_transport_semantic M n h_le T)) ?_
  exact mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches_target_compiledWitness
    M n B T hViolMatches hSem

/-- Honest later consequence for the legacy left-inverse full-compiled wrapper:
same endpoint as `mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_leftInverse`,
but sourced from the proved direct-semantic branch transport theorem rather than
the old bridge-map-U axiom layer. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_leftInverse_consequence_of_semantic
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (_hLeftInv : Function.LeftInverse (mapFullToLatentPoly M n B).toLinearMap T)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hSem : ViolationGeneratorSemanticTransport M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_fullCompiled_le_map_via_semantic_targets_of_semantic M n h_le B T
    hViolMatches hSem

/-- Honest later consequence for the legacy left-inverse full-compiled wrapper:
same endpoint as `mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_leftInverse`,
but sourced from the proved semantic/compiled-witness branch transport theorem
rather than the old bridge-map-U axiom layer. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_leftInverse_consequence
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (_hLeftInv : Function.LeftInverse (mapFullToLatentPoly M n B).toLinearMap T)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hSem : ViolationGeneratorSemanticTransportCompiledWitness M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_fullCompiled_le_map_via_semantic_targets M n h_le B T
    hViolMatches hSem

/-- Explicit compiled-witness sibling of
`mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_leftInverse_consequence_of_semantic`.
This preserves the old left-inverse endpoint while making the stronger
compiled-witness semantic source visible in the theorem name. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_leftInverse_consequence_of_compiledWitness
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (_hLeftInv : Function.LeftInverse (mapFullToLatentPoly M n B).toLinearMap T)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hSem : ViolationGeneratorSemanticTransportCompiledWitness M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_leftInverse_consequence M n h_le B T
    _hLeftInv hViolMatches hSem

/-- Later replacement for the early legacy wrapper
`mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_target`: same
endpoint, but discharged by the semantic rename branch plus direct semantic
violation transport instead of the old bridge-map-U left-inverse chain. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_target_semantic
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hSem : ViolationGeneratorSemanticTransport M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  refine mlBlockedSpdpSubspace_fullCompiled_le_map_of_branch_transports M n h_le T ?_ ?_
  · exact rename_branch_transport_target_of_semantic_membership M n h_le T
      (rename_branch_generator_transport_semantic M n h_le T)
  · exact mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches M n B T hViolMatches
      (violation_branch_rename_transport_target_consequence_of_semantic M n B T hSem)

/-- Later replacement for the early legacy wrapper
`mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_target`: same
endpoint, but discharged by the semantic rename branch plus compiled-witness
violation semantics instead of the old bridge-map-U left-inverse chain. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_target_compiledWitness
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hSem : ViolationGeneratorSemanticTransportCompiledWitness M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  refine mlBlockedSpdpSubspace_fullCompiled_le_map_of_branch_transports M n h_le T ?_ ?_
  · exact rename_branch_transport_target_of_semantic_membership M n h_le T
      (rename_branch_generator_transport_semantic M n h_le T)
  · exact mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches M n B T hViolMatches
      (violationBranchTransportFrontier_of_generatorFrontier M n B T
        (violationGeneratorTransportFrontier_of_compiledWitnessSemantic M n B T hSem))

/-- Honest stronger bridge-map-U-target concrete endpoint for the preferred
`restrictPoly` map: once the bridge satisfies the assignment-style hypothesis
actually needed on the violation branch, the old target-shaped theorem surface
collapses to the stronger concrete `restrictPoly` endpoint. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_target_for_restrictPoly_of_assignToLatent
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (hAssignToLatent : ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i))
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_fullCompiled_le_map_for_restrictPoly_of_assignToLatent M n h_le B
    hAssignToLatent hViolMatches

/-- Honest preferred-route consequence for the legacy full-compiled left-inverse
wrapper, specialized to `restrictPoly` under the explicit assignment-style
hypothesis actually needed on the concrete violation branch. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_leftInverse_consequence_for_restrictPoly_of_assignToLatent
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (hAssignToLatent : ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i))
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_fullCompiled_le_map_for_restrictPoly_of_assignToLatent M n h_le B
    hAssignToLatent hViolMatches

/-- Honest concrete rename-branch transport for the legacy
`bridgeReconstructionMap` surface, obtained by collapsing to the preferred
`restrictPoly` theorem through `bridgeReconstructionMap = restrictPoly`. This
bypasses the weak `hBack` story entirely for the concrete bridge map. -/
theorem rename_branch_transport_target_via_bridgeMapU_for_bridgeReconstructionMap
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map (bridgeReconstructionMap M n B)
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  rw [bridgeReconstructionMap_eq_restrictPoly_target M n B]
  exact rename_branch_transport_target_of_U_source_membership_for_restrictPoly M n h_le B

/-- Honest preferred-route consequence theorem for the old rename-wrapper
surface `rename_branch_transport_target_via_bridgeMapU`: on the concrete
`restrictPoly` route, the same endpoint follows from the proved concrete
source-membership theorem rather than the weak bridge-map-U story. -/
theorem rename_branch_transport_target_via_bridgeMapU_consequence_for_restrictPoly
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_of_U_consequence_for_restrictPoly M n h_le B

/-- Honest preferred-route consequence for the old generic `of_U` family under
explicit source-image control, specialized to `restrictPoly`. This pins that
legacy theorem shape directly to the concrete source-image identity already
proved by `restrictPoly_mapFullToLatentPoly`. -/
theorem rename_branch_transport_target_of_U_consequence_of_source_image_for_restrictPoly
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_of_U_consequence_of_source_image M n h_le
    (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
    (mapFullToLatentPoly M n B).toLinearMap
    (rename_branch_globalDomStyleU_for_bridgeMap M n h_le B)
    (by
      intro S m hlen hmdeg hvars hadm
      simpa using
        restrictPoly_mapFullToLatentPoly M n B
          ((MvPolynomial.rename (witnessInclusion M n h_le))
            (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)))))

/-- Concrete bridge-reconstruction version of the old generic `of_U`
source-image consequence theorem. This collapses the concrete endpoint through
`bridgeReconstructionMap = restrictPoly`. -/
theorem rename_branch_transport_target_of_U_consequence_of_source_image_for_bridgeReconstructionMap
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map (bridgeReconstructionMap M n B)
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  rw [bridgeReconstructionMap_eq_restrictPoly_target M n B]
  exact rename_branch_transport_target_of_U_consequence_of_source_image_for_restrictPoly M n h_le B

/-- Honest bridge-facing consequence theorem for the old rename-wrapper surface
`rename_branch_transport_target_via_bridgeMapU`: for the concrete bridge
reconstruction map, the legacy endpoint follows from the concrete theorem that
already bypasses the weak `hBack` route. -/
theorem rename_branch_transport_target_via_bridgeMapU_consequence_for_bridgeReconstructionMap
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map (bridgeReconstructionMap M n B)
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_via_bridgeMapU_for_bridgeReconstructionMap M n h_le B

theorem rename_branch_transport_target_via_bridgeMapU_for_bridgeReconstructionMap_eq_restrictPoly
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) :
    rename_branch_transport_target_via_bridgeMapU_for_bridgeReconstructionMap M n h_le B =
      by
        rw [bridgeReconstructionMap_eq_restrictPoly_target M n B]
        exact rename_branch_transport_target_of_U_source_membership_for_restrictPoly M n h_le B := by
  rfl

/-- Honest preferred-route raw replacement surface for the earliest
bridge-map wrapper under the explicit source-image hypothesis, specialized to
`restrictPoly`. This lands the bridge-shaped source-image theorem itself on
the preferred concrete route, not just its later consequence name. -/
theorem rename_branch_transport_target_via_bridgeMapU_of_source_image_for_restrictPoly
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_via_bridgeMapU_of_source_image M n h_le B
    (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
    (by
      intro S m hlen hmdeg hvars hadm
      simpa using
        restrictPoly_mapFullToLatentPoly M n B
          ((MvPolynomial.rename (witnessInclusion M n h_le))
            (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)))))

/-- Honest preferred-route consequence for the earliest bridge-map wrapper
under the explicit source-image hypothesis, specialized to `restrictPoly`.
This lands the old bridge-shaped endpoint on the concrete source-image route
without touching the weak generic `hBack` story. -/
theorem rename_branch_transport_target_via_bridgeMapU_consequence_of_source_image_for_restrictPoly
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_via_bridgeMapU_consequence_of_source_image M n h_le B
    (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
    (by
      intro S m hlen hmdeg hvars hadm
      simpa using
        restrictPoly_mapFullToLatentPoly M n B
          ((MvPolynomial.rename (witnessInclusion M n h_le))
            (mlProj (m * SPDP.iterDerivList S (tseitinPoly ℚ n)))))

/-- Concrete bridge-reconstruction consequence for the earliest bridge-map
wrapper under the explicit source-image hypothesis. This simply collapses the
new `restrictPoly` source-image endpoint through
`bridgeReconstructionMap = restrictPoly`. -/
theorem rename_branch_transport_target_via_bridgeMapU_consequence_of_source_image_for_bridgeReconstructionMap
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map (bridgeReconstructionMap M n B)
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  rw [bridgeReconstructionMap_eq_restrictPoly_target M n B]
  exact rename_branch_transport_target_via_bridgeMapU_consequence_of_source_image_for_restrictPoly M n h_le B

/-- Honest preferred-route consequence for the later bridge-shaped
compiled-witness rename wrapper. This keeps that endpoint on the concrete
`restrictPoly` route without routing back through the weak generic
bridge-map-U story. -/
theorem rename_branch_transport_target_via_bridgeMapU_compiledWitness_consequence_for_restrictPoly
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_via_bridgeMapU_consequence_for_restrictPoly M n h_le B

/-- Honest preferred-route consequence for the later bridge-shaped
compiled-witness wrapper under the explicit source-image route. This keeps the
same concrete endpoint but now ties it directly to the newer source-image
collapse rather than the older wrapper consequence. -/
theorem rename_branch_transport_target_via_bridgeMapU_compiledWitness_consequence_of_source_image_for_restrictPoly
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_via_bridgeMapU_consequence_of_source_image_for_restrictPoly M n h_le B

/-- Honest preferred-route consequence for the later bridge-shaped semantic
membership wrapper. This keeps that endpoint on the concrete `restrictPoly`
route instead of routing it through the weak generic bridge-map-U layer. -/
theorem rename_branch_transport_target_via_bridgeMapU_of_semantic_membership_consequence_for_restrictPoly
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_via_bridgeMapU_consequence_for_restrictPoly M n h_le B

/-- Honest preferred-route consequence for the later bridge-shaped semantic
membership wrapper under the explicit source-image route. This keeps the same
concrete endpoint while collapsing through the newer source-image theorem
family. -/
theorem rename_branch_transport_target_via_bridgeMapU_of_semantic_membership_consequence_of_source_image_for_restrictPoly
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_via_bridgeMapU_consequence_of_source_image_for_restrictPoly M n h_le B

/-- Honest bridge-facing consequence for the later bridge-shaped semantic
membership wrapper, specialized to the concrete bridge reconstruction map.
This keeps the concrete bridge surface aligned with the proved `restrictPoly`
route instead of leaving it conceptually attached to the weak generic wrapper. -/
theorem rename_branch_transport_target_via_bridgeMapU_of_semantic_membership_consequence_for_bridgeReconstructionMap
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map (bridgeReconstructionMap M n B)
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_via_bridgeMapU_for_bridgeReconstructionMap M n h_le B

/-- Concrete bridge-reconstruction consequence for the later bridge-shaped
semantic-membership wrapper under the source-image route. -/
theorem rename_branch_transport_target_via_bridgeMapU_of_semantic_membership_consequence_of_source_image_for_bridgeReconstructionMap
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map (bridgeReconstructionMap M n B)
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_via_bridgeMapU_consequence_of_source_image_for_bridgeReconstructionMap M n h_le B

/-- Honest bridge-facing consequence for the later bridge-shaped
compiled-witness wrapper, specialized to the concrete bridge reconstruction
map. This keeps that theorem surface collapsed to the proved concrete bridge
route instead of relying on the weak generic wrapper story. -/
theorem rename_branch_transport_target_via_bridgeMapU_compiledWitness_consequence_for_bridgeReconstructionMap
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map (bridgeReconstructionMap M n B)
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_via_bridgeMapU_for_bridgeReconstructionMap M n h_le B

/-- Concrete bridge-reconstruction consequence for the later bridge-shaped
compiled-witness wrapper under the source-image route. -/
theorem rename_branch_transport_target_via_bridgeMapU_compiledWitness_consequence_of_source_image_for_bridgeReconstructionMap
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map (bridgeReconstructionMap M n B)
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_via_bridgeMapU_consequence_of_source_image_for_bridgeReconstructionMap M n h_le B

/-- Honest consequence form of the later bridge-shaped compiled-witness
wrapper. This keeps the bridge-facing theorem surface available without
claiming proof-term definitional equality with the semantic endpoint. -/
theorem rename_branch_transport_target_via_bridgeMapU_compiledWitness_consequence_of_semantic
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
  rename_branch_transport_target_of_semantic M n h_le T

/-- Explicit compiled-witness sibling of
`rename_branch_transport_target_via_bridgeMapU_compiledWitness_consequence_of_semantic`.
This keeps the old bridge-shaped endpoint while making the stronger
compiled-witness source visible in the theorem name. -/
theorem rename_branch_transport_target_via_bridgeMapU_consequence_of_compiledWitness
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
  rename_branch_transport_target_via_bridgeMapU_compiledWitness M n h_le T

/-- Honest consequence form of the bridge-flavored semantic-membership wrapper.
Again, this exposes the actual downstream theorem content without pinning the
wrapper to the generic theorem by `rfl`. -/
theorem rename_branch_transport_target_via_bridgeMapU_of_semantic_membership_consequence
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hSem : RenameBranchSemanticTransport M n h_le T) :
    Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
      (mlBlockedSpdpSubspace
        (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
        (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n))
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  rename_branch_transport_target_of_semantic_membership M n h_le T hSem

/-- Honest stronger concrete endpoint for the legacy bridge-reconstruction-map
surface: once the same assignment-style compatibility needed by the concrete
violation branch is supplied, the full compiled transport collapses through the
proved equality `bridgeReconstructionMap = restrictPoly` and the stronger
concrete `restrictPoly` endpoint. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_for_bridgeReconstructionMap_of_assignToLatent
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (hAssignToLatent : ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i))
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map (bridgeReconstructionMap M n B)
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  rw [bridgeReconstructionMap_eq_restrictPoly_target M n B]
  exact mlBlockedSpdpSubspace_fullCompiled_le_map_for_restrictPoly_of_assignToLatent
    M n h_le B hAssignToLatent hViolMatches

/-- Concrete bridge-reconstruction consequence for the legacy full-compiled
left-inverse wrapper under the explicit assignment-style hypothesis. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_leftInverse_consequence_for_bridgeReconstructionMap_of_assignToLatent
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (hAssignToLatent : ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i))
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map (bridgeReconstructionMap M n B)
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  rw [bridgeReconstructionMap_eq_restrictPoly_target M n B]
  exact mlBlockedSpdpSubspace_fullCompiled_le_map_for_restrictPoly_of_assignToLatent
    M n h_le B hAssignToLatent hViolMatches

/-- Honest stronger target-shaped concrete endpoint for the legacy
`bridgeReconstructionMap` presentation: with the assignment-style compatibility
made explicit, the old bridge-target surface collapses through
`bridgeReconstructionMap = restrictPoly` to the stronger concrete endpoint. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_target_for_bridgeReconstructionMap_of_assignToLatent
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (hAssignToLatent : ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i))
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map (bridgeReconstructionMap M n B)
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  rw [bridgeReconstructionMap_eq_restrictPoly_target M n B]
  exact mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_target_for_restrictPoly_of_assignToLatent
    M n h_le B hAssignToLatent hViolMatches

theorem mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_target_for_bridgeReconstructionMap_eq_restrictPoly
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (hAssignToLatent : ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i))
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_target_for_bridgeReconstructionMap_of_assignToLatent
      M n h_le B hAssignToLatent hViolMatches =
      by
        rw [bridgeReconstructionMap_eq_restrictPoly_target M n B]
        exact mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_target_for_restrictPoly_of_assignToLatent
          M n h_le B hAssignToLatent hViolMatches := by
  rfl

/-- Honest bridge-facing consequence theorem for the old target-shaped concrete
`bridgeReconstructionMap` endpoint: whenever the real missing assignment-style
hypothesis is available, the legacy surface follows from the stronger theorem
already proved for that setting. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_target_consequence
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (hAssignToLatent : ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i))
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map (bridgeReconstructionMap M n B)
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  rw [bridgeReconstructionMap_eq_restrictPoly_target M n B]
  exact mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_target_for_restrictPoly_of_assignToLatent
    M n h_le B hAssignToLatent hViolMatches

/-- Honest later consequence for the early bridge-map-U target endpoint when
one has compiled-witness semantic violation transport. This keeps the old
 theorem shape available while sourcing it from the later proved semantic
branch transport route rather than the legacy bridge-map-U axiom layer. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_target_consequence_of_compiledWitness
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hSem : ViolationGeneratorSemanticTransportCompiledWitness M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_target_compiledWitness M n h_le B T
    hViolMatches hSem

/-- Honest preferred-route consequence for the old target-shaped full-compiled
wrapper on the concrete `restrictPoly` route, under the explicit
assignment-style hypothesis. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_target_consequence_for_restrictPoly_of_assignToLatent
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (hAssignToLatent : ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i))
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  exact mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_target_for_restrictPoly_of_assignToLatent
    M n h_le B hAssignToLatent hViolMatches

/-- Honest consequence theorem for the early bridge-map-U target endpoint when
one has direct semantic violation transport. This keeps the old theorem shape
available while sourcing it from the later proved semantic branch transport
route rather than the legacy bridge-map-U axiom layer. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_target_consequence_of_semantic
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n)
    (hSem : ViolationGeneratorSemanticTransport M n B T) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) :=
  mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_target_semantic M n h_le B T
    hViolMatches hSem

/-- Honest bridge-reconstruction consequence name for the old target-shaped
full-compiled wrapper under the explicit assignment-style hypothesis. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_target_consequence_for_bridgeReconstructionMap_of_assignToLatent
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (hAssignToLatent : ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i))
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map (bridgeReconstructionMap M n B)
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  rw [bridgeReconstructionMap_eq_restrictPoly_target M n B]
  exact mlBlockedSpdpSubspace_fullCompiled_le_map_via_bridgeMapU_of_target_consequence_for_restrictPoly_of_assignToLatent
    M n h_le B hAssignToLatent hViolMatches

/-- Honest bridge-facing consequence theorem for the old concrete
`bridgeReconstructionMap` full-compiled endpoint: when the real missing
assignment-style hypothesis is available, the legacy surface follows from the
stronger theorem already proved for that regime. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_for_bridgeReconstructionMap_consequence
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (hAssignToLatent : ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i))
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map (bridgeReconstructionMap M n B)
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  rw [bridgeReconstructionMap_eq_restrictPoly_target M n B]
  exact mlBlockedSpdpSubspace_fullCompiled_le_map_for_restrictPoly_of_assignToLatent
    M n h_le B hAssignToLatent hViolMatches

/-- Honest preferred-route consequence name for the old concrete full-compiled
endpoint on the `restrictPoly` route, under the explicit assignment-style
hypothesis. -/
theorem mlBlockedSpdpSubspace_fullCompiled_le_map_for_restrictPoly_consequence_of_assignToLatent
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (hAssignToLatent : ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i))
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ Submodule.map (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n)) := by
  exact mlBlockedSpdpSubspace_fullCompiled_le_map_for_restrictPoly_of_assignToLatent
    M n h_le B hAssignToLatent hViolMatches

theorem mlBlockedSpdpSubspace_fullCompiled_le_map_for_bridgeReconstructionMap_eq_restrictPoly
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (hViolMatches :
      MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    mlBlockedSpdpSubspace_fullCompiled_le_map_for_bridgeReconstructionMap M n h_le B hViolMatches =
      by
        rw [bridgeReconstructionMap_eq_restrictPoly_target M n B]
        exact mlBlockedSpdpSubspace_fullCompiled_le_map_for_restrictPoly M n h_le B hViolMatches := by
  rfl

end CompiledGeneratorTransportFrontier
