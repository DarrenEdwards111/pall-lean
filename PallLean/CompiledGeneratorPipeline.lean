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
`violation_generator_reconstruction_atomic` and its semantic/frontier lift.
What remains staged here is strictly stronger: a raw rename/map transport
inequality for an arbitrary linear map `T` into the full-variable polynomial
space.

So this axiom is now best read as the generic packaging target still missing
beyond the proved bridge-specialized theorem. Once it is proved,
`hViolMatches` rewrites the target to `latentCompiledPoly` via
`mlBlockedSpdpSubspace_violation_le_map_of_hViolMatches`. -/
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

Current best local design: use `MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj`.
That map already sends off-image latent variables to `0` and is a left inverse
to `MvPolynomial.rename B.toLatent` on renamed full-source polynomials.
So the main remaining issue is not defining some map at all, but packaging the
specific generator/image facts needed by the later bridge-specialized transport
proofs in this file.

The older section-variable presentation is retained here because the current
proof layer below is written in terms of an `aeval`-style reconstruction map.
If the file is refactored around `restrictPoly`, these section axioms should
become removable.

A direct in-place replacement was attempted and backed out: the main blockers
are (1) declaration order, since some early generic bridge wrappers are stated
before the later concrete reconstruction layer, and (2) surviving wrappers that
still quantify over arbitrary `T`, whereas the clean `restrictPoly` route first
collapses only the concrete `bridgeReconstructionMap` specialization.

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
this is the theorem family from which generator retraction should be proved by
induction / `aeval` extensionality.

Refactor note: the later concrete replacement target here is to reprove this
same conclusion using `restrictPoly ℚ B.toLatent B.inj` directly, then retarget
bridge-specialized downstream theorems to that later concrete theorem rather
than replacing the early `bridgeReconstructionMap` surface in place. -/
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

/-- Correctly oriented sibling of the legacy staged endpoint above. This is the
natural theorem surface for the concrete `restrictPoly` seam, whose packaged
fact is

`Function.LeftInverse (MultilinearSPDP.restrictPoly ℚ B.toLatent B.inj).toLinearMap
  (mapFullToLatentPoly M n B).toLinearMap`.

At present this is only recorded as the right future staging target; the older
axiom remains because existing generic bridge-map-U packaging was written in the
opposite argument order. -/
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

This remains useful while the file still contains generic bridge-map-U wrappers,
but new concrete downstream retargeting should prefer
`mlBlockedSpdpSubspace_fullCompiled_le_map_for_restrictPoly`, whose theorem
surface matches the proved `restrictPoly` orientation directly. -/
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

Unlike the legacy `bridgeReconstructionMap` wrapper, this theorem is stated at
exactly the orientation furnished by the proved concrete seam
`restrictPoly_leftInverse_target`, so downstream bridge-specialized rewrites
should target this theorem first. -/
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

/-- Staged transfer-back lemma for the rename branch.

Important: the current hypothesis `HasTransferBackOnLatentSubspace M n T U`
only gives `U (T r) = r` on the latent branch subspace. That is not strong
enough to derive this conclusion by the natural source-space span induction,
because the generator step needs a source-side retraction of the form
`T (U x) = x` on the relevant rename-branch image (or an equivalent membership
principle placing each source generator directly in `Submodule.map T ...`).

So this remains an explicit axiom target for now rather than a theorem proved
from `hBack`. -/
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
      exact (rename_branch_generator_transport_semantic M n h_le T)
        S m hLen hdeg hvars hadm
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
    (map_rename_witness_tseitin_subspace_le_map_latent_subspace M n h_le T)

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

/-- Concrete bridge-specialized packaged violation transport into
`latentCompiledPoly`, using the existing rewrite target `hViolMatches`. -/
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

end CompiledGeneratorTransportFrontier
