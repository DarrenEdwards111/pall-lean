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

/-- Critical remaining obligation (isolated): renamed-Tseitin branch transport
into the latent map-image under the chosen bridge map. -/
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
