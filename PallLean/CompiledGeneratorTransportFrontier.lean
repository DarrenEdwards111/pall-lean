import PallLean.CompiledAssemblyRoadmap

/-!
# CompiledGeneratorTransportFrontier

This file isolates the exact next mathematical step in the compiled-side endgame:
prove generator-level transport from the compiled SPDP generators into the latent
SPDP generators. Once this is done, the elementwise transport target and the
reverse-transfer / fine-bound chain are already wired in `CompiledAssemblyRoadmap`.
-/

namespace CompiledGeneratorTransportFrontier

open CompiledAssemblyRoadmap
open LatentFullBridge LatentCompiler MultilinearSPDP NPWitness Compiler TuringMachine
open MvPolynomial

/-- Explicit frontier alias: the generator-level transport theorem is the exact
next proof-bearing obligation for the compiled-to-latent transfer route. -/
def generatorTransportFrontier
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) : Prop :=
  ∀ (S : List (Fin (numVars M n (Nat.log 2 n))))
    (m : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ),
    S.length = Nat.log 2 n →
    m.totalDegree ≤ Nat.log 2 n →
    m.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible (compiledPartition M n) S →
    ∃ (S' : List (Fin (latentNumVars M n)))
      (m' : MvPolynomial (Fin (latentNumVars M n)) ℚ),
      S'.length = Nat.log 2 n ∧
      m'.totalDegree ≤ Nat.log 2 n ∧
      m'.vars ⊆ S'.toFinset ∧
      SPDP.isBlockAdmissible (latentPartition M n) S' ∧
      mlProj (m * SPDP.iterDerivList S (fullCompiledPoly ℚ M n h_le)) =
        T (mlProj (m' * SPDP.iterDerivList S' (latentCompiledPoly M n)))

/-- The roadmap target `compiled_generator_transport_target` is exactly this
frontier proposition. -/
theorem generatorTransportFrontier_iff_roadmap_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) :
    generatorTransportFrontier M n h_le T ↔
      (∀ (S : List (Fin (numVars M n (Nat.log 2 n))))
        (m : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ),
        S.length = Nat.log 2 n →
        m.totalDegree ≤ Nat.log 2 n →
        m.vars ⊆ S.toFinset →
        SPDP.isBlockAdmissible (compiledPartition M n) S →
        ∃ (S' : List (Fin (latentNumVars M n)))
          (m' : MvPolynomial (Fin (latentNumVars M n)) ℚ),
          S'.length = Nat.log 2 n ∧
          m'.totalDegree ≤ Nat.log 2 n ∧
          m'.vars ⊆ S'.toFinset ∧
          SPDP.isBlockAdmissible (latentPartition M n) S' ∧
          mlProj (m * SPDP.iterDerivList S (fullCompiledPoly ℚ M n h_le)) =
            T (mlProj (m' * SPDP.iterDerivList S' (latentCompiledPoly M n)))) := by
  rfl

/-- One-line handoff: once generator transport is proved, the roadmap's exact
minimal elementwise transport target is immediately available. -/
theorem compiled_subspace_element_transport_of_generator_frontier
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hGen : generatorTransportFrontier M n h_le T) :
    ∀ q : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ,
      q ∈ mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
            (fullCompiledPoly ℚ M n h_le) →
      ∃ r : MvPolynomial (Fin (latentNumVars M n)) ℚ,
        r ∈ mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
              (latentCompiledPoly M n)
          ∧ q = T r :=
  compiled_subspace_element_transport_target M n h_le T hGen

end CompiledGeneratorTransportFrontier
