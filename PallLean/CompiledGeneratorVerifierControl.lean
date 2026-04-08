import PallLean.CompiledGeneratorLinearity

/-!
# CompiledGeneratorVerifierControl

Next honest cut on the generator-transport frontier: if the verifier contribution
at a compiled generator vanishes, then the full compiled generator is exactly the
violation contribution. This reduces the remaining transport work to proving the
verifier-side vanishing/control theorem for the relevant `(S,m)` instances.
-/

namespace CompiledGeneratorTransportFrontier

open CompiledAssemblyRoadmap
open LatentFullBridge LatentCompiler MultilinearSPDP NPWitness Compiler TuringMachine
open MvPolynomial SPDP

/-- If the verifier contribution vanishes for a given compiled generator,
then the full compiled generator collapses to the violation contribution. -/
theorem compiled_generator_eq_violation_of_verifier_zero
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (S : List (Fin (numVars M n (Nat.log 2 n))))
    (m : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hVerZero : mlProj (m * iterDerivList S (verifierSheetOf ℚ M n h_le)) = 0) :
    mlProj (m * iterDerivList S (fullCompiledPoly ℚ M n h_le)) =
      mlProj (m * iterDerivList S (violationPolyOf ℚ M n)) := by
  rw [compiled_generator_decomposition]
  rw [hVerZero, zero_add]

end CompiledGeneratorTransportFrontier
