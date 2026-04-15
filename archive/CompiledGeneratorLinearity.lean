import PallLean.CompiledGeneratorTransportFrontier

/-!
# CompiledGeneratorLinearity

Direct algebraic decomposition for compiled SPDP generators.
This is the first concrete step in the generator-transport frontier: every
compiled generator over `fullCompiledPoly` splits into verifier and violation
contributions by linearity of iterated derivatives, multiplication, and mlProj.
-/

namespace CompiledGeneratorTransportFrontier

open CompiledAssemblyRoadmap
open LatentFullBridge LatentCompiler MultilinearSPDP NPWitness Compiler TuringMachine
open MvPolynomial SPDP

/-- Direct generator decomposition for the paper/full compiled polynomial.
This is the honest first cut toward generator transport: before transporting any
individual generator, split it into its verifier and violation summands. -/
theorem compiled_generator_decomposition
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (S : List (Fin (numVars M n (Nat.log 2 n))))
    (m : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) :
    mlProj (m * iterDerivList S (fullCompiledPoly ℚ M n h_le)) =
      mlProj (m * iterDerivList S (verifierSheetOf ℚ M n h_le))
      + mlProj (m * iterDerivList S (violationPolyOf ℚ M n)) := by
  unfold fullCompiledPoly
  rw [iterDerivList_add, mul_add, mlProj_add]

end CompiledGeneratorTransportFrontier
