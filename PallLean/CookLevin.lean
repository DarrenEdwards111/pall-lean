/-
  CookLevin.lean — Cook-Levin Decomposition (documentation)

  The compiled_separation_axiom in CompiledSeparation.lean combines
  three sub-claims. This file documents the decomposition for
  transparency, but the main proof uses the combined axiom.

  Sub-claims:
  1. Cook-Levin construction: DTM → width-3 CNF (standard CS)
  2. Profile compression: block-local → rank ≤ √n (§8/§17.3)
  3. Extraction: perm rank ≤ compiled rank (§40/Lemma 206)
-/
import PallLean.CompiledPoly
import PallLean.TuringMachine
import Mathlib.Tactic

namespace CookLevin

open CompiledPoly TuringMachine

/-- A Cook-Levin CNF correctly encodes DTM M at input size n. -/
structure CookLevinEncoding (M : DTM) (n : ℕ) where
  k : ℕ
  cnf : CookLevinCNF (compiledVarCount k n)
  hlp : HasLocalPartition cnf

end CookLevin
