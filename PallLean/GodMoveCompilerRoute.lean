import PallLean.GodMoveExtractionML
import PallLean.MultilinearSPDP

/-!
# GodMoveCompilerRoute

Concrete paper-faithful God-Move wrappers for the current compiler/scaffold route,
built from the theorem-level multilinear extraction machinery already present in
`MultilinearSPDP.lean`.

This file does not introduce new axioms. It packages the existing extraction
inequality in a form that is easier to reuse from a separation pipeline.
-/

namespace GodMoveCompilerRoute

open SPDP
open Compiler
open MultilinearSPDP
open NPWitness
open Tseitin
open GodMoveExtractionML
open MvPolynomial
open TuringMachine

/--
Concrete God-Move extraction inequality for the current compiler route.

This is the paper-faithful bridge in the form actually needed on the active
multilinear path:

* NP-side hard object: `tseitinPoly F n`
* P-side compiled scaffold: `fullCompiledPoly F M n h_le`
* comparison under the scaffold-induced compiled partition
-/
theorem compiler_godMove_extraction_rank_monotone
    (F : Type*) [Field F] [Nontrivial F]
    (M : DTM) (n : ℕ)
    (hsolves : True)
    (hn : n ≥ 32)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (κ ℓ : ℕ)
    (hκ : κ ≥ 5) :
    mlBlockedSpdpRank (tseitinPartition n) κ ℓ (tseitinPoly F n)
      ≤
    mlBlockedSpdpRank (compiledPartition M n) κ ℓ (fullCompiledPoly F M n h_le) :=
  extraction_rank_monotone F n M hsolves hn h_le κ ℓ hκ

/--
A packaged `GodMoveData`-style object is not needed on the current route because
`extraction_rank_monotone` is already available theorem-level.  This theorem just
re-exposes it under a paper-faithful God-Move name.
-/
abbrev godMove_extraction_rank_monotone :=
  compiler_godMove_extraction_rank_monotone

end GodMoveCompilerRoute
