import PallLean.Paper93.DeepMath.PathB.RouteBTouchedMonomialCodedFiniteSpanKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedBackgroundNormalFormKR

/-!
# Route B atom-trace background to coded finite-span bridge

This file composes the concrete untouched-background atom-trace classifier with
Route B's final coded finite-span target.  It is deliberately a bridge: the
local §9.3 theorem still has to construct the atom-trace row classifier and the
per-code local basis.  No global ambient span is introduced here.
-/

set_option exponentiation.threshold 1024

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- Paper-faithful coded basis data routed through the concrete untouched
background atom-trace classifier.

For every exact monomial touched row datum `D`, this asks for the real §9.3
atom-trace row theorem for the exact filtered untouched background attached to
`D.S`, and for a finite local basis indexed by the coded word that spans the
resulting Khatri--Rao product basis.  This keeps the actual factors and the
normal-form classifier visible instead of jumping to an arbitrary global span. -/
def CookLevinTouchedMonomialAtomTraceCodedBasisData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (C₃ : ℕ)
    (_hC₃ : Nat.log 2 (C₃ ^ 2) + 1 ≤ 200)
    (codeOf : TouchedMonomialInterfaceDatum M n hn2 htb hns →
      touchedKRWords C₃ (Nat.log 2 n))
    (localBasis : touchedKRWords C₃ (Nat.log 2 n) → Fin C₃ →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ),
    ∀ D : TouchedMonomialInterfaceDatum M n hn2 htb hns,
      ∃ (B : SPDP.BlockPartition (cookLevinTableau M n hn2 htb hns).numVars)
        (ℓ typeBudget : ℕ)
        (A : UntouchedBackgroundConcreteAtomTraceCompiledChartRowsForList
          M n hn2 htb hns D.S B ℓ typeBudget),
        ∀ p ∈ mlProjProductBasis
            (MlProjFar.mlMonomialBasis
              (cookLevinRowLocalWindow M n hn2 htb hns D.S))
            (zeroProfileProjectedNormalFormGlobalBasis
              (zeroProfileProjectedNormalFormFamily_of_concreteData
                (untouchedBackgroundConcreteNormalFormClassifierForList_of_atomTraceCompiledChartRows
                  M n hn2 htb hns D.S B ℓ A).data)),
          p ∈ Submodule.span ℚ
            ((Set.range (localBasis (codeOf D))) : Set
              (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))

/-- Exact-budget version of the atom-trace coded-basis datum.

The only background input per row is the canonical exact-budget local-chart
row theorem; the arbitrary `typeBudget` parameter is eliminated by
`untouchedBackgroundAtomTraceExactTypeBudget`. -/
def CookLevinTouchedMonomialAtomTraceExactCodedBasisData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (C₃ : ℕ)
    (_hC₃ : Nat.log 2 (C₃ ^ 2) + 1 ≤ 200)
    (codeOf : TouchedMonomialInterfaceDatum M n hn2 htb hns →
      touchedKRWords C₃ (Nat.log 2 n))
    (localBasis : touchedKRWords C₃ (Nat.log 2 n) → Fin C₃ →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ),
    ∀ D : TouchedMonomialInterfaceDatum M n hn2 htb hns,
      ∃ (B : SPDP.BlockPartition (cookLevinTableau M n hn2 htb hns).numVars)
        (ℓ : ℕ)
        (A : UntouchedBackgroundConcreteAtomTraceExactCompiledChartRowsForList
          M n hn2 htb hns D.S B ℓ),
        ∀ p ∈ mlProjProductBasis
            (MlProjFar.mlMonomialBasis
              (cookLevinRowLocalWindow M n hn2 htb hns D.S))
            (zeroProfileProjectedNormalFormGlobalBasis
              (zeroProfileProjectedNormalFormFamily_of_concreteData
                (untouchedBackgroundConcreteNormalFormClassifierForList_of_atomTraceCompiledChartRows
                  M n hn2 htb hns D.S B ℓ
                    (untouchedBackgroundConcreteAtomTraceCompiledChartRowsForList_of_exact
                      M n hn2 htb hns D.S B ℓ A)).data)),
          p ∈ Submodule.span ℚ
            ((Set.range (localBasis (codeOf D))) : Set
              (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))

/-- Exact-budget atom-trace coded basis data forgets to the budgeted bridge. -/
theorem touchedMonomialAtomTraceCodedBasisData_of_exact
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hData : CookLevinTouchedMonomialAtomTraceExactCodedBasisData
      M n hn2 htb hns) :
    CookLevinTouchedMonomialAtomTraceCodedBasisData M n hn2 htb hns := by
  classical
  rcases hData with ⟨C₃, hC₃, codeOf, localBasis, hrowBasis⟩
  refine ⟨C₃, hC₃, codeOf, localBasis, ?_⟩
  intro D
  rcases hrowBasis D with ⟨B, ℓ, A, hbasis⟩
  refine ⟨B, ℓ, untouchedBackgroundAtomTraceExactTypeBudget n,
    untouchedBackgroundConcreteAtomTraceCompiledChartRowsForList_of_exact
      M n hn2 htb hns D.S B ℓ A, ?_⟩
  simpa using hbasis

/-- Concrete atom-trace coded basis data supplies the final coded finite-span
Route B target.  The proof is just the faithful composition: exact touched row
→ concrete background product basis → per-code local basis span. -/
theorem touchedMonomialCodedFiniteSpan_of_atomTraceCodedBasis
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hData : CookLevinTouchedMonomialAtomTraceCodedBasisData
      M n hn2 htb hns) :
    CookLevinTouchedMonomialCodedFiniteSpanData M n hn2 htb hns := by
  classical
  rcases hData with ⟨C₃, hC₃, codeOf, localBasis, hrowBasis⟩
  refine ⟨C₃, hC₃, codeOf, localBasis, ?_⟩
  intro D
  rcases hrowBasis D with ⟨B, ℓ, typeBudget, A, hbasis⟩
  let C := untouchedBackgroundConcreteNormalFormClassifierForList_of_atomTraceCompiledChartRows
    M n hn2 htb hns D.S B ℓ A
  have hprod : D.row ∈ Submodule.span ℚ
      (↑(mlProjProductBasis
        (MlProjFar.mlMonomialBasis
          (cookLevinRowLocalWindow M n hn2 htb hns D.S))
        (zeroProfileProjectedNormalFormGlobalBasis
          (zeroProfileProjectedNormalFormFamily_of_concreteData C.data))) : Set
        (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)) := by
    simpa [TouchedMonomialInterfaceDatum.row, C] using
      touchedMonomialSplitRow_mem_rowWindowProductBasis_of_concreteBackgroundConcreteNormalForm_list
        M n hn2 htb hns D.S D.T D.alloc D.hTsubset D.hout C
  exact (Submodule.span_le.mpr (by
    intro p hp
    exact hbasis p hp)) hprod

/-- Uniform concrete atom-trace coded basis data. -/
def Step247UniformTouchedMonomialAtomTraceCodedBasisData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinTouchedMonomialAtomTraceCodedBasisData M n hn2 htb hns

/-- Uniform atom-trace coded basis data closes the remaining packaging gap to
`Step247UniformTouchedMonomialCodedFiniteSpanData`. -/
theorem step247UniformTouchedMonomialCodedFiniteSpanData_of_atomTraceCodedBasis
    (hData : Step247UniformTouchedMonomialAtomTraceCodedBasisData) :
    Step247UniformTouchedMonomialCodedFiniteSpanData := by
  intro M n hn hn2 htb hns
  exact touchedMonomialCodedFiniteSpan_of_atomTraceCodedBasis
    M n hn2 htb hns (hData M n hn hn2 htb hns)

/-- Uniform exact-budget concrete atom-trace coded basis data. -/
def Step247UniformTouchedMonomialAtomTraceExactCodedBasisData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinTouchedMonomialAtomTraceExactCodedBasisData M n hn2 htb hns

/-- Uniform exact-budget atom-trace coded basis data forgets to the budgeted
atom-trace coded-basis bridge. -/
theorem step247UniformTouchedMonomialAtomTraceCodedBasisData_of_exact
    (hData : Step247UniformTouchedMonomialAtomTraceExactCodedBasisData) :
    Step247UniformTouchedMonomialAtomTraceCodedBasisData := by
  intro M n hn hn2 htb hns
  exact touchedMonomialAtomTraceCodedBasisData_of_exact
    M n hn2 htb hns (hData M n hn hn2 htb hns)

/-- Uniform exact-budget atom-trace coded basis data closes the final coded
finite-span target. -/
theorem step247UniformTouchedMonomialCodedFiniteSpanData_of_atomTraceExactCodedBasis
    (hData : Step247UniformTouchedMonomialAtomTraceExactCodedBasisData) :
    Step247UniformTouchedMonomialCodedFiniteSpanData :=
  step247UniformTouchedMonomialCodedFiniteSpanData_of_atomTraceCodedBasis
    (step247UniformTouchedMonomialAtomTraceCodedBasisData_of_exact hData)

/-! ## Axiom audit anchors -/

#print axioms touchedMonomialAtomTraceCodedBasisData_of_exact
#print axioms touchedMonomialCodedFiniteSpan_of_atomTraceCodedBasis
#print axioms step247UniformTouchedMonomialAtomTraceCodedBasisData_of_exact
#print axioms step247UniformTouchedMonomialCodedFiniteSpanData_of_atomTraceCodedBasis
#print axioms step247UniformTouchedMonomialCodedFiniteSpanData_of_atomTraceExactCodedBasis

end PallLean.Paper93.DeepMath.PathB
