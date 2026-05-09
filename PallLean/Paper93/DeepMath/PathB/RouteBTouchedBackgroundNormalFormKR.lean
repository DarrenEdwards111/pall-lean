import PallLean.Paper93.DeepMath.PathB.RouteBTouchedKRProductComposition
import PallLean.Paper93.DeepMath.PathB.ZeroProfileNormalFormInstantiationProgress

/-!
# Route B untouched-background normal-form bridge

The touched split row has already been factored as

`mlProj ((touched local row) * untouchedBackgroundProduct)`.

This file connects the untouched background factor to the existing zero-profile
normal-form machinery.  We do **not** introduce an ambient monomial span or drop
background factors.  Instead, we require the paper §9.3 normal-form row map for
an exact factorization of the untouched background and extract its global basis
at the zero-shift/zero-derivative row.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- The exact list of untouched Cook--Levin constraint factors for a touched
row `S`.  This is just the filtered untouched constraint set, converted to a
list for the existing `Fin L → polynomial` normal-form APIs. -/
noncomputable def untouchedBackgroundFactorList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) :
    List (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) :=
  (((Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).filter
    (fun i => i ∉ cookLevinTouchedConstraints M n hn2 htb hns S)).toList.map
      (fun i => cookLevinConstraintFactor M n hn2 htb hns i))

/-- The untouched background list product is definitionally the filtered
untouched background product. -/
theorem untouchedBackgroundFactorList_prod_eq
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) :
    (untouchedBackgroundFactorList M n hn2 htb hns S).prod =
      untouchedBackgroundProduct M n hn2 htb hns S := by
  classical
  unfold untouchedBackgroundFactorList untouchedBackgroundProduct
  rw [Finset.prod_map_toList]

/-- The `Fin L` family extracted from the exact untouched factor list has
product equal to the untouched background product. -/
theorem untouchedBackgroundFactorFamily_prod_eq
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) :
    Finset.univ.prod
        (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
          (untouchedBackgroundFactorList M n hn2 htb hns S).get i) =
      untouchedBackgroundProduct M n hn2 htb hns S := by
  classical
  let factors := untouchedBackgroundFactorList M n hn2 htb hns S
  have hfin :
      factors.prod =
        Finset.univ.prod (fun i : Fin factors.length => factors.get i) := by
    rw [← Fin.prod_univ_getElem]
    simp [List.get_eq_getElem]
  have hlist : factors.prod = untouchedBackgroundProduct M n hn2 htb hns S := by
    simpa [factors] using untouchedBackgroundFactorList_prod_eq M n hn2 htb hns S
  simpa [factors] using hfin.symm.trans hlist

/-- The zero-profile normal-form row map with identity projection spans the
multilinear projection of the raw product row.  This is the `S=[]`, `shift=1`
row of the existing normal-form interface. -/
theorem mlProj_product_mem_normalFormGlobalBasis_of_idRowMap
    {N L κ typeBudget : ℕ}
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (F : ZeroProfileProjectedNormalFormFamily N κ typeBudget)
    (hmap : ZeroProfileProjectedNormalFormRowMap factors
      (LinearMap.id : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ) F) :
    MultilinearSPDP.mlProj (Finset.univ.prod factors) ∈
      Submodule.span ℚ
        (↑(zeroProfileProjectedNormalFormGlobalBasis F) :
          Set (MvPolynomial (Fin N) ℚ)) := by
  classical
  have hrow := zeroProfileProjectedNormalFormRowMap_row_mem_compressedSpan
    factors
    (LinearMap.id : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)
    F hmap [] (by simp) (1 : MvPolynomial (Fin N) ℚ) (by simp)
  simpa [zeroProfileProjectedNormalFormCompressedSpan, LinearMap.id_apply] using hrow

/-- If a normal-form factor family has product exactly equal to the untouched
background, its global normal-form basis spans `mlProj` of that background. -/
theorem mlProj_untouchedBackground_mem_normalFormGlobalBasis_of_idRowMap
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {L typeBudget : ℕ}
    (factors : Fin L →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (F : ZeroProfileProjectedNormalFormFamily
      (cookLevinTableau M n hn2 htb hns).numVars (Nat.log 2 n) typeBudget)
    (hmap : ZeroProfileProjectedNormalFormRowMap factors
      (LinearMap.id :
        MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
          MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) F)
    (hprod : Finset.univ.prod factors =
      untouchedBackgroundProduct M n hn2 htb hns S) :
    MultilinearSPDP.mlProj
        (untouchedBackgroundProduct M n hn2 htb hns S) ∈
      Submodule.span ℚ
        (↑(zeroProfileProjectedNormalFormGlobalBasis F) : Set
          (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)) := by
  rw [← hprod]
  exact mlProj_product_mem_normalFormGlobalBasis_of_idRowMap factors F hmap

/-- The global basis supplied by a projected normal-form family obeys its
explicit type budget. -/
theorem untouchedBackgroundNormalFormGlobalBasis_card_le
    {N κ typeBudget : ℕ}
    (F : ZeroProfileProjectedNormalFormFamily N κ typeBudget) :
    (zeroProfileProjectedNormalFormGlobalBasis F).card ≤ typeBudget :=
  zeroProfileProjectedNormalFormGlobalBasis_card_le_typeBudget F

/-- Main bridge: an identity-projected zero-profile normal-form row map for an
exact untouched-background factorization supplies the background span consumed
by the touched/background Khatri--Rao composition theorem. -/
theorem touchedMonomialSplitRow_mem_rowWindowProductBasis_of_backgroundNormalForm
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (T : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hT : T ⊆ S)
    (hout : ∀ i, i ∉ cookLevinTouchedConstraints M n hn2 htb hns S.toList → alloc i = [])
    {L typeBudget : ℕ}
    (factors : Fin L →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (F : ZeroProfileProjectedNormalFormFamily
      (cookLevinTableau M n hn2 htb hns).numVars (Nat.log 2 n) typeBudget)
    (hmap : ZeroProfileProjectedNormalFormRowMap factors
      (LinearMap.id :
        MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
          MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) F)
    (hprod : Finset.univ.prod factors =
      untouchedBackgroundProduct M n hn2 htb hns S.toList) :
    touchedMonomialSplitRow M n hn2 htb hns S.toList T alloc ∈
      Submodule.span ℚ
        (↑(mlProjProductBasis
          (MlProjFar.mlMonomialBasis
            (cookLevinRowLocalWindow M n hn2 htb hns S.toList))
          (zeroProfileProjectedNormalFormGlobalBasis F)) : Set
          (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)) := by
  exact touchedMonomialSplitRow_mem_rowWindowProductBasis_of_projectedBackgroundSpan
    M n hn2 htb hns S T alloc hT hout
    (zeroProfileProjectedNormalFormGlobalBasis F)
    (mlProj_untouchedBackground_mem_normalFormGlobalBasis_of_idRowMap
      M n hn2 htb hns S.toList factors F hmap hprod)

/-- Same as `touchedMonomialSplitRow_mem_rowWindowProductBasis_of_backgroundNormalForm`,
but with the untouched factor family fixed to the concrete filtered
Cook--Levin factor list.  The only remaining input is the actual §9.3
normal-form row map for that concrete family. -/
theorem touchedMonomialSplitRow_mem_rowWindowProductBasis_of_concreteBackgroundNormalForm
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (T : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hT : T ⊆ S)
    (hout : ∀ i, i ∉ cookLevinTouchedConstraints M n hn2 htb hns S.toList → alloc i = [])
    {typeBudget : ℕ}
    (F : ZeroProfileProjectedNormalFormFamily
      (cookLevinTableau M n hn2 htb hns).numVars (Nat.log 2 n) typeBudget)
    (hmap : ZeroProfileProjectedNormalFormRowMap
      (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S.toList).length =>
        (untouchedBackgroundFactorList M n hn2 htb hns S.toList).get i)
      (LinearMap.id :
        MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
          MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) F) :
    touchedMonomialSplitRow M n hn2 htb hns S.toList T alloc ∈
      Submodule.span ℚ
        (↑(mlProjProductBasis
          (MlProjFar.mlMonomialBasis
            (cookLevinRowLocalWindow M n hn2 htb hns S.toList))
          (zeroProfileProjectedNormalFormGlobalBasis F)) : Set
          (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)) := by
  exact touchedMonomialSplitRow_mem_rowWindowProductBasis_of_backgroundNormalForm
    M n hn2 htb hns S T alloc hT hout
    (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S.toList).length =>
      (untouchedBackgroundFactorList M n hn2 htb hns S.toList).get i)
    F hmap
    (untouchedBackgroundFactorFamily_prod_eq M n hn2 htb hns S.toList)

/-- At paper scale, if the normal-form family budget is itself bounded by
`n^C`, then the combined touched/background product basis has size
`n^(200+C)`. -/
theorem rowWindowBackgroundNormalFormProductBasis_card_le_pow_add
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hS : S.card ≤ Nat.log 2 n)
    {typeBudget C : ℕ}
    (F : ZeroProfileProjectedNormalFormFamily
      (cookLevinTableau M n hn2 htb hns).numVars (Nat.log 2 n) typeBudget)
    (hbudget : typeBudget ≤ n ^ C) :
    (mlProjProductBasis
      (MlProjFar.mlMonomialBasis
        (cookLevinRowLocalWindow M n hn2 htb hns S.toList))
      (zeroProfileProjectedNormalFormGlobalBasis F)).card ≤
        n ^ (200 + C) := by
  exact rowWindowProductBasis_card_le_pow_add_budget
    M n hn hn2 htb hns S hS
    (zeroProfileProjectedNormalFormGlobalBasis F)
    ((zeroProfileProjectedNormalFormGlobalBasis_card_le_typeBudget F).trans hbudget)

/-! ## Axiom audit anchors -/

#print axioms untouchedBackgroundFactorList_prod_eq
#print axioms untouchedBackgroundFactorFamily_prod_eq
#print axioms mlProj_product_mem_normalFormGlobalBasis_of_idRowMap
#print axioms mlProj_untouchedBackground_mem_normalFormGlobalBasis_of_idRowMap
#print axioms untouchedBackgroundNormalFormGlobalBasis_card_le
#print axioms touchedMonomialSplitRow_mem_rowWindowProductBasis_of_backgroundNormalForm
#print axioms touchedMonomialSplitRow_mem_rowWindowProductBasis_of_concreteBackgroundNormalForm
#print axioms rowWindowBackgroundNormalFormProductBasis_card_le_pow_add

end PallLean.Paper93.DeepMath.PathB
