import PallLean.Paper93.DeepMath.PathB.RouteBTouchedLocalMonomialBasisKR
import PallLean.IterDerivHelpers

/-!
# Route B touched/untouched background factorization

This file makes explicit the algebraic interface between the touched local
product and the untouched background product.  Under the existing support
compatibility hypothesis `hout`, all allocations on untouched constraints are
empty, so the untouched side is the undifferentiated Cook--Levin background
factor product.  This is the exact object the profile/monoid normal-form
machinery must act on.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- The undifferentiated product over all constraints outside the touched set. -/
noncomputable def untouchedBackgroundProduct
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) :
    MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ :=
  ((Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).filter
    (fun i => i ∉ cookLevinTouchedConstraints M n hn2 htb hns S)).prod
      (fun i => cookLevinConstraintFactor M n hn2 htb hns i)

/-- Under `hout`, the allocated untouched product is exactly the
undifferentiated background product. -/
theorem untouchedAllocatedProduct_eq_background
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hout : ∀ i, i ∉ cookLevinTouchedConstraints M n hn2 htb hns S → alloc i = []) :
    ((Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).filter
      (fun i => i ∉ cookLevinTouchedConstraints M n hn2 htb hns S)).prod
        (fun i => SPDP.iterDerivList (alloc i)
          (cookLevinConstraintFactor M n hn2 htb hns i)) =
      untouchedBackgroundProduct M n hn2 htb hns S := by
  classical
  unfold untouchedBackgroundProduct
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [hout i hi, IterDerivHelpers.iterDerivList_nil]

/-- The full touched split product factors as the touched local product times
the undifferentiated untouched background product. -/
theorem touchedAllocatedSplitProduct_eq_touchedLocal_mul_background
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hout : ∀ i, i ∉ cookLevinTouchedConstraints M n hn2 htb hns S → alloc i = []) :
    touchedAllocatedSplitProduct M n hn2 htb hns S alloc =
      touchedAllocatedProductOnly M n hn2 htb hns S alloc *
        untouchedBackgroundProduct M n hn2 htb hns S := by
  classical
  unfold touchedAllocatedSplitProduct touchedAllocatedProductOnly
  rw [untouchedAllocatedProduct_eq_background M n hn2 htb hns S alloc hout]

/-- The monomial split row is the multilinear projection of a touched local
monomial part times the undifferentiated untouched background. -/
theorem touchedMonomialSplitRow_eq_mlProj_local_mul_background
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (T : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hout : ∀ i, i ∉ cookLevinTouchedConstraints M n hn2 htb hns S → alloc i = []) :
    touchedMonomialSplitRow M n hn2 htb hns S T alloc =
      MultilinearSPDP.mlProj
        ((touchedShiftMonomial T *
            touchedAllocatedProductOnly M n hn2 htb hns S alloc) *
          untouchedBackgroundProduct M n hn2 htb hns S) := by
  unfold touchedMonomialSplitRow touchedSplitRow touchedAllocatedProductOnly untouchedBackgroundProduct
  rw [untouchedAllocatedProduct_eq_background M n hn2 htb hns S alloc hout]
  simp [untouchedBackgroundProduct, mul_assoc]

/-! ## Axiom audit anchors -/

#print axioms untouchedAllocatedProduct_eq_background
#print axioms touchedAllocatedSplitProduct_eq_touchedLocal_mul_background
#print axioms touchedMonomialSplitRow_eq_mlProj_local_mul_background

end PallLean.Paper93.DeepMath.PathB
