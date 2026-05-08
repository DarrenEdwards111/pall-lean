import PallLean.Paper93.DeepMath.PathB.RouteBConcreteLocalDerivativeFacts

/-!
# Route B support-compatible allocation cover

This is the next paper-faithful narrowing of the Khatri--Rao seam.

A Leibniz allocation that differentiates a local Cook--Levin factor `(1 - Cᵢ)`
in a variable outside that factor's support contributes zero.  Therefore the
nonzero rows that the KR family must cover are exactly the support-compatible
allocations.  This file proves that reduction against the concrete constraint
indexing from the previous layer.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler

/-- If a derivative allocation for constraint `i` contains a variable outside
that concrete factor's support, the allocated derivative of the factor is zero. -/
theorem cookLevinAllocatedFactor_eq_zero_of_mem_notMem_support
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : cookLevinConstraintIdx M n hn2 htb hns)
    (d : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {v : Fin (cookLevinTableau M n hn2 htb hns).numVars}
    (hv : v ∈ d)
    (hnot : v ∉ ((cookLevinTableau M n hn2 htb hns).constraints.get i).support) :
    SPDP.iterDerivList d (cookLevinConstraintFactor M n hn2 htb hns i) = 0 := by
  apply IterDerivHelpers.iterDerivList_eq_zero_of_mem_notMem_vars d v
  · exact hv
  · intro hvvars
    exact hnot (cookLevinConstraintFactor_vars_subset_support M n hn2 htb hns i hvvars)

/-- If one allocated concrete factor is zero, the whole allocated product is
zero. -/
theorem cookLevinAllocatedProduct_eq_zero_of_factor_zero
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (i : cookLevinConstraintIdx M n hn2 htb hns)
    (hzero : SPDP.iterDerivList (alloc i)
      (cookLevinConstraintFactor M n hn2 htb hns i) = 0) :
    (Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).prod
        (fun j => SPDP.iterDerivList (alloc j)
          (cookLevinConstraintFactor M n hn2 htb hns j)) = 0 := by
  exact Finset.prod_eq_zero (Finset.mem_univ i) hzero

/-- If any allocation differentiates a factor outside its support, the allocated
Leibniz product row is zero even after multiplication by `m` and multilinear
projection. -/
theorem mlProj_allocatedProduct_eq_zero_of_not_supportCompatible
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hbad : ∃ i, ∃ v ∈ alloc i,
      v ∉ ((cookLevinTableau M n hn2 htb hns).constraints.get i).support) :
    MultilinearSPDP.mlProj
        (m * (Finset.univ : Finset
          (cookLevinConstraintIdx M n hn2 htb hns)).prod
            (fun i => SPDP.iterDerivList (alloc i)
              (cookLevinConstraintFactor M n hn2 htb hns i))) = 0 := by
  rcases hbad with ⟨i, v, hv, hnot⟩
  have hfac : SPDP.iterDerivList (alloc i)
      (cookLevinConstraintFactor M n hn2 htb hns i) = 0 :=
    cookLevinAllocatedFactor_eq_zero_of_mem_notMem_support M n hn2 htb hns i
      (alloc i) hv hnot
  have hprod : (Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).prod
        (fun j => SPDP.iterDerivList (alloc j)
          (cookLevinConstraintFactor M n hn2 htb hns j)) = 0 :=
    cookLevinAllocatedProduct_eq_zero_of_factor_zero M n hn2 htb hns alloc i hfac
  rw [hprod, mul_zero]
  simp

/-- A support-compatible version of the local derivative allocation seam.  The
cover only has to handle allocations that differentiate each constraint factor
inside that constraint's own support. -/
def CookLevinSupportCompatibleAllocationCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ G : Finset (MvPolynomial
      (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ),
    G.card ≤ n ^ 200 ∧
    ∀ (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (alloc : cookLevinConstraintIdx M n hn2 htb hns →
        List (Fin (cookLevinTableau M n hn2 htb hns).numVars)),
      (∀ i, ∀ v ∈ alloc i, v ∈ S) →
      (∀ i, ∀ v ∈ alloc i,
        v ∈ ((cookLevinTableau M n hn2 htb hns).constraints.get i).support) →
      (∀ i, (SPDP.iterDerivList (alloc i)
        (cookLevinConstraintFactor M n hn2 htb hns i)).vars.card ≤ 10) →
      (∀ i, (SPDP.iterDerivList (alloc i)
        (cookLevinConstraintFactor M n hn2 htb hns i)).totalDegree ≤ 6) →
      MultilinearSPDP.mlProj
          (m * (Finset.univ : Finset
            (cookLevinConstraintIdx M n hn2 htb hns)).prod
              (fun i => SPDP.iterDerivList (alloc i)
                (cookLevinConstraintFactor M n hn2 htb hns i))) ∈
        Submodule.span ℚ (↑G : Set (MvPolynomial
          (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))

/-- A support-compatible cover implies the local-derivative cover: bad
allocations are zero rows, and good allocations are covered by hypothesis. -/
theorem localDerivativeAllocationCoverData_of_supportCompatibleAllocationCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hSupp : CookLevinSupportCompatibleAllocationCoverData M n hn2 htb hns) :
    CookLevinConcreteLocalDerivativeAllocationCoverData M n hn2 htb hns := by
  rcases hSupp with ⟨G, hcard, hcover⟩
  refine ⟨G, hcard, ?_⟩
  intro S m alloc hall hvars hdeg
  by_cases hcompat : ∀ i, ∀ v ∈ alloc i,
      v ∈ ((cookLevinTableau M n hn2 htb hns).constraints.get i).support
  · exact hcover S m alloc hall hcompat hvars hdeg
  · have hbad : ∃ i, ∃ v ∈ alloc i,
        v ∉ ((cookLevinTableau M n hn2 htb hns).constraints.get i).support := by
      push_neg at hcompat
      exact hcompat
    rw [mlProj_allocatedProduct_eq_zero_of_not_supportCompatible M n hn2 htb hns m alloc hbad]
    exact Submodule.zero_mem _

/-- Uniform support-compatible allocation cover data at paper scale. -/
def Step247UniformSupportCompatibleAllocationCoverData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinSupportCompatibleAllocationCoverData M n hn2 htb hns

/-- Uniform support-compatible cover data implies the local derivative seam. -/
theorem step247UniformConcreteLocalDerivativeAllocationCoverData_of_supportCompatibleAllocationCoverData
    (hSupp : Step247UniformSupportCompatibleAllocationCoverData) :
    Step247UniformConcreteLocalDerivativeAllocationCoverData := by
  intro M n hn hn2 htb hns
  exact localDerivativeAllocationCoverData_of_supportCompatibleAllocationCoverData
    M n hn2 htb hns (hSupp M n hn hn2 htb hns)

/-- Uniform support-compatible allocation cover data closes Route B. -/
theorem noBoundedSATDeciderAtPaperScale_of_supportCompatibleAllocationCoverData_TPhi
    (hSupp : Step247UniformSupportCompatibleAllocationCoverData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_localDerivativeAllocationCoverData_TPhi
    (step247UniformConcreteLocalDerivativeAllocationCoverData_of_supportCompatibleAllocationCoverData
      hSupp)

/-! ## Axiom audit anchors -/

#print axioms cookLevinAllocatedFactor_eq_zero_of_mem_notMem_support
#print axioms cookLevinAllocatedProduct_eq_zero_of_factor_zero
#print axioms mlProj_allocatedProduct_eq_zero_of_not_supportCompatible
#print axioms localDerivativeAllocationCoverData_of_supportCompatibleAllocationCoverData
#print axioms step247UniformConcreteLocalDerivativeAllocationCoverData_of_supportCompatibleAllocationCoverData
#print axioms noBoundedSATDeciderAtPaperScale_of_supportCompatibleAllocationCoverData_TPhi

end PallLean.Paper93.DeepMath.PathB
