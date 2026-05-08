import PallLean.Paper93.DeepMath.PathB.RouteBSupportCompatibleAllocationCover

/-!
# Route B length-pruned allocation cover

This file removes another over-approximation from the concrete KR seam.
A local Cook--Levin factor `(1 - Cᵢ)` has degree at most 6, so any allocated
iterated derivative of that factor with a derivative list of length > 6 is zero.
Consequently the nonzero support-compatible rows only require local allocation
lists of length at most 6.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler

/-- If more than six derivatives are allocated to one concrete Cook--Levin
factor, that allocated local derivative is zero. -/
theorem cookLevinAllocatedFactor_eq_zero_of_length_gt_six
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : cookLevinConstraintIdx M n hn2 htb hns)
    (d : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : 6 < d.length) :
    SPDP.iterDerivList d (cookLevinConstraintFactor M n hn2 htb hns i) = 0 := by
  apply MultilinearSPDP.iterDerivList_eq_zero_of_totalDegree_lt
  exact lt_of_le_of_lt
    (cookLevinConstraintFactor_totalDegree_le_six M n hn2 htb hns i)
    hlen

/-- If one allocation list is longer than six, the whole allocated Leibniz row
is zero after multilinear projection. -/
theorem mlProj_allocatedProduct_eq_zero_of_factor_length_gt_six
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hbad : ∃ i, 6 < (alloc i).length) :
    MultilinearSPDP.mlProj
        (m * (Finset.univ : Finset
          (cookLevinConstraintIdx M n hn2 htb hns)).prod
            (fun i => SPDP.iterDerivList (alloc i)
              (cookLevinConstraintFactor M n hn2 htb hns i))) = 0 := by
  rcases hbad with ⟨i, hlen⟩
  have hfac : SPDP.iterDerivList (alloc i)
      (cookLevinConstraintFactor M n hn2 htb hns i) = 0 :=
    cookLevinAllocatedFactor_eq_zero_of_length_gt_six M n hn2 htb hns i
      (alloc i) hlen
  have hprod : (Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).prod
        (fun j => SPDP.iterDerivList (alloc j)
          (cookLevinConstraintFactor M n hn2 htb hns j)) = 0 :=
    cookLevinAllocatedProduct_eq_zero_of_factor_zero M n hn2 htb hns alloc i hfac
  rw [hprod, mul_zero]
  simp

/-- Length-pruned support-compatible cover data.  The final KR construction only
has to cover allocations satisfying both:

* each derivative variable lies in that constraint's support;
* each local allocation list has length at most 6.
-/
def CookLevinLengthPrunedAllocationCoverData
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
      (∀ i, (alloc i).length ≤ 6) →
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

/-- A length-pruned cover implies the support-compatible cover: allocations with
some local length > 6 are zero rows; the rest are covered by hypothesis. -/
theorem supportCompatibleAllocationCoverData_of_lengthPrunedAllocationCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hLen : CookLevinLengthPrunedAllocationCoverData M n hn2 htb hns) :
    CookLevinSupportCompatibleAllocationCoverData M n hn2 htb hns := by
  rcases hLen with ⟨G, hcard, hcover⟩
  refine ⟨G, hcard, ?_⟩
  intro S m alloc hall hcompat hvars hdeg
  by_cases hlen : ∀ i, (alloc i).length ≤ 6
  · exact hcover S m alloc hall hcompat hlen hvars hdeg
  · have hbad : ∃ i, 6 < (alloc i).length := by
      push_neg at hlen
      exact hlen
    rw [mlProj_allocatedProduct_eq_zero_of_factor_length_gt_six M n hn2 htb hns m alloc hbad]
    exact Submodule.zero_mem _

/-- Uniform length-pruned allocation cover data at paper scale. -/
def Step247UniformLengthPrunedAllocationCoverData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinLengthPrunedAllocationCoverData M n hn2 htb hns

/-- Uniform length-pruned cover data implies the support-compatible seam. -/
theorem step247UniformSupportCompatibleAllocationCoverData_of_lengthPrunedAllocationCoverData
    (hLen : Step247UniformLengthPrunedAllocationCoverData) :
    Step247UniformSupportCompatibleAllocationCoverData := by
  intro M n hn hn2 htb hns
  exact supportCompatibleAllocationCoverData_of_lengthPrunedAllocationCoverData
    M n hn2 htb hns (hLen M n hn hn2 htb hns)

/-- Uniform length-pruned allocation cover data closes Route B. -/
theorem noBoundedSATDeciderAtPaperScale_of_lengthPrunedAllocationCoverData_TPhi
    (hLen : Step247UniformLengthPrunedAllocationCoverData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_supportCompatibleAllocationCoverData_TPhi
    (step247UniformSupportCompatibleAllocationCoverData_of_lengthPrunedAllocationCoverData
      hLen)

/-! ## Axiom audit anchors -/

#print axioms cookLevinAllocatedFactor_eq_zero_of_length_gt_six
#print axioms mlProj_allocatedProduct_eq_zero_of_factor_length_gt_six
#print axioms supportCompatibleAllocationCoverData_of_lengthPrunedAllocationCoverData
#print axioms step247UniformSupportCompatibleAllocationCoverData_of_lengthPrunedAllocationCoverData
#print axioms noBoundedSATDeciderAtPaperScale_of_lengthPrunedAllocationCoverData_TPhi

end PallLean.Paper93.DeepMath.PathB
