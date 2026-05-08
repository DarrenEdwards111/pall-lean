import PallLean.Paper93.DeepMath.PathB.RouteBConcreteConstraintAllocationCover

/-!
# Route B concrete local derivative facts

This file records the local facts that the final Khatri--Rao counting argument
is allowed to use for each concrete Cook--Levin factor `(1 - Cᵢ)`:

* the factor uses only the support of constraint `Cᵢ`;
* that support has size ≤ 10;
* every allocated iterated derivative of that factor still uses ≤ 10 variables;
* every allocated iterated derivative has degree ≤ 6.

Then it defines a slightly more local cover seam where the term-cover proof may
assume these per-factor facts explicitly.  Since the facts are proved here for
every concrete allocation, this local seam implies the concrete allocation cover.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler

/-- The variables of a concrete Cook--Levin factor `(1 - Cᵢ)` are contained in
the support of the underlying local constraint. -/
theorem cookLevinConstraintFactor_vars_subset_support
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : cookLevinConstraintIdx M n hn2 htb hns) :
    (cookLevinConstraintFactor M n hn2 htb hns i).vars ⊆
      ((cookLevinTableau M n hn2 htb hns).constraints.get i).support := by
  intro x hx
  unfold cookLevinConstraintFactor at hx
  have hsub := MvPolynomial.vars_sub_subset
    (p := (1 : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))
    (q := ((cookLevinTableau M n hn2 htb hns).constraints.get i).poly)
  have hx' := hsub hx
  simp [MvPolynomial.vars_one] at hx'
  exact ((cookLevinTableau M n hn2 htb hns).constraints.get i).vars_contained hx'

/-- A concrete Cook--Levin factor `(1 - Cᵢ)` uses at most 10 variables. -/
theorem cookLevinConstraintFactor_vars_card_le_ten
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : cookLevinConstraintIdx M n hn2 htb hns) :
    (cookLevinConstraintFactor M n hn2 htb hns i).vars.card ≤ 10 := by
  exact le_trans
    (Finset.card_le_card
      (cookLevinConstraintFactor_vars_subset_support M n hn2 htb hns i))
    (((cookLevinTableau M n hn2 htb hns).constraints.get i).support_bound)

/-- A concrete Cook--Levin factor `(1 - Cᵢ)` has total degree at most 6. -/
theorem cookLevinConstraintFactor_totalDegree_le_six
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : cookLevinConstraintIdx M n hn2 htb hns) :
    (cookLevinConstraintFactor M n hn2 htb hns i).totalDegree ≤ 6 := by
  unfold cookLevinConstraintFactor
  calc (((1 : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) -
        ((cookLevinTableau M n hn2 htb hns).constraints.get i).poly).totalDegree)
      ≤ max (1 : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ).totalDegree
          (((cookLevinTableau M n hn2 htb hns).constraints.get i).poly.totalDegree) :=
        MvPolynomial.totalDegree_sub _ _
    _ ≤ max 0 6 := by
        apply max_le_max
        · rw [MvPolynomial.totalDegree_one]
        · exact ((cookLevinTableau M n hn2 htb hns).constraints.get i).degree_bound
    _ = 6 := by norm_num

/-- An allocated derivative of a concrete factor still uses at most 10
variables. -/
theorem cookLevinAllocatedFactor_vars_card_le_ten
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : cookLevinConstraintIdx M n hn2 htb hns)
    (d : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) :
    (SPDP.iterDerivList d (cookLevinConstraintFactor M n hn2 htb hns i)).vars.card ≤ 10 := by
  have hsubset := Step222.vars_iterDerivList_subset d
    (cookLevinConstraintFactor M n hn2 htb hns i)
  exact le_trans (Finset.card_le_card hsubset)
    (cookLevinConstraintFactor_vars_card_le_ten M n hn2 htb hns i)

/-- An allocated derivative of a concrete factor has total degree at most 6. -/
theorem cookLevinAllocatedFactor_totalDegree_le_six
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : cookLevinConstraintIdx M n hn2 htb hns)
    (d : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) :
    (SPDP.iterDerivList d (cookLevinConstraintFactor M n hn2 htb hns i)).totalDegree ≤ 6 := by
  exact le_trans (SPDP.totalDegree_iterDerivList_le d
    (cookLevinConstraintFactor M n hn2 htb hns i))
    (cookLevinConstraintFactor_totalDegree_le_six M n hn2 htb hns i)

/-- A local-facts version of the concrete constraint allocation cover seam.  The
cover proof may assume the proven per-factor support/degree facts for each
allocated derivative. -/
def CookLevinConcreteLocalDerivativeAllocationCoverData
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

/-- Local-derivative allocation cover data implies the concrete constraint
allocation cover, because the local facts are true for every allocation. -/
theorem concreteConstraintAllocationCoverData_of_localDerivativeAllocationCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hLocal : CookLevinConcreteLocalDerivativeAllocationCoverData M n hn2 htb hns) :
    CookLevinConcreteConstraintAllocationCoverData M n hn2 htb hns := by
  rcases hLocal with ⟨G, hcard, hcover⟩
  refine ⟨G, hcard, ?_⟩
  intro S m alloc hall
  exact hcover S m alloc hall
    (fun i => cookLevinAllocatedFactor_vars_card_le_ten M n hn2 htb hns i (alloc i))
    (fun i => cookLevinAllocatedFactor_totalDegree_le_six M n hn2 htb hns i (alloc i))

/-- Uniform local-derivative allocation cover data at paper scale. -/
def Step247UniformConcreteLocalDerivativeAllocationCoverData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinConcreteLocalDerivativeAllocationCoverData M n hn2 htb hns

/-- Uniform local-derivative allocation cover data discharges the concrete
constraint allocation seam. -/
theorem step247UniformConcreteConstraintAllocationCoverData_of_localDerivativeAllocationCoverData
    (hLocal : Step247UniformConcreteLocalDerivativeAllocationCoverData) :
    Step247UniformConcreteConstraintAllocationCoverData := by
  intro M n hn hn2 htb hns
  exact concreteConstraintAllocationCoverData_of_localDerivativeAllocationCoverData
    M n hn2 htb hns (hLocal M n hn hn2 htb hns)

/-- Uniform local-derivative allocation cover data closes Route B. -/
theorem noBoundedSATDeciderAtPaperScale_of_localDerivativeAllocationCoverData_TPhi
    (hLocal : Step247UniformConcreteLocalDerivativeAllocationCoverData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_concreteConstraintAllocationCoverData_TPhi
    (step247UniformConcreteConstraintAllocationCoverData_of_localDerivativeAllocationCoverData
      hLocal)

/-! ## Axiom audit anchors -/

#print axioms cookLevinConstraintFactor_vars_subset_support
#print axioms cookLevinConstraintFactor_vars_card_le_ten
#print axioms cookLevinConstraintFactor_totalDegree_le_six
#print axioms cookLevinAllocatedFactor_vars_card_le_ten
#print axioms cookLevinAllocatedFactor_totalDegree_le_six
#print axioms concreteConstraintAllocationCoverData_of_localDerivativeAllocationCoverData
#print axioms step247UniformConcreteConstraintAllocationCoverData_of_localDerivativeAllocationCoverData
#print axioms noBoundedSATDeciderAtPaperScale_of_localDerivativeAllocationCoverData_TPhi

end PallLean.Paper93.DeepMath.PathB
