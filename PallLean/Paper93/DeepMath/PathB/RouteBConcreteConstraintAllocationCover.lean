import PallLean.Paper93.DeepMath.PathB.RouteBLeibnizAllocationCover

/-!
# Route B concrete constraint allocation cover

This file removes the last arbitrary product presentation from the allocation
cover seam.  The factor index is now the actual finite type of positions in the
Cook--Levin constraint list, and each factor is literally `(1 - Cᵢ)`.

The remaining proof after this file is therefore the paper's Khatri--Rao cover
for derivative allocations across the concrete Cook--Levin constraints.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler

/-- The concrete finite index type of Cook--Levin constraints. -/
abbrev cookLevinConstraintIdx
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Type :=
  Fin (cookLevinTableau M n hn2 htb hns).constraints.length

/-- The actual factor `(1 - Cᵢ)` at a concrete constraint-list index. -/
noncomputable def cookLevinConstraintFactor
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : cookLevinConstraintIdx M n hn2 htb hns) :
    MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ :=
  (1 : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) -
    ((cookLevinTableau M n hn2 htb hns).constraints.get i).poly

/-- The concrete product over constraint-list indices equals the compiled
Cook--Levin product. -/
theorem cookLevinCompiledProduct_eq_constraintIdx_prod
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    cookLevinCompiledProduct M n hn2 htb hns =
      (Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).prod
        (cookLevinConstraintFactor M n hn2 htb hns) := by
  rw [cookLevinCompiledProduct_eq_factor_product]
  symm
  rw [← Fin.prod_ofFn]
  have hlist :
      List.ofFn (cookLevinConstraintFactor M n hn2 htb hns) =
        (cookLevinTableau M n hn2 htb hns).constraints.map
          (fun c => (1 : MvPolynomial
            (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) - c.poly) := by
    apply List.ext_get
    · simp
    · intro j h₁ h₂
      simp [cookLevinConstraintFactor]
  rw [hlist]

/-- Concrete allocation-cover data over the real Cook--Levin constraint list. -/
def CookLevinConcreteConstraintAllocationCoverData
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
      MultilinearSPDP.mlProj
          (m * (Finset.univ : Finset
            (cookLevinConstraintIdx M n hn2 htb hns)).prod
              (fun i => SPDP.iterDerivList (alloc i)
                (cookLevinConstraintFactor M n hn2 htb hns i))) ∈
        Submodule.span ℚ (↑G : Set (MvPolynomial
          (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))

/-- Concrete constraint allocation cover implies the generic allocation cover. -/
theorem cookLevinLeibnizAllocationCoverData_of_concreteConstraintAllocationCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hConcrete : CookLevinConcreteConstraintAllocationCoverData M n hn2 htb hns) :
    CookLevinLeibnizAllocationCoverData M n hn2 htb hns := by
  rcases hConcrete with ⟨G, hcard, hcover⟩
  refine ⟨cookLevinConstraintIdx M n hn2 htb hns, inferInstance,
    (Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)),
    cookLevinConstraintFactor M n hn2 htb hns, G,
    cookLevinCompiledProduct_eq_constraintIdx_prod M n hn2 htb hns,
    hcard, ?_⟩
  intro S m alloc hall
  exact hcover S m alloc hall

/-- Concrete constraint allocation cover implies the plain `cookLevinQ` P-side
bound. -/
theorem plainCookLevinQPSideBound_of_concreteConstraintAllocationCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hConcrete : CookLevinConcreteConstraintAllocationCoverData M n hn2 htb hns) :
    PlainCookLevinQPSideBound M n hn2 htb hns :=
  plainCookLevinQPSideBound_of_allocationCoverData M n hn2 htb hns
    (cookLevinLeibnizAllocationCoverData_of_concreteConstraintAllocationCoverData
      M n hn2 htb hns hConcrete)

/-- Uniform concrete constraint allocation cover data at paper scale. -/
def Step247UniformConcreteConstraintAllocationCoverData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinConcreteConstraintAllocationCoverData M n hn2 htb hns

/-- Uniform concrete allocation cover data discharges the generic allocation
cover seam. -/
theorem step247UniformLeibnizAllocationCoverData_of_concreteConstraintAllocationCoverData
    (hConcrete : Step247UniformConcreteConstraintAllocationCoverData) :
    Step247UniformLeibnizAllocationCoverData := by
  intro M n hn hn2 htb hns
  exact cookLevinLeibnizAllocationCoverData_of_concreteConstraintAllocationCoverData
    M n hn2 htb hns (hConcrete M n hn hn2 htb hns)

/-- Uniform concrete allocation cover data closes the Route B `T_Φ` no-decider
surface. -/
theorem noBoundedSATDeciderAtPaperScale_of_concreteConstraintAllocationCoverData_TPhi
    (hConcrete : Step247UniformConcreteConstraintAllocationCoverData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_allocationCoverData_TPhi
    (step247UniformLeibnizAllocationCoverData_of_concreteConstraintAllocationCoverData
      hConcrete)

/-! ## Axiom audit anchors -/

#print axioms cookLevinCompiledProduct_eq_constraintIdx_prod
#print axioms cookLevinLeibnizAllocationCoverData_of_concreteConstraintAllocationCoverData
#print axioms plainCookLevinQPSideBound_of_concreteConstraintAllocationCoverData
#print axioms step247UniformLeibnizAllocationCoverData_of_concreteConstraintAllocationCoverData
#print axioms noBoundedSATDeciderAtPaperScale_of_concreteConstraintAllocationCoverData_TPhi

end PallLean.Paper93.DeepMath.PathB
