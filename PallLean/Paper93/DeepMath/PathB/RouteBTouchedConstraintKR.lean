import PallLean.Paper93.DeepMath.PathB.RouteBRowFaithfulLengthPrunedKR

/-!
# Route B touched-constraint KR seam

A support-compatible allocation can only assign derivatives to constraints whose
local support meets the SPDP row list `S`.  This file makes that combinatorial
fact explicit for the final Khatri--Rao count.

The touched constraints are exactly the concrete Cook--Levin constraints whose
support intersects `S.toFinset`.  Outside that finite touched set, every
support-compatible allocation is forced to be `[]`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler

/-- Concrete constraints whose local support intersects the SPDP row `S`. -/
noncomputable def cookLevinTouchedConstraints
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) :
    Finset (cookLevinConstraintIdx M n hn2 htb hns) :=
  (Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).filter
    (fun i => (((cookLevinTableau M n hn2 htb hns).constraints.get i).support ∩
      S.toFinset).Nonempty)

/-- If a support-compatible allocation assigns a derivative to constraint `i`,
then `i` is touched by the row `S`. -/
theorem mem_touched_of_mem_supportCompatible_alloc
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hall : ∀ i, ∀ v ∈ alloc i, v ∈ S)
    (hcompat : ∀ i, ∀ v ∈ alloc i,
      v ∈ ((cookLevinTableau M n hn2 htb hns).constraints.get i).support)
    (i : cookLevinConstraintIdx M n hn2 htb hns)
    {v : Fin (cookLevinTableau M n hn2 htb hns).numVars}
    (hv : v ∈ alloc i) :
    i ∈ cookLevinTouchedConstraints M n hn2 htb hns S := by
  classical
  unfold cookLevinTouchedConstraints
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨v, by
    simp only [Finset.mem_inter, List.mem_toFinset]
    exact ⟨hcompat i v hv, hall i v hv⟩⟩

/-- Outside the touched constraint set, every support-compatible allocation is
forced to be empty. -/
theorem alloc_eq_nil_of_not_mem_touched
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hall : ∀ i, ∀ v ∈ alloc i, v ∈ S)
    (hcompat : ∀ i, ∀ v ∈ alloc i,
      v ∈ ((cookLevinTableau M n hn2 htb hns).constraints.get i).support)
    (i : cookLevinConstraintIdx M n hn2 htb hns)
    (hnot : i ∉ cookLevinTouchedConstraints M n hn2 htb hns S) :
    alloc i = [] := by
  classical
  cases halloc : alloc i with
  | nil => rfl
  | cons v rest =>
      have hv : v ∈ alloc i := by
        rw [halloc]
        simp
      exact False.elim
        (hnot (mem_touched_of_mem_supportCompatible_alloc
          M n hn2 htb hns S alloc hall hcompat i hv))

/-- Touched-constraint row-faithful KR data.

The final KR proof may now assume allocations are empty outside the actual
constraints touched by the row `S`. -/
def CookLevinTouchedConstraintKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ G : Finset (MvPolynomial
      (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ),
    G.card ≤ n ^ 200 ∧
    ∀ (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (alloc : cookLevinConstraintIdx M n hn2 htb hns →
        List (Fin (cookLevinTableau M n hn2 htb hns).numVars)),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible (cookLevinTableau M n hn2 htb hns).partition S →
      (∀ i, ∀ v ∈ alloc i, v ∈ S) →
      (∀ i, ∀ v ∈ alloc i,
        v ∈ ((cookLevinTableau M n hn2 htb hns).constraints.get i).support) →
      (∀ i, (alloc i).length ≤ 6) →
      (∀ i, i ∉ cookLevinTouchedConstraints M n hn2 htb hns S → alloc i = []) →
      MultilinearSPDP.mlProj
          (m * (Finset.univ : Finset
            (cookLevinConstraintIdx M n hn2 htb hns)).prod
              (fun i => SPDP.iterDerivList (alloc i)
                (cookLevinConstraintFactor M n hn2 htb hns i))) ∈
        Submodule.span ℚ (↑G : Set (MvPolynomial
          (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))

/-- Touched-constraint KR data implies the row-faithful length-pruned KR seam. -/
theorem rowFaithfulLengthPrunedKRData_of_touchedConstraintKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hTouched : CookLevinTouchedConstraintKRData M n hn2 htb hns) :
    CookLevinRowFaithfulLengthPrunedKRData M n hn2 htb hns := by
  rcases hTouched with ⟨G, hcard, hcover⟩
  refine ⟨G, hcard, ?_⟩
  intro S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc
  exact hcover S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc
    (fun i hnot => alloc_eq_nil_of_not_mem_touched
      M n hn2 htb hns S alloc hall hcompat i hnot)

/-- Uniform touched-constraint KR data at paper scale. -/
def Step247UniformTouchedConstraintKRData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinTouchedConstraintKRData M n hn2 htb hns

/-- Uniform touched-constraint KR data implies the row-faithful KR seam. -/
theorem step247UniformRowFaithfulLengthPrunedKRData_of_touchedConstraintKRData
    (hTouched : Step247UniformTouchedConstraintKRData) :
    Step247UniformRowFaithfulLengthPrunedKRData := by
  intro M n hn hn2 htb hns
  exact rowFaithfulLengthPrunedKRData_of_touchedConstraintKRData
    M n hn2 htb hns (hTouched M n hn hn2 htb hns)

/-- Uniform touched-constraint KR data closes Route B. -/
theorem noBoundedSATDeciderAtPaperScale_of_touchedConstraintKRData_TPhi
    (hTouched : Step247UniformTouchedConstraintKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_rowFaithfulLengthPrunedKRData_TPhi
    (step247UniformRowFaithfulLengthPrunedKRData_of_touchedConstraintKRData
      hTouched)

/-! ## Axiom audit anchors -/

#print axioms mem_touched_of_mem_supportCompatible_alloc
#print axioms alloc_eq_nil_of_not_mem_touched
#print axioms rowFaithfulLengthPrunedKRData_of_touchedConstraintKRData
#print axioms step247UniformRowFaithfulLengthPrunedKRData_of_touchedConstraintKRData
#print axioms noBoundedSATDeciderAtPaperScale_of_touchedConstraintKRData_TPhi

end PallLean.Paper93.DeepMath.PathB
