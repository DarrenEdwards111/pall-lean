import PallLean.Paper93.DeepMath.PathB.RouteBTouchedConcreteWindowKR

/-!
# Route B touched window-source KR seam

This file removes one more proof-shaped degree of freedom from the concrete
window seam.  A non-dormant local window source is no longer allowed to carry an
independent proof that it is touched; it must be an element of the concrete
support fibre of the row variable at that KR position:

`{ i | rowVarAt(j) ∈ support(Cᵢ) }`.

Membership in that fibre implies membership in `cookLevinTouchedConstraints`,
because `rowVarAt(j)` is literally an element of the row list `S`.  Thus the
source of each non-dormant window is now backed by the actual Cook--Levin local
support relation.
-/

set_option exponentiation.threshold 1024

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- The row variable at position `j` is a member of the row list `S`. -/
theorem touchedRowVarAt_mem
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : S.length = Nat.log 2 n)
    (j : Fin (Nat.log 2 n)) :
    touchedRowVarAt M n hn2 htb hns S hlen j ∈ S := by
  unfold touchedRowVarAt
  exact List.get_mem S ⟨j.val, by simp [hlen, j.isLt]⟩

/-- Concrete support fibre for the row variable at KR position `j`. -/
noncomputable def touchedWindowSupportFibre
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : S.length = Nat.log 2 n)
    (j : Fin (Nat.log 2 n)) :
    Finset (cookLevinConstraintIdx M n hn2 htb hns) :=
  (Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).filter
    (fun i => touchedRowVarAt M n hn2 htb hns S hlen j ∈
      ((cookLevinTableau M n hn2 htb hns).constraints.get i).support)

/-- Any constraint in the row-variable support fibre is genuinely touched. -/
theorem mem_touched_of_mem_windowSupportFibre
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : S.length = Nat.log 2 n)
    (j : Fin (Nat.log 2 n))
    (i : cookLevinConstraintIdx M n hn2 htb hns)
    (hi : i ∈ touchedWindowSupportFibre M n hn2 htb hns S hlen j) :
    i ∈ cookLevinTouchedConstraints M n hn2 htb hns S := by
  classical
  unfold touchedWindowSupportFibre at hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  unfold cookLevinTouchedConstraints
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨touchedRowVarAt M n hn2 htb hns S hlen j, ?_⟩
  simp only [Finset.mem_inter, List.mem_toFinset]
  exact ⟨hi, touchedRowVarAt_mem M n hn2 htb hns S hlen j⟩

/-- Source choice for one window: either dormant (`none`) or a concrete
constraint from the row-variable support fibre. -/
structure TouchedWindowSource
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : S.length = Nat.log 2 n)
    (j : Fin (Nat.log 2 n)) where
  source : Option (cookLevinConstraintIdx M n hn2 htb hns)
  source_mem_fibre : ∀ i, source = some i →
    i ∈ touchedWindowSupportFibre M n hn2 htb hns S hlen j

/-- Turn fibre-backed source data plus an interface symbol into the previous
concrete-window record. -/
def touchedConcreteWindow_of_source
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : S.length = Nat.log 2 n)
    (j : Fin (Nat.log 2 n))
    (src : TouchedWindowSource M n hn2 htb hns S hlen j)
    (interface : PallLean.Paper93.InterfaceType) :
    TouchedConcreteWindow M n hn2 htb hns S hlen j where
  rowVar := touchedRowVarAt M n hn2 htb hns S hlen j
  rowVar_eq := rfl
  source := src.source
  source_touched := by
    intro i hi
    exact mem_touched_of_mem_windowSupportFibre M n hn2 htb hns S hlen j i
      (src.source_mem_fibre i hi)
  source_support := by
    intro i hi
    have hfibre := src.source_mem_fibre i hi
    unfold touchedWindowSupportFibre at hfibre
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hfibre
  interface := interface

/-- Window-source KR data.

The hard theorem is now: choose, for each row position, a dormant/source fibre
entry and an interface symbol, then prove the exact split row is interpreted by
those symbols. -/
def CookLevinTouchedWindowSourceKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (interp : touchedKRWords 16 (Nat.log 2 n) →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (_sourceOf :
      (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) →
      (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) →
      (alloc : cookLevinConstraintIdx M n hn2 htb hns →
        List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) →
      (hlen : S.length = Nat.log 2 n) →
      (j : Fin (Nat.log 2 n)) →
        TouchedWindowSource M n hn2 htb hns S hlen j)
    (interfaceOf :
      (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) →
      (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) →
      (alloc : cookLevinConstraintIdx M n hn2 htb hns →
        List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) →
      (hlen : S.length = Nat.log 2 n) →
      (j : Fin (Nat.log 2 n)) →
        PallLean.Paper93.InterfaceType),
    ∀ (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (alloc : cookLevinConstraintIdx M n hn2 htb hns →
        List (Fin (cookLevinTableau M n hn2 htb hns).numVars)),
      (hlen : S.length = Nat.log 2 n) →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible (cookLevinTableau M n hn2 htb hns).partition S →
      (∀ i, ∀ v ∈ alloc i, v ∈ S) →
      (∀ i, ∀ v ∈ alloc i,
        v ∈ ((cookLevinTableau M n hn2 htb hns).constraints.get i).support) →
      (∀ i, (alloc i).length ≤ 6) →
      (∀ i, i ∉ cookLevinTouchedConstraints M n hn2 htb hns S → alloc i = []) →
      touchedSplitRow M n hn2 htb hns S m alloc =
        interp (fun j => touchedInterfaceStateCode (interfaceOf S m alloc hlen j))

/-- Source-fibre data supplies the concrete-window seam. -/
theorem touchedConcreteWindowKRData_of_touchedWindowSourceKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hData : CookLevinTouchedWindowSourceKRData M n hn2 htb hns) :
    CookLevinTouchedConcreteWindowKRData M n hn2 htb hns := by
  rcases hData with ⟨interp, sourceOf, interfaceOf, hsound⟩
  refine ⟨interp, ?_, ?_⟩
  · intro S m alloc hlen j
    exact touchedConcreteWindow_of_source M n hn2 htb hns S hlen j
      (sourceOf S m alloc hlen j) (interfaceOf S m alloc hlen j)
  · intro S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc hout
    exact hsound S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc hout

/-- Uniform source-fibre KR data at paper scale. -/
def Step247UniformTouchedWindowSourceKRData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinTouchedWindowSourceKRData M n hn2 htb hns

/-- Uniform source-fibre data implies the concrete-window seam. -/
theorem step247UniformTouchedConcreteWindowKRData_of_touchedWindowSourceKRData
    (hData : Step247UniformTouchedWindowSourceKRData) :
    Step247UniformTouchedConcreteWindowKRData := by
  intro M n hn hn2 htb hns
  exact touchedConcreteWindowKRData_of_touchedWindowSourceKRData
    M n hn2 htb hns (hData M n hn hn2 htb hns)

/-- Uniform source-fibre data closes Route B. -/
theorem noBoundedSATDeciderAtPaperScale_of_touchedWindowSourceKRData_TPhi
    (hData : Step247UniformTouchedWindowSourceKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedConcreteWindowKRData_TPhi
    (step247UniformTouchedConcreteWindowKRData_of_touchedWindowSourceKRData hData)

/-! ## Axiom audit anchors -/

#print axioms touchedRowVarAt_mem
#print axioms mem_touched_of_mem_windowSupportFibre
#print axioms touchedConcreteWindow_of_source
#print axioms touchedConcreteWindowKRData_of_touchedWindowSourceKRData
#print axioms step247UniformTouchedConcreteWindowKRData_of_touchedWindowSourceKRData
#print axioms noBoundedSATDeciderAtPaperScale_of_touchedWindowSourceKRData_TPhi

end PallLean.Paper93.DeepMath.PathB
