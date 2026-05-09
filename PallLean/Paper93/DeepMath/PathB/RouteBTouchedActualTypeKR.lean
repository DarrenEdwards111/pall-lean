import PallLean.Paper93.DeepMath.PathB.RouteBTouchedTypedSourceKR

/-!
# Route B touched actual-type KR seam

This file removes the remaining arbitrary constraint-type map from the
source/interface word.  For every non-dormant source `some i`, the emitted
`InterfaceType.constraintType` is forced to be the actual Cook--Levin type
`cookLevinConstraintType M n ... i`.

The remaining data is therefore exactly the next paper-local obligation:
choose real source windows and their bounded local normal-form state, and prove
that the resulting actual Cook--Levin interface word interprets the touched
split row.
-/

set_option exponentiation.threshold 1024

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- The concrete three-segment Cook--Levin constraint type on the actual
constraint-list index type used by the allocation/touched seams.

This mirrors the canonical concrete classification from `WithinProfileBound`:
the initial `n` slots are booleanity, the next adjacency-list segment is
adjacency, and the remaining local transition skeleton is transition-left. -/
noncomputable def cookLevinConstraintIdxType
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    cookLevinConstraintIdx M n hn2 htb hns → SymmetricPowerBound.ConstraintType :=
  fun i =>
    if i.1 < n then
      SymmetricPowerBound.ConstraintType.booleanity
    else if i.1 < n + (PaperFaithfulSeparation.adjConstraintList n).length then
      SymmetricPowerBound.ConstraintType.adjacency
    else
      SymmetricPowerBound.ConstraintType.transitionLeft

/-- Constraint type forced directly by the actual Cook--Levin constraint-list
index classification. Dormant windows retain the fixed dormant booleanity
symbol. -/
noncomputable def touchedActualSourceConstraintType
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)}
    {hlen : S.length = Nat.log 2 n}
    {j : Fin (Nat.log 2 n)}
    (src : TouchedWindowSource M n hn2 htb hns S hlen j) :
    SymmetricPowerBound.ConstraintType :=
  touchedSourceConstraintType (cookLevinConstraintIdxType M n hn2 htb hns) src

/-- The actual Cook--Levin interface symbol for a touched/dormant source and a
bounded local state. -/
noncomputable def touchedActualInterface
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)}
    {hlen : S.length = Nat.log 2 n}
    {j : Fin (Nat.log 2 n)}
    (src : TouchedWindowSource M n hn2 htb hns S hlen j)
    (localState : Fin 4) : PallLean.Paper93.InterfaceType :=
  touchedTypedInterface (cookLevinConstraintIdxType M n hn2 htb hns) src localState

/-- Actual-type source KR data.

No independent type map remains: the interface word is assembled from the
selected support-fibre source using `cookLevinConstraintType`. -/
def CookLevinTouchedActualTypeKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (interp : touchedKRWords 16 (Nat.log 2 n) →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (sourceOf :
      (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) →
      (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) →
      (alloc : cookLevinConstraintIdx M n hn2 htb hns →
        List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) →
      (hlen : S.length = Nat.log 2 n) →
      (j : Fin (Nat.log 2 n)) →
        TouchedWindowSource M n hn2 htb hns S hlen j)
    (localStateOf :
      (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) →
      (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) →
      (alloc : cookLevinConstraintIdx M n hn2 htb hns →
        List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) →
      (hlen : S.length = Nat.log 2 n) →
      (j : Fin (Nat.log 2 n)) → Fin 4),
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
        interp (fun j => touchedInterfaceStateCode
          (touchedActualInterface (sourceOf S m alloc hlen j)
            (localStateOf S m alloc hlen j)))

/-- Actual-type data supplies the typed-source seam by instantiating the type map
with `cookLevinConstraintType`. -/
theorem touchedTypedSourceKRData_of_touchedActualTypeKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hData : CookLevinTouchedActualTypeKRData M n hn2 htb hns) :
    CookLevinTouchedTypedSourceKRData M n hn2 htb hns := by
  rcases hData with ⟨interp, sourceOf, localStateOf, hsound⟩
  refine ⟨interp, cookLevinConstraintIdxType M n hn2 htb hns, sourceOf, localStateOf, ?_⟩
  intro S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc hout
  exact hsound S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc hout

/-- Uniform actual-type KR data at paper scale. -/
def Step247UniformTouchedActualTypeKRData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinTouchedActualTypeKRData M n hn2 htb hns

/-- Uniform actual-type data implies the typed-source seam. -/
theorem step247UniformTouchedTypedSourceKRData_of_touchedActualTypeKRData
    (hData : Step247UniformTouchedActualTypeKRData) :
    Step247UniformTouchedTypedSourceKRData := by
  intro M n hn hn2 htb hns
  exact touchedTypedSourceKRData_of_touchedActualTypeKRData
    M n hn2 htb hns (hData M n hn hn2 htb hns)

/-- Uniform actual-type data closes Route B. -/
theorem noBoundedSATDeciderAtPaperScale_of_touchedActualTypeKRData_TPhi
    (hData : Step247UniformTouchedActualTypeKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedTypedSourceKRData_TPhi
    (step247UniformTouchedTypedSourceKRData_of_touchedActualTypeKRData hData)

/-! ## Axiom audit anchors -/

#print axioms cookLevinConstraintIdxType
#print axioms touchedActualSourceConstraintType
#print axioms touchedActualInterface
#print axioms touchedTypedSourceKRData_of_touchedActualTypeKRData
#print axioms step247UniformTouchedTypedSourceKRData_of_touchedActualTypeKRData
#print axioms noBoundedSATDeciderAtPaperScale_of_touchedActualTypeKRData_TPhi

end PallLean.Paper93.DeepMath.PathB
