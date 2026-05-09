import PallLean.Paper93.DeepMath.PathB.RouteBTouchedWindowSourceKR

/-!
# Route B touched typed-source KR seam

This file removes the arbitrary `interfaceOf` function from the support-fibre
window-source seam.  The interface symbol is now forced to be assembled from:

* a concrete Cook--Levin constraint-type map on actual constraint indices;
* the selected source in the row-variable support fibre; and
* a bounded local normal-form state `Fin 4`.

Thus, whenever a window is non-dormant, its emitted `InterfaceType.constraintType`
is exactly the type of the selected Cook--Levin constraint.  Dormant windows use
the fixed dormant type.  The only remaining freedom is the real paper content:
construct the type map/local state map from Cook--Levin local gadgets and prove
the interpretation identity.
-/

set_option exponentiation.threshold 1024

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- Constraint type read from a source choice.  Dormant windows use the fixed
dormant type; non-dormant windows use the actual selected constraint's type. -/
def touchedSourceConstraintType
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (constraintTypeOf :
      cookLevinConstraintIdx M n hn2 htb hns → SymmetricPowerBound.ConstraintType)
    {S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)}
    {hlen : S.length = Nat.log 2 n}
    {j : Fin (Nat.log 2 n)}
    (src : TouchedWindowSource M n hn2 htb hns S hlen j) :
    SymmetricPowerBound.ConstraintType :=
  match src.source with
  | none => SymmetricPowerBound.ConstraintType.booleanity
  | some i => constraintTypeOf i

/-- The interface symbol forced by a typed source plus bounded local state. -/
def touchedTypedInterface
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (constraintTypeOf :
      cookLevinConstraintIdx M n hn2 htb hns → SymmetricPowerBound.ConstraintType)
    {S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)}
    {hlen : S.length = Nat.log 2 n}
    {j : Fin (Nat.log 2 n)}
    (src : TouchedWindowSource M n hn2 htb hns S hlen j)
    (localState : Fin 4) : PallLean.Paper93.InterfaceType where
  constraintType := touchedSourceConstraintType constraintTypeOf src
  localState := localState

/-- Typed-source KR data.

`interfaceOf` has disappeared.  The emitted interface word is built from
`sourceOf`, `constraintTypeOf`, and `localStateOf`. -/
def CookLevinTouchedTypedSourceKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (interp : touchedKRWords 16 (Nat.log 2 n) →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (constraintTypeOf :
      cookLevinConstraintIdx M n hn2 htb hns → SymmetricPowerBound.ConstraintType)
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
          (touchedTypedInterface constraintTypeOf (sourceOf S m alloc hlen j)
            (localStateOf S m alloc hlen j)))

/-- Typed-source data supplies the previous source-fibre seam by constructing
`interfaceOf` from the forced typed source. -/
theorem touchedWindowSourceKRData_of_touchedTypedSourceKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hData : CookLevinTouchedTypedSourceKRData M n hn2 htb hns) :
    CookLevinTouchedWindowSourceKRData M n hn2 htb hns := by
  rcases hData with ⟨interp, constraintTypeOf, sourceOf, localStateOf, hsound⟩
  refine ⟨interp, sourceOf, ?_, ?_⟩
  · intro S m alloc hlen j
    exact touchedTypedInterface constraintTypeOf (sourceOf S m alloc hlen j)
      (localStateOf S m alloc hlen j)
  · intro S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc hout
    exact hsound S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc hout

/-- Uniform typed-source KR data at paper scale. -/
def Step247UniformTouchedTypedSourceKRData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinTouchedTypedSourceKRData M n hn2 htb hns

/-- Uniform typed-source data implies the source-fibre seam. -/
theorem step247UniformTouchedWindowSourceKRData_of_touchedTypedSourceKRData
    (hData : Step247UniformTouchedTypedSourceKRData) :
    Step247UniformTouchedWindowSourceKRData := by
  intro M n hn hn2 htb hns
  exact touchedWindowSourceKRData_of_touchedTypedSourceKRData
    M n hn2 htb hns (hData M n hn hn2 htb hns)

/-- Uniform typed-source data closes Route B. -/
theorem noBoundedSATDeciderAtPaperScale_of_touchedTypedSourceKRData_TPhi
    (hData : Step247UniformTouchedTypedSourceKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedWindowSourceKRData_TPhi
    (step247UniformTouchedWindowSourceKRData_of_touchedTypedSourceKRData hData)

/-! ## Axiom audit anchors -/

#print axioms touchedSourceConstraintType
#print axioms touchedTypedInterface
#print axioms touchedWindowSourceKRData_of_touchedTypedSourceKRData
#print axioms step247UniformTouchedWindowSourceKRData_of_touchedTypedSourceKRData
#print axioms noBoundedSATDeciderAtPaperScale_of_touchedTypedSourceKRData_TPhi

end PallLean.Paper93.DeepMath.PathB
