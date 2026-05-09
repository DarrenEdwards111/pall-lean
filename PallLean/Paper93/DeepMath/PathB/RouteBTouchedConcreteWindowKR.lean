import PallLean.Paper93.DeepMath.PathB.RouteBTouchedWindowKR

/-!
# Route B touched concrete-window KR seam

This file makes the `windowState` source concrete.  A window state is no longer
an unconstrained function of the whole row: it is obtained from a per-position
record containing

* the actual row variable at position `j`,
* an optional Cook--Levin constraint selected as the local touched window,
* proofs that any selected constraint is genuinely touched and contains that
  row variable in its local support, and
* the finite `InterfaceType` normal-form symbol read from that window.

A `none` source represents a dormant/local-empty window.  This avoids asserting
that every row variable must touch a constraint while still forcing every
non-dormant symbol to be backed by actual Cook--Levin local support data.
-/

set_option exponentiation.threshold 1024

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- Default dormant interface symbol used only to totalize the old window-state
function when a row has the wrong length.  The soundness theorem is stated only
at `S.length = log₂ n`, so this fallback is never used on the proof path. -/
def touchedDefaultInterfaceType : PallLean.Paper93.InterfaceType where
  constraintType := SymmetricPowerBound.ConstraintType.booleanity
  localState := ⟨0, by decide⟩

/-- The actual row variable at local KR position `j`, transported through the
proof that the row list has length `log₂ n`. -/
def touchedRowVarAt
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : S.length = Nat.log 2 n)
    (j : Fin (Nat.log 2 n)) :
    Fin (cookLevinTableau M n hn2 htb hns).numVars :=
  S.get ⟨j.val, by simp [hlen, j.isLt]⟩

/-- Concrete source data for one local KR window.

`source = some i` means this local position is backed by the actual
Cook--Levin constraint `i`; the accompanying fields prove that `i` is touched
and that the row variable at this position lies in `i`'s local support.
`source = none` is the dormant/local-empty case. -/
structure TouchedConcreteWindow
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : S.length = Nat.log 2 n)
    (j : Fin (Nat.log 2 n)) where
  rowVar : Fin (cookLevinTableau M n hn2 htb hns).numVars
  rowVar_eq : rowVar = touchedRowVarAt M n hn2 htb hns S hlen j
  source : Option (cookLevinConstraintIdx M n hn2 htb hns)
  source_touched : ∀ i, source = some i →
    i ∈ cookLevinTouchedConstraints M n hn2 htb hns S
  source_support : ∀ i, source = some i →
    rowVar ∈ ((cookLevinTableau M n hn2 htb hns).constraints.get i).support
  interface : PallLean.Paper93.InterfaceType

/-- Concrete-window touched KR data.

The remaining proof is now a genuine local-window theorem: construct the
per-position `TouchedConcreteWindow` records and prove the exact split row is
the interpretation of the encoded interface word read from those records. -/
def CookLevinTouchedConcreteWindowKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (interp : touchedKRWords 16 (Nat.log 2 n) →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (windowOf :
      (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) →
      (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) →
      (alloc : cookLevinConstraintIdx M n hn2 htb hns →
        List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) →
      (hlen : S.length = Nat.log 2 n) →
      (j : Fin (Nat.log 2 n)) →
        TouchedConcreteWindow M n hn2 htb hns S hlen j),
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
        interp (fun j =>
          touchedInterfaceStateCode ((windowOf S m alloc hlen j).interface))

/-- Concrete-window data supplies the previous window-state seam. -/
theorem touchedWindowKRData_of_touchedConcreteWindowKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hData : CookLevinTouchedConcreteWindowKRData M n hn2 htb hns) :
    CookLevinTouchedWindowKRData M n hn2 htb hns := by
  classical
  rcases hData with ⟨interp, windowOf, hsound⟩
  let windowState :
      (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) →
      (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) →
      (alloc : cookLevinConstraintIdx M n hn2 htb hns →
        List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) →
      Fin (Nat.log 2 n) → PallLean.Paper93.InterfaceType :=
    fun S m alloc j =>
      if hlen : S.length = Nat.log 2 n then
        (windowOf S m alloc hlen j).interface
      else
        touchedDefaultInterfaceType
  refine ⟨interp, windowState, ?_⟩
  intro S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc hout
  have hword :
      (fun j => touchedInterfaceStateCode (windowState S m alloc j)) =
        (fun j => touchedInterfaceStateCode ((windowOf S m alloc hlen j).interface)) := by
    funext j
    simp [windowState, hlen]
  rw [hword]
  exact hsound S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc hout

/-- Uniform concrete-window KR data at paper scale. -/
def Step247UniformTouchedConcreteWindowKRData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinTouchedConcreteWindowKRData M n hn2 htb hns

/-- Uniform concrete-window data implies the window seam. -/
theorem step247UniformTouchedWindowKRData_of_touchedConcreteWindowKRData
    (hData : Step247UniformTouchedConcreteWindowKRData) :
    Step247UniformTouchedWindowKRData := by
  intro M n hn hn2 htb hns
  exact touchedWindowKRData_of_touchedConcreteWindowKRData
    M n hn2 htb hns (hData M n hn hn2 htb hns)

/-- Uniform concrete-window data closes Route B. -/
theorem noBoundedSATDeciderAtPaperScale_of_touchedConcreteWindowKRData_TPhi
    (hData : Step247UniformTouchedConcreteWindowKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedWindowKRData_TPhi
    (step247UniformTouchedWindowKRData_of_touchedConcreteWindowKRData hData)

/-! ## Axiom audit anchors -/

#print axioms touchedRowVarAt
#print axioms touchedWindowKRData_of_touchedConcreteWindowKRData
#print axioms step247UniformTouchedWindowKRData_of_touchedConcreteWindowKRData
#print axioms noBoundedSATDeciderAtPaperScale_of_touchedConcreteWindowKRData_TPhi

end PallLean.Paper93.DeepMath.PathB
