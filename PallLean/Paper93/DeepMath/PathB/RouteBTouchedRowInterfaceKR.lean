import PallLean.Paper93.DeepMath.PathB.RouteBTouchedCanonicalSourceKR

/-!
# Route B touched row-interface KR seam

This file corrects the final local-state seam in the paper-faithful direction.
The §9.3 local normal form is a row/window object: it depends not only on the
static support geometry of the selected Cook--Levin constraint, but also on the
SPDP row data (`m` and derivative allocation `alloc`).

We therefore make the four-state component of `InterfaceType` a concrete
row-local state:

* bit 0 records whether the row variable participates in the shift monomial
  `m` (`v ∈ m.vars`);
* bit 1 records whether the row variable is one of the derivative variables
  allocated to the selected local constraint.

This is still finite (`Fin 4`) and local, but no longer incorrectly ignores the
actual row/window choices.  The remaining theorem is the exact interpretation
identity for the resulting canonical row-interface word.
-/

set_option exponentiation.threshold 1024

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- Encode two local row bits into the fixed four-state alphabet. -/
def rowLocalStateCode (inShift inDeriv : Bool) : Fin 4 :=
  match inShift, inDeriv with
  | false, false => ⟨0, by decide⟩
  | true,  false => ⟨1, by decide⟩
  | false, true  => ⟨2, by decide⟩
  | true,  true  => ⟨3, by decide⟩

/-- Whether the row variable at position `j` participates in the derivative
allocation of the selected canonical source.  Dormant windows have no selected
derivative source. -/
noncomputable def canonicalTouchedDerivBit
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : S.length = Nat.log 2 n)
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (j : Fin (Nat.log 2 n)) : Bool :=
  match canonicalTouchedSourceIdx M n hn2 htb hns S hlen j with
  | none => false
  | some i =>
      decide (touchedRowVarAt M n hn2 htb hns S hlen j ∈ alloc i)

/-- Concrete row-local state for one KR position, derived from the row's shift
monomial and selected derivative allocation. -/
noncomputable def canonicalTouchedRowLocalState
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : S.length = Nat.log 2 n)
    (j : Fin (Nat.log 2 n)) : Fin 4 :=
  rowLocalStateCode
    (decide (touchedRowVarAt M n hn2 htb hns S hlen j ∈ m.vars))
    (canonicalTouchedDerivBit M n hn2 htb hns S hlen alloc j)

/-- Fully row-aware canonical interface symbol at one KR position.  The source
and constraint type come from the actual support fibre; the local state comes
from the concrete SPDP row data. -/
noncomputable def canonicalTouchedRowInterface
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : S.length = Nat.log 2 n)
    (j : Fin (Nat.log 2 n)) : PallLean.Paper93.InterfaceType :=
  touchedActualInterface
    (canonicalTouchedWindowSource M n hn2 htb hns S hlen j)
    (canonicalTouchedRowLocalState M n hn2 htb hns S m alloc hlen j)

/-- Non-dormant derivative bit expands to membership in the selected allocation
list. -/
theorem canonicalTouchedDerivBit_eq_true_of_source
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : S.length = Nat.log 2 n)
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (j : Fin (Nat.log 2 n))
    (i : cookLevinConstraintIdx M n hn2 htb hns)
    (hi : canonicalTouchedSourceIdx M n hn2 htb hns S hlen j = some i) :
    canonicalTouchedDerivBit M n hn2 htb hns S hlen alloc j =
      decide (touchedRowVarAt M n hn2 htb hns S hlen j ∈ alloc i) := by
  unfold canonicalTouchedDerivBit
  simp [hi]

/-- Row-interface KR data.

The interface word is now canonically determined by the concrete Cook--Levin
source/type data plus the actual SPDP row data (`m`, `alloc`).  The remaining
content is exactly the local-gadget interpretation theorem. -/
def CookLevinTouchedRowInterfaceKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (interp : touchedKRWords 16 (Nat.log 2 n) →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ),
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
          (canonicalTouchedRowInterface M n hn2 htb hns S m alloc hlen j))

/-- Row-interface data supplies the canonical-source seam by using the row-local
state as `localStateOf`. -/
theorem touchedCanonicalSourceKRData_of_touchedRowInterfaceKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hData : CookLevinTouchedRowInterfaceKRData M n hn2 htb hns) :
    CookLevinTouchedCanonicalSourceKRData M n hn2 htb hns := by
  rcases hData with ⟨interp, hsound⟩
  refine ⟨interp, ?_, ?_⟩
  · intro S m alloc hlen j
    exact canonicalTouchedRowLocalState M n hn2 htb hns S m alloc hlen j
  · intro S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc hout
    exact hsound S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc hout

/-- Uniform row-interface KR data at paper scale. -/
def Step247UniformTouchedRowInterfaceKRData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinTouchedRowInterfaceKRData M n hn2 htb hns

/-- Uniform row-interface data implies the canonical-source seam. -/
theorem step247UniformTouchedCanonicalSourceKRData_of_touchedRowInterfaceKRData
    (hData : Step247UniformTouchedRowInterfaceKRData) :
    Step247UniformTouchedCanonicalSourceKRData := by
  intro M n hn hn2 htb hns
  exact touchedCanonicalSourceKRData_of_touchedRowInterfaceKRData
    M n hn2 htb hns (hData M n hn hn2 htb hns)

/-- Uniform row-interface data closes Route B. -/
theorem noBoundedSATDeciderAtPaperScale_of_touchedRowInterfaceKRData_TPhi
    (hData : Step247UniformTouchedRowInterfaceKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedCanonicalSourceKRData_TPhi
    (step247UniformTouchedCanonicalSourceKRData_of_touchedRowInterfaceKRData hData)

/-! ## Axiom audit anchors -/

#print axioms rowLocalStateCode
#print axioms canonicalTouchedDerivBit
#print axioms canonicalTouchedRowLocalState
#print axioms canonicalTouchedRowInterface
#print axioms canonicalTouchedDerivBit_eq_true_of_source
#print axioms touchedCanonicalSourceKRData_of_touchedRowInterfaceKRData
#print axioms step247UniformTouchedCanonicalSourceKRData_of_touchedRowInterfaceKRData
#print axioms noBoundedSATDeciderAtPaperScale_of_touchedRowInterfaceKRData_TPhi

end PallLean.Paper93.DeepMath.PathB
