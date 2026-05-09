import PallLean.Paper93.DeepMath.PathB.RouteBTouchedExtractorKR
import PallLean.Paper93.InterfaceAlphabet

/-!
# Route B touched window KR seam

This file pins the extractor state to the paper's finite interface-local window
alphabet.  Instead of an arbitrary `Fin C₃` state extractor, the state at each
row position is an actual `InterfaceType`:

* a Cook--Levin `ConstraintType`, and
* a bounded local normal-form state `Fin 4`.

We then encode `InterfaceType` into the fixed alphabet `Fin 16`, matching the
paper §9/§40 constant local alphabet.  The remaining substantive theorem is now
the window soundness identity: the exact split row equals the interpretation of
the word obtained by reading these local windows.
-/

set_option exponentiation.threshold 1024

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- Numeric code for the four Cook--Levin constraint types. -/
def touchedConstraintTypeCode : SymmetricPowerBound.ConstraintType → Fin 4
  | SymmetricPowerBound.ConstraintType.booleanity => ⟨0, by decide⟩
  | SymmetricPowerBound.ConstraintType.adjacency => ⟨1, by decide⟩
  | SymmetricPowerBound.ConstraintType.transitionLeft => ⟨2, by decide⟩
  | SymmetricPowerBound.ConstraintType.transitionRight => ⟨3, by decide⟩

/-- Encode the paper interface-local symbol `(constraint type, local state)` into
`Fin 16 = Fin (4 * 4)`. -/
def touchedInterfaceStateCode (σ : PallLean.Paper93.InterfaceType) : Fin 16 :=
  ⟨(touchedConstraintTypeCode σ.constraintType).val * 4 + σ.localState.val, by
    have hτ : (touchedConstraintTypeCode σ.constraintType).val < 4 :=
      (touchedConstraintTypeCode σ.constraintType).isLt
    have hs : σ.localState.val < 4 := σ.localState.isLt
    omega⟩

/-- Window-form touched KR data.

The per-position state is now a genuine paper interface-local symbol.  The
interpretation reads the encoded length-`log n` word and returns the exact
normal-form polynomial for the split row.
-/
def CookLevinTouchedWindowKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (interp : touchedKRWords 16 (Nat.log 2 n) →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (windowState :
      (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) →
      (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) →
      (alloc : cookLevinConstraintIdx M n hn2 htb hns →
        List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) →
      Fin (Nat.log 2 n) → PallLean.Paper93.InterfaceType),
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
      touchedSplitRow M n hn2 htb hns S m alloc =
        interp (fun j => touchedInterfaceStateCode (windowState S m alloc j))

/-- The fixed paper interface alphabet satisfies the exponent budget required by
Route B's `n^200` envelope. -/
theorem touchedInterfaceAlphabet_log_bound : Nat.log 2 16 + 1 ≤ 200 := by
  decide

/-- Window-form KR data supplies the extractor-form seam, with `C₃ = 16`. -/
theorem touchedExtractorKRData_of_touchedWindowKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hData : CookLevinTouchedWindowKRData M n hn2 htb hns) :
    CookLevinTouchedExtractorKRData M n hn2 htb hns := by
  rcases hData with ⟨interp, windowState, hsound⟩
  refine ⟨16, interp,
    (fun S m alloc j => touchedInterfaceStateCode (windowState S m alloc j)),
    touchedInterfaceAlphabet_log_bound, ?_⟩
  intro S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc hout
  exact hsound S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc hout

/-- Uniform window-form KR data at paper scale. -/
def Step247UniformTouchedWindowKRData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinTouchedWindowKRData M n hn2 htb hns

/-- Uniform window-form KR data implies the extractor seam. -/
theorem step247UniformTouchedExtractorKRData_of_touchedWindowKRData
    (hData : Step247UniformTouchedWindowKRData) :
    Step247UniformTouchedExtractorKRData := by
  intro M n hn hn2 htb hns
  exact touchedExtractorKRData_of_touchedWindowKRData
    M n hn2 htb hns (hData M n hn hn2 htb hns)

/-- Uniform window-form KR data closes Route B. -/
theorem noBoundedSATDeciderAtPaperScale_of_touchedWindowKRData_TPhi
    (hData : Step247UniformTouchedWindowKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedExtractorKRData_TPhi
    (step247UniformTouchedExtractorKRData_of_touchedWindowKRData hData)

/-! ## Axiom audit anchors -/

#print axioms touchedInterfaceStateCode
#print axioms touchedInterfaceAlphabet_log_bound
#print axioms touchedExtractorKRData_of_touchedWindowKRData
#print axioms step247UniformTouchedExtractorKRData_of_touchedWindowKRData
#print axioms noBoundedSATDeciderAtPaperScale_of_touchedWindowKRData_TPhi

end PallLean.Paper93.DeepMath.PathB
