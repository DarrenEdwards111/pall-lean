import PallLean.Paper93.DeepMath.PathB.RouteBTouchedLocalAlphabetKR

/-!
# Route B touched extractor KR seam

This file removes the last opaque `∃ word` classifier from the local-alphabet
KR surface.  The paper proof classifies a row by reading a bounded local state
at each of the `κ = log₂ n` row positions.  We expose exactly that shape:

* `localState S m alloc j : Fin C₃` extracts the local normal-form state at
  position `j : Fin(log₂ n)`;
* the global KR word is the function `j ↦ localState ... j`;
* the split row equals the interpretation of this extracted word.

The actual remaining work is now to instantiate `localState` from the real
Cook--Levin local compiled-coordinate windows and prove the interpretation
identity.  No arbitrary global generator/span is introduced.
-/

set_option exponentiation.threshold 1024

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- The extracted word assembled from the row-local classifier. -/
def touchedExtractedWord
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (C₃ : ℕ)
    (localState :
      (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) →
      (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) →
      (alloc : cookLevinConstraintIdx M n hn2 htb hns →
        List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) →
      Fin (Nat.log 2 n) → Fin C₃)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) :
    touchedKRWords C₃ (Nat.log 2 n) :=
  fun j => localState S m alloc j

/-- Extractor-form touched KR data.

The classifier is not an existential word.  It is a per-position local-state
extractor whose assembled word is interpreted back to the exact split row.
This is the paper's finite-state / Khatri--Rao normal-form shape.
-/
def CookLevinTouchedExtractorKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (C₃ : ℕ)
    (interp : touchedKRWords C₃ (Nat.log 2 n) →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (localState :
      (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) →
      (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) →
      (alloc : cookLevinConstraintIdx M n hn2 htb hns →
        List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) →
      Fin (Nat.log 2 n) → Fin C₃),
    Nat.log 2 C₃ + 1 ≤ 200 ∧
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
        interp (touchedExtractedWord M n hn2 htb hns C₃ localState S m alloc)

/-- Extractor-form KR data supplies the local-alphabet classifier seam by taking
the classified word to be the extracted word. -/
theorem touchedLocalAlphabetKRData_of_touchedExtractorKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hData : CookLevinTouchedExtractorKRData M n hn2 htb hns) :
    CookLevinTouchedLocalAlphabetKRData M n hn2 htb hns := by
  rcases hData with ⟨C₃, interp, localState, hC₃, hsound⟩
  refine ⟨C₃, interp, hC₃, ?_⟩
  intro S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc hout
  refine ⟨touchedExtractedWord M n hn2 htb hns C₃ localState S m alloc, ?_⟩
  exact hsound S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc hout

/-- Uniform extractor-form KR data at paper scale. -/
def Step247UniformTouchedExtractorKRData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinTouchedExtractorKRData M n hn2 htb hns

/-- Uniform extractor-form KR data implies the local-alphabet seam. -/
theorem step247UniformTouchedLocalAlphabetKRData_of_touchedExtractorKRData
    (hData : Step247UniformTouchedExtractorKRData) :
    Step247UniformTouchedLocalAlphabetKRData := by
  intro M n hn hn2 htb hns
  exact touchedLocalAlphabetKRData_of_touchedExtractorKRData
    M n hn2 htb hns (hData M n hn hn2 htb hns)

/-- Uniform extractor-form KR data closes Route B. -/
theorem noBoundedSATDeciderAtPaperScale_of_touchedExtractorKRData_TPhi
    (hData : Step247UniformTouchedExtractorKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedLocalAlphabetKRData_TPhi
    (step247UniformTouchedLocalAlphabetKRData_of_touchedExtractorKRData hData)

/-! ## Axiom audit anchors -/

#print axioms touchedLocalAlphabetKRData_of_touchedExtractorKRData
#print axioms step247UniformTouchedLocalAlphabetKRData_of_touchedExtractorKRData
#print axioms noBoundedSATDeciderAtPaperScale_of_touchedExtractorKRData_TPhi

end PallLean.Paper93.DeepMath.PathB
