import PallLean.Paper93.DeepMath.PathB.RouteBTouchedRowInterfaceKR

/-!
# Route B touched row-interface uniqueness seam

The previous row-interface file exposed the desired exact classifier

`row = interp (canonical row-interface word)`.

There is a crucial paper-faithful obstruction: such an `interp` is legitimate
only if the canonical local word is a *complete normal form* for the exact row.
We therefore isolate the real §9.3 normal-form theorem as a uniqueness
principle: two admissible touched rows with the same canonical row-interface
word have the same exact split row.

From that uniqueness theorem we construct the interpreter by choosing one
representative row for each inhabited word-fibre.  No arbitrary global span is
introduced: the only mathematical content is precisely the fibre-uniqueness
normal-form theorem.
-/

set_option exponentiation.threshold 1024

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- A concrete admissible touched row datum for the row-interface classifier. -/
structure TouchedRowInterfaceDatum
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)
  m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ
  alloc : cookLevinConstraintIdx M n hn2 htb hns →
    List (Fin (cookLevinTableau M n hn2 htb hns).numVars)
  hlen : S.length = Nat.log 2 n
  hdeg : m.totalDegree ≤ Nat.log 2 n
  hmvars : m.vars ⊆ S.toFinset
  hadm : SPDP.isBlockAdmissible (cookLevinTableau M n hn2 htb hns).partition S
  hall : ∀ i, ∀ v ∈ alloc i, v ∈ S
  hcompat : ∀ i, ∀ v ∈ alloc i,
    v ∈ ((cookLevinTableau M n hn2 htb hns).constraints.get i).support
  hlenAlloc : ∀ i, (alloc i).length ≤ 6
  hout : ∀ i, i ∉ cookLevinTouchedConstraints M n hn2 htb hns S → alloc i = []

/-- The exact split row attached to an admissible datum. -/
noncomputable def TouchedRowInterfaceDatum.row
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : TouchedRowInterfaceDatum M n hn2 htb hns) :
    MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ :=
  touchedSplitRow M n hn2 htb hns D.S D.m D.alloc

/-- The canonical coded row-interface word attached to an admissible datum. -/
noncomputable def TouchedRowInterfaceDatum.word
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : TouchedRowInterfaceDatum M n hn2 htb hns) :
    touchedKRWords 16 (Nat.log 2 n) :=
  fun j => touchedInterfaceStateCode
    (canonicalTouchedRowInterface M n hn2 htb hns D.S D.m D.alloc D.hlen j)

/-- Equality of canonical coded row words decodes pointwise to equality of the
concrete row-interface symbols.  This is the first finite-alphabet normal-form
payload: after injectivity of `Fin 16`, no information is hidden in the code. -/
theorem TouchedRowInterfaceDatum.interface_eq_of_word_eq
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {D₁ D₂ : TouchedRowInterfaceDatum M n hn2 htb hns}
    (hword : D₁.word = D₂.word) (j : Fin (Nat.log 2 n)) :
    canonicalTouchedRowInterface M n hn2 htb hns D₁.S D₁.m D₁.alloc D₁.hlen j =
      canonicalTouchedRowInterface M n hn2 htb hns D₂.S D₂.m D₂.alloc D₂.hlen j := by
  apply touchedInterfaceStateCode_injective
  simpa [TouchedRowInterfaceDatum.word] using congrFun hword j

/-- The row-interface word determines the concrete four-state local code at
position `j`. -/
theorem TouchedRowInterfaceDatum.localState_eq_of_word_eq
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {D₁ D₂ : TouchedRowInterfaceDatum M n hn2 htb hns}
    (hword : D₁.word = D₂.word) (j : Fin (Nat.log 2 n)) :
    canonicalTouchedRowLocalState M n hn2 htb hns D₁.S D₁.m D₁.alloc D₁.hlen j =
      canonicalTouchedRowLocalState M n hn2 htb hns D₂.S D₂.m D₂.alloc D₂.hlen j := by
  have hif := TouchedRowInterfaceDatum.interface_eq_of_word_eq
    (D₁ := D₁) (D₂ := D₂) hword j
  exact congrArg PallLean.Paper93.InterfaceType.localState hif

/-- The decoded local state determines the two concrete row-local bits: whether
the row variable appears in the shift monomial and whether it appears in the
selected derivative allocation. -/
theorem TouchedRowInterfaceDatum.rowLocalBits_eq_of_word_eq
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {D₁ D₂ : TouchedRowInterfaceDatum M n hn2 htb hns}
    (hword : D₁.word = D₂.word) (j : Fin (Nat.log 2 n)) :
    (decide (touchedRowVarAt M n hn2 htb hns D₁.S D₁.hlen j ∈ D₁.m.vars),
        canonicalTouchedDerivBit M n hn2 htb hns D₁.S D₁.hlen D₁.alloc j) =
      (decide (touchedRowVarAt M n hn2 htb hns D₂.S D₂.hlen j ∈ D₂.m.vars),
        canonicalTouchedDerivBit M n hn2 htb hns D₂.S D₂.hlen D₂.alloc j) := by
  apply rowLocalStateCode_injective
  simpa [canonicalTouchedRowLocalState] using
    TouchedRowInterfaceDatum.localState_eq_of_word_eq
      (D₁ := D₁) (D₂ := D₂) hword j

/-- The row-interface word determines the shift-membership bit at position `j`. -/
theorem TouchedRowInterfaceDatum.shiftBit_eq_of_word_eq
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {D₁ D₂ : TouchedRowInterfaceDatum M n hn2 htb hns}
    (hword : D₁.word = D₂.word) (j : Fin (Nat.log 2 n)) :
    decide (touchedRowVarAt M n hn2 htb hns D₁.S D₁.hlen j ∈ D₁.m.vars) =
      decide (touchedRowVarAt M n hn2 htb hns D₂.S D₂.hlen j ∈ D₂.m.vars) := by
  exact congrArg Prod.fst
    (TouchedRowInterfaceDatum.rowLocalBits_eq_of_word_eq
      (D₁ := D₁) (D₂ := D₂) hword j)

/-- The row-interface word determines the selected derivative-allocation bit at
position `j`. -/
theorem TouchedRowInterfaceDatum.derivBit_eq_of_word_eq
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {D₁ D₂ : TouchedRowInterfaceDatum M n hn2 htb hns}
    (hword : D₁.word = D₂.word) (j : Fin (Nat.log 2 n)) :
    canonicalTouchedDerivBit M n hn2 htb hns D₁.S D₁.hlen D₁.alloc j =
      canonicalTouchedDerivBit M n hn2 htb hns D₂.S D₂.hlen D₂.alloc j := by
  exact congrArg Prod.snd
    (TouchedRowInterfaceDatum.rowLocalBits_eq_of_word_eq
      (D₁ := D₁) (D₂ := D₂) hword j)

/-- Equality of row-interface words also determines the emitted actual
Cook--Levin constraint type at each position.  This is the branch-type component
of the §9.3 local classifier. -/
theorem TouchedRowInterfaceDatum.constraintType_eq_of_word_eq
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {D₁ D₂ : TouchedRowInterfaceDatum M n hn2 htb hns}
    (hword : D₁.word = D₂.word) (j : Fin (Nat.log 2 n)) :
    (canonicalTouchedRowInterface M n hn2 htb hns D₁.S D₁.m D₁.alloc D₁.hlen j).constraintType =
      (canonicalTouchedRowInterface M n hn2 htb hns D₂.S D₂.m D₂.alloc D₂.hlen j).constraintType := by
  have hif := TouchedRowInterfaceDatum.interface_eq_of_word_eq
    (D₁ := D₁) (D₂ := D₂) hword j
  exact congrArg PallLean.Paper93.InterfaceType.constraintType hif

/-- The paper §9.3 local-normal-form uniqueness theorem needed for the exact
row-interface interpreter.

This is the non-shortcut content: the canonical local row-interface word must
be complete for the exact touched split row. -/
def CookLevinTouchedRowInterfaceUniqueData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ D₁ D₂ : TouchedRowInterfaceDatum M n hn2 htb hns,
    D₁.word = D₂.word → D₁.row = D₂.row

/-- Representative existence for a row-interface word. -/
def touchedRowWordInhabited
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (word : touchedKRWords 16 (Nat.log 2 n)) : Prop :=
  ∃ D : TouchedRowInterfaceDatum M n hn2 htb hns, D.word = word

/-- The canonical interpreter induced by the uniqueness theorem: choose one
representative row from each inhabited word-fibre, and use zero on empty
fibres. -/
noncomputable def touchedRowInterfaceInterpOfUnique
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (word : touchedKRWords 16 (Nat.log 2 n)) :
    MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ := by
  classical
  exact
    if h : touchedRowWordInhabited M n hn2 htb hns word then
      (Classical.choose h).row
    else
      0

/-- On an inhabited fibre, the chosen representative has the requested word. -/
theorem touchedRowInterfaceInterpOfUnique_choose_word
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (word : touchedKRWords 16 (Nat.log 2 n))
    (h : touchedRowWordInhabited M n hn2 htb hns word) :
    (Classical.choose h).word = word :=
  Classical.choose_spec h

/-- The uniqueness theorem constructs the exact row-interface interpreter. -/
theorem touchedRowInterfaceKRData_of_unique
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (huniq : CookLevinTouchedRowInterfaceUniqueData M n hn2 htb hns) :
    CookLevinTouchedRowInterfaceKRData M n hn2 htb hns := by
  classical
  refine ⟨touchedRowInterfaceInterpOfUnique M n hn2 htb hns, ?_⟩
  intro S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc hout
  let D : TouchedRowInterfaceDatum M n hn2 htb hns :=
    { S := S
      m := m
      alloc := alloc
      hlen := hlen
      hdeg := hdeg
      hmvars := hmvars
      hadm := hadm
      hall := hall
      hcompat := hcompat
      hlenAlloc := hlenAlloc
      hout := hout }
  have hinh : touchedRowWordInhabited M n hn2 htb hns D.word := ⟨D, rfl⟩
  have hchosenWord :
      (Classical.choose hinh).word = D.word :=
    touchedRowInterfaceInterpOfUnique_choose_word M n hn2 htb hns D.word hinh
  have hrow : (Classical.choose hinh).row = D.row :=
    huniq (Classical.choose hinh) D hchosenWord
  change D.row = touchedRowInterfaceInterpOfUnique M n hn2 htb hns D.word
  rw [show touchedRowInterfaceInterpOfUnique M n hn2 htb hns D.word =
      (Classical.choose hinh).row by
    unfold touchedRowInterfaceInterpOfUnique
    simp [hinh]]
  exact hrow.symm

/-- Uniform row-interface uniqueness at paper scale. -/
def Step247UniformTouchedRowInterfaceUniqueData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinTouchedRowInterfaceUniqueData M n hn2 htb hns

/-- Uniform uniqueness supplies uniform row-interface KR data. -/
theorem step247UniformTouchedRowInterfaceKRData_of_unique
    (huniq : Step247UniformTouchedRowInterfaceUniqueData) :
    Step247UniformTouchedRowInterfaceKRData := by
  intro M n hn hn2 htb hns
  exact touchedRowInterfaceKRData_of_unique M n hn2 htb hns
    (huniq M n hn hn2 htb hns)

/-- Uniform row-interface uniqueness closes Route B through the established
row-interface chain. -/
theorem noBoundedSATDeciderAtPaperScale_of_touchedRowInterfaceUniqueData_TPhi
    (huniq : Step247UniformTouchedRowInterfaceUniqueData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedRowInterfaceKRData_TPhi
    (step247UniformTouchedRowInterfaceKRData_of_unique huniq)

/-! ## Axiom audit anchors -/

#print axioms TouchedRowInterfaceDatum.row
#print axioms TouchedRowInterfaceDatum.word
#print axioms TouchedRowInterfaceDatum.interface_eq_of_word_eq
#print axioms TouchedRowInterfaceDatum.localState_eq_of_word_eq
#print axioms TouchedRowInterfaceDatum.rowLocalBits_eq_of_word_eq
#print axioms TouchedRowInterfaceDatum.shiftBit_eq_of_word_eq
#print axioms TouchedRowInterfaceDatum.derivBit_eq_of_word_eq
#print axioms TouchedRowInterfaceDatum.constraintType_eq_of_word_eq
#print axioms touchedRowInterfaceInterpOfUnique
#print axioms touchedRowInterfaceInterpOfUnique_choose_word
#print axioms touchedRowInterfaceKRData_of_unique
#print axioms step247UniformTouchedRowInterfaceKRData_of_unique
#print axioms noBoundedSATDeciderAtPaperScale_of_touchedRowInterfaceUniqueData_TPhi

end PallLean.Paper93.DeepMath.PathB
