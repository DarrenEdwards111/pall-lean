import PallLean.Paper93.DeepMath.PathB.RouteBTouchedMonomialShiftKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedRowInterfaceKR

/-!
# Route B touched monomial-interface uniqueness seam

This is the paper-faithful version of the final local-normal-form seam after
separating arbitrary shift polynomials from the finite local classifier.

The finite local word classifies only monomial-shift rows.  Arbitrary SPDP
multipliers are handled by the linearity bridge in
`RouteBTouchedMonomialShiftKR`, not encoded into the finite alphabet.
-/

set_option exponentiation.threshold 1024

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- A concrete admissible touched row datum with a monomial shift support `T`. -/
structure TouchedMonomialInterfaceDatum
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)
  T : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars)
  alloc : cookLevinConstraintIdx M n hn2 htb hns →
    List (Fin (cookLevinTableau M n hn2 htb hns).numVars)
  hlen : S.length = Nat.log 2 n
  hTsubset : T ⊆ S.toFinset
  hadm : SPDP.isBlockAdmissible (cookLevinTableau M n hn2 htb hns).partition S
  hall : ∀ i, ∀ v ∈ alloc i, v ∈ S
  hcompat : ∀ i, ∀ v ∈ alloc i,
    v ∈ ((cookLevinTableau M n hn2 htb hns).constraints.get i).support
  hlenAlloc : ∀ i, (alloc i).length ≤ 6
  hout : ∀ i, i ∉ cookLevinTouchedConstraints M n hn2 htb hns S → alloc i = []

/-- The exact monomial-shift split row attached to a datum. -/
noncomputable def TouchedMonomialInterfaceDatum.row
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : TouchedMonomialInterfaceDatum M n hn2 htb hns) :
    MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ :=
  touchedMonomialSplitRow M n hn2 htb hns D.S D.T D.alloc

/-- The canonical coded interface word for a monomial-shift datum. -/
noncomputable def TouchedMonomialInterfaceDatum.word
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : TouchedMonomialInterfaceDatum M n hn2 htb hns) :
    touchedKRWords 16 (Nat.log 2 n) :=
  fun j => touchedInterfaceStateCode
    (canonicalTouchedRowInterface M n hn2 htb hns D.S
      (touchedShiftMonomial D.T) D.alloc D.hlen j)

/-- Paper §9.3 local-normal-form uniqueness for monomial touched rows.

This is the real finite-normal-form theorem: the canonical local word must be
complete for the exact monomial-shift touched split row. -/
def CookLevinTouchedMonomialInterfaceUniqueData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ D₁ D₂ : TouchedMonomialInterfaceDatum M n hn2 htb hns,
    D₁.word = D₂.word → D₁.row = D₂.row

/-- A monomial-interface word is inhabited if it arises from an admissible
monomial touched row. -/
def touchedMonomialWordInhabited
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (word : touchedKRWords 16 (Nat.log 2 n)) : Prop :=
  ∃ D : TouchedMonomialInterfaceDatum M n hn2 htb hns, D.word = word

/-- Interpreter induced by monomial-interface uniqueness: choose one exact row
from each inhabited word fibre, and use zero on empty fibres. -/
noncomputable def touchedMonomialInterfaceInterpOfUnique
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (word : touchedKRWords 16 (Nat.log 2 n)) :
    MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ := by
  classical
  exact
    if h : touchedMonomialWordInhabited M n hn2 htb hns word then
      (Classical.choose h).row
    else
      0

/-- On an inhabited monomial-interface fibre, the representative has the target
word. -/
theorem touchedMonomialInterfaceInterpOfUnique_choose_word
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (word : touchedKRWords 16 (Nat.log 2 n))
    (h : touchedMonomialWordInhabited M n hn2 htb hns word) :
    (Classical.choose h).word = word :=
  Classical.choose_spec h

/-- Monomial-interface uniqueness supplies the monomial-shift KR cover.

The generator family is exactly the image of all finite local words under the
uniqueness-induced interpreter, so the cardinality is `16^(log₂ n)` and hence
fits the Route B `n^200` budget by the already exposed Step 223 arithmetic. -/
theorem touchedMonomialShiftKRData_of_monomialInterfaceUnique
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (huniq : CookLevinTouchedMonomialInterfaceUniqueData M n hn2 htb hns) :
    CookLevinTouchedMonomialShiftKRData M n hn2 htb hns := by
  classical
  let interp := touchedMonomialInterfaceInterpOfUnique M n hn2 htb hns
  let G := touchedLocalAlphabetGeneratorSet M n hn2 htb hns 16 interp
  refine ⟨G, ?_, ?_⟩
  · have hGcard : G.card ≤ 16 ^ Nat.log 2 n := by
      simpa [G, interp] using
        touchedLocalAlphabetGeneratorSet_card_le M n hn2 htb hns 16 interp
    exact hGcard.trans
      (touchedKR_constant_card_le_n_pow_200 16 n hn
        touchedInterfaceAlphabet_log_bound)
  · intro S T alloc hlen hTsubset hadm hall hcompat hlenAlloc hout
    let D : TouchedMonomialInterfaceDatum M n hn2 htb hns :=
      { S := S
        T := T
        alloc := alloc
        hlen := hlen
        hTsubset := hTsubset
        hadm := hadm
        hall := hall
        hcompat := hcompat
        hlenAlloc := hlenAlloc
        hout := hout }
    have hinh : touchedMonomialWordInhabited M n hn2 htb hns D.word := ⟨D, rfl⟩
    have hchosenWord :
        (Classical.choose hinh).word = D.word :=
      touchedMonomialInterfaceInterpOfUnique_choose_word M n hn2 htb hns D.word hinh
    have hrow : (Classical.choose hinh).row = D.row :=
      huniq (Classical.choose hinh) D hchosenWord
    have hrowInterp : D.row = interp D.word := by
      change D.row = touchedMonomialInterfaceInterpOfUnique M n hn2 htb hns D.word
      rw [show touchedMonomialInterfaceInterpOfUnique M n hn2 htb hns D.word =
          (Classical.choose hinh).row by
        unfold touchedMonomialInterfaceInterpOfUnique
        simp [hinh]]
      exact hrow.symm
    change D.row ∈ Submodule.span ℚ (↑G : Set (MvPolynomial
      (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))
    rw [hrowInterp]
    exact Submodule.subset_span (by
      change interp D.word ∈ G
      unfold G touchedLocalAlphabetGeneratorSet touchedKRWordFinset
      exact Finset.mem_image.mpr ⟨D.word, by simp, rfl⟩)

/-- Uniform monomial-interface uniqueness at paper scale. -/
def Step247UniformTouchedMonomialInterfaceUniqueData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinTouchedMonomialInterfaceUniqueData M n hn2 htb hns

/-- Uniform monomial-interface uniqueness supplies uniform monomial-shift KR
data. -/
theorem step247UniformTouchedMonomialShiftKRData_of_monomialInterfaceUnique
    (huniq : Step247UniformTouchedMonomialInterfaceUniqueData) :
    Step247UniformTouchedMonomialShiftKRData := by
  intro M n hn hn2 htb hns
  exact touchedMonomialShiftKRData_of_monomialInterfaceUnique
    M n hn hn2 htb hns (huniq M n hn hn2 htb hns)

/-- Uniform monomial-interface uniqueness closes Route B via the monomial-shift
linearity bridge. -/
theorem noBoundedSATDeciderAtPaperScale_of_touchedMonomialInterfaceUniqueData_TPhi
    (huniq : Step247UniformTouchedMonomialInterfaceUniqueData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedMonomialShiftKRData_TPhi
    (step247UniformTouchedMonomialShiftKRData_of_monomialInterfaceUnique huniq)

/-! ## Axiom audit anchors -/

#print axioms TouchedMonomialInterfaceDatum.row
#print axioms TouchedMonomialInterfaceDatum.word
#print axioms touchedMonomialInterfaceInterpOfUnique
#print axioms touchedMonomialInterfaceInterpOfUnique_choose_word
#print axioms touchedMonomialShiftKRData_of_monomialInterfaceUnique
#print axioms step247UniformTouchedMonomialShiftKRData_of_monomialInterfaceUnique
#print axioms noBoundedSATDeciderAtPaperScale_of_touchedMonomialInterfaceUniqueData_TPhi

end PallLean.Paper93.DeepMath.PathB
