import PallLean.Paper93.DeepMath.PathB.RouteBTouchedMonomialInterfaceUniqueKR

/-!
# Route B touched monomial-interface span seam

The exact fibre-uniqueness statement is stronger than the P-side KR argument
requires.  Cook--Levin transition skeleton factors carry machine-dependent
rational coefficients (`transCoeff M q`), and those coefficients should live in
the ambient linear span, not in the finite local alphabet.

This file states the paper-faithful final normal-form target as a *span*
theorem for monomial-shift rows: each exact monomial touched row is in the span
of the generator attached to its canonical local interface word.  The global
generator family is still the image of all `16^(log n)` local words; arbitrary
polynomial shifts are still handled later by the monomial-shift linearity
bridge.
-/

set_option exponentiation.threshold 1024

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- Paper-faithful monomial-interface span data.

`normalFormGenerator word` is the local KR/Kronecker generator associated to a
canonical interface word.  The substantive theorem is `row_mem`: every exact
monomial-shift touched split row lands in the one-dimensional span of the
generator for its own canonical word.  This is the right algebraic target when
local gadgets have coefficients: scalars are handled by the span, not encoded
in the finite word.
-/
def CookLevinTouchedMonomialInterfaceSpanData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ normalFormGenerator : touchedKRWords 16 (Nat.log 2 n) →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ,
    ∀ D : TouchedMonomialInterfaceDatum M n hn2 htb hns,
      D.row ∈ Submodule.span ℚ
        ({normalFormGenerator D.word} : Set
          (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))

/-- The global image of the per-word normal-form generator. -/
noncomputable def touchedMonomialInterfaceGeneratorSet
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (normalFormGenerator : touchedKRWords 16 (Nat.log 2 n) →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) :
    Finset (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) :=
  (touchedKRWordFinset 16 (Nat.log 2 n)).image normalFormGenerator

/-- The image generator family has the expected `16^(log₂ n)` cardinality. -/
theorem touchedMonomialInterfaceGeneratorSet_card_le
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (normalFormGenerator : touchedKRWords 16 (Nat.log 2 n) →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) :
    (touchedMonomialInterfaceGeneratorSet M n hn2 htb hns normalFormGenerator).card ≤
      16 ^ Nat.log 2 n := by
  classical
  unfold touchedMonomialInterfaceGeneratorSet
  calc
    ((touchedKRWordFinset 16 (Nat.log 2 n)).image normalFormGenerator).card
        ≤ (touchedKRWordFinset 16 (Nat.log 2 n)).card := Finset.card_image_le
    _ = 16 ^ Nat.log 2 n := touchedKRWordFinset_card 16 (Nat.log 2 n)

/-- Monomial-interface span data supplies the monomial-shift KR cover. -/
theorem touchedMonomialShiftKRData_of_monomialInterfaceSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hspan : CookLevinTouchedMonomialInterfaceSpanData M n hn2 htb hns) :
    CookLevinTouchedMonomialShiftKRData M n hn2 htb hns := by
  classical
  rcases hspan with ⟨normalFormGenerator, hrow⟩
  let G := touchedMonomialInterfaceGeneratorSet M n hn2 htb hns normalFormGenerator
  refine ⟨G, ?_, ?_⟩
  · have hGcard : G.card ≤ 16 ^ Nat.log 2 n := by
      simpa [G] using
        touchedMonomialInterfaceGeneratorSet_card_le M n hn2 htb hns normalFormGenerator
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
    change D.row ∈ Submodule.span ℚ (↑G : Set (MvPolynomial
      (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))
    have hlocal := hrow D
    exact (Submodule.span_mono (by
      intro p hp
      rw [Set.mem_singleton_iff] at hp
      rw [hp]
      change normalFormGenerator D.word ∈ G
      unfold G touchedMonomialInterfaceGeneratorSet touchedKRWordFinset
      exact Finset.mem_image.mpr ⟨D.word, by simp, rfl⟩)) hlocal

/-- Uniform monomial-interface span data at paper scale. -/
def Step247UniformTouchedMonomialInterfaceSpanData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinTouchedMonomialInterfaceSpanData M n hn2 htb hns

/-- Uniform monomial-interface span data supplies uniform monomial-shift KR
data. -/
theorem step247UniformTouchedMonomialShiftKRData_of_monomialInterfaceSpan
    (hspan : Step247UniformTouchedMonomialInterfaceSpanData) :
    Step247UniformTouchedMonomialShiftKRData := by
  intro M n hn hn2 htb hns
  exact touchedMonomialShiftKRData_of_monomialInterfaceSpan
    M n hn hn2 htb hns (hspan M n hn hn2 htb hns)

/-- Uniform monomial-interface span data closes Route B via the monomial-shift
linearity bridge. -/
theorem noBoundedSATDeciderAtPaperScale_of_touchedMonomialInterfaceSpanData_TPhi
    (hspan : Step247UniformTouchedMonomialInterfaceSpanData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedMonomialShiftKRData_TPhi
    (step247UniformTouchedMonomialShiftKRData_of_monomialInterfaceSpan hspan)

/-! ## Axiom audit anchors -/

#print axioms touchedMonomialInterfaceGeneratorSet_card_le
#print axioms touchedMonomialShiftKRData_of_monomialInterfaceSpan
#print axioms step247UniformTouchedMonomialShiftKRData_of_monomialInterfaceSpan
#print axioms noBoundedSATDeciderAtPaperScale_of_touchedMonomialInterfaceSpanData_TPhi

end PallLean.Paper93.DeepMath.PathB
