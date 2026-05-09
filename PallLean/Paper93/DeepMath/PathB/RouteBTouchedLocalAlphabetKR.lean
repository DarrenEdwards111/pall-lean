import PallLean.Paper93.DeepMath.PathB.RouteBTouchedConstantKR

/-!
# Route B touched local-alphabet KR seam

This file sharpens the constant-`C₃` touched KR seam into the paper's local
normal-form/classifier shape.

Instead of assuming an arbitrary finite generator set `G`, the remaining
obligation is now to provide:

* an absolute local alphabet `Fin C₃`;
* an interpretation of length-`log₂ n` words over that alphabet as row
  normal-form polynomials;
* a classifier sending each exact split touched row to one such word.

The generator family is then definitionally the image of the finite word set
under the interpretation map.  Its cardinality is bounded by `C₃^(log₂ n)` by
finite-function counting, and the row span follows from equality with the
classified normal form.  This avoids broadening to any global ambient monomial
span.
-/

set_option exponentiation.threshold 1024

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- Local KR words of length `κ` over an alphabet of size `C₃`. -/
abbrev touchedKRWords (C₃ κ : ℕ) : Type := Fin κ → Fin C₃

/-- The finite word family used for the local-alphabet KR generator set. -/
noncomputable def touchedKRWordFinset (C₃ κ : ℕ) : Finset (touchedKRWords C₃ κ) :=
  Finset.univ

/-- The number of `κ`-step local KR words is exactly `C₃^κ`. -/
theorem touchedKRWordFinset_card (C₃ κ : ℕ) :
    (touchedKRWordFinset C₃ κ).card = C₃ ^ κ := by
  classical
  unfold touchedKRWordFinset touchedKRWords
  simp

/-- The exact split touched row polynomial whose local normal form must be
classified by the Khatri--Rao construction. -/
noncomputable def touchedSplitRow
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) :
    MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ :=
  MultilinearSPDP.mlProj
    (m *
      (((Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).filter
        (fun i => i ∈ cookLevinTouchedConstraints M n hn2 htb hns S)).prod
          (fun i => SPDP.iterDerivList (alloc i)
            (cookLevinConstraintFactor M n hn2 htb hns i)) *
      ((Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).filter
        (fun i => i ∉ cookLevinTouchedConstraints M n hn2 htb hns S)).prod
          (fun i => SPDP.iterDerivList (alloc i)
            (cookLevinConstraintFactor M n hn2 htb hns i))))

/-- Local-alphabet touched split KR data.

This is the paper-faithful normal-form surface: every exact split row is equal
to the interpretation of one word in a fixed local alphabet, with word length
`log₂ n`.  The generator set is therefore the image of all such words, not an
ad hoc global span.
-/
def CookLevinTouchedLocalAlphabetKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (C₃ : ℕ)
    (interp : touchedKRWords C₃ (Nat.log 2 n) →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ),
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
      ∃ word : touchedKRWords C₃ (Nat.log 2 n),
        touchedSplitRow M n hn2 htb hns S m alloc = interp word

/-- The local-alphabet image generator family. -/
noncomputable def touchedLocalAlphabetGeneratorSet
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (C₃ : ℕ)
    (interp : touchedKRWords C₃ (Nat.log 2 n) →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) :
    Finset (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) :=
  (touchedKRWordFinset C₃ (Nat.log 2 n)).image interp

/-- The local-alphabet image family has size at most `C₃^(log₂ n)`. -/
theorem touchedLocalAlphabetGeneratorSet_card_le
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (C₃ : ℕ)
    (interp : touchedKRWords C₃ (Nat.log 2 n) →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) :
    (touchedLocalAlphabetGeneratorSet M n hn2 htb hns C₃ interp).card ≤
      C₃ ^ Nat.log 2 n := by
  classical
  unfold touchedLocalAlphabetGeneratorSet
  calc
    ((touchedKRWordFinset C₃ (Nat.log 2 n)).image interp).card
        ≤ (touchedKRWordFinset C₃ (Nat.log 2 n)).card := Finset.card_image_le
    _ = C₃ ^ Nat.log 2 n := touchedKRWordFinset_card C₃ (Nat.log 2 n)

/-- Local-alphabet KR data supplies the constant-`C₃` split KR seam. -/
theorem touchedConstantSplitKRData_of_touchedLocalAlphabetKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hData : CookLevinTouchedLocalAlphabetKRData M n hn2 htb hns) :
    CookLevinTouchedConstantSplitKRData M n hn2 htb hns := by
  classical
  rcases hData with ⟨C₃, interp, hC₃, hclass⟩
  refine ⟨C₃, touchedLocalAlphabetGeneratorSet M n hn2 htb hns C₃ interp,
    hC₃, ?_, ?_⟩
  · exact touchedLocalAlphabetGeneratorSet_card_le M n hn2 htb hns C₃ interp
  · intro S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc hout
    rcases hclass S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc hout with
      ⟨word, hrow⟩
    unfold touchedSplitRow at hrow
    rw [hrow]
    exact Submodule.subset_span (by
      unfold touchedLocalAlphabetGeneratorSet
      exact Finset.mem_image.mpr ⟨word, by simp [touchedKRWordFinset], rfl⟩)

/-- Uniform local-alphabet KR data at paper scale. -/
def Step247UniformTouchedLocalAlphabetKRData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinTouchedLocalAlphabetKRData M n hn2 htb hns

/-- Uniform local-alphabet KR data implies the constant split seam. -/
theorem step247UniformTouchedConstantSplitKRData_of_touchedLocalAlphabetKRData
    (hData : Step247UniformTouchedLocalAlphabetKRData) :
    Step247UniformTouchedConstantSplitKRData := by
  intro M n hn hn2 htb hns
  exact touchedConstantSplitKRData_of_touchedLocalAlphabetKRData
    M n hn2 htb hns (hData M n hn hn2 htb hns)

/-- Uniform local-alphabet KR data closes Route B. -/
theorem noBoundedSATDeciderAtPaperScale_of_touchedLocalAlphabetKRData_TPhi
    (hData : Step247UniformTouchedLocalAlphabetKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedConstantSplitKRData_TPhi
    (step247UniformTouchedConstantSplitKRData_of_touchedLocalAlphabetKRData hData)

/-! ## Axiom audit anchors -/

#print axioms touchedKRWordFinset_card
#print axioms touchedLocalAlphabetGeneratorSet_card_le
#print axioms touchedConstantSplitKRData_of_touchedLocalAlphabetKRData
#print axioms step247UniformTouchedConstantSplitKRData_of_touchedLocalAlphabetKRData
#print axioms noBoundedSATDeciderAtPaperScale_of_touchedLocalAlphabetKRData_TPhi

end PallLean.Paper93.DeepMath.PathB
