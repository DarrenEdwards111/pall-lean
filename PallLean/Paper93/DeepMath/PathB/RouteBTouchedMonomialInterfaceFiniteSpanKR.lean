import PallLean.Paper93.DeepMath.PathB.RouteBTouchedMonomialInterfaceSpanKR

/-!
# Route B touched monomial-interface finite-span seam

The one-generator-per-word span seam is still a narrow special case of the
paper's local KR/profile argument.  A finite local interface word should index a
bounded-dimensional local normal-form space, not necessarily a single vector.

This file exposes that exact shape with a fixed `Fin 16` local basis at every
word.  The global generator set is indexed by `(word, basisSlot)`, so its size
is at most `16 * 16^(log n)`, which is still bounded by the Step 223 polynomial
envelope (via `256^(log n)`).
-/

set_option exponentiation.threshold 1024

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- A fixed `Fin 16` local basis per canonical interface word.  The real
Cook--Levin normal-form theorem must construct this basis from the local gadget
/Khatri--Rao factors and prove every exact monomial row lands in the span of
its word's basis. -/
def CookLevinTouchedMonomialInterfaceFiniteSpanData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ localBasis : touchedKRWords 16 (Nat.log 2 n) → Fin 16 →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ,
    ∀ D : TouchedMonomialInterfaceDatum M n hn2 htb hns,
      D.row ∈ Submodule.span ℚ
        ((Set.range (localBasis D.word)) : Set
          (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))

/-- Global generator set obtained from all words and their bounded local-basis
slots. -/
noncomputable def touchedMonomialInterfaceFiniteGeneratorSet
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (localBasis : touchedKRWords 16 (Nat.log 2 n) → Fin 16 →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) :
    Finset (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) :=
  (Finset.univ : Finset (touchedKRWords 16 (Nat.log 2 n) × Fin 16)).image
    (fun wb => localBasis wb.1 wb.2)

/-- The finite generator set has at most `16 * 16^(log₂ n)` elements. -/
theorem touchedMonomialInterfaceFiniteGeneratorSet_card_le
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (localBasis : touchedKRWords 16 (Nat.log 2 n) → Fin 16 →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) :
    (touchedMonomialInterfaceFiniteGeneratorSet M n hn2 htb hns localBasis).card ≤
      16 * 16 ^ Nat.log 2 n := by
  classical
  unfold touchedMonomialInterfaceFiniteGeneratorSet touchedKRWords
  calc
    ((Finset.univ : Finset ((Fin (Nat.log 2 n) → Fin 16) × Fin 16)).image
        (fun wb => localBasis wb.1 wb.2)).card
        ≤ (Finset.univ : Finset ((Fin (Nat.log 2 n) → Fin 16) × Fin 16)).card :=
      Finset.card_image_le
    _ = 16 ^ Nat.log 2 n * 16 := by simp
    _ = 16 * 16 ^ Nat.log 2 n := by rw [mul_comm]

/-- The fixed `Fin 16`-basis overhead is absorbed by replacing `16` with
`256` in the Step 223 `C^log n` estimate. -/
theorem sixteen_mul_sixteen_pow_log_le_twofiftysix_pow_log
    (n : ℕ) (hn2 : n ≥ 2) :
    16 * 16 ^ Nat.log 2 n ≤ 256 ^ Nat.log 2 n := by
  have hlog : 1 ≤ Nat.log 2 n := by
    exact Nat.le_log_of_pow_le (by decide : 1 < 2)
      (by simpa using hn2)
  calc
    16 * 16 ^ Nat.log 2 n = 16 ^ (Nat.log 2 n + 1) := by
      rw [pow_succ, mul_comm]
    _ ≤ 16 ^ (2 * Nat.log 2 n) := by
      apply Nat.pow_le_pow_right (by decide : 1 ≤ 16)
      omega
    _ = (16 ^ 2) ^ Nat.log 2 n := by
      rw [pow_mul]
    _ = 256 ^ Nat.log 2 n := by norm_num

/-- The fixed local-basis generator count fits into the `n^200` envelope at
paper scale. -/
theorem touchedMonomialInterfaceFiniteGeneratorSet_card_le_n_pow_200
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (localBasis : touchedKRWords 16 (Nat.log 2 n) → Fin 16 →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) :
    (touchedMonomialInterfaceFiniteGeneratorSet M n hn2 htb hns localBasis).card ≤
      n ^ 200 := by
  have hcard := touchedMonomialInterfaceFiniteGeneratorSet_card_le
    M n hn2 htb hns localBasis
  exact hcard.trans
    ((sixteen_mul_sixteen_pow_log_le_twofiftysix_pow_log n hn2).trans
      (touchedKR_constant_card_le_n_pow_200 256 n hn (by decide)))

/-- Finite-span data supplies the monomial-shift KR cover. -/
theorem touchedMonomialShiftKRData_of_monomialInterfaceFiniteSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hfinite : CookLevinTouchedMonomialInterfaceFiniteSpanData M n hn2 htb hns) :
    CookLevinTouchedMonomialShiftKRData M n hn2 htb hns := by
  classical
  rcases hfinite with ⟨localBasis, hrow⟩
  let G := touchedMonomialInterfaceFiniteGeneratorSet M n hn2 htb hns localBasis
  refine ⟨G, ?_, ?_⟩
  · exact touchedMonomialInterfaceFiniteGeneratorSet_card_le_n_pow_200
      M n hn hn2 htb hns localBasis
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
      rcases hp with ⟨slot, rfl⟩
      change localBasis D.word slot ∈ G
      unfold G touchedMonomialInterfaceFiniteGeneratorSet
      exact Finset.mem_image.mpr ⟨(D.word, slot), by simp, rfl⟩)) hlocal

/-- Uniform finite-span data at paper scale. -/
def Step247UniformTouchedMonomialInterfaceFiniteSpanData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinTouchedMonomialInterfaceFiniteSpanData M n hn2 htb hns

/-- Uniform finite-span data supplies uniform monomial-shift KR data. -/
theorem step247UniformTouchedMonomialShiftKRData_of_monomialInterfaceFiniteSpan
    (hfinite : Step247UniformTouchedMonomialInterfaceFiniteSpanData) :
    Step247UniformTouchedMonomialShiftKRData := by
  intro M n hn hn2 htb hns
  exact touchedMonomialShiftKRData_of_monomialInterfaceFiniteSpan
    M n hn hn2 htb hns (hfinite M n hn hn2 htb hns)

/-- Uniform finite-span data closes Route B via the monomial-shift linearity
bridge. -/
theorem noBoundedSATDeciderAtPaperScale_of_touchedMonomialInterfaceFiniteSpanData_TPhi
    (hfinite : Step247UniformTouchedMonomialInterfaceFiniteSpanData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedMonomialShiftKRData_TPhi
    (step247UniformTouchedMonomialShiftKRData_of_monomialInterfaceFiniteSpan hfinite)

/-! ## Axiom audit anchors -/

#print axioms touchedMonomialInterfaceFiniteGeneratorSet_card_le
#print axioms sixteen_mul_sixteen_pow_log_le_twofiftysix_pow_log
#print axioms touchedMonomialInterfaceFiniteGeneratorSet_card_le_n_pow_200
#print axioms touchedMonomialShiftKRData_of_monomialInterfaceFiniteSpan
#print axioms step247UniformTouchedMonomialShiftKRData_of_monomialInterfaceFiniteSpan
#print axioms noBoundedSATDeciderAtPaperScale_of_touchedMonomialInterfaceFiniteSpanData_TPhi

end PallLean.Paper93.DeepMath.PathB
