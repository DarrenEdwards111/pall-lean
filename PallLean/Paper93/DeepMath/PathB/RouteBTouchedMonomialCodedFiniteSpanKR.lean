import PallLean.Paper93.DeepMath.PathB.RouteBTouchedMonomialInterfaceFiniteSpanKR

/-!
# Route B touched monomial coded finite-span seam

The concrete `InterfaceType = Fin 16` seam is useful as a small interface
skeleton, but it is not yet the full paper §9.3 local chart code.  The local KR
normal form may need a larger absolute alphabet to encode bounded coordinate
and local-gadget chart data.  This file exposes that paper-faithful final
shape:

* an absolute alphabet size `C₃` with Step-223 polynomial growth;
* a canonical code word of length `log n` for each exact monomial touched row;
* a bounded local basis (`Fin C₃`) attached to each word;
* every exact monomial touched row lies in the span of its word's local basis.

The global generator count is `C₃ * C₃^(log n)`, absorbed into
`(C₃^2)^(log n)` at paper scale.
-/

set_option exponentiation.threshold 1024

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- Fully coded finite-span data for exact monomial touched rows.  This is the
paper's local chart/KR target: construct the code and the per-code bounded
basis from actual Cook--Levin local gadget normal forms. -/
def CookLevinTouchedMonomialCodedFiniteSpanData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (C₃ : ℕ)
    (_hC₃ : Nat.log 2 (C₃ ^ 2) + 1 ≤ 200)
    (codeOf : TouchedMonomialInterfaceDatum M n hn2 htb hns →
      touchedKRWords C₃ (Nat.log 2 n))
    (localBasis : touchedKRWords C₃ (Nat.log 2 n) → Fin C₃ →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ),
    ∀ D : TouchedMonomialInterfaceDatum M n hn2 htb hns,
      D.row ∈ Submodule.span ℚ
        ((Set.range (localBasis (codeOf D))) : Set
          (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))

/-- The fixed-interface finite-span theorem is a special case of the coded
finite-span target, with `C₃ = 16` and the canonical interface word as the code.
This is only a packaging bridge: it does not replace the paper's local chart
proof, but it ensures any eventual fixed-interface chart theorem lands directly
in the final coded Route B target. -/
theorem touchedMonomialCodedFiniteSpan_of_interfaceFiniteSpan
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hfinite : CookLevinTouchedMonomialInterfaceFiniteSpanData
      M n hn2 htb hns) :
    CookLevinTouchedMonomialCodedFiniteSpanData M n hn2 htb hns := by
  rcases hfinite with ⟨localBasis, hrow⟩
  refine ⟨16, ?_, (fun D => D.word), localBasis, ?_⟩
  · decide
  · intro D
    exact hrow D
/-- Global generator set from coded words and bounded basis slots. -/
noncomputable def touchedMonomialCodedFiniteGeneratorSet
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (C₃ : ℕ)
    (localBasis : touchedKRWords C₃ (Nat.log 2 n) → Fin C₃ →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) :
    Finset (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) :=
  (Finset.univ : Finset (touchedKRWords C₃ (Nat.log 2 n) × Fin C₃)).image
    (fun wb => localBasis wb.1 wb.2)

/-- The coded finite generator set has at most `C₃ * C₃^(log₂ n)` elements. -/
theorem touchedMonomialCodedFiniteGeneratorSet_card_le
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (C₃ : ℕ)
    (localBasis : touchedKRWords C₃ (Nat.log 2 n) → Fin C₃ →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) :
    (touchedMonomialCodedFiniteGeneratorSet M n hn2 htb hns C₃ localBasis).card ≤
      C₃ * C₃ ^ Nat.log 2 n := by
  classical
  unfold touchedMonomialCodedFiniteGeneratorSet touchedKRWords
  calc
    ((Finset.univ : Finset ((Fin (Nat.log 2 n) → Fin C₃) × Fin C₃)).image
        (fun wb => localBasis wb.1 wb.2)).card
        ≤ (Finset.univ : Finset ((Fin (Nat.log 2 n) → Fin C₃) × Fin C₃)).card :=
      Finset.card_image_le
    _ = C₃ ^ Nat.log 2 n * C₃ := by simp [Fintype.card_fin]
    _ = C₃ * C₃ ^ Nat.log 2 n := by rw [mul_comm]

/-- The one-slot-per-word overhead is absorbed by squaring the alphabet, for
`log₂ n ≥ 1`. -/
theorem C_mul_C_pow_log_le_C_sq_pow_log
    (C₃ n : ℕ) (hn2 : n ≥ 2) :
    C₃ * C₃ ^ Nat.log 2 n ≤ (C₃ ^ 2) ^ Nat.log 2 n := by
  have hlog : 1 ≤ Nat.log 2 n := by
    exact Nat.le_log_of_pow_le (by decide : 1 < 2)
      (by simpa using hn2)
  by_cases hC : C₃ = 0
  · subst hC
    simp
  · calc
      C₃ * C₃ ^ Nat.log 2 n = C₃ ^ (Nat.log 2 n + 1) := by
        rw [pow_succ, mul_comm]
      _ ≤ C₃ ^ (2 * Nat.log 2 n) := by
        apply Nat.pow_le_pow_right
        · exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hC)
        · omega
      _ = (C₃ ^ 2) ^ Nat.log 2 n := by rw [pow_mul]

/-- Coded finite generator count fits inside the Route B polynomial envelope. -/
theorem touchedMonomialCodedFiniteGeneratorSet_card_le_n_pow_200
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (C₃ : ℕ)
    (hC₃ : Nat.log 2 (C₃ ^ 2) + 1 ≤ 200)
    (localBasis : touchedKRWords C₃ (Nat.log 2 n) → Fin C₃ →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) :
    (touchedMonomialCodedFiniteGeneratorSet M n hn2 htb hns C₃ localBasis).card ≤
      n ^ 200 := by
  have hcard := touchedMonomialCodedFiniteGeneratorSet_card_le
    M n hn2 htb hns C₃ localBasis
  exact hcard.trans
    ((C_mul_C_pow_log_le_C_sq_pow_log C₃ n hn2).trans
      (touchedKR_constant_card_le_n_pow_200 (C₃ ^ 2) n hn hC₃))

/-- Coded finite-span data supplies the monomial-shift KR cover. -/
theorem touchedMonomialShiftKRData_of_monomialCodedFiniteSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hData : CookLevinTouchedMonomialCodedFiniteSpanData M n hn2 htb hns) :
    CookLevinTouchedMonomialShiftKRData M n hn2 htb hns := by
  classical
  rcases hData with ⟨C₃, hC₃, codeOf, localBasis, hrow⟩
  let G := touchedMonomialCodedFiniteGeneratorSet M n hn2 htb hns C₃ localBasis
  refine ⟨G, ?_, ?_⟩
  · exact touchedMonomialCodedFiniteGeneratorSet_card_le_n_pow_200
      M n hn hn2 htb hns C₃ hC₃ localBasis
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
      change localBasis (codeOf D) slot ∈ G
      unfold G touchedMonomialCodedFiniteGeneratorSet
      exact Finset.mem_image.mpr ⟨(codeOf D, slot), by simp, rfl⟩)) hlocal

/-- Uniform coded finite-span data at paper scale. -/
def Step247UniformTouchedMonomialCodedFiniteSpanData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinTouchedMonomialCodedFiniteSpanData M n hn2 htb hns


/-- Uniform fixed-interface finite-span data supplies the final coded finite-span
Route B target. -/
theorem step247UniformTouchedMonomialCodedFiniteSpanData_of_interfaceFiniteSpan
    (hfinite : Step247UniformTouchedMonomialInterfaceFiniteSpanData) :
    Step247UniformTouchedMonomialCodedFiniteSpanData := by
  intro M n hn hn2 htb hns
  exact touchedMonomialCodedFiniteSpan_of_interfaceFiniteSpan
    M n hn2 htb hns (hfinite M n hn hn2 htb hns)

/-- Uniform coded finite-span data supplies uniform monomial-shift KR data. -/
theorem step247UniformTouchedMonomialShiftKRData_of_monomialCodedFiniteSpan
    (hData : Step247UniformTouchedMonomialCodedFiniteSpanData) :
    Step247UniformTouchedMonomialShiftKRData := by
  intro M n hn hn2 htb hns
  exact touchedMonomialShiftKRData_of_monomialCodedFiniteSpan
    M n hn hn2 htb hns (hData M n hn hn2 htb hns)

/-- Uniform coded finite-span data closes Route B via the monomial-shift
linearity bridge. -/
theorem noBoundedSATDeciderAtPaperScale_of_touchedMonomialCodedFiniteSpanData_TPhi
    (hData : Step247UniformTouchedMonomialCodedFiniteSpanData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedMonomialShiftKRData_TPhi
    (step247UniformTouchedMonomialShiftKRData_of_monomialCodedFiniteSpan hData)

/-! ## Axiom audit anchors -/

#print axioms touchedMonomialCodedFiniteSpan_of_interfaceFiniteSpan
#print axioms step247UniformTouchedMonomialCodedFiniteSpanData_of_interfaceFiniteSpan
#print axioms touchedMonomialCodedFiniteGeneratorSet_card_le
#print axioms C_mul_C_pow_log_le_C_sq_pow_log
#print axioms touchedMonomialCodedFiniteGeneratorSet_card_le_n_pow_200
#print axioms touchedMonomialShiftKRData_of_monomialCodedFiniteSpan
#print axioms step247UniformTouchedMonomialShiftKRData_of_monomialCodedFiniteSpan
#print axioms noBoundedSATDeciderAtPaperScale_of_touchedMonomialCodedFiniteSpanData_TPhi

end PallLean.Paper93.DeepMath.PathB
