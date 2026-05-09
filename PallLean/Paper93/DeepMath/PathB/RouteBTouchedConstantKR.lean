import PallLean.Paper93.DeepMath.PathB.RouteBTouchedIncidenceCountKR

/-!
# Route B touched constant KR seam

This file exposes the paper-faithful `C₃^κ` Khatri--Rao surface for the
already split touched-row problem.

The previous incidence seam uses a generator family with cardinality
`≤ n^200`.  The paper's actual KR accounting is sharper and more structural:
a fixed local alphabet/normal-form constant `C₃` gives `≤ C₃^κ` rows, and with
`κ = log₂ n` this is polynomial in `n`.  Here we keep that constant explicit
and convert `C₃^log n` to the existing `n^200` Route B budget only by the
paper's Step 223 arithmetic.  The remaining work is therefore the real local
Khatri--Rao construction of the `C₃`-alphabet generator family, not a global
ambient span shortcut.
-/

set_option exponentiation.threshold 1024

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- The touched split KR obligation with the paper's absolute local KR constant
made explicit.

`C₃` is the finite local compiled-coordinate / normal-form alphabet size from
the Khatri--Rao proof.  The span obligation is still the exact split row from
`RouteBTouchedSplitKR`; the only change is that the generator count is stated
as `C₃^(log₂ n)` instead of immediately as `n^200`.
-/
def CookLevinTouchedConstantSplitKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (C₃ : ℕ) (G : Finset (MvPolynomial
      (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)),
    Nat.log 2 C₃ + 1 ≤ 200 ∧
    G.card ≤ C₃ ^ Nat.log 2 n ∧
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
      MultilinearSPDP.mlProj
          (m *
            (((Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).filter
              (fun i => i ∈ cookLevinTouchedConstraints M n hn2 htb hns S)).prod
                (fun i => SPDP.iterDerivList (alloc i)
                  (cookLevinConstraintFactor M n hn2 htb hns i)) *
            ((Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).filter
              (fun i => i ∉ cookLevinTouchedConstraints M n hn2 htb hns S)).prod
                (fun i => SPDP.iterDerivList (alloc i)
                  (cookLevinConstraintFactor M n hn2 htb hns i)))) ∈
        Submodule.span ℚ (↑G : Set (MvPolynomial
          (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))

/-- The `C₃^log n` paper KR count fits inside the Route B `n^200` envelope at
the paper scale `n ≥ 2^804`, provided the explicit constant exponent satisfies
`log₂ C₃ + 1 ≤ 200`. -/
theorem touchedKR_constant_card_le_n_pow_200
    (C₃ n : ℕ) (hn : (2 : ℕ) ^ 804 ≤ n)
    (hC₃ : Nat.log 2 C₃ + 1 ≤ 200) :
    C₃ ^ Nat.log 2 n ≤ n ^ 200 := by
  have hn1 : (1 : ℕ) ≤ n := by
    have h2_le_2_804 : (2 : ℕ) ≤ (2 : ℕ) ^ 804 := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ 804 :=
          Nat.pow_le_pow_right (by decide : (1 : ℕ) ≤ 2) (by decide : 1 ≤ 804)
    exact le_trans (by decide : (1 : ℕ) ≤ 2) (le_trans h2_le_2_804 hn)
  exact (Step223.C_3_pow_log_n_le_n_pow_const C₃ n hn).trans
    (Nat.pow_le_pow_right hn1 hC₃)

/-- At paper scale, constant-split KR data supplies the split KR seam. -/
theorem touchedSplitKRData_of_touchedConstantSplitKRData
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hData : CookLevinTouchedConstantSplitKRData M n hn2 htb hns) :
    CookLevinTouchedSplitKRData M n hn2 htb hns := by
  rcases hData with ⟨C₃, G, hC₃, hcard, hcover⟩
  refine ⟨G, ?_, hcover⟩
  exact hcard.trans (touchedKR_constant_card_le_n_pow_200 C₃ n hn hC₃)

/-- Uniform constant-split KR data at paper scale. -/
def Step247UniformTouchedConstantSplitKRData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinTouchedConstantSplitKRData M n hn2 htb hns

/-- Uniform constant-split KR data implies the split-touched seam. -/
theorem step247UniformTouchedSplitKRData_of_touchedConstantSplitKRData
    (hData : Step247UniformTouchedConstantSplitKRData) :
    Step247UniformTouchedSplitKRData := by
  intro M n hn hn2 htb hns
  exact touchedSplitKRData_of_touchedConstantSplitKRData
    M n hn hn2 htb hns (hData M n hn hn2 htb hns)

/-- Uniform constant-split KR data also supplies the incidence-count seam; the
incidence count itself is already proved in `RouteBTouchedIncidenceCountKR`. -/
theorem step247UniformTouchedIncidenceSplitKRData_of_touchedConstantSplitKRData
    (hData : Step247UniformTouchedConstantSplitKRData) :
    Step247UniformTouchedIncidenceSplitKRData := by
  intro M n hn hn2 htb hns
  exact touchedIncidenceSplitKRData_of_touchedSplitKRData
    M n hn2 htb hns
    (touchedSplitKRData_of_touchedConstantSplitKRData
      M n hn hn2 htb hns (hData M n hn hn2 htb hns))

/-- Uniform constant-split KR data closes Route B. -/
theorem noBoundedSATDeciderAtPaperScale_of_touchedConstantSplitKRData_TPhi
    (hData : Step247UniformTouchedConstantSplitKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedSplitKRData_TPhi
    (step247UniformTouchedSplitKRData_of_touchedConstantSplitKRData hData)

/-! ## Axiom audit anchors -/

#print axioms touchedKR_constant_card_le_n_pow_200
#print axioms touchedSplitKRData_of_touchedConstantSplitKRData
#print axioms step247UniformTouchedSplitKRData_of_touchedConstantSplitKRData
#print axioms step247UniformTouchedIncidenceSplitKRData_of_touchedConstantSplitKRData
#print axioms noBoundedSATDeciderAtPaperScale_of_touchedConstantSplitKRData_TPhi

end PallLean.Paper93.DeepMath.PathB
