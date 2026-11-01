import GodMoveSATSourceCanonicity
import Def12Measure

/-!
# G4 link: the branch's SAT characteristic vs a linear-time function under the paper's Def. 12

Kernel link of D9/D11 (`Def12Measure`) to the branch's own SAT polynomial
`GodMoveSATSourceCanonicity.languageCharacteristic SATLang L` at codex/godmove-gap-repairs @ 21921958
(which every correct SAT decider's normalized machine source equals, `machineSource_eq_SATCharacteristic`).

Multilinearity comes from the branch's `interpolate_isMultilinear`; no hypothesis about SAT is assumed.
The "easy" comparison polynomial is `subsetPoly m κ` (the MLE of the linear-time function
`[|y| = κ ∧ y ⊆ x]`, [C]/[I], NOTES G4.3 item 7-8), placed on the first `m+m` of `L` coordinates.
-/

set_option autoImplicit false

namespace G4SATLink

open MvPolynomial
open GodMoveBooleanInterpolation GodMoveSATSourceCanonicity
open PallLean.Paper93.DeepMath.PathB.SeparationTarget (SATLang)

/-- `subsetPoly` placed on `L = m+m` coordinates. -/
noncomputable def easyEven (L m κ : ℕ) (h : L = m + m) : MvPolynomial (Fin L) ℚ :=
  rename (Fin.cast h.symm) (Def12Measure.subsetPoly (F := ℚ) m κ)

/-- `subsetPoly` placed on the first `m+m` of `L = m+m+1` coordinates (last bit ignored). -/
noncomputable def easyOdd (L m κ : ℕ) (h : L = m + m + 1) : MvPolynomial (Fin L) ℚ :=
  rename (Fin.cast h.symm ∘ Fin.castSucc) (Def12Measure.subsetPoly (F := ℚ) m κ)

theorem satChar_isMultilinear (L : ℕ) :
    Def12Measure.IsMultilinear (languageCharacteristic SATLang L) := by
  intro α hα i
  exact interpolate_isMultilinear _ α hα i

/-- Even lengths. -/
theorem satChar_def12_le_even (c : Def12Measure.Conv) (L m : ℕ) (hL : L = m + m)
    (B B' : Def12Measure.BlockPartition L) (κ ℓ : ℕ) (hκ : 3 * κ ≤ 2 * m) (hℓ : 3 * ℓ ≤ 2 * m) :
    Def12Measure.def12Rank c B' κ ℓ (languageCharacteristic SATLang L) ≤
      4 ^ (κ + ℓ) * Def12Measure.def12Rank c B' κ ℓ (easyEven L m κ hL) := by
  have hp := satChar_isMultilinear L
  subst hL
  have he : easyEven (m + m) m κ rfl = Def12Measure.subsetPoly (F := ℚ) m κ := by
    simp [easyEven]
  rw [he]
  exact Def12Measure.multilinear_le_four_pow_mul_subset c B' κ ℓ hκ hℓ _ hp

/-- Odd lengths. -/
theorem satChar_def12_le_odd (c : Def12Measure.Conv) (L m : ℕ) (hL : L = m + m + 1)
    (B : Def12Measure.BlockPartition (m + m)) (B' : Def12Measure.BlockPartition L) (κ ℓ : ℕ)
    (hκ : 3 * κ ≤ 2 * m) (hℓ : 3 * ℓ ≤ 2 * m) :
    Def12Measure.def12Rank c B' κ ℓ (languageCharacteristic SATLang L) ≤
      4 ^ (κ + ℓ + 1) * Def12Measure.def12Rank c B' κ ℓ (easyOdd L m κ hL) := by
  have hp := satChar_isMultilinear L
  subst hL
  have he : easyOdd (m + m + 1) m κ rfl =
      rename (R := ℚ) Fin.castSucc (Def12Measure.subsetPoly (F := ℚ) m κ) := by
    simp [easyOdd]
  rw [he]
  exact Def12Measure.multilinear_le_four_pow_mul_subset_odd c B B' κ ℓ hκ hℓ _ hp

/-- Every length, every partition: the branch's SAT polynomial is within `4^(κ+ℓ+1)` of an
embedded `subsetPoly` (a linear-time function's MLE) under Def. 12, both conventions.
Exactly one of the two hypotheses `L = L/2 + L/2`, `L = L/2 + L/2 + 1` holds (`length_parity`). -/
theorem length_parity (L : ℕ) : L = L / 2 + L / 2 ∨ L = L / 2 + L / 2 + 1 := by omega

theorem satChar_def12_le_easy (c : Def12Measure.Conv) (L : ℕ) (B' : Def12Measure.BlockPartition L)
    (κ ℓ : ℕ) (hκ : 3 * κ ≤ 2 * (L / 2)) (hℓ : 3 * ℓ ≤ 2 * (L / 2)) :
    (∀ h : L = L / 2 + L / 2,
      Def12Measure.def12Rank c B' κ ℓ (languageCharacteristic SATLang L) ≤
        4 ^ (κ + ℓ + 1) * Def12Measure.def12Rank c B' κ ℓ (easyEven L (L / 2) κ h)) ∧
    (∀ h : L = L / 2 + L / 2 + 1,
      Def12Measure.def12Rank c B' κ ℓ (languageCharacteristic SATLang L) ≤
        4 ^ (κ + ℓ + 1) * Def12Measure.def12Rank c B' κ ℓ (easyOdd L (L / 2) κ h)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine (satChar_def12_le_even c L (L / 2) h B' B' κ ℓ hκ hℓ).trans ?_
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  · exact satChar_def12_le_odd c L (L / 2) h ⟨L / 2 + L / 2, id⟩ B' κ ℓ hκ hℓ

theorem nine_mul_add_six_le_two_pow (k : ℕ) (hk : 7 ≤ k) : 9 * k + 6 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

theorem nine_log_add_six_le (n : ℕ) (hn : 128 ≤ n) : 9 * Nat.log 2 n + 6 ≤ n := by
  have hp : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  by_cases hk : 7 ≤ Nat.log 2 n
  · exact (nine_mul_add_six_le_two_pow _ hk).trans hp
  · omega

theorem four_pow_log_le (n : ℕ) (hn : 1 ≤ n) :
    4 ^ (Nat.log 2 n + Nat.log 2 n + 1) ≤ 4 * n ^ 4 := by
  have hp : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h4 : (4 : ℕ) ^ (Nat.log 2 n + Nat.log 2 n + 1) = 4 * (2 ^ Nat.log 2 n) ^ 4 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; ring_nf
  rw [h4]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp 4)

/-- Paper parameters (branch's source length `L = unitSourceLength (n/3)`, κ = ℓ = ⌊log₂ n⌋),
for every `n ≥ 128` (in particular the paper window `n ≥ 2^804`), every partition, both Def. 12
conventions: the SAT polynomial's Def. 12 rank is at most `4·n⁴` times that of an embedded
linear-time `subsetPoly`. Hence no Def. 12 rank threshold separates SAT from a linear-time function
by more than a polynomial factor at these parameters. -/
theorem satChar_def12_le_easy_paper (c : Def12Measure.Conv) (n : ℕ) (hn : 128 ≤ n)
    (B' : Def12Measure.BlockPartition (unitSourceLength (n / 3))) :
    let L := unitSourceLength (n / 3)
    let k := Nat.log 2 n
    (∀ h : L = L / 2 + L / 2,
      Def12Measure.def12Rank c B' k k (languageCharacteristic SATLang L) ≤
        4 * n ^ 4 * Def12Measure.def12Rank c B' k k (easyEven L (L / 2) k h)) ∧
    (∀ h : L = L / 2 + L / 2 + 1,
      Def12Measure.def12Rank c B' k k (languageCharacteristic SATLang L) ≤
        4 * n ^ 4 * Def12Measure.def12Rank c B' k k (easyOdd L (L / 2) k h)) := by
  intro L k
  have hL : n / 3 ≤ L := n_le_unitSourceLength (n / 3)
  have hlog := nine_log_add_six_le n hn
  have hk : 3 * k ≤ 2 * (L / 2) := by omega
  have hpow := four_pow_log_le n (by omega)
  obtain ⟨h1, h2⟩ := satChar_def12_le_easy c L B' k k hk hk
  exact ⟨fun h => (h1 h).trans (Nat.mul_le_mul_right _ hpow),
    fun h => (h2 h).trans (Nat.mul_le_mul_right _ hpow)⟩

end G4SATLink

#print axioms G4SATLink.satChar_isMultilinear
#print axioms G4SATLink.satChar_def12_le_even
#print axioms G4SATLink.satChar_def12_le_odd
#print axioms G4SATLink.satChar_def12_le_easy
#print axioms G4SATLink.satChar_def12_le_easy_paper
#print axioms G4SATLink.length_parity
set_option pp.fullNames true in
#check @G4SATLink.satChar_def12_le_easy_paper
