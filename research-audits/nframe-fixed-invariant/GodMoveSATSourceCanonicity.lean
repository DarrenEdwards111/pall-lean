import GodMoveMachineSourceMinor

/-!
# What SAT correctness determines in the normalized machine source

At any fixed encoded input length, normalization identifies every correct
decider with the same language characteristic. The resulting polynomial
does not retain differences in machine implementation or clock.

For the existing positive-unit query family, the encoded source length is
at most quadratic in the assignment-variable count. Its already proved
binomial minor therefore excludes every polynomial rank bound in that
actual encoded length, not just in the smaller family parameter. The
derivative order remains log₂ n; the shift budget is arbitrary.

These are semantic equalities and rank lower bounds. They do not prove a
rank upper bound from SAT runtime or a separation theorem.
-/

namespace GodMoveSATSourceCanonicity

open MvPolynomial SPDP MultilinearSPDP
open GodMoveBooleanInterpolation GodMoveCircuitConnection
open GodMoveMachineFaceExtraction GodMoveMachineSourceMinor
open GodMoveSymbolicPinnedInput GodMovePinnedSATQueries GodMoveUnitCharacteristic
open GodMoveMonomialMinor (discreteBlocks)
open PallLean.Paper93.DeepMath.PathB
open ComposableMachine ComposablePpolyDischarge SATCircuitSeparationBridge
open CookLevinReduction CookLevinEmitCodec SeparationTarget

/-- Canonical Boolean polynomial of a language on all words of one length.
Its definition is semantic and carries no polynomial construction bound. -/
noncomputable def languageCharacteristic (language : List Bool → Bool) (L : ℕ) : Poly L :=
  interpolate (fun a : Assignment L => language (wordOfFin a))

/-- Operational correctness fixes the normalized source exactly, without
requiring a runtime bound, polynomial identity, or rank hypothesis. -/
theorem normalizedSource_eq_languageCharacteristic
    (M : Machine) (language : List Bool → Bool) (T : ℕ → ℕ)
    (hD : Decides M language T) (L : ℕ) :
    circuitTarget (circuitFor M L (T L)) = languageCharacteristic language L := by
  rw [circuitTarget_eq_interpolate]
  apply interpolate_congr
  intro a
  rw [circuitFor_output]
  simpa only [wordOfFin_length] using (hD (wordOfFin a)).2

/-- Every two correct deciders have the same normalized source at a fixed
input length, even if their machines and halting clocks differ. -/
theorem normalizedSource_independent_of_decider
    (M₁ M₂ : Machine) (language : List Bool → Bool) (T₁ T₂ : ℕ → ℕ)
    (h₁ : Decides M₁ language T₁) (h₂ : Decides M₂ language T₂) (L : ℕ) :
    circuitTarget (circuitFor M₁ L (T₁ L)) =
      circuitTarget (circuitFor M₂ L (T₂ L)) := by
  rw [normalizedSource_eq_languageCharacteristic M₁ language T₁ h₁,
    normalizedSource_eq_languageCharacteristic M₂ language T₂ h₂]

theorem machineSource_eq_SATCharacteristic
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) (φ : Formula) (n : ℕ) :
    machineSource M T φ n = languageCharacteristic SATLang (inputTemplate φ n).length :=
  normalizedSource_eq_languageCharacteristic M SATLang T hD _

theorem machineSource_independent_of_SAT_decider
    (M₁ M₂ : Machine) (T₁ T₂ : ℕ → ℕ)
    (h₁ : Decides M₁ SATLang T₁) (h₂ : Decides M₂ SATLang T₂) (φ : Formula) (n : ℕ) :
    machineSource M₁ T₁ φ n = machineSource M₂ T₂ φ n :=
  normalizedSource_independent_of_decider M₁ M₂ SATLang T₁ T₂ h₁ h₂ _

/-- The production bit length of the positive-unit pinned query template. -/
def unitSourceLength (n : ℕ) : ℕ := (inputTemplate (unitFormula n) n).length

theorem encoded_unitFormula_length_le (n : ℕ) :
    (encodeFormula' (unitFormula n)).length ≤ (n + 1) + n * (2 * n + 8) := by
  have hc : ∀ c ∈ unitFormula n, c.length ≤ 1 := by
    intro c hc
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    simp
  have hv : ∀ c ∈ unitFormula n, ∀ l ∈ c, l.1 ≤ n :=
    fun c hc l hl => Nat.le_of_lt (unitFormula_variablesBelow n c hc l hl)
  have h := encodeFormula'_length_le (unitFormula n) n 1 hc hv
  simpa only [unitFormula_length, one_add_one_eq_two, one_mul,
    show 2 + (2 * n + 6) = 2 * n + 8 by omega] using h

/-- No relation between formula size and n is assumed: the quadratic bound
is derived directly for these actual unit formulas and their codec. -/
theorem unitSourceLength_le_quadratic (n : ℕ) :
    unitSourceLength n ≤ 23 * (n + 1) ^ 2 := by
  have he := encoded_unitFormula_length_le n
  have ht := inputTemplate_length_le (unitFormula n) n
  unfold unitSourceLength
  nlinarith

theorem n_le_unitSourceLength (n : ℕ) : n ≤ unitSourceLength n := by
  unfold unitSourceLength
  rw [inputTemplate_length]
  omega

theorem unitSourceLength_add_one_le (n : ℕ) (hn : 1 ≤ n) :
    unitSourceLength n + 1 ≤ 96 * n ^ 2 := by
  have h := unitSourceLength_le_quadratic n
  nlinarith

/-- The existing source minor is superpolynomial in the actual encoded
length as well. The shift budget may depend arbitrarily on the family index. -/
theorem no_eventual_polynomial_encoded_source_bound
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) (ell : ℕ → ℕ) :
    ¬ ∃ C d n0 : ℕ, ∀ n ≥ n0,
      mlBlockedSpdpRank (discreteBlocks (unitSourceLength n)) (Nat.log 2 n) (ell n)
        (machineSource M T (unitFormula n) n) ≤ C * (unitSourceLength n + 1) ^ d := by
  rintro ⟨C, d, n0, hbound⟩
  apply no_eventual_polynomial_machineSource_strict_bound M T hD
  refine ⟨C * 96 ^ d, 2 * d, max n0 1, ?_⟩
  intro n hn
  have hn0 : n0 ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  calc
    _ ≤ mlBlockedSpdpRank (discreteBlocks (unitSourceLength n)) (Nat.log 2 n) (ell n)
        (machineSource M T (unitFormula n) n) :=
      mlBlockedSpdpRank_mono_ell _ _ (Nat.zero_le _) _
    _ ≤ C * (unitSourceLength n + 1) ^ d := hbound n hn0
    _ ≤ C * (96 * n ^ 2) ^ d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (unitSourceLength_add_one_le n hn1) _)
    _ = (C * 96 ^ d) * n ^ (2 * d) := by rw [mul_pow, ← pow_mul, mul_assoc]

/-- The cutoff may instead be expressed in encoded input length itself. -/
theorem no_polynomial_encoded_source_bound_after_length_cutoff
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) (ell : ℕ → ℕ) :
    ¬ ∃ C d L0 : ℕ, ∀ n, L0 ≤ unitSourceLength n →
      mlBlockedSpdpRank (discreteBlocks (unitSourceLength n)) (Nat.log 2 n) (ell n)
        (machineSource M T (unitFormula n) n) ≤ C * (unitSourceLength n + 1) ^ d := by
  rintro ⟨C, d, L0, hbound⟩
  exact no_eventual_polynomial_encoded_source_bound M T hD ell
    ⟨C, d, L0, fun n hn => hbound n (hn.trans (n_le_unitSourceLength n))⟩

theorem no_eventual_polynomial_encoded_source_inclusive_bound
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) (ell : ℕ → ℕ) :
    ¬ ∃ C d n0 : ℕ, ∀ n ≥ n0,
      mlBlockedSpdpRankInc (discreteBlocks (unitSourceLength n)) (Nat.log 2 n) (ell n)
        (machineSource M T (unitFormula n) n) ≤ C * (unitSourceLength n + 1) ^ d := by
  rintro ⟨C, d, n0, hbound⟩
  apply no_eventual_polynomial_encoded_source_bound M T hD ell
  exact ⟨C, d, n0, fun n hn => (Submodule.finrank_mono
    (mlBlockedSpdpSubspace_le_inc _ _ _ _)).trans (hbound n hn)⟩

end GodMoveSATSourceCanonicity

#print axioms GodMoveSATSourceCanonicity.normalizedSource_eq_languageCharacteristic
#print axioms GodMoveSATSourceCanonicity.normalizedSource_independent_of_decider
#print axioms GodMoveSATSourceCanonicity.machineSource_eq_SATCharacteristic
#print axioms GodMoveSATSourceCanonicity.machineSource_independent_of_SAT_decider
#print axioms GodMoveSATSourceCanonicity.unitSourceLength_le_quadratic
#print axioms GodMoveSATSourceCanonicity.no_eventual_polynomial_encoded_source_bound
#print axioms GodMoveSATSourceCanonicity.no_polynomial_encoded_source_bound_after_length_cutoff
#print axioms GodMoveSATSourceCanonicity.no_eventual_polynomial_encoded_source_inclusive_bound
