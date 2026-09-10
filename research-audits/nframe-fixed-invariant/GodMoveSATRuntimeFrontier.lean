import GodMoveSATPaperWindowLower
import GodMoveCircuitPolynomialSize
import GodMoveShiftedRankUpper

/-!
# Exact strength of the remaining SAT-runtime rank estimate

This file does not prove the requested polynomial runtime-rank bound.
It accounts for the actual encoded length and arbitrary polynomial-clock
constants, then proves that such a bound, restricted to polynomial-clock
SAT deciders, is equivalent to the faithful SAT-not-in-P target.

The forward implication uses the proved lower bound at the exact paper
log/log window. The reverse implication is vacuous: if no polynomial SAT
decider exists, there is no machine satisfying the premises of the bound.
This equivalence validates the conditional contradiction but supplies no
independent estimate of rank from runtime.

The unconditional upper estimate proved here is quasipolynomial: the exact
paper source lies between n^(log₂ n / 4) and n^(3 log₂ n) under SAT correctness.
Only the lower bound uses SAT; the upper bound applies to every machine.
-/

namespace GodMoveSATRuntimeFrontier

open MultilinearSPDP
open GodMoveSATUnitExtraction GodMoveMachineFaceExtraction GodMoveUnitCharacteristic
open GodMoveMonomialMinor (discreteBlocks)
open PallLean.Paper93.DeepMath.PathB ComposableMachine SeparationTarget
open PvsNPSeparatingInvariant (PolyBounded)
open CookLevinEmitClockBounds3 (PB_add PB_id PB_const)

/-- Exact encoded bit length used by the operational paper-source family. -/
abbrev paperInputLength (n : ℕ) := unitInputLength (n / 3)

/-- The actual normalized source at the unchanged paper derivative/shift window. -/
noncomputable def paperSourceRank (M : Machine) (T : ℕ → ℕ) (n : ℕ) : ℕ :=
  mlBlockedSpdpRank (discreteBlocks (paperInputLength n))
    (Nat.log 2 n) (Nat.log 2 n)
    (machineSource M T (unitFormula (n / 3)) (n / 3))

/-- The true codec length fits the cubic base needed for the rank estimate. -/
theorem twice_paperInputLength_le_cube (n : ℕ) (hn : 2 ^ 20 ≤ n) :
    2 * paperInputLength n ≤ n ^ 3 := by
  have hL := GodMoveSATSourceCanonicity.unitSourceLength_le_quadratic (n / 3)
  have hdiv : n / 3 + 1 ≤ n + 1 := by omega
  have hsq := Nat.pow_le_pow_left hdiv 2
  have hn1 : 1 ≤ n := (by norm_num : 1 ≤ (2 : ℕ) ^ 20).trans hn
  have hn184 : 184 ≤ n := (by norm_num : 184 ≤ (2 : ℕ) ^ 20).trans hn
  have hlarge := Nat.mul_le_mul_right (n ^ 2) hn184
  change 2 * GodMoveSATSourceCanonicity.unitSourceLength (n / 3) ≤ n ^ 3
  nlinarith

/-- A proved upper bound on the actual source. Its exponent grows with
the derivative order, so it is not the requested polynomial runtime bound. -/
theorem paperSourceRank_le_quasipolynomial
    (M : Machine) (T : ℕ → ℕ) (n : ℕ) (hn : 2 ^ 20 ≤ n) :
    paperSourceRank M T n ≤ n ^ (3 * Nat.log 2 n) := by
  calc
    paperSourceRank M T n ≤ (2 * paperInputLength n) ^ Nat.log 2 n :=
      GodMoveShiftedRankUpper.strict_rank_le_two_mul_vars_pow _ _ _ _
    _ ≤ (n ^ 3) ^ Nat.log 2 n :=
      Nat.pow_le_pow_left (twice_paperInputLength_le_cube n hn) _
    _ = n ^ (3 * Nat.log 2 n) := by rw [pow_mul]

/-- Matched upper and lower growth bounds at the same source, encoded
length, discrete partition, and paper derivative/shift parameters. -/
theorem paperSourceRank_growth_bounds
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (n : ℕ) (hn : 2 ^ 20 ≤ n) :
    n ^ (Nat.log 2 n / 4) ≤ paperSourceRank M T n ∧
      paperSourceRank M T n ≤ n ^ (3 * Nat.log 2 n) :=
  ⟨GodMoveSATPaperWindowLower.paper_window_rank_ge_power M T hD n _ hn,
    paperSourceRank_le_quasipolynomial M T n hn⟩

/-- Polynomial-clock substitution with arbitrary constants, exponents,
encoded-length families, and eventual cutoffs. No rank fact is assumed here. -/
theorem encoded_bound_of_runtime_bound
    (R L T : ℕ → ℕ) (hT : PolyBounded T)
    (hR : ∃ C d n0 : ℕ, ∀ n ≥ n0,
      R n ≤ C * (L n + T (L n) + 1) ^ d) :
    ∃ C d n0 : ℕ, ∀ n ≥ n0, R n ≤ C * (L n + 1) ^ d := by
  obtain ⟨a, b, hbudget⟩ := PB_add (PB_add PB_id hT) (PB_const 1)
  obtain ⟨C, d, n0, hbound⟩ := hR
  refine ⟨C * a ^ d, b * d, n0, ?_⟩
  intro n hn
  calc
    R n ≤ C * (L n + T (L n) + 1) ^ d := hbound n hn
    _ ≤ C * (a * (L n + 1) ^ b) ^ d :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left (hbudget (L n)) d)
    _ = (C * a ^ d) * (L n + 1) ^ (b * d) := by
      rw [mul_pow, ← pow_mul, mul_assoc]

/-- Under a hypothetical polynomial SAT clock, a polynomial bound in
input-plus-runtime would contradict the already proved source minor.
The bound itself is not asserted. -/
theorem no_eventual_runtime_bound_of_polynomial_clock
    (M : Machine) (T : ℕ → ℕ) (hT : PolyBounded T) (hD : Decides M SATLang T) :
    ¬ ∃ C d n0 : ℕ, ∀ n ≥ n0,
      paperSourceRank M T n ≤ C * (paperInputLength n + T (paperInputLength n) + 1) ^ d := by
  intro hbound
  exact GodMoveSATPaperWindowLower.no_eventual_polynomial_paper_source_encoded_bound M T hD
    (encoded_bound_of_runtime_bound (paperSourceRank M T) paperInputLength T hT hbound)

/-- The unresolved estimate, restricted to hypothetical polynomial-clock
SAT deciders. This is a proposition definition, not an assumption or theorem.
The constants may depend on the machine and its clock, but not on n. -/
def SATPolynomialClockRankBound : Prop :=
  ∀ (M : Machine) (T : ℕ → ℕ), PolyBounded T → Decides M SATLang T →
    ∃ C d n0 : ℕ, ∀ n ≥ n0,
      paperSourceRank M T n ≤ C * (paperInputLength n + T (paperInputLength n) + 1) ^ d

/-- This particular remaining estimate has the full strength of separation.
The reverse direction uses the absence of a polynomial SAT decider; it does
not derive a bound for superpolynomial-clock deciders. -/
theorem satPolynomialClockRankBound_iff_separation :
    SATPolynomialClockRankBound ↔ SAT_not_in_P := by
  constructor
  · intro hbound
    rintro ⟨M, T, hT, hD⟩
    exact no_eventual_runtime_bound_of_polynomial_clock M T hT hD (hbound M T hT hD)
  · intro hsep M T hT hD
    exact False.elim (hsep ⟨M, T, hT, hD⟩)

/-- A valid conditional separation theorem. Its argument is exactly the
unproved runtime-rank estimate, with no rank bridge hidden in another field. -/
theorem separation_of_SATPolynomialClockRankBound
    (hbound : SATPolynomialClockRankBound) : SAT_not_in_P :=
  satPolynomialClockRankBound_iff_separation.mp hbound

end GodMoveSATRuntimeFrontier

#print axioms GodMoveSATRuntimeFrontier.twice_paperInputLength_le_cube
#print axioms GodMoveSATRuntimeFrontier.paperSourceRank_le_quasipolynomial
#print axioms GodMoveSATRuntimeFrontier.paperSourceRank_growth_bounds
#print axioms GodMoveSATRuntimeFrontier.encoded_bound_of_runtime_bound
#print axioms GodMoveSATRuntimeFrontier.no_eventual_runtime_bound_of_polynomial_clock
#print axioms GodMoveSATRuntimeFrontier.satPolynomialClockRankBound_iff_separation
#print axioms GodMoveSATRuntimeFrontier.separation_of_SATPolynomialClockRankBound
