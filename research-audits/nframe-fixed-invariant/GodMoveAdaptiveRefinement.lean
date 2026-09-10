import GodMoveAdaptiveDiscovery
import GodMoveNumericCounterexample

/-!
# The adaptive numeric driver follows genuine semantic refinements

Every successful iteration of the actual adaptive driver supplies a semantic
counterexample through its nonzero rational residual. Starting from matching
sample and numeric row spans preserves this relationship after insertion.
Consequently the returned sample trace has at most `wireRank c` steps.

Together with separation and independent sampled-column selection, this gives
exactly `wireRank c` returned samples and basis wires. Oracle correctness is
an explicit assumption; neither the dimension identities nor the iteration
bound provide a polynomial implementation of the existential oracle.
-/

namespace GodMoveAdaptiveRefinement

open GodMoveBooleanInterpolation GodMoveBooleanWireTable GodMoveRationalRowBasis
open GodMoveCubeWitnessSearch GodMoveAdaptiveDiscovery GodMoveNumericCounterexample
open GodMoveSampleRefinement GodMoveComputedWireRank GodMoveExhaustiveWireBasis
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer (CGate)

theorem sampleRowSpan_append_singleton {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (a : Assignment n) :
    GodMoveRowSpanSeparation.rowSpan c (samples ++ [a]) =
      GodMoveRowSpanSeparation.rowSpan c samples ⊔ Submodule.span ℚ {wireRow c a} := by
  induction samples with
  | nil => simp [sampleRowSpan_nil, sampleRowSpan_cons]
  | cons b samples ih =>
      simp only [List.cons_append, sampleRowSpan_cons, ih, sup_assoc]

/-- Each emitted assignment is a counterexample to the sample set preceding
it; the recursive driver itself supplies the complete successful trace. -/
theorem adaptive_successful {n : ℕ} (O : CubeOracle) (hO : OracleCorrect O)
    (c : List (CGate n)) (fuel : ℕ) (B : RowBasis c.length)
    (samples : List (Assignment n))
    (hspan : GodMoveRationalRowBasis.rowSpan B =
      GodMoveRowSpanSeparation.rowSpan c samples) :
    SuccessfulRefinements c samples (adaptive O c fuel B).samples := by
  induction fuel generalizing B samples with
  | zero => trivial
  | succ fuel ih =>
      cases ha : (findWitnessWithCount O (outside c B)).1 with
      | none => simp [adaptive, ha, SuccessfulRefinements]
      | some a =>
          simp only [adaptive, ha, SuccessfulRefinements]
          refine ⟨counterexample_of_accepts c samples B hspan a
            (attempt_some_accepts O hO c B a ha), ?_⟩
          apply ih (insert B (wireRow c a)) (samples ++ [a])
          rw [insert_span, hspan, sampleRowSpan_append_singleton]

/-- The executable driver beginning with the empty numeric basis emits a
successful semantic refinement trace beginning with no samples. -/
theorem adaptiveSamples_successful {n : ℕ} (O : CubeOracle) (hO : OracleCorrect O)
    (c : List (CGate n)) :
    SuccessfulRefinements c [] (adaptiveSamples O c) := by
  apply adaptive_successful O hO c (c.length + 1) (empty c.length) []
  rw [empty_span, sampleRowSpan_nil]

theorem adaptiveSamples_length_le_wireRank {n : ℕ} (O : CubeOracle)
    (hO : OracleCorrect O) (c : List (CGate n)) :
    (adaptiveSamples O c).length ≤ wireRank c :=
  successful_steps_le_wireRank c (adaptiveSamples O c) (adaptiveSamples_successful O hO c)

theorem adaptiveBasis_length_le_samples {n : ℕ} (O : CubeOracle)
    (c : List (CGate n)) :
    (adaptiveBasisIndices O c).length ≤ (adaptiveSamples O c).length := by
  simpa [adaptiveBasisIndices, selectedIndices, selectedColumns] using
    selectRows_length_le (columnTable c (adaptiveSamples O c))

/-- A complete adaptive run returns exactly one sample per independent wire
direction, matching the number of independently selected basis wires. -/
theorem adaptiveSamples_length_eq_wireRank {n : ℕ} (O : CubeOracle)
    (hO : OracleCorrect O) (c : List (CGate n)) :
    (adaptiveSamples O c).length = wireRank c := by
  apply Nat.le_antisymm (adaptiveSamples_length_le_wireRank O hO c)
  have h := adaptiveBasis_length_le_samples O c
  rwa [adaptiveBasis_length_eq_wireRank O hO c] at h

theorem adaptiveSamples_length_eq_basis {n : ℕ} (O : CubeOracle)
    (hO : OracleCorrect O) (c : List (CGate n)) :
    (adaptiveSamples O c).length = (adaptiveBasisIndices O c).length := by
  rw [adaptiveSamples_length_eq_wireRank O hO c, adaptiveBasis_length_eq_wireRank O hO c]

/-- Each retained sample accounts for one witness search, with at most one
additional search establishing that no further counterexample exists. -/
theorem adaptive_queries_le_samples {n : ℕ} (O : CubeOracle)
    (c : List (CGate n)) (fuel : ℕ) (B : RowBasis c.length) :
    (adaptive O c fuel B).queries ≤ ((adaptive O c fuel B).samples.length + 1) * (n + 1) := by
  induction fuel generalizing B with
  | zero => simp [adaptive]
  | succ fuel ih =>
      have hq := findWitnessWithCount_count_le O (outside c B)
      cases ha : (findWitnessWithCount O (outside c B)).1 with
      | none => simpa only [adaptive, ha, List.length_nil, Nat.zero_add, one_mul] using hq
      | some a =>
          have ht := ih (insert B (wireRow c a))
          simp only [adaptive, ha, List.length_cons]
          nlinarith

/-- The exact returned sample dimension sharpens the bound on existential
decision queries. These query counts do not bound the cost per query. -/
theorem adaptiveSearch_queries_le_wireRank {n : ℕ} (O : CubeOracle)
    (hO : OracleCorrect O) (c : List (CGate n)) :
    (adaptiveSearch O c).queries ≤ (wireRank c + 1) * (n + 1) := by
  have h := adaptive_queries_le_samples O c (c.length + 1) (empty c.length)
  change (adaptiveSearch O c).queries ≤ ((adaptiveSamples O c).length + 1) * (n + 1) at h
  rwa [adaptiveSamples_length_eq_wireRank O hO c] at h

end GodMoveAdaptiveRefinement

#print axioms GodMoveAdaptiveRefinement.adaptive_successful
#print axioms GodMoveAdaptiveRefinement.adaptiveSamples_successful
#print axioms GodMoveAdaptiveRefinement.adaptiveSamples_length_le_wireRank
#print axioms GodMoveAdaptiveRefinement.adaptiveBasis_length_le_samples
#print axioms GodMoveAdaptiveRefinement.adaptiveSamples_length_eq_wireRank
#print axioms GodMoveAdaptiveRefinement.adaptiveSamples_length_eq_basis
#print axioms GodMoveAdaptiveRefinement.adaptive_queries_le_samples
#print axioms GodMoveAdaptiveRefinement.adaptiveSearch_queries_le_wireRank
