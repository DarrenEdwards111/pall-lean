import GodMoveCubeWitnessSearch
import GodMoveExhaustiveWireBasis

/-!
# Adaptive sample and basis discovery with a decision oracle

Each round asks whether any Boolean assignment produces a wire row outside
the current rational span. Witness self-reduction finds such a point using at
most `n+1` existential decision queries. Insertion adds an independent row.
Starting with `s+1` rounds of fuel therefore suffices for separation, retains
at most `s` assignments, and uses at most `(s+1)*(n+1)` decision queries.

The oracle and its correctness are explicit inputs. A decision query is not
a single circuit evaluation: it answers an existential question over the
whole Boolean cube. No polynomial implementation of these queries, polynomial
rational bit-cost bound, or superpolynomial SAT lower bound is supplied.
-/

namespace GodMoveAdaptiveDiscovery

open GodMoveBooleanInterpolation GodMoveBooleanWireTable GodMoveRationalRowBasis
open GodMoveCubeWitnessSearch GodMoveSamplingBarrier GodMoveComputedWireRank
open GodMoveSampledWireBasis GodMoveExhaustiveWireBasis GodMoveSampledSAT
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer (CGate)

structure SearchResult (n : ℕ) where
  samples : List (Assignment n)
  queries : ℕ

/-- An executable numeric predicate. Its existential decision is the oracle
operation whose implementation cost remains external. -/
def outside {n : ℕ} (c : List (CGate n)) (B : RowBasis c.length) : Assignment n → Bool :=
  fun a => accepts B (wireRow c a)

def adaptive {n : ℕ} (O : CubeOracle) (c : List (CGate n)) :
    ℕ → RowBasis c.length → SearchResult n
  | 0, _ => ⟨[], 0⟩
  | fuel + 1, B =>
    let attempt := findWitnessWithCount O (outside c B)
    match attempt.1 with
    | none => ⟨[], attempt.2⟩
    | some a =>
      let rest := adaptive O c fuel (insert B (wireRow c a))
      ⟨a :: rest.samples, attempt.2 + rest.queries⟩

theorem attempt_some_accepts {n : ℕ} (O : CubeOracle) (hO : OracleCorrect O)
    (c : List (CGate n)) (B : RowBasis c.length) (a : Assignment n)
    (ha : (findWitnessWithCount O (outside c B)).1 = some a) :
    accepts B (wireRow c a) = true :=
  findWitness_some_correct O hO (outside c B) a ha

theorem attempt_none_spans {n : ℕ} (O : CubeOracle) (hO : OracleCorrect O)
    (c : List (CGate n)) (B : RowBasis c.length)
    (hn : (findWitnessWithCount O (outside c B)).1 = none) (a : Assignment n) :
    wireRow c a ∈ GodMoveRationalRowBasis.rowSpan B := by
  by_contra hnot
  have hyes := (accepts_iff B (wireRow c a)).mpr hnot
  exact ((findWitness_none_iff O hO (outside c B)).mp hn) ⟨a, hyes⟩

theorem adaptive_sample_budget {n : ℕ} (O : CubeOracle) (hO : OracleCorrect O)
    (c : List (CGate n)) (fuel : ℕ) (B : RowBasis c.length) :
    B.count + (adaptive O c fuel B).samples.length ≤ c.length := by
  induction fuel generalizing B with
  | zero => simpa only [adaptive, List.length_nil, Nat.add_zero] using count_le_width B
  | succ fuel ih =>
    cases ha : (findWitnessWithCount O (outside c B)).1 with
    | none =>
      simpa only [adaptive, ha, List.length_nil, Nat.add_zero] using count_le_width B
    | some a =>
      have hinc := insert_count B (wireRow c a)
      rw [attempt_some_accepts O hO c B a ha] at hinc
      have ht := ih (insert B (wireRow c a))
      simp only [adaptive, ha, List.length_cons]
      simp only [↓reduceIte] at hinc
      omega

/-- The instrumentation counts each existential oracle call made by witness
search. No cost for implementing an oracle call is assigned here. -/
theorem adaptive_query_budget {n : ℕ} (O : CubeOracle)
    (c : List (CGate n)) (fuel : ℕ) (B : RowBasis c.length) :
    (adaptive O c fuel B).queries ≤ fuel * (n + 1) := by
  induction fuel generalizing B with
  | zero => simp [adaptive]
  | succ fuel ih =>
    have hq := findWitnessWithCount_count_le O (outside c B)
    cases ha : (findWitnessWithCount O (outside c B)).1 with
    | none =>
      simp only [adaptive, ha]
      nlinarith
    | some a =>
      have ht := ih (insert B (wireRow c a))
      simp only [adaptive, ha]
      nlinarith

theorem sampleRowSpan_nil {n : ℕ} (c : List (CGate n)) :
    GodMoveRowSpanSeparation.rowSpan c [] = ⊥ := by
  simp [GodMoveRowSpanSeparation.rowSpan]

theorem sampleRowSpan_cons {n : ℕ} (c : List (CGate n))
    (a : Assignment n) (samples : List (Assignment n)) :
    GodMoveRowSpanSeparation.rowSpan c (a :: samples) =
      Submodule.span ℚ {wireRow c a} ⊔ GodMoveRowSpanSeparation.rowSpan c samples := by
  classical
  simp [GodMoveRowSpanSeparation.rowSpan, Submodule.span_insert]

/-- With sufficient fuel, the old span and new sample rows together cover
every Boolean wire row. Each successful round consumes a basis dimension. -/
theorem adaptive_covers {n : ℕ} (O : CubeOracle) (hO : OracleCorrect O)
    (c : List (CGate n)) (fuel : ℕ) (B : RowBasis c.length)
    (hbudget : c.length < B.count + fuel) (a : Assignment n) :
    wireRow c a ∈ GodMoveRationalRowBasis.rowSpan B ⊔
      GodMoveRowSpanSeparation.rowSpan c (adaptive O c fuel B).samples := by
  induction fuel generalizing B with
  | zero => have hb := count_le_width B; omega
  | succ fuel ih =>
    cases ha : (findWitnessWithCount O (outside c B)).1 with
    | none =>
      simp only [adaptive, ha, sampleRowSpan_nil, sup_bot_eq]
      exact attempt_none_spans O hO c B ha a
    | some b =>
      have hinc := insert_count B (wireRow c b)
      rw [attempt_some_accepts O hO c B b ha] at hinc
      simp only [↓reduceIte] at hinc
      have ht := ih (insert B (wireRow c b)) (by omega)
      rw [insert_span, sup_assoc] at ht
      simpa only [adaptive, ha, sampleRowSpan_cons] using ht

def adaptiveSearch {n : ℕ} (O : CubeOracle) (c : List (CGate n)) : SearchResult n :=
  adaptive O c (c.length + 1) (empty c.length)

def adaptiveSamples {n : ℕ} (O : CubeOracle) (c : List (CGate n)) : List (Assignment n) :=
  (adaptiveSearch O c).samples

theorem adaptiveSamples_separates {n : ℕ} (O : CubeOracle) (hO : OracleCorrect O)
    (c : List (CGate n)) : SeparatesWires c (adaptiveSamples O c) := by
  apply GodMoveRowSpanSeparation.separates_of_all_rows_mem
  intro a
  have h := adaptive_covers O hO c (c.length + 1) (empty c.length) (by simp) a
  simpa only [empty_span, bot_sup_eq] using h

theorem adaptiveSamples_length_le {n : ℕ} (O : CubeOracle) (hO : OracleCorrect O)
    (c : List (CGate n)) : (adaptiveSamples O c).length ≤ c.length := by
  have h := adaptive_sample_budget O hO c (c.length + 1) (empty c.length)
  simpa only [empty_count, Nat.zero_add] using h

theorem adaptiveSearch_queries_le {n : ℕ} (O : CubeOracle) (c : List (CGate n)) :
    (adaptiveSearch O c).queries ≤ (c.length + 1) * (n + 1) :=
  adaptive_query_budget O c (c.length + 1) (empty c.length)

/-- Column selection uses the discovered samples. This definition does not
invoke the exhaustive Boolean-table constructor. -/
def adaptiveBasisIndices {n : ℕ} (O : CubeOracle) (c : List (CGate n)) :
    List (Fin c.length) := selectedIndices c (adaptiveSamples O c)

theorem adaptiveBasis_spans {n : ℕ} (O : CubeOracle) (hO : OracleCorrect O)
    (c : List (CGate n)) :
    chosenWireSpace c (adaptiveBasisIndices O c) = wireSpace c :=
  chosenWireSpace_eq_of_columns c (adaptiveSamples O c) (adaptiveBasisIndices O c)
    (adaptiveSamples_separates O hO c) (every_column_mem c (adaptiveSamples O c))

theorem adaptiveBasis_linearIndependent {n : ℕ} (O : CubeOracle)
    (c : List (CGate n)) : LinearIndependent ℚ (chosenWire c (adaptiveBasisIndices O c)) :=
  chosenWire_linearIndependent c (adaptiveSamples O c) (adaptiveBasisIndices O c)
    (selectedColumns_linearIndependent c (adaptiveSamples O c))

theorem adaptiveBasis_length_eq_wireRank {n : ℕ} (O : CubeOracle) (hO : OracleCorrect O)
    (c : List (CGate n)) : (adaptiveBasisIndices O c).length = wireRank c :=
  chosenWire_length_eq_rank c (adaptiveBasisIndices O c)
    (adaptiveBasis_spans O hO c) (adaptiveBasis_linearIndependent O c)

def adaptiveSelector (O : CubeOracle) : SampleSelector := fun _ c => adaptiveSamples O c

def adaptiveSATWord (O : CubeOracle) := sampledSATWord (adaptiveSelector O)

theorem adaptiveSATWord_eq_SATLang (O : CubeOracle) (hO : OracleCorrect O) (x : List Bool) :
    adaptiveSATWord O x = PallLean.Paper93.DeepMath.PathB.SeparationTarget.SATLang x :=
  sampledSATWord_eq_SATLang (adaptiveSelector O) (fun _ c => adaptiveSamples_separates O hO c) x

end GodMoveAdaptiveDiscovery

#print axioms GodMoveAdaptiveDiscovery.attempt_some_accepts
#print axioms GodMoveAdaptiveDiscovery.attempt_none_spans
#print axioms GodMoveAdaptiveDiscovery.adaptive_sample_budget
#print axioms GodMoveAdaptiveDiscovery.adaptive_query_budget
#print axioms GodMoveAdaptiveDiscovery.adaptive_covers
#print axioms GodMoveAdaptiveDiscovery.adaptiveSamples_separates
#print axioms GodMoveAdaptiveDiscovery.adaptiveSamples_length_le
#print axioms GodMoveAdaptiveDiscovery.adaptiveSearch_queries_le
#print axioms GodMoveAdaptiveDiscovery.adaptiveBasis_spans
#print axioms GodMoveAdaptiveDiscovery.adaptiveBasis_linearIndependent
#print axioms GodMoveAdaptiveDiscovery.adaptiveBasis_length_eq_wireRank
#print axioms GodMoveAdaptiveDiscovery.adaptiveSATWord_eq_SATLang
