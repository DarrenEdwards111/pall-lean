import GodMoveMachineRowFinder
import GodMoveAdaptiveRefinement

/-!
# Sample and basis discovery using a supplied actual SAT machine

The existential work is performed by encoded circuit queries to a supplied
clocked SAT machine. The row finder generates and serializes its own rational
relations; this driver has no `CubeOracle` or `OracleCorrect` parameter.

Correctness requires the stated SAT-machine correctness hypothesis. The
number of machine calls is polynomial in circuit width and gate count.
`GodMoveMachineDiscoveryPrecision` derives polynomial coefficient bit bounds
throughout this computation. Full construction runtime remains unproved.
-/

namespace GodMoveMachineDiscovery

open GodMoveBooleanInterpolation GodMoveBooleanWireTable GodMoveRationalRowBasis
open GodMoveMachineRowFinder GodMoveSamplingBarrier GodMoveComputedWireRank
open GodMoveSampledWireBasis GodMoveExhaustiveWireBasis GodMoveSampledSAT
open GodMoveAdaptiveDiscovery (SearchResult sampleRowSpan_nil sampleRowSpan_cons)
open GodMoveAdaptiveRefinement (sampleRowSpan_append_singleton)
open GodMoveNumericCounterexample GodMoveSampleRefinement
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer (CGate)
open ComposableMachine SeparationTarget

def discover (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) :
    ℕ → RowBasis c.length → SearchResult n
  | 0, _ => ⟨[], 0⟩
  | fuel + 1, B =>
    let attempt := findRowWithCount M T c B
    match attempt.1 with
    | none => ⟨[], attempt.2⟩
    | some a =>
      let rest := discover M T c fuel (insert B (wireRow c a))
      ⟨a :: rest.samples, attempt.2 + rest.queries⟩

theorem none_spans (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    {n : ℕ} (c : List (CGate n)) (B : RowBasis c.length)
    (hn : (findRowWithCount M T c B).1 = none) (a : Assignment n) :
    wireRow c a ∈ GodMoveRationalRowBasis.rowSpan B := by
  by_contra hnot
  have hyes := (accepts_iff B (wireRow c a)).mpr hnot
  have hno := (findRow_none_iff M T hD c B).mp hn a
  rw [hno] at hyes
  contradiction

theorem discover_sample_budget (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    {n : ℕ} (c : List (CGate n)) (fuel : ℕ) (B : RowBasis c.length) :
    B.count + (discover M T c fuel B).samples.length ≤ c.length := by
  induction fuel generalizing B with
  | zero => simpa only [discover, List.length_nil, Nat.add_zero] using count_le_width B
  | succ fuel ih =>
    cases ha : (findRowWithCount M T c B).1 with
    | none => simpa only [discover, ha, List.length_nil, Nat.add_zero] using count_le_width B
    | some a =>
      have hinc := insert_count B (wireRow c a)
      rw [findRow_some_correct M T hD c B a ha] at hinc
      simp only [↓reduceIte] at hinc
      have ht := ih (insert B (wireRow c a))
      simp only [discover, ha, List.length_cons]
      omega

theorem discover_query_budget (M : Machine) (T : ℕ → ℕ)
    {n : ℕ} (c : List (CGate n)) (fuel : ℕ) (B : RowBasis c.length) :
    (discover M T c fuel B).queries ≤ fuel * (c.length * (n + 1)) := by
  induction fuel generalizing B with
  | zero => simp [discover]
  | succ fuel ih =>
    have hq := findRow_queries_le M T c B
    cases ha : (findRowWithCount M T c B).1 with
    | none => simp only [discover, ha]; nlinarith
    | some a =>
      have ht := ih (insert B (wireRow c a))
      simp only [discover, ha]
      nlinarith

theorem discover_covers (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    {n : ℕ} (c : List (CGate n)) (fuel : ℕ) (B : RowBasis c.length)
    (hbudget : c.length < B.count + fuel) (a : Assignment n) :
    wireRow c a ∈ GodMoveRationalRowBasis.rowSpan B ⊔
      GodMoveRowSpanSeparation.rowSpan c (discover M T c fuel B).samples := by
  induction fuel generalizing B with
  | zero => have hb := count_le_width B; omega
  | succ fuel ih =>
    cases ha : (findRowWithCount M T c B).1 with
    | none =>
      simp only [discover, ha, sampleRowSpan_nil, sup_bot_eq]
      exact none_spans M T hD c B ha a
    | some b =>
      have hinc := insert_count B (wireRow c b)
      rw [findRow_some_correct M T hD c B b ha] at hinc
      simp only [↓reduceIte] at hinc
      have ht := ih (insert B (wireRow c b)) (by omega)
      rw [insert_span, sup_assoc] at ht
      simpa only [discover, ha, sampleRowSpan_cons] using ht

theorem discover_successful (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    {n : ℕ} (c : List (CGate n)) (fuel : ℕ) (B : RowBasis c.length)
    (samples : List (Assignment n))
    (hspan : GodMoveRationalRowBasis.rowSpan B = GodMoveRowSpanSeparation.rowSpan c samples) :
    SuccessfulRefinements c samples (discover M T c fuel B).samples := by
  induction fuel generalizing B samples with
  | zero => trivial
  | succ fuel ih =>
    cases ha : (findRowWithCount M T c B).1 with
    | none => simp [discover, ha, SuccessfulRefinements]
    | some a =>
      simp only [discover, ha, SuccessfulRefinements]
      refine ⟨counterexample_of_accepts c samples B hspan a
        (findRow_some_correct M T hD c B a ha), ?_⟩
      apply ih (insert B (wireRow c a)) (samples ++ [a])
      rw [insert_span, hspan, sampleRowSpan_append_singleton]

def machineSearch (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) : SearchResult n :=
  discover M T c (c.length + 1) (empty c.length)

def machineSamples (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) : List (Assignment n) := (machineSearch M T c).samples

theorem machineSamples_separates (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    {n : ℕ} (c : List (CGate n)) : SeparatesWires c (machineSamples M T c) := by
  apply GodMoveRowSpanSeparation.separates_of_all_rows_mem
  intro a
  have h := discover_covers M T hD c (c.length + 1) (empty c.length) (by simp) a
  simpa only [empty_span, bot_sup_eq] using h

theorem machineSamples_successful (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    {n : ℕ} (c : List (CGate n)) :
    SuccessfulRefinements c [] (machineSamples M T c) := by
  apply discover_successful M T hD c (c.length + 1) (empty c.length) []
  rw [empty_span, sampleRowSpan_nil]

theorem machineSearch_queries_le (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) :
    (machineSearch M T c).queries ≤ (c.length + 1) * (c.length * (n + 1)) :=
  discover_query_budget M T c (c.length + 1) (empty c.length)

def machineBasisIndices (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) : List (Fin c.length) := selectedIndices c (machineSamples M T c)

theorem machineBasis_spans (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    {n : ℕ} (c : List (CGate n)) :
    chosenWireSpace c (machineBasisIndices M T c) = wireSpace c :=
  chosenWireSpace_eq_of_columns c (machineSamples M T c) (machineBasisIndices M T c)
    (machineSamples_separates M T hD c) (every_column_mem c (machineSamples M T c))

theorem machineBasis_linearIndependent (M : Machine) (T : ℕ → ℕ)
    {n : ℕ} (c : List (CGate n)) :
    LinearIndependent ℚ (chosenWire c (machineBasisIndices M T c)) :=
  chosenWire_linearIndependent c (machineSamples M T c) (machineBasisIndices M T c)
    (selectedColumns_linearIndependent c (machineSamples M T c))

theorem machineBasis_length_eq_wireRank (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    {n : ℕ} (c : List (CGate n)) : (machineBasisIndices M T c).length = wireRank c :=
  chosenWire_length_eq_rank c (machineBasisIndices M T c)
    (machineBasis_spans M T hD c) (machineBasis_linearIndependent M T c)

theorem machineSamples_length_eq_wireRank (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) :
    (machineSamples M T c).length = wireRank c := by
  apply Nat.le_antisymm
  · exact successful_steps_le_wireRank c _ (machineSamples_successful M T hD c)
  · have h : (machineBasisIndices M T c).length ≤ (machineSamples M T c).length := by
      simpa only [machineBasisIndices, selectedIndices, List.length_map] using
        selectRows_length_le (columnTable c (machineSamples M T c))
    rwa [machineBasis_length_eq_wireRank M T hD c] at h

/-- The same supplied SAT machine discovers a basis for its own unrolled
computation on an input slice. That basis captures the actual SAT decision
polynomial, and its size obeys the previously derived machine-clock bound.
This is conditional on SAT correctness; it is not a lower bound on the rank. -/
theorem actualMachine_basis_connection (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) (L : ℕ) :
    let c := ComposablePpolyDischarge.circuitFor M L (T L)
    let indices := machineBasisIndices M T c
    chosenWireSpace c indices = wireSpace c ∧
      satDecisionTarget L ∈ chosenWireSpace c indices ∧
      indices.length = wireRank c ∧
      indices.length ≤ GodMoveCircuitRuntimeCost.circuitConstant M *
        (L + T L + 1) ^ 4 := by
  dsimp only
  have hs := machineBasis_spans M T hD (ComposablePpolyDischarge.circuitFor M L (T L))
  have hr := machineBasis_length_eq_wireRank M T hD
    (ComposablePpolyDischarge.circuitFor M L (T L))
  refine ⟨hs, ?_, hr, ?_⟩
  · rw [hs]
    exact satDecisionTarget_mem_actualWireSpace M T hD L
  · rw [hr]
    exact unrolled_wireRank_le_clock M L (T L)

end GodMoveMachineDiscovery

#print axioms GodMoveMachineDiscovery.discover_sample_budget
#print axioms GodMoveMachineDiscovery.discover_query_budget
#print axioms GodMoveMachineDiscovery.discover_covers
#print axioms GodMoveMachineDiscovery.discover_successful
#print axioms GodMoveMachineDiscovery.machineSamples_separates
#print axioms GodMoveMachineDiscovery.machineSearch_queries_le
#print axioms GodMoveMachineDiscovery.machineBasis_spans
#print axioms GodMoveMachineDiscovery.machineBasis_linearIndependent
#print axioms GodMoveMachineDiscovery.machineBasis_length_eq_wireRank
#print axioms GodMoveMachineDiscovery.machineSamples_length_eq_wireRank
#print axioms GodMoveMachineDiscovery.actualMachine_basis_connection
