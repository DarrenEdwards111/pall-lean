import GodMoveBoundaryNFrameGauge
import GodMoveExecutableBoundary

/-!
# Actual tape growth and the cost of materializing boundary coordinates

The operational machine's local transition, forced head-zero initialization,
and one-cell head-movement bound imply `head ≤ t` and
`tape.length ≤ max(input.length, t)`. Halting, reset, optional writes,
rereading, and cell reuse are all covered by these actual transition rules.

For any specified coordinate codec with nonempty records, explicitly writing
q coordinate records on this tape requires q output bits. A linear boundary
preserving the existing designated derivative minor therefore requires at
least `choose(m,k) - input.length` steps to materialize one dense row.

For that explicit materialization contract, the unchanged production action
of the canonical boundary gauge, at unit rank/barrier weights, is at most
`input.length + t + 1`. If the input is shorter than the minor dimension,
the action is at most `t + 1`. These are actual action/runtime comparisons
for this restricted construction, not an action bound for a bare decider.

The serialization equality is an explicit hypothesis. This does not require
an arbitrary SAT decider to construct such a boundary, provide an efficient
extractor, or bound the rank of an implicitly described matrix. In particular,
an identity matrix can have a short implicit description and large rank.
No correctness or decoding property of a supplied codec is inferred merely
from nonempty records; the size bound holds for every such codec.
-/

namespace GodMoveBoundaryRuntimeCost

open PallLean.Paper93.DeepMath.PathB ComposableMachine
open GodMoveMonomialMinor GodMoveDesignatedPositiveBoundary
open GodMoveBoundaryNFrameGauge (boundaryGauge boundaryGauge_action)
open PallLean.Paper93.NFrame PallLean.Paper93.Concrete

/-- A sharp physical space bound, derived directly from legal machine steps. -/
theorem run_head_tape_bounds (M : Machine) (x : List Bool) (t : ℕ) :
    (run M t (init M x)).hd ≤ t ∧
      (run M t (init M x)).tp.length ≤ max x.length t := by
  induction t with
  | zero => simp [init]
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [run_succ]
    set c := run M t (init M x) with hc
    by_cases hh : M.halt c.st = true
    · rw [step_of_halted M hh]
      exact ⟨by omega, by omega⟩
    · have hh' : M.halt c.st = false := Bool.eq_false_of_not_eq_true hh
      have hstep : step M c =
          ⟨(M.δ c.st (c.tp.getD c.hd false)).1,
            moveHead c.hd (M.δ c.st (c.tp.getD c.hd false)).2.2,
            (match (M.δ c.st (c.tp.getD c.hd false)).2.1 with
              | none => c.tp | some w => writeAt c.tp c.hd w)⟩ := by
        unfold step
        rw [hh']
        rfl
      rw [hstep]
      refine ⟨?_, ?_⟩
      · exact (moveHead_le _ _).trans (by omega)
      · cases hw : (M.δ c.st (c.tp.getD c.hd false)).2.1 with
        | none => simp only; omega
        | some w => simp only [writeAt_length]; omega

theorem transOut_length_le_max (M : Machine) (x : List Bool) (t : ℕ) :
    (transOut M x t).length ≤ max x.length t :=
  (run_head_tape_bounds M x t).2

theorem transOut_length_le_input_add_time (M : Machine) (x : List Bool) (t : ℕ) :
    (transOut M x t).length ≤ x.length + t := by
  have h := transOut_length_le_max M x t
  omega

/-- Explicit dense coordinate records, in the order of the finite index type. -/
def coordinateRecords {q : ℕ} (encode : ℚ → List Bool) (v : Fin q → ℚ) :
    List (List Bool) := List.ofFn fun i => encode (v i)

/-- Every nonempty record needs at least one cell in its flattened output. -/
theorem length_le_flatten_length (records : List (List Bool))
    (hne : ∀ r ∈ records, 0 < r.length) : records.length ≤ records.flatten.length := by
  induction records with
  | nil => simp
  | cons r records ih =>
    have hr := hne r (by simp)
    have ht := ih (fun s hs => hne s (by simp [hs]))
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

theorem coordinate_count_le_serialized_length {q : ℕ}
    (encode : ℚ → List Bool) (v : Fin q → ℚ)
    (hne : ∀ i, 0 < (encode (v i)).length) :
    q ≤ (coordinateRecords encode v).flatten.length := by
  have h := length_le_flatten_length (coordinateRecords encode v) (by
    intro r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact hne i)
  simpa only [coordinateRecords, List.length_ofFn] using h

/-- This is a lower bound for a machine that actually writes the specified
coordinate records. The exact tape-output equation supplies that contract. -/
theorem materialized_boundary_dimension_le_max {q : ℕ}
    (M : Machine) (x : List Bool) (t : ℕ)
    (encode : ℚ → List Bool) (v : Fin q → ℚ)
    (hne : ∀ i, 0 < (encode (v i)).length)
    (houtput : transOut M x t = (coordinateRecords encode v).flatten) :
    q ≤ max x.length t := by
  have hsize := coordinate_count_le_serialized_length encode v hne
  rw [← houtput] at hsize
  exact hsize.trans (transOut_length_le_max M x t)

theorem materialized_boundary_dimension_le_input_add_time {q : ℕ}
    (M : Machine) (x : List Bool) (t : ℕ)
    (encode : ℚ → List Bool) (v : Fin q → ℚ)
    (hne : ∀ i, 0 < (encode (v i)).length)
    (houtput : transOut M x t = (coordinateRecords encode v).flatten) :
    q ≤ x.length + t := by
  have h := materialized_boundary_dimension_le_max M x t encode v hne houtput
  omega

/-- Preserving the designated derivative minor and explicitly materializing
a boundary row incurs its binomial dimension in actual input-plus-time. -/
theorem materialized_designated_minor_cost {m k q : ℕ}
    (B : Poly m →ₗ[ℚ] (Fin q → ℚ))
    (hB : LinearIndependent ℚ (fun S : KSubset m k => B (qRow S.val)))
    (M : Machine) (x : List Bool) (t : ℕ)
    (encode : ℚ → List Bool) (p : Poly m)
    (hne : ∀ i, 0 < (encode (B p i)).length)
    (houtput : transOut M x t = (coordinateRecords encode (B p)).flatten) :
    Nat.choose m k ≤ x.length + t :=
  (faithful_designated_boundary_dimension B hB).trans
    (materialized_boundary_dimension_le_input_add_time M x t encode (B p) hne houtput)

theorem materialized_designated_minor_time_lower {m k q : ℕ}
    (B : Poly m →ₗ[ℚ] (Fin q → ℚ))
    (hB : LinearIndependent ℚ (fun S : KSubset m k => B (qRow S.val)))
    (M : Machine) (x : List Bool) (t : ℕ)
    (encode : ℚ → List Bool) (p : Poly m)
    (hne : ∀ i, 0 < (encode (B p i)).length)
    (houtput : transOut M x t = (coordinateRecords encode (B p)).flatten) :
    Nat.choose m k - x.length ≤ t := by
  have h := materialized_designated_minor_cost B hB M x t encode p hne houtput
  omega

/-- If the initial tape is shorter than the minor dimension, its full
dimension is a lower bound for this explicit constructor's clock. -/
theorem materialized_designated_minor_time_lower_of_short_input {m k q : ℕ}
    (B : Poly m →ₗ[ℚ] (Fin q → ℚ))
    (hB : LinearIndependent ℚ (fun S : KSubset m k => B (qRow S.val)))
    (M : Machine) (x : List Bool) (t : ℕ) (hinput : x.length < Nat.choose m k)
    (encode : ℚ → List Bool) (p : Poly m)
    (hne : ∀ i, 0 < (encode (B p i)).length)
    (houtput : transOut M x t = (coordinateRecords encode (B p)).flatten) :
    Nat.choose m k ≤ t := by
  have hdim := faithful_designated_boundary_dimension B hB
  have hsize := materialized_boundary_dimension_le_max M x t encode (B p) hne houtput
  omega

/-- The actual expander/positive boundary supplies the independence theorem;
this specialization adds no assumed rank or minor-preservation certificate. -/
theorem positive_boundary_materialization_cost
    {m k q c : ℕ} {Edge : Type*} [Fintype Edge] [DecidableEq Edge]
    (G : TseitinGraph (Fin m) Edge) (hexp : G.HasExpansion c)
    (hwindow : 4 * k ≤ m) (erased : Finset Edge) (herased : erased.card < 2 * c)
    (hcapacity : Nat.choose m k ≤ q)
    (M : Machine) (x : List Bool) (t : ℕ)
    (encode : ℚ → List Bool) (p : Poly m)
    (hne : ∀ i, 0 < (encode (designatedBoundary (k := k) G erased q p i)).length)
    (houtput : transOut M x t =
      (coordinateRecords encode (designatedBoundary (k := k) G erased q p)).flatten) :
    Nat.choose m k ≤ x.length + t :=
  materialized_designated_minor_cost (designatedBoundary (k := k) G erased q)
    (boundary_qRows_linearIndependent G hexp hwindow erased herased hcapacity)
    M x t encode p hne houtput

/-- The exact unchanged production action of this zero-coordinate gauge is
`r + 1/(1+r)`, and hence at most `r+1`. The graph may be any actual production
regular graph; its edge term vanishes on the specified coordinate field. -/
theorem boundaryGauge_unit_action_le_rank_add_one (m k : ℕ) {d : ℕ}
    (G : RegularGraphFixed m d) (α : ℝ) :
    fullLagrangianFixed α 1 1 G (boundaryGauge m k) ≤ (Nat.choose m k : ℝ) + 1 := by
  rw [boundaryGauge_action]
  simp only [one_mul]
  have h : 1 / (1 + (Nat.choose m k : ℝ)) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by
      have hr : (0 : ℝ) ≤ Nat.choose m k := Nat.cast_nonneg _
      linarith)
  linarith

/-- Runtime controls this concrete production gauge action when the machine
actually materializes a dense row of a boundary preserving the designated
minor. The statement does not infer that contract from SAT correctness. -/
theorem materialized_boundaryGauge_action_le_input_add_time
    {m k q d : ℕ} (G : RegularGraphFixed m d) (α : ℝ)
    (B : GodMoveMonomialMinor.Poly m →ₗ[ℚ] (Fin q → ℚ))
    (hB : LinearIndependent ℚ (fun S : KSubset m k => B (qRow S.val)))
    (M : Machine) (x : List Bool) (t : ℕ)
    (encode : ℚ → List Bool) (p : GodMoveMonomialMinor.Poly m)
    (hne : ∀ i, 0 < (encode (B p i)).length)
    (houtput : transOut M x t = (coordinateRecords encode (B p)).flatten) :
    fullLagrangianFixed α 1 1 G (boundaryGauge m k) ≤ (x.length : ℝ) + t + 1 := by
  have hdim : (Nat.choose m k : ℝ) ≤ (x.length : ℝ) + t := by
    exact_mod_cast materialized_designated_minor_cost B hB M x t encode p hne houtput
  have haction := boundaryGauge_unit_action_le_rank_add_one m k G α
  linarith

/-- The sharper action/runtime bound when the input does not already contain
as many bits as the retained minor has dimensions. -/
theorem materialized_boundaryGauge_action_le_time_add_one
    {m k q d : ℕ} (G : RegularGraphFixed m d) (α : ℝ)
    (B : GodMoveMonomialMinor.Poly m →ₗ[ℚ] (Fin q → ℚ))
    (hB : LinearIndependent ℚ (fun S : KSubset m k => B (qRow S.val)))
    (M : Machine) (x : List Bool) (t : ℕ) (hinput : x.length < Nat.choose m k)
    (encode : ℚ → List Bool) (p : GodMoveMonomialMinor.Poly m)
    (hne : ∀ i, 0 < (encode (B p i)).length)
    (houtput : transOut M x t = (coordinateRecords encode (B p)).flatten) :
    fullLagrangianFixed α 1 1 G (boundaryGauge m k) ≤ (t : ℝ) + 1 := by
  have hdim : (Nat.choose m k : ℝ) ≤ t := by
    exact_mod_cast materialized_designated_minor_time_lower_of_short_input
      B hB M x t hinput encode p hne houtput
  have haction := boundaryGauge_unit_action_le_rank_add_one m k G α
  linarith

/-- The expander/positive boundary supplies preservation, so only its proved
graph hypotheses and the explicit physical output contract are needed. -/
theorem positive_boundaryGauge_action_le_input_add_time
    {m k q c d : ℕ} {Edge : Type*} [Fintype Edge] [DecidableEq Edge]
    (G : RegularGraphFixed m d) (α : ℝ)
    (H : TseitinGraph (Fin m) Edge) (hexp : H.HasExpansion c)
    (hwindow : 4 * k ≤ m) (erased : Finset Edge) (herased : erased.card < 2 * c)
    (hcapacity : Nat.choose m k ≤ q)
    (M : Machine) (x : List Bool) (t : ℕ)
    (encode : ℚ → List Bool) (p : GodMoveMonomialMinor.Poly m)
    (hne : ∀ i, 0 < (encode (designatedBoundary (k := k) H erased q p i)).length)
    (houtput : transOut M x t =
      (coordinateRecords encode (designatedBoundary (k := k) H erased q p)).flatten) :
    fullLagrangianFixed α 1 1 G (boundaryGauge m k) ≤ (x.length : ℝ) + t + 1 :=
  materialized_boundaryGauge_action_le_input_add_time G α
    (designatedBoundary (k := k) H erased q)
    (boundary_qRows_linearIndependent H hexp hwindow erased herased hcapacity)
    M x t encode p hne houtput

/-- The production gauge retains the data of the direct binary-code boundary
as well as the earlier enumerated boundary, on every input polynomial. -/
theorem boundaryGauge_preserves_executableBoundary {m k E : ℕ}
    (H : TseitinGraph (Fin m) (Fin E)) (erased : Finset (Fin E))
    (q : ℕ) (p : GodMoveMonomialMinor.Poly m) :
    GodMoveExecutableBoundary.designatedBoundary (k := k) H erased q
        ((boundaryGauge m k).projection p) =
      GodMoveExecutableBoundary.designatedBoundary (k := k) H erased q p := by
  ext j
  change (∑ S : KSubset m k,
      GodMoveBoundaryNFrameGauge.rowCoordinates m k
        (GodMoveBoundaryNFrameGauge.rowSynthesis m k
          (GodMoveBoundaryNFrameGauge.rowCoordinates m k p)) S * _) =
    ∑ S : KSubset m k, GodMoveBoundaryNFrameGauge.rowCoordinates m k p S * _
  rw [GodMoveBoundaryNFrameGauge.coordinates_synthesis]

/-- The executable-code construction, actual row-preserving production
gauge, and operational runtime bound meet in this single theorem. The dense
output contract remains explicit and is not inferred from SAT correctness. -/
theorem executable_boundaryGauge_action_le_input_add_time
    {m k q c d E : ℕ} (G : RegularGraphFixed m d) (α : ℝ)
    (H : TseitinGraph (Fin m) (Fin E)) (hexp : H.HasExpansion c)
    (hwindow : 4 * k ≤ m) (erased : Finset (Fin E)) (herased : erased.card < 2 * c)
    (hcapacity : Nat.choose m k ≤ q)
    (M : Machine) (x : List Bool) (t : ℕ)
    (encode : ℚ → List Bool) (p : GodMoveMonomialMinor.Poly m)
    (hne : ∀ i, 0 < (encode
      (GodMoveExecutableBoundary.designatedBoundary (k := k) H erased q p i)).length)
    (houtput : transOut M x t = (coordinateRecords encode
      (GodMoveExecutableBoundary.designatedBoundary (k := k) H erased q p)).flatten) :
    fullLagrangianFixed α 1 1 G (boundaryGauge m k) ≤ (x.length : ℝ) + t + 1 :=
  materialized_boundaryGauge_action_le_input_add_time G α
    (GodMoveExecutableBoundary.designatedBoundary (k := k) H erased q)
    (GodMoveExecutableBoundary.boundary_qRows_linearIndependent
      H hexp hwindow erased herased hcapacity)
    M x t encode p hne houtput

/-- An explicit dense constructor cannot fit the logarithmic minor within a
polynomial total input-plus-time budget. This is not a SAT-decider bound. -/
theorem no_polynomial_budget_materialization {m q : ℕ}
    (d : ℕ) (hm : 2 ^ (max 20 (4 * (d + 1))) ≤ m)
    (B : Poly m →ₗ[ℚ] (Fin q → ℚ))
    (hB : LinearIndependent ℚ (fun S : KSubset m (Nat.log 2 m) => B (qRow S.val)))
    (M : Machine) (x : List Bool) (t : ℕ) (hbudget : x.length + t ≤ m ^ d)
    (encode : ℚ → List Bool) (p : Poly m)
    (hne : ∀ i, 0 < (encode (B p i)).length) :
    transOut M x t ≠ (coordinateRecords encode (B p)).flatten := by
  intro houtput
  exact (not_le_of_gt (npow_lt_choose_log m d hm))
    ((materialized_designated_minor_cost B hB M x t encode p hne houtput).trans hbudget)

end GodMoveBoundaryRuntimeCost

#print axioms GodMoveBoundaryRuntimeCost.run_head_tape_bounds
#print axioms GodMoveBoundaryRuntimeCost.transOut_length_le_input_add_time
#print axioms GodMoveBoundaryRuntimeCost.coordinate_count_le_serialized_length
#print axioms GodMoveBoundaryRuntimeCost.materialized_boundary_dimension_le_input_add_time
#print axioms GodMoveBoundaryRuntimeCost.materialized_designated_minor_cost
#print axioms GodMoveBoundaryRuntimeCost.materialized_designated_minor_time_lower
#print axioms GodMoveBoundaryRuntimeCost.materialized_designated_minor_time_lower_of_short_input
#print axioms GodMoveBoundaryRuntimeCost.positive_boundary_materialization_cost
#print axioms GodMoveBoundaryRuntimeCost.boundaryGauge_unit_action_le_rank_add_one
#print axioms GodMoveBoundaryRuntimeCost.materialized_boundaryGauge_action_le_input_add_time
#print axioms GodMoveBoundaryRuntimeCost.materialized_boundaryGauge_action_le_time_add_one
#print axioms GodMoveBoundaryRuntimeCost.positive_boundaryGauge_action_le_input_add_time
#print axioms GodMoveBoundaryRuntimeCost.boundaryGauge_preserves_executableBoundary
#print axioms GodMoveBoundaryRuntimeCost.executable_boundaryGauge_action_le_input_add_time
#print axioms GodMoveBoundaryRuntimeCost.no_polynomial_budget_materialization
