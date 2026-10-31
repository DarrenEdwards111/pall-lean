import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSolverRelativeFutureContinuationQuotient

/-!
# Succinct future-continuation resource audit

The semantic future quotient of the expander SAT family has `2^r` classes, but
cardinality is not a succinct complexity measure.  This file audits the first
natural replacement: the number of bits needed to represent a future class,
together with the locality of reading and updating those bits.

The result is an exact calibration and another no-go.  Every Boolean future
experiment with `r` named contexts has a canonical `r`-bit truth-table
presentation: store the answer to each context and evaluate context `i` by
reading bit `i`.  For the expanded SAT residual this presentation is optimal,
because all `2^r` signatures occur, but optimal width is still only `r`.

Moreover the canonical code supports single-coordinate involutive updates;
different updates commute and a query reads exactly one coordinate.  Thus the
full solver-relative SAT continuation quotient simultaneously has exponential
cardinality, linear description width, and maximally local read/write
dynamics.  None of those resources yields a superpolynomial lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.SuccinctFutureContinuationResourceAudit

open SATDepthMachine
open BranchSpanningDynamicHolonomy
open ExpanderSATQueryContinuation
open NonLocalActionHolonomyConservation
open SolverRelativeFutureContinuationQuotient

variable {State Context : Type*}

/-- A width-`w` Boolean presentation of all future answers. -/
structure BitPresentation (E : FutureExperiment State Context Bool)
    (w : ℕ) where
  encode : State → (Fin w → Bool)
  evaluate : (Fin w → Bool) → Context → Bool
  faithful : ∀ state context,
    evaluate (encode state) context = E.answer state context

namespace BitPresentation

/-- Forget the bit syntax and retain an ordinary faithful finite
representation. -/
def toFaithfulRepresentation [Fintype State]
    {E : FutureExperiment State Context Bool} {w : ℕ}
    (P : BitPresentation E w) :
    FutureExperiment.FaithfulRepresentation E (Fin w → Bool) where
  encode := P.encode
  decode := P.evaluate
  faithful := P.faithful

/-- A width-`w` presentation realizes at most `2^w` future classes. -/
theorem quotientRank_le_two_pow [Fintype State]
    {E : FutureExperiment State Context Bool} {w : ℕ}
    (P : BitPresentation E w) :
    E.quotientRank ≤ 2 ^ w := by
  have h := FutureExperiment.quotientRank_le_code_card
    E (Fin w → Bool) P.toFaithfulRepresentation
  simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using h

end BitPresentation

/-! ## The universal truth-table presentation -/

/-- Every Boolean experiment with `r` named future contexts has a canonical
`r`-bit presentation, independently of how difficult its answers are to
compute from the original state. -/
def truthTablePresentation (E : FutureExperiment State (Fin r) Bool) :
    BitPresentation E r where
  encode := E.answer
  evaluate := fun bits i => bits i
  faithful := by
    intro state i
    rfl

/-- Its evaluator is literally one coordinate projection. -/
theorem truthTablePresentation_evaluate
    (E : FutureExperiment State (Fin r) Bool)
    (bits : Fin r → Bool) (i : Fin r) :
    (truthTablePresentation E).evaluate bits i = bits i := rfl

/-- Toggle one coordinate of a succinct future signature. -/
def toggleCoordinate {r : ℕ} (i : Fin r) (bits : Fin r → Bool) :
    Fin r → Bool :=
  fun j => if j = i then !bits j else bits j

@[simp] theorem toggleCoordinate_at {r : ℕ} (i : Fin r)
    (bits : Fin r → Bool) :
    toggleCoordinate i bits i = !bits i := by
  simp [toggleCoordinate]

theorem toggleCoordinate_off {r : ℕ} (i j : Fin r)
    (hji : j ≠ i) (bits : Fin r → Bool) :
    toggleCoordinate i bits j = bits j := by
  simp [toggleCoordinate, hji]

/-- A local update is an involution. -/
theorem toggleCoordinate_involutive {r : ℕ} (i : Fin r)
    (bits : Fin r → Bool) :
    toggleCoordinate i (toggleCoordinate i bits) = bits := by
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [toggleCoordinate, hji]

/-- Distinct or repeated single-coordinate updates commute. -/
theorem toggleCoordinate_commute {r : ℕ} (i j : Fin r)
    (bits : Fin r → Bool) :
    toggleCoordinate i (toggleCoordinate j bits) =
      toggleCoordinate j (toggleCoordinate i bits) := by
  by_cases hij : i = j
  · subst j
    rfl
  · funext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp_all [toggleCoordinate]

/-- Updating coordinate `i` changes no future answer except possibly context
`i`, because evaluation itself is coordinate-local. -/
theorem truthTable_update_invisible_off_context
    (E : FutureExperiment State (Fin r) Bool)
    (bits : Fin r → Bool) (i j : Fin r) (hji : j ≠ i) :
    (truthTablePresentation E).evaluate (toggleCoordinate i bits) j =
      (truthTablePresentation E).evaluate bits j := by
  exact toggleCoordinate_off i j hji bits

/-! ## Exact expander/SAT calibration -/

variable {V Edge ι : Type}
variable [Fintype V] [DecidableEq V]
variable [Fintype Edge] [DecidableEq Edge]
variable [Fintype ι] [DecidableEq ι]

/-- The canonical succinct presentation of the solver-relative expander
future quotient. -/
noncomputable def expanderTruthTablePresentation
    {U : MachineModel} (D : DecisionMachine U)
    (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V) :
    BitPresentation
      (expanderSolverFutureExperiment D G hc hexp readSet hread hmed)
      (Fintype.card ι) :=
  truthTablePresentation _

/-- SAT correctness identifies the canonical truth-table code with the
natural expander residual bits. -/
theorem expanderTruthTable_encode_eq_residualBits
    {U : MachineModel} (D : DecisionMachine U) (hD : DecidesSAT U D)
    (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V)
    (x : Edge → ZMod 2) :
    (expanderTruthTablePresentation D G hc hexp readSet hread hmed).encode x =
      expanderResidualBits G readSet x := by
  let F := expanderResidualSATQueries G hc hexp readSet hread hmed
  exact F.answers_eq_label D hD x

/-- Any bit presentation of the full solver-relative expander continuation
semantics needs at least `r` bits. -/
theorem expanderBitPresentation_force_width
    {U : MachineModel} (D : DecisionMachine U) (hD : DecidesSAT U D)
    (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V)
    {w : ℕ}
    (P : BitPresentation
      (expanderSolverFutureExperiment D G hc hexp readSet hread hmed) w) :
    Fintype.card ι ≤ w := by
  have hlower : 2 ^ Fintype.card ι ≤ 2 ^ w := by
    rw [← expanderSolver_quotientRank_eq_two_pow
      D hD G hc hexp readSet hread hmed]
    exact P.quotientRank_le_two_pow
  exact (Nat.pow_le_pow_iff_right (by omega)).mp hlower

/-- The lower bound is tight: the canonical code uses exactly `r` bits and
answers every future context by one coordinate projection. -/
theorem expander_minimum_bit_width_eq_r
    {U : MachineModel} (D : DecisionMachine U) (hD : DecidesSAT U D)
    (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V) :
    Nonempty (BitPresentation
        (expanderSolverFutureExperiment D G hc hexp readSet hread hmed)
        (Fintype.card ι)) ∧
      (∀ w, BitPresentation
        (expanderSolverFutureExperiment D G hc hexp readSet hread hmed) w →
        Fintype.card ι ≤ w) := by
  constructor
  · exact ⟨expanderTruthTablePresentation
      D G hc hexp readSet hread hmed⟩
  · intro w P
    exact expanderBitPresentation_force_width
      D hD G hc hexp readSet hread hmed P

/-- A proposed polynomial-width succinct presentation at one expander scale. -/
structure PolynomialWidthPresentationAt
    {U : MachineModel} (D : DecisionMachine U)
    (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V)
    (k : ℕ) : Type where
  width : ℕ
  presentation : BitPresentation
    (expanderSolverFutureExperiment D G hc hexp readSet hread hmed) width
  polynomialWidth : width ≤ (Fintype.card ι) ^ k

/-- **Succinct no-go calibration.**  Unlike a polynomial-cardinality quotient,
a polynomial-width presentation is not contradictory.  Every SAT-correct
decider's full expander continuation semantics has one already at exponent
`1`, with exact width `r`. -/
noncomputable def expander_has_linearWidthPresentation
    {U : MachineModel} (D : DecisionMachine U) (_hD : DecidesSAT U D)
    (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V) :
    PolynomialWidthPresentationAt
      D G hc hexp readSet hread hmed 1 where
  width := Fintype.card ι
  presentation := expanderTruthTablePresentation
    D G hc hexp readSet hread hmed
  polynomialWidth := by simp

/-!
## Audit verdict

Moving from quotient cardinality to bit width repairs the representation
mistake but removes the hoped-for lower bound.  The exact SAT continuation
quotient needs `r` bits, and `r` bits suffice.  Its evaluator reads one bit;
its natural coordinate updates are local commuting involutions.

Therefore state width, query locality, update locality, action length, raw
outcome count, and pairwise commutators are all calibrated and exhausted on
this family.  The next resource would have to charge the *uniform computation
of the encoding or evaluator from the original SAT syntax*, not merely the
size and local dynamics of an already materialized residual signature.

But a polynomial-time SAT solver would itself provide such a uniform
evaluator.  Proving that every such evaluator needs superpolynomial circuit or
machine complexity is exactly a nonuniform or uniform SAT lower bound.  It
cannot be obtained from semantic quotient faithfulness alone.
-/

end PallLean.Paper93.DeepMath.PathB.SuccinctFutureContinuationResourceAudit

#print axioms PallLean.Paper93.DeepMath.PathB.SuccinctFutureContinuationResourceAudit.BitPresentation.quotientRank_le_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.SuccinctFutureContinuationResourceAudit.toggleCoordinate_commute
#print axioms PallLean.Paper93.DeepMath.PathB.SuccinctFutureContinuationResourceAudit.expanderTruthTable_encode_eq_residualBits
#print axioms PallLean.Paper93.DeepMath.PathB.SuccinctFutureContinuationResourceAudit.expanderBitPresentation_force_width
#print axioms PallLean.Paper93.DeepMath.PathB.SuccinctFutureContinuationResourceAudit.expander_minimum_bit_width_eq_r
#print axioms PallLean.Paper93.DeepMath.PathB.SuccinctFutureContinuationResourceAudit.expander_has_linearWidthPresentation
