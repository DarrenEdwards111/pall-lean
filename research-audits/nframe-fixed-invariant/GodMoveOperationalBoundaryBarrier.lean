import GodMoveBoundaryRuntimeCost
import GodMoveBoundaryRuntimeBarrier

/-!
# Actual machine serialization at polynomially related encoded lengths

This connects the numerical materialization barrier to the existing legal
machine semantics. Exact dense-coordinate tape output gives
`q(n) ≤ inputLength(n) + T(inputLength(n))`; the varying input allowance is
accounted for rather than treated as a fixed startup constant.

Polynomial input length and a polynomial clock in that encoded length would
make this entire budget polynomial in n, contradicting the proved boundary
growth at m = n/3 and derivative order log₂ n. The actual pinned-unit input
family has its required quadratic length bound and is included explicitly.

The constructor must satisfy the stated serialization equation. Nothing
here says SAT correctness forces such output, or charges a compact operator
description for coordinates that it never materializes. The supplied codec
need only have nonempty coordinate records for the size argument; a decoding
or exact-value theorem for that codec is a separate property.
-/

namespace GodMoveOperationalBoundaryBarrier

open PallLean.Paper93.DeepMath.PathB ComposableMachine
open PvsNPSeparatingInvariant (PolyBounded)
open CookLevinEmitClockBounds3 (PB_add)
open GodMoveBoundaryRuntimeCost GodMoveBoundaryRuntimeBarrier
open GodMoveMonomialMinor GodMoveDesignatedPositiveBoundary
open GodMoveSATUnitExtraction GodMoveUnitCharacteristic
open GodMovePinnedSATQueries GodMoveSymbolicPinnedInput
open GodMoveExpanderBoundaryExamples
open CookLevinEmitCodec

/-- Polynomial clocks remain polynomial after a polynomial encoded-length
substitution, with the encoding cost included in the exponent and constant. -/
theorem polynomial_clock_at_polynomial_length (L T : ℕ → ℕ)
    (hL : PolyBounded L) (hT : PolyBounded T) :
    PolyBounded (fun n => T (L n)) := by
  obtain ⟨c, a, hc⟩ := hL
  obtain ⟨d, b, hd⟩ := hT
  refine ⟨d * (c + 1) ^ b, a * b, ?_⟩
  intro n
  have hpos : 1 ≤ (n + 1) ^ a := Nat.one_le_pow a (n + 1) (by omega)
  have hlength : L n + 1 ≤ (c + 1) * (n + 1) ^ a := by
    have h := hc n
    nlinarith
  calc
    T (L n) ≤ d * (L n + 1) ^ b := hd (L n)
    _ ≤ d * ((c + 1) * (n + 1) ^ a) ^ b :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlength b)
    _ = (d * (c + 1) ^ b) * (n + 1) ^ (a * b) := by
      rw [mul_pow, ← pow_mul, mul_assoc]

/-- The numerical write allowance follows from actual legal machine steps
and the exact serialized output, including the varying initial tape length. -/
theorem actual_serialization_budget (q L T : ℕ → ℕ)
    (M : Machine) (x : ℕ → List Bool) (hx : ∀ n, (x n).length = L n)
    (encode : ℕ → ℚ → List Bool) (v : ∀ n, Fin (q n) → ℚ)
    (hne : ∀ n i, 0 < (encode n (v n i)).length)
    (houtput : ∀ n, transOut M (x n) (T (L n)) =
      (coordinateRecords (encode n) (v n)).flatten) :
    ∀ n, q n ≤ L n + T (L n) := by
  intro n
  simpa only [hx n] using
    materialized_boundary_dimension_le_input_add_time M (x n) (T (L n))
      (encode n) (v n) (hne n) (houtput n)

/-- Actual dense output with the proved growing dimension cannot be produced
by a clock polynomial in its polynomially bounded encoded input length. -/
theorem actual_dense_constructor_not_polynomial (q L T : ℕ → ℕ)
    (hg : BoundaryGrowth q) (hL : PolyBounded L)
    (M : Machine) (x : ℕ → List Bool) (hx : ∀ n, (x n).length = L n)
    (encode : ℕ → ℚ → List Bool) (v : ∀ n, Fin (q n) → ℚ)
    (hne : ∀ n i, 0 < (encode n (v n i)).length)
    (houtput : ∀ n, transOut M (x n) (T (L n)) =
      (coordinateRecords (encode n) (v n)).flatten) :
    ¬ PolyBounded T := by
  intro hT
  have hcost := actual_serialization_budget q L T M x hx encode v hne houtput
  have hnot := explicit_materialization_not_polynomial q (fun n => L n + T (L n))
    hg 1 0 (fun n => by simpa using hcost n)
  exact hnot (PB_add hL (polynomial_clock_at_polynomial_length L T hL hT))

/-- The output contract need only hold beyond a specified cutoff. This
avoids imposing a dense-output layout on irrelevant small input sizes. -/
theorem actual_dense_constructor_not_polynomial_eventually
    (q L T : ℕ → ℕ) (n0 : ℕ) (hg : BoundaryGrowth q) (hL : PolyBounded L)
    (M : Machine) (x : ℕ → List Bool) (hx : ∀ n, (x n).length = L n)
    (encode : ℕ → ℚ → List Bool) (v : ∀ n, Fin (q n) → ℚ)
    (hne : ∀ n, n0 ≤ n → ∀ i, 0 < (encode n (v n i)).length)
    (houtput : ∀ n, n0 ≤ n → transOut M (x n) (T (L n)) =
      (coordinateRecords (encode n) (v n)).flatten) :
    ¬ PolyBounded T := by
  intro hT
  obtain ⟨C, d, hbudget⟩ :=
    PB_add hL (polynomial_clock_at_polynomial_length L T hL hT)
  apply no_eventual_polynomial q hg
  refine ⟨C * 2 ^ d, d, max n0 1, ?_⟩
  intro n hn
  have hn0 : n0 ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hcost := materialized_boundary_dimension_le_input_add_time M (x n) (T (L n))
    (encode n) (v n) (hne n hn0) (houtput n hn0)
  rw [hx n] at hcost
  calc
    q n ≤ L n + T (L n) := hcost
    _ ≤ C * (n + 1) ^ d := hbudget n
    _ ≤ C * (2 * n) ^ d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) d)
    _ = (C * 2 ^ d) * n ^ d := by rw [mul_pow, mul_assoc]

/-- Growth is derived from the actual designated derivative-row family,
without replacing it by the full-monomial rows. -/
theorem growth_of_designated_boundaries (q : ℕ → ℕ)
    (B : ∀ n, Poly (n / 3) →ₗ[ℚ] (Fin (q n) → ℚ))
    (hB : ∀ n, LinearIndependent ℚ
      (fun S : KSubset (n / 3) (Nat.log 2 n) => B n (qRow S.val))) :
    BoundaryGrowth q := by
  intro n hn
  exact (BinomialBound.binomial_lower_bound_concrete n hn).trans
    ((Nat.choose_mono (Nat.log 2 n) (by omega : n / 30 ≤ n / 3)).trans
      (faithful_designated_boundary_dimension (B n) (hB n)))

theorem growth_of_designated_boundaries_at_paper_window (q : ℕ → ℕ)
    (B : ∀ n, Poly (n / 3) →ₗ[ℚ] (Fin (q n) → ℚ))
    (hB : ∀ n, 2 ^ 20 ≤ n → LinearIndependent ℚ
      (fun S : KSubset (n / 3) (Nat.log 2 n) => B n (qRow S.val))) :
    BoundaryGrowth q := by
  intro n hn
  exact (BinomialBound.binomial_lower_bound_concrete n hn).trans
    ((Nat.choose_mono (Nat.log 2 n) (by omega : n / 30 ≤ n / 3)).trans
      (faithful_designated_boundary_dimension (B n) (hB n hn)))

/-- Exact quadratic encoded-length control for the operational paper family. -/
theorem paper_input_length_polynomial :
    PolyBounded (fun n => unitInputLength (n / 3)) := by
  refine ⟨23, 2, ?_⟩
  intro n
  exact (GodMoveSATSourceCanonicity.unitSourceLength_le_quadratic (n / 3)).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (Nat.add_le_add_right (Nat.div_le_self n 3) 1) 2))

/-- A genuine encoded member of the pinned-unit query family. No satisfying
assignment or SAT computation is used to construct this input word. -/
def paperPinnedWord (n : ℕ) (a : Fin (n / 3) → Bool) : List Bool :=
  encodeFormula' (pinnedFormula (unitFormula (n / 3)) a)

theorem paperPinnedWord_length (n : ℕ) (a : Fin (n / 3) → Bool) :
    (paperPinnedWord n a).length = unitInputLength (n / 3) :=
  encoded_pinned_length (unitFormula (n / 3)) a

/-- The theorem for actual encoded pinned-unit inputs and designated rows.
The only constructor premise is explicit dense boundary output; no premise
asserts or concludes that every SAT decider performs that construction. -/
theorem paper_designated_dense_constructor_not_polynomial
    (q T : ℕ → ℕ)
    (B : ∀ n, Poly (n / 3) →ₗ[ℚ] (Fin (q n) → ℚ))
    (hB : ∀ n, 2 ^ 20 ≤ n → LinearIndependent ℚ
      (fun S : KSubset (n / 3) (Nat.log 2 n) => B n (qRow S.val)))
    (M : Machine) (a : ∀ n, Fin (n / 3) → Bool)
    (encode : ℕ → ℚ → List Bool) (p : ∀ n, Poly (n / 3))
    (hne : ∀ n, 2 ^ 20 ≤ n → ∀ i, 0 < (encode n (B n (p n) i)).length)
    (houtput : ∀ n, 2 ^ 20 ≤ n → transOut M (paperPinnedWord n (a n))
        (T (unitInputLength (n / 3))) =
      (coordinateRecords (encode n) (B n (p n))).flatten) :
    ¬ PolyBounded T :=
  actual_dense_constructor_not_polynomial_eventually
    q (fun n => unitInputLength (n / 3)) T (2 ^ 20)
    (growth_of_designated_boundaries_at_paper_window q B hB) paper_input_length_polynomial
    M (fun n => paperPinnedWord n (a n)) (fun n => paperPinnedWord_length n (a n))
    encode (fun n => B n (p n)) hne houtput

/-- The actual positive designated-row boundary on the existing complete
graph, with no erased edges and exactly the retained minor dimension. -/
noncomputable def paperPositiveBoundary (n : ℕ) :
    GodMoveMonomialMinor.Poly (n / 3) →ₗ[ℚ]
      (Fin (Nat.choose (n / 3) (Nat.log 2 n)) → ℚ) :=
  designatedBoundary (k := Nat.log 2 n) (completeGraph (n / 3)) ∅
    (Nat.choose (n / 3) (Nat.log 2 n))

theorem paperPositiveBoundary_rows_independent (n : ℕ) (hn : 2 ^ 20 ≤ n) :
    LinearIndependent ℚ (fun S : KSubset (n / 3) (Nat.log 2 n) =>
      paperPositiveBoundary n (qRow S.val)) := by
  exact boundary_qRows_linearIndependent (completeGraph (n / 3))
    (completeGraph_hasExpansion (n / 3)) (paper_window n hn) ∅ (by simp) le_rfl

/-- Concrete positive-boundary specialization: growth and row preservation
are proved, while actual dense serialization remains the constructor's
explicit operational obligation. -/
theorem paper_positive_dense_constructor_not_polynomial
    (T : ℕ → ℕ) (M : Machine) (a : ∀ n, Fin (n / 3) → Bool)
    (encode : ℕ → ℚ → List Bool) (p : ∀ n, Poly (n / 3))
    (hne : ∀ n, 2 ^ 20 ≤ n → ∀ i,
      0 < (encode n (paperPositiveBoundary n (p n) i)).length)
    (houtput : ∀ n, 2 ^ 20 ≤ n → transOut M (paperPinnedWord n (a n))
        (T (unitInputLength (n / 3))) =
      (coordinateRecords (encode n) (paperPositiveBoundary n (p n))).flatten) :
    ¬ PolyBounded T :=
  paper_designated_dense_constructor_not_polynomial
    (fun n => Nat.choose (n / 3) (Nat.log 2 n)) T paperPositiveBoundary
    paperPositiveBoundary_rows_independent M a encode p hne houtput

end GodMoveOperationalBoundaryBarrier

#print axioms GodMoveOperationalBoundaryBarrier.polynomial_clock_at_polynomial_length
#print axioms GodMoveOperationalBoundaryBarrier.actual_serialization_budget
#print axioms GodMoveOperationalBoundaryBarrier.actual_dense_constructor_not_polynomial
#print axioms GodMoveOperationalBoundaryBarrier.actual_dense_constructor_not_polynomial_eventually
#print axioms GodMoveOperationalBoundaryBarrier.growth_of_designated_boundaries
#print axioms GodMoveOperationalBoundaryBarrier.growth_of_designated_boundaries_at_paper_window
#print axioms GodMoveOperationalBoundaryBarrier.paper_input_length_polynomial
#print axioms GodMoveOperationalBoundaryBarrier.paperPinnedWord_length
#print axioms GodMoveOperationalBoundaryBarrier.paper_designated_dense_constructor_not_polynomial
#print axioms GodMoveOperationalBoundaryBarrier.paperPositiveBoundary_rows_independent
#print axioms GodMoveOperationalBoundaryBarrier.paper_positive_dense_constructor_not_polynomial
