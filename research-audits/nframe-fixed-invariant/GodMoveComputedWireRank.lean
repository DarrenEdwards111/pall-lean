import GodMoveCircuitPolynomialSize
import GodMoveBooleanDifferentiation

/-!
# A normalization-safe rank of actually computed wires

Take the linear span of the normalized polynomials emitted by the actual
shared arithmetic DAG. These are symbolic denotations across an input slice,
not polynomial data explicitly produced by a single concrete machine run.
Each Boolean-circuit gate output appends one vector, so the rank
increases by at most one, regardless of fan-out, reuse, or repeated reads.
Normalization is applied to this existing wire span, where it is a linear
map and cannot increase dimension. The final characteristic belongs to it.

This supplies a computation-dependent rank with a derived clock upper bound.
It does not give an efficient algorithm for expanding the normalized wires
or computing their span dimension, nor a one-dimension bound per machine step.
It does not contain all derivatives of its output in general: that tempting
lower-bound extraction is formally refuted at the existing SPDP parameters.
-/

namespace GodMoveComputedWireRank

open GodMoveBooleanInterpolation GodMoveCircuitNormalization GodMoveCircuitConnection
open GodMoveCircuitRuntimeCost GodMoveCircuitPolynomialSize
open GodMoveCircuitArithmetization (AExpr runArithmetic arithGate)
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer (CGate)
open ComposableMachine CookLevinReduction CookLevinEmitCodec
open PvsNPSeparatingInvariant (PolyBounded)
open MultilinearSPDP

noncomputable def spanWires {n : ℕ} (xs : List (Poly n)) : Submodule ℚ (Poly n) :=
  Submodule.span ℚ (↑xs.toFinset : Set (Poly n))

instance spanWires_finite {n : ℕ} (xs : List (Poly n)) :
    FiniteDimensional ℚ (spanWires xs) :=
  Module.Finite.span_of_finite ℚ xs.toFinset.finite_toSet

theorem spanWires_finrank_le_length {n : ℕ} (xs : List (Poly n)) :
    Module.finrank ℚ (spanWires xs) ≤ xs.length := by
  classical
  have h : Module.finrank ℚ (spanWires xs) ≤ xs.toFinset.card := by
    simpa [spanWires] using finrank_span_le_card (R := ℚ) (↑xs.toFinset : Set (Poly n))
  exact h.trans (List.toFinset_card_le xs)

theorem spanWires_append_singleton {n : ℕ} (xs : List (Poly n)) (p : Poly n) :
    spanWires (xs ++ [p]) = spanWires xs ⊔ Submodule.span ℚ {p} := by
  classical
  simp [spanWires, List.toFinset_append, Submodule.span_insert, sup_comm]

theorem spanWires_map {n : ℕ} (xs : List (Poly n)) (f : Poly n →ₗ[ℚ] Poly n) :
    spanWires (xs.map f) = (spanWires xs).map f := by
  classical
  unfold spanWires
  rw [Submodule.map_span]
  apply congrArg (Submodule.span ℚ)
  ext p
  simp

theorem runArithmetic_append {n : ℕ} {R : Type*} [Ring R]
    (x : Fin n → R) (vals : List R) (c d : List (AExpr n)) :
    runArithmetic x vals (c ++ d) = runArithmetic x (runArithmetic x vals c) d := by
  induction c generalizing vals with
  | nil => rfl
  | cons g gs ih => simpa only [List.cons_append, runArithmetic] using ih _

/-- Exact polynomial wire values of the compiled shared program. -/
noncomputable def rawWires {n : ℕ} (c : List (CGate n)) : List (Poly n) :=
  runArithmetic MvPolynomial.X [] (GodMoveCircuitArithmetization.compile c)

noncomputable def normalizedWires {n : ℕ} (c : List (CGate n)) : List (Poly n) :=
  (rawWires c).map GodMoveCircuitNormalization.normalize

noncomputable def wireSpace {n : ℕ} (c : List (CGate n)) : Submodule ℚ (Poly n) :=
  spanWires (normalizedWires c)

noncomputable def wireRank {n : ℕ} (c : List (CGate n)) : ℕ :=
  Module.finrank ℚ (wireSpace c)

instance wireSpace_finite {n : ℕ} (c : List (CGate n)) :
    FiniteDimensional ℚ (wireSpace c) := spanWires_finite _

theorem rawWires_length {n : ℕ} (c : List (CGate n)) : (rawWires c).length = c.length := by
  simp [rawWires, GodMoveCircuitArithmetization.runArithmetic_length,
    GodMoveCircuitArithmetization.compile_length]

theorem normalizedWires_length {n : ℕ} (c : List (CGate n)) :
    (normalizedWires c).length = c.length := by simp [normalizedWires, rawWires_length]

/-- A real rank bound from the number of emitted wire values. -/
theorem wireRank_le_length {n : ℕ} (c : List (CGate n)) : wireRank c ≤ c.length := by
  exact (spanWires_finrank_le_length (normalizedWires c)).trans_eq
    (normalizedWires_length c)

/-- Here normalization maps an already-formed linear space, rather than
recomputing derivatives of a normalized source polynomial. -/
theorem wireSpace_eq_image {n : ℕ} (c : List (CGate n)) :
    wireSpace c = (spanWires (rawWires c)).map (normalizeLinearMap n) :=
  spanWires_map _ _

theorem normalization_does_not_increase_wire_rank {n : ℕ} (c : List (CGate n)) :
    wireRank c ≤ Module.finrank ℚ (spanWires (rawWires c)) := by
  unfold wireRank
  rw [wireSpace_eq_image]
  exact Submodule.finrank_map_le _ _

theorem rawWires_append_gate {n : ℕ} (c : List (CGate n)) (g : CGate n) :
    rawWires (c ++ [g]) = rawWires c ++ [(arithGate g).eval MvPolynomial.X (rawWires c)] := by
  simp [rawWires, GodMoveCircuitArithmetization.compile, runArithmetic_append, runArithmetic]

/-- Each legal gate adds exactly one candidate vector to the computed space. -/
theorem wireSpace_append_gate {n : ℕ} (c : List (CGate n)) (g : CGate n) :
    wireSpace (c ++ [g]) = wireSpace c ⊔
      Submodule.span ℚ {normalize ((arithGate g).eval MvPolynomial.X (rawWires c))} := by
  simp only [wireSpace, normalizedWires, rawWires_append_gate, List.map_append,
    List.map_cons, List.map_nil, spanWires_append_singleton]

/-- Reuse and rereading cannot force more than one new span direction in a
single gate. This is derived from the operational list update. -/
theorem wireRank_append_gate_le {n : ℕ} (c : List (CGate n)) (g : CGate n) :
    wireRank (c ++ [g]) ≤ wireRank c + 1 := by
  unfold wireRank
  rw [wireSpace_append_gate]
  exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans
    (Nat.add_le_add_left (by simpa using
      (finrank_span_le_card (R := ℚ)
        ({normalize ((arithGate g).eval MvPolynomial.X (rawWires c))} : Set (Poly n)))) _)

theorem normalized_getD_mem_span {n : ℕ} (xs : List (Poly n)) (i : ℕ) :
    normalize (xs.getD i 0) ∈ spanWires (xs.map GodMoveCircuitNormalization.normalize) := by
  classical
  by_cases hi : i < xs.length
  · rw [List.getD_eq_getElem _ _ hi]
    apply Submodule.subset_span
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
    exact ⟨xs[i], List.getElem_mem hi, rfl⟩
  · rw [List.getD_eq_default _ _ (by omega)]
    have hz : normalize (0 : Poly n) = 0 := (normalizeLinearMap n).map_zero
    rw [hz]
    exact Submodule.zero_mem _

/-- Exact output capture, without a derivative-span containment assumption. -/
theorem circuitTarget_mem_wireSpace {n : ℕ} (c : List (CGate n)) :
    circuitTarget c ∈ wireSpace c :=
  normalized_getD_mem_span (rawWires c) (c.length - 1)

theorem verifierCharacteristic_mem_machine_wireSpace {n : ℕ}
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SeparationTarget.SATLang T)
    (φ : Formula) (hvars : GodMovePinnedSATQueries.VariablesBelow n φ) :
    GodMoveFaithfulHandshake.verifierCharacteristic n φ ∈
      wireSpace (compactCircuit M T φ n) := by
  rw [← compactTarget_eq_verifierCharacteristic M T hD φ hvars]
  exact circuitTarget_mem_wireSpace _

/-- The computed rank is bounded by a polynomial in encoded query length and
the supplied machine clock, without any assumed locality of derivative rows. -/
theorem machine_wireRank_le_clock (M : Machine) (T : ℕ → ℕ) (φ : Formula) (n : ℕ) :
    wireRank (compactCircuit M T φ n) ≤ circuitConstant M *
      ((GodMoveSymbolicPinnedInput.inputTemplate φ n).length +
        T (GodMoveSymbolicPinnedInput.inputTemplate φ n).length + 1) ^ 4 :=
  (wireRank_le_length _).trans (compactCircuit_length_le M T φ n)

theorem machine_wireRank_polynomial (M : Machine) {T : ℕ → ℕ} (hT : PolyBounded T) :
    ∃ C d : ℕ, ∀ (φ : Formula) (n : ℕ), wireRank (compactCircuit M T φ n) ≤
      C * ((encodeFormula' φ).length + n + 1) ^ d := by
  obtain ⟨C, d, h⟩ := compactCircuit_polynomial_size M hT
  exact ⟨C, d, fun φ n => (wireRank_le_length _).trans (h φ n)⟩

/-- This target is the SAT decision predicate over encoded input bits. It is
different from the assignment-verification predicate of a fixed formula. -/
noncomputable def satDecisionTarget (L : ℕ) : Poly L :=
  interpolate (SATCircuitSeparationBridge.SATFamily L)

theorem unrolled_wireRank_le_clock (M : Machine) (L t : ℕ) :
    wireRank (ComposablePpolyDischarge.circuitFor M L t) ≤
      circuitConstant M * (L + t + 1) ^ 4 :=
  (wireRank_le_length _).trans (circuitFor_length_le_quartic M L t)

/-- The same computed-wire rank has a polynomial upper bound on the original
machine input slices, independently of the pinned-query construction. -/
theorem unrolled_wireRank_polynomial (M : Machine) {T : ℕ → ℕ} (hT : PolyBounded T) :
    PolyBounded (fun L => wireRank (ComposablePpolyDischarge.circuitFor M L (T L))) :=
  CookLevinEmitClockBounds3.PB_le (fun _ => wireRank_le_length _)
    (ComposablePpolyDischarge.circuitFor_length_polyBounded M T hT)

theorem actualSATCircuit_target (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SeparationTarget.SATLang T) (L : ℕ) :
    circuitTarget (ComposablePpolyDischarge.circuitFor M L (T L)) = satDecisionTarget L := by
  rw [circuitTarget_eq_interpolate]
  exact interpolate_congr
    (ComposablePpolyDischarge.circuitFor_computes M SeparationTarget.SATLang T hD L)

/-- The real SAT decision characteristic belongs to the computed wire space.
This does not assert that its derivative space belongs to it. -/
theorem satDecisionTarget_mem_actualWireSpace (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SeparationTarget.SATLang T) (L : ℕ) :
    satDecisionTarget L ∈ wireSpace (ComposablePpolyDischarge.circuitFor M L (T L)) := by
  rw [← actualSATCircuit_target M T hD L]
  exact circuitTarget_mem_wireSpace _

/-- Merely capturing one output polynomial cannot provide a large dimension
lower bound: every polynomial lies in a space of dimension at most one. -/
theorem output_capture_alone {n : ℕ} (p : Poly n) :
    p ∈ spanWires [p] ∧ Module.finrank ℚ (spanWires [p]) ≤ 1 := by
  constructor
  · apply Submodule.subset_span
    simp
  · exact spanWires_finrank_le_length [p]

/-- The target itself lies in the bounded wire span, but its entire derivative
space cannot be recovered inside that span for every circuit. -/
theorem not_all_derivatives_captured :
    ¬ ∀ n (c : List (CGate n)),
      mlBlockedSpdpSubspace (GodMoveMonomialMinor.discreteBlocks n) (Nat.log 2 n) 0
        (circuitTarget c) ≤ wireSpace c := by
  intro h
  apply no_polynomial_circuitTarget_strict_bound
  refine ⟨1, 1, ?_⟩
  intro n c
  have hdim : mlBlockedSpdpRank (GodMoveMonomialMinor.discreteBlocks n) (Nat.log 2 n) 0
      (circuitTarget c) ≤ wireRank c := Submodule.finrank_mono (h n c)
  have hlength := hdim.trans (wireRank_le_length c)
  simpa using hlength.trans (show c.length ≤ n + c.length + 1 by omega)

/-- Repairing the derivative algebra does not put its entire row family in
the bounded computed-wire space. This states the failed combination directly. -/
theorem not_all_repaired_rows_captured :
    ¬ ∀ n (c : List (CGate n)) (S : List (Fin n)) (shift : Poly n),
      S.length = Nat.log 2 n → shift.totalDegree ≤ 0 → shift.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible (GodMoveMonomialMinor.discreteBlocks n) S →
      mlProj (shift * normalize (GodMoveBooleanDifferentiation.iterFiniteDifference S
        (GodMoveCircuitArithmetization.rawPoly c))) ∈ wireSpace c := by
  intro h
  apply not_all_derivatives_captured
  intro n c
  apply Submodule.span_le.mpr
  rintro q ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
  have hrow := h n c S m hlen hdeg hvars hadm
  rw [GodMoveBooleanDifferentiation.finiteDifference_row_eq] at hrow
  exact hrow

end GodMoveComputedWireRank

#print axioms GodMoveComputedWireRank.wireRank_le_length
#print axioms GodMoveComputedWireRank.wireSpace_eq_image
#print axioms GodMoveComputedWireRank.normalization_does_not_increase_wire_rank
#print axioms GodMoveComputedWireRank.wireSpace_append_gate
#print axioms GodMoveComputedWireRank.wireRank_append_gate_le
#print axioms GodMoveComputedWireRank.circuitTarget_mem_wireSpace
#print axioms GodMoveComputedWireRank.verifierCharacteristic_mem_machine_wireSpace
#print axioms GodMoveComputedWireRank.machine_wireRank_le_clock
#print axioms GodMoveComputedWireRank.machine_wireRank_polynomial
#print axioms GodMoveComputedWireRank.unrolled_wireRank_le_clock
#print axioms GodMoveComputedWireRank.unrolled_wireRank_polynomial
#print axioms GodMoveComputedWireRank.actualSATCircuit_target
#print axioms GodMoveComputedWireRank.satDecisionTarget_mem_actualWireSpace
#print axioms GodMoveComputedWireRank.output_capture_alone
#print axioms GodMoveComputedWireRank.not_all_derivatives_captured
#print axioms GodMoveComputedWireRank.not_all_repaired_rows_captured
