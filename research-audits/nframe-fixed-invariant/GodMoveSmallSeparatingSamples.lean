import GodMoveSamplingBarrier
import GodMoveSampledWireGauge
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Small separating sample lists exist

Restrict Boolean evaluation to the finite-dimensional computed-wire space.
Choose a basis from the span of those evaluation functionals and one Boolean
assignment representing each chosen functional. At most `wireRank c` samples
are needed. Vanishing there forces every Boolean evaluation to vanish; because
all polynomials in the wire space are multilinear, the polynomial is zero.

Thus the required sample-list length is polynomial in circuit gate count.
This is an existence result using finite-dimensional basis selection and
classical choice, not an efficient sample-discovery algorithm. It supplies
no bound on the time needed to find the list, an inverse matrix, or basis
coordinates. The sampling-to-SAT correctness reduction remains relevant.
-/

namespace GodMoveSmallSeparatingSamples

open MvPolynomial MultilinearSPDP
open GodMoveBooleanInterpolation GodMoveCircuitNormalization
open GodMoveBooleanDifferentiation GodMoveComputedWireRank GodMoveSamplingBarrier
open GodMoveSampledWireGauge (sampleEval)
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer (CGate)

/-- Normalization fixes the entire span of normalized circuit wires. -/
theorem normalize_eq_self_of_mem_wireSpace {n : ℕ} (c : List (CGate n))
    (p : Poly n) (hp : p ∈ wireSpace c) : normalize p = p := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      have hp' : p ∈ normalizedWires c := by simpa using hp
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp'
      exact normalize_idempotent q
  | zero => exact (normalizeLinearMap n).map_zero
  | add p q _ _ hp hq => simp [normalize_add, hp, hq]
  | smul a p _ hp =>
      change normalizeLinearMap n (a • p) = a • p
      rw [map_smul]
      exact congrArg (fun q : Poly n => a • q) hp

theorem isMultilinear_of_mem_wireSpace {n : ℕ} (c : List (CGate n))
    (p : Poly n) (hp : p ∈ wireSpace c) : IsMultilinear p := by
  rw [← normalize_eq_self_of_mem_wireSpace c p hp]
  exact normalize_isMultilinear p

/-- A Boolean evaluation functional restricted to the actual computed-wire space. -/
noncomputable def restrictedEval {n : ℕ} (c : List (CGate n)) (a : Assignment n) :
    Module.Dual ℚ (wireSpace c) :=
  (sampleEval a).comp (wireSpace c).subtype

@[simp] theorem restrictedEval_apply {n : ℕ} (c : List (CGate n))
    (a : Assignment n) (p : wireSpace c) :
    restrictedEval c a p = MvPolynomial.eval (booleanPoint a) p.val := rfl

/-- A basis of the evaluation span provides a separating list of at most the
actual wire-space dimension. This asserts existence, not an efficient selector. -/
theorem exists_separating_samples_le_wireRank {n : ℕ} (c : List (CGate n)) :
    ∃ samples : List (Assignment n), samples.length ≤ wireRank c ∧
      SeparatesWires c samples := by
  classical
  letI : Module.Finite ℚ (wireSpace c) := wireSpace_finite c
  letI : Module.Finite ℚ (Module.Dual ℚ (wireSpace c)) :=
    Module.Finite.of_basis (Module.Free.chooseBasis ℚ (wireSpace c)).dualBasis
  let E := Set.range (restrictedEval c)
  letI : Module.Finite ℚ (Submodule.span ℚ E) :=
    Module.Finite.span_of_finite ℚ (Set.finite_range (restrictedEval c))
  let d := Module.finrank ℚ (Submodule.span ℚ E)
  have hd : d ≤ wireRank c := by
    have hdim := Submodule.finrank_le (Submodule.span ℚ E)
    simpa only [Subspace.dual_finrank_eq, wireRank] using hdim
  obtain ⟨f, hf, hspan, _⟩ := Submodule.exists_fun_fin_finrank_span_eq ℚ E
  have hpre : ∀ i : Fin d, ∃ a : Assignment n, restrictedEval c a = f i := hf
  choose sample hsample using hpre
  let samples := (List.finRange d).map sample
  refine ⟨samples, ?_, ?_⟩
  · simpa [samples] using hd
  · intro p hp hzero
    have hvanish : ∀ l ∈ Submodule.span ℚ (Set.range f), l (⟨p, hp⟩ : wireSpace c) = 0 := by
      intro l hl
      induction hl using Submodule.span_induction with
      | mem l hl =>
          obtain ⟨i, rfl⟩ := hl
          rw [← hsample i]
          exact hzero (sample i) (by simp [samples])
      | zero => rfl
      | add l m _ _ hl hm => simp [hl, hm]
      | smul a l _ hl => simp [hl]
    apply multilinear_eq_of_boolean_eval p 0 (isMultilinear_of_mem_wireSpace c p hp)
      (by simp [IsMultilinear])
    intro a
    have ha : restrictedEval c a ∈ Submodule.span ℚ (Set.range f) := by
      rw [hspan]
      exact Submodule.subset_span ⟨a, rfl⟩
    simpa using hvanish (restrictedEval c a) ha

/-- Consequently a separating list exists with at most one sample per circuit gate. -/
theorem exists_separating_samples_le_length {n : ℕ} (c : List (CGate n)) :
    ∃ samples : List (Assignment n), samples.length ≤ c.length ∧
      SeparatesWires c samples := by
  obtain ⟨samples, hlen, hsep⟩ := exists_separating_samples_le_wireRank c
  exact ⟨samples, hlen.trans (wireRank_le_length c), hsep⟩

end GodMoveSmallSeparatingSamples

#print axioms GodMoveSmallSeparatingSamples.isMultilinear_of_mem_wireSpace
#print axioms GodMoveSmallSeparatingSamples.exists_separating_samples_le_wireRank
#print axioms GodMoveSmallSeparatingSamples.exists_separating_samples_le_length
