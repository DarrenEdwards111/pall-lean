import GodMoveComputedWireRank
import PallLean.Paper93.NFrame.LagrangianFunctional

/-!
# An explicit sampled projection in the production gauge type

A supplied finite list of basis polynomials, Boolean sample assignments and
rational inverse weights defines a gauge directly by weighted evaluations.
The finite matrix identity is a certificate checked independently of any
rank bound: its weighted sample evaluations are the coordinate duals of the
supplied basis. No complementary subspace is chosen in this construction.

The projection has exactly the span of that basis as its range, is idempotent,
and has rank exactly the number of basis vectors. If the supplied span equals
the computed-wire space, the gauge fixes every computed normalized wire and
the characteristic target, with rank exactly the operational wire rank.

This constructs the projection from certificate data; it does not efficiently
find that data. Arbitrary rational weights and polynomial basis entries carry
no coefficient-bit or representation-size bound here. The statements do not
claim efficient normal-form expansion, a SAT rank lower bound, or variational
minimality.
-/

namespace GodMoveSampledWireGauge

open MvPolynomial
open GodMoveBooleanInterpolation GodMoveCircuitNormalization
open GodMoveComputedWireRank GodMoveCircuitConnection
open PallLean.Paper93.NFrame
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer (CGate)
open scoped BigOperators

/-- With `A[j,k] = basis[k](samples[j])`, the equation is `weights * A = I`.
The basis, samples and numeric matrix are explicit supplied data. -/
structure SampleCertificate (n r : ℕ) where
  basis : Fin r → Poly n
  samples : Fin r → Assignment n
  weights : Fin r → Fin r → ℚ
  duality : ∀ i k : Fin r,
    (∑ j : Fin r, weights i j *
      MvPolynomial.eval (booleanPoint (samples j)) (basis k)) =
      if i = k then 1 else 0

noncomputable def sampleEval {n : ℕ} (a : Assignment n) : Poly n →ₗ[ℚ] ℚ :=
  (MvPolynomial.aeval (booleanPoint a)).toLinearMap

@[simp] theorem sampleEval_apply {n : ℕ} (a : Assignment n) (p : Poly n) :
    sampleEval a p = MvPolynomial.eval (booleanPoint a) p := rfl

/-- The `i`th coordinate functional is an explicit weighted sum of evaluations. -/
noncomputable def basisDual {n r : ℕ} (s : SampleCertificate n r) (i : Fin r) :
    Poly n →ₗ[ℚ] ℚ :=
  ∑ j : Fin r, s.weights i j • sampleEval (s.samples j)

theorem basisDual_apply {n r : ℕ} (s : SampleCertificate n r) (i : Fin r) (p : Poly n) :
    basisDual s i p = ∑ j : Fin r,
      s.weights i j * MvPolynomial.eval (booleanPoint (s.samples j)) p := by
  simp [basisDual]

@[simp] theorem basisDual_basis {n r : ℕ} (s : SampleCertificate n r) (i k : Fin r) :
    basisDual s i (s.basis k) = if i = k then 1 else 0 := by
  rw [basisDual_apply]
  exact s.duality i k

/-- The source-to-basis projection, constructed directly from the supplied matrix. -/
noncomputable def projection {n r : ℕ} (s : SampleCertificate n r) :
    Poly n →ₗ[ℚ] Poly n :=
  ∑ i : Fin r, (basisDual s i).smulRight (s.basis i)

theorem projection_apply {n r : ℕ} (s : SampleCertificate n r) (p : Poly n) :
    projection s p = ∑ i : Fin r, (basisDual s i p) • s.basis i := by
  simp [projection]

theorem projection_weighted_evaluations {n r : ℕ} (s : SampleCertificate n r)
    (p : Poly n) :
    projection s p = ∑ i : Fin r,
      (∑ j : Fin r, s.weights i j *
        MvPolynomial.eval (booleanPoint (s.samples j)) p) • s.basis i := by
  simp only [projection_apply, basisDual_apply]

/-- Executable rational matrix-vector arithmetic on the supplied sample values. -/
def sampleCoefficients {r : ℕ} (weights : Fin r → Fin r → ℚ)
    (values : Fin r → ℚ) (i : Fin r) : ℚ :=
  ∑ j : Fin r, weights i j * values j

/-- Executable reconstruction from the sample values and basis values at a
requested point. The displayed formula uses `r²+r` rational multiplications
and finite sums; no bound on the bit sizes of those rationals is assumed. -/
def reconstructValue {r : ℕ} (weights : Fin r → Fin r → ℚ)
    (values basisValues : Fin r → ℚ) : ℚ :=
  ∑ i : Fin r, sampleCoefficients weights values i * basisValues i

/-- Projection evaluation is the finite numeric kernel, requiring only the
sample evaluations of the input and the basis evaluations at the requested point.
Neither expanded output coefficients nor a complementary subspace appear. -/
theorem eval_projection_eq_reconstructValue {n r : ℕ} (s : SampleCertificate n r)
    (p : Poly n) (x : Fin n → ℚ) :
    MvPolynomial.eval x (projection s p) =
      reconstructValue s.weights
        (fun j => MvPolynomial.eval (booleanPoint (s.samples j)) p)
        (fun i => MvPolynomial.eval x (s.basis i)) := by
  simp [projection_apply, basisDual_apply, reconstructValue, sampleCoefficients]

@[simp] theorem projection_basis {n r : ℕ} (s : SampleCertificate n r) (k : Fin r) :
    projection s (s.basis k) = s.basis k := by
  simp [projection_apply]

noncomputable def basisSpace {n r : ℕ} (s : SampleCertificate n r) :
    Submodule ℚ (Poly n) := Submodule.span ℚ (Set.range s.basis)

instance basisSpace_finite {n r : ℕ} (s : SampleCertificate n r) :
    Module.Finite ℚ (basisSpace s) :=
  Module.Finite.span_of_finite ℚ (Set.finite_range s.basis)

theorem projection_mem_basisSpace {n r : ℕ} (s : SampleCertificate n r) (p : Poly n) :
    projection s p ∈ basisSpace s := by
  rw [projection_apply]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨i, rfl⟩

/-- Every vector in the certified basis span is fixed by the explicit projection. -/
theorem projection_fixes {n r : ℕ} (s : SampleCertificate n r) (p : Poly n)
    (hp : p ∈ basisSpace s) : projection s p = p := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨i, rfl⟩ := hp
      exact projection_basis s i
  | zero => exact (projection s).map_zero
  | add p q _ _ hp hq => simp [map_add, hp, hq]
  | smul a p _ hp => simp [hp]

theorem projection_range {n r : ℕ} (s : SampleCertificate n r) :
    LinearMap.range (projection s) = basisSpace s := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact projection_mem_basisSpace s q
  · intro hp
    exact ⟨p, projection_fixes s p hp⟩

theorem projection_idempotent {n r : ℕ} (s : SampleCertificate n r) :
    (projection s).comp (projection s) = projection s := by
  apply LinearMap.ext
  intro p
  exact projection_fixes s _ (projection_mem_basisSpace s p)

/-- Linear independence follows from the finite numeric duality equations. -/
theorem basis_linearIndependent {n r : ℕ} (s : SampleCertificate n r) :
    LinearIndependent ℚ s.basis := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrArg (basisDual s i) hg
  simpa using h

theorem basisSpace_finrank {n r : ℕ} (s : SampleCertificate n r) :
    Module.finrank ℚ (basisSpace s) = r := by
  simpa [basisSpace] using finrank_span_eq_card (basis_linearIndependent s)

theorem projection_rank {n r : ℕ} (s : SampleCertificate n r) :
    Module.finrank ℚ (LinearMap.range (projection s)) = r := by
  rw [projection_range, basisSpace_finrank]

/-- An actual production gauge with no chosen linear complement. -/
noncomputable def sampledGauge {n r : ℕ} (s : SampleCertificate n r) : CandidateGauge n where
  projection := projection s
  is_idempotent := projection_idempotent s
  rank_finite := by
    rw [projection_range]
    infer_instance

theorem sampledGauge_range {n r : ℕ} (s : SampleCertificate n r) :
    LinearMap.range (sampledGauge s).projection = basisSpace s := projection_range s

theorem sampledGauge_rank {n r : ℕ} (s : SampleCertificate n r) :
    Module.finrank ℚ (LinearMap.range (sampledGauge s).projection) = r := projection_rank s

/-- The projection only uses the finite sample evaluations. -/
theorem projection_eq_of_samples_eq {n r : ℕ} (s : SampleCertificate n r)
    (p q : Poly n) (h : ∀ j,
      MvPolynomial.eval (booleanPoint (s.samples j)) p =
        MvPolynomial.eval (booleanPoint (s.samples j)) q) :
    projection s p = projection s q := by
  simp only [projection_weighted_evaluations, h]

/-- Boolean normalization is invisible to this explicitly sampled projection. -/
theorem projection_normalize {n r : ℕ} (s : SampleCertificate n r) (p : Poly n) :
    projection s (normalize p) = projection s p := by
  apply projection_eq_of_samples_eq
  intro j
  exact eval_normalize p (s.samples j)

/-- The supplied samples determine every vector in the certified span. -/
theorem samples_determine_on_span {n r : ℕ} (s : SampleCertificate n r)
    (p q : Poly n) (hp : p ∈ basisSpace s) (hq : q ∈ basisSpace s)
    (h : ∀ j, MvPolynomial.eval (booleanPoint (s.samples j)) p =
      MvPolynomial.eval (booleanPoint (s.samples j)) q) : p = q := by
  rw [← projection_fixes s p hp, ← projection_fixes s q hq]
  exact projection_eq_of_samples_eq s p q h

/-- Exact wire-space realization when the supplied basis spans that actual space. -/
theorem sampledGauge_wire_range {n r : ℕ} (s : SampleCertificate n r)
    (c : List (CGate n)) (hspan : basisSpace s = wireSpace c) :
    LinearMap.range (sampledGauge s).projection = wireSpace c := by
  rw [sampledGauge_range, hspan]

theorem sampledGauge_wire_rank {n r : ℕ} (s : SampleCertificate n r)
    (c : List (CGate n)) (hspan : basisSpace s = wireSpace c) :
    Module.finrank ℚ (LinearMap.range (sampledGauge s).projection) = wireRank c := by
  rw [sampledGauge_wire_range s c hspan]
  rfl

theorem sampledGauge_fixes_wire {n r : ℕ} (s : SampleCertificate n r)
    (c : List (CGate n)) (hspan : basisSpace s = wireSpace c)
    (p : Poly n) (hp : p ∈ normalizedWires c) : (sampledGauge s).projection p = p := by
  apply projection_fixes
  rw [hspan]
  apply Submodule.subset_span
  simpa using hp

theorem sampledGauge_fixes_target {n r : ℕ} (s : SampleCertificate n r)
    (c : List (CGate n)) (hspan : basisSpace s = wireSpace c) :
    (sampledGauge s).projection (circuitTarget c) = circuitTarget c := by
  apply projection_fixes
  rw [hspan]
  exact circuitTarget_mem_wireSpace c

end GodMoveSampledWireGauge

#print axioms GodMoveSampledWireGauge.projection_weighted_evaluations
#print axioms GodMoveSampledWireGauge.eval_projection_eq_reconstructValue
#print axioms GodMoveSampledWireGauge.projection_range
#print axioms GodMoveSampledWireGauge.projection_idempotent
#print axioms GodMoveSampledWireGauge.basis_linearIndependent
#print axioms GodMoveSampledWireGauge.sampledGauge_rank
#print axioms GodMoveSampledWireGauge.projection_normalize
#print axioms GodMoveSampledWireGauge.samples_determine_on_span
#print axioms GodMoveSampledWireGauge.sampledGauge_wire_rank
#print axioms GodMoveSampledWireGauge.sampledGauge_fixes_wire
#print axioms GodMoveSampledWireGauge.sampledGauge_fixes_target
