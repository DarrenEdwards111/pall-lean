import GodMoveProjectionSamples
import GodMoveTrackedOrthogonalizationCost
import GodMoveProjectionWeightPrecision

/-!
# Constructing the discovered wire projection's numeric certificate

The descriptor stores its samples, original basis-wire references, and
computed rational inverse weights. The duality equations follow from the
proved cached matrix algorithm. Combining this with actual SAT-machine
discovery supplies the complete existing WireCertificate without asking
the caller for weights, matrix identities, or a spanning certificate.

The supplied machine's SAT correctness is still required by discovery.
No total bit-runtime bound for that discovery program, efficient expanded
polynomial evaluation, derivative containment, or separation is asserted.
The range here is exactly the computed-wire space, not the snapshot space.
-/

namespace GodMoveConstructedProjection

open GodMoveBooleanInterpolation GodMoveProjectionSamples
open GodMoveSampledWireGauge GodMoveWireSampleCertificate
open GodMoveSampledWireBasis GodMoveMachineDiscovery GodMoveComputedWireRank
open GodMoveExhaustiveWireBasis GodMoveTrackedOrthogonalization
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer (CGate)
open ComposableMachine SeparationTarget
open scoped BigOperators

/-- Finite stored data; no polynomial expansion or semantic proof fields. -/
structure Descriptor {n : ℕ} (c : List (CGate n)) (r : ℕ) where
  data : SampleData c r
  weights : Vector (Vector ℚ r) r

def buildDescriptorWithCost {n r : ℕ} {c : List (CGate n)} (d : SampleData c r) :
    GodMoveTrackedOrthogonalizationCost.Counted (Descriptor c r) :=
  let A := sampleMatrix d
  let W := GodMoveTrackedOrthogonalizationCost.inverseWeights A
  ⟨⟨d, Vector.ofFn (fun i => Vector.ofFn (W.value i))⟩, W.operations⟩

def buildDescriptor {n r : ℕ} {c : List (CGate n)} (d : SampleData c r) : Descriptor c r :=
  (buildDescriptorWithCost d).value

/-- Arithmetic count of the executed weight-building loops; sample acquisition,
memory traffic and rational bit complexity are not counted as arithmetic ops. -/
theorem buildDescriptor_operations_le_cubic {n r : ℕ} {c : List (CGate n)}
    (d : SampleData c r) : (buildDescriptorWithCost d).operations ≤ 8 * r ^ 3 :=
  GodMoveTrackedOrthogonalizationCost.inverseWeights_operations_le_cubic _

theorem buildDescriptor_weights_eq_inverse {n r : ℕ} {c : List (CGate n)}
    (d : SampleData c r) (i j : Fin r) :
    ((buildDescriptor d).weights.get i).get j = inverseWeights (sampleMatrix d) i j := by
  simp [buildDescriptor, buildDescriptorWithCost, Vector.get]

theorem sampleMatrix_boolean {n r : ℕ} {c : List (CGate n)} (d : SampleData c r) :
    ∀ i j, sampleMatrix d i j = 0 ∨ sampleMatrix d i j = 1 := by
  intro i j
  rw [sampleMatrix_apply]
  simp only [GodMoveBooleanWireTable.wireRow, bit]
  split <;> simp

/-- Final canonical inverse weights have polynomial bit length. This does
not bound all intermediate rational values in the weight-building loops. -/
theorem buildDescriptor_weight_precision {n r : ℕ} {c : List (CGate n)}
    (d : SampleData c r) (hLI : LinearIndependent ℚ (sampleMatrix d)) (i j : Fin r) :
    (((buildDescriptor d).weights.get i).get j).num.natAbs.size ≤ (r + 1) ^ 2 + 1 ∧
      (((buildDescriptor d).weights.get i).get j).den.size ≤ (r + 1) ^ 2 + 1 := by
  simp only [buildDescriptor_weights_eq_inverse]
  exact GodMoveProjectionWeightPrecision.rational_leftInverse_entry_precision
    (sampleMatrix d) (inverseWeights (sampleMatrix d)) (sampleMatrix_boolean d)
    (inverseWeights_mul _ hLI) i j

theorem buildDescriptor_duality {n r : ℕ} {c : List (CGate n)} (d : SampleData c r)
    (hLI : LinearIndependent ℚ (sampleMatrix d)) (i k : Fin r) :
    (∑ j : Fin r, ((buildDescriptor d).weights.get i).get j *
      MvPolynomial.eval (booleanPoint (d.points.get j))
        (GodMoveRowSpanSeparation.wirePolynomial c (d.indices.get k))) =
      if i = k then 1 else 0 := by
  have h := congrFun (congrFun (inverseWeights_mul (sampleMatrix d) hLI) i) k
  simpa only [buildDescriptor_weights_eq_inverse, Matrix.mul_apply, Matrix.one_apply,
    sampleMatrix_eq_polynomial_eval] using h

/-- The finite duality proof is obtained from the computed weights. -/
noncomputable def certificate {n r : ℕ} {c : List (CGate n)} (d : SampleData c r)
    (hLI : LinearIndependent ℚ (sampleMatrix d)) : SampleCertificate n r where
  basis := fun i => GodMoveRowSpanSeparation.wirePolynomial c (d.indices.get i)
  samples := d.points.get
  weights := fun i j => ((buildDescriptor d).weights.get i).get j
  duality := buildDescriptor_duality d hLI

/-- The numeric entry point reads the already built descriptor. It does
not rerun discovery or rebuild the inverse for each weight lookup. -/
def evaluateDescriptor {n r : ℕ} {c : List (CGate n)} (D : Descriptor c r)
    (sampleValues : Vector ℚ r) (a : Assignment n) : ℚ :=
  reconstructFromCircuit c D.data.indices.get
    (fun i j => (D.weights.get i).get j) sampleValues.get a

theorem eval_projection_eq_descriptor {n r : ℕ} {c : List (CGate n)}
    (d : SampleData c r) (hLI : LinearIndependent ℚ (sampleMatrix d))
    (p : Poly n) (a : Assignment n) :
    MvPolynomial.eval (booleanPoint a) ((sampledGauge (certificate d hLI)).projection p) =
      evaluateDescriptor (buildDescriptor d)
        (Vector.ofFn (fun j => MvPolynomial.eval (booleanPoint (d.points.get j)) p)) a := by
  rw [show (sampledGauge (certificate d hLI)).projection = projection (certificate d hLI)
    from rfl, eval_projection_eq_reconstructValue]
  unfold evaluateDescriptor reconstructFromCircuit
  congr 1
  · funext j
    simp [certificate, Vector.get]
  · funext i
    exact eval_normalizedWire c a (d.indices.get i).val

theorem ofLists_certificate_span {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (indices : List (Fin c.length))
    (hlen : indices.length = samples.length)
    (hLI : LinearIndependent ℚ (sampleMatrix (ofLists c samples indices hlen))) :
    basisSpace (certificate (ofLists c samples indices hlen) hLI) =
      chosenWireSpace c indices := by
  unfold basisSpace chosenWireSpace
  congr 1
  exact ofLists_basis_range c samples indices hlen

def machineDescriptor (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    {n : ℕ} (c : List (CGate n)) : Descriptor c (machineSamples M T c).length :=
  buildDescriptor (machineSampleData M T hD c)

/-- Fully constructed from the supplied SAT machine and original circuit.
Only SAT correctness is assumed; numeric duality and global wire spanning
are consequences of the executable construction. -/
noncomputable def machineCertificate (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) :
    WireCertificate c (machineSamples M T c).length where
  data := certificate (machineSampleData M T hD c)
    (machineSampleData_rows_linearIndependent M T hD c)
  wireIndex := (machineSampleData M T hD c).indices.get
  basis_eq_wire := fun _ => rfl
  span_eq := by
    dsimp only [machineSampleData]
    rw [ofLists_certificate_span]
    exact machineBasis_spans M T hD c

theorem machineCertificate_weights_eq_descriptor (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n))
    (i j : Fin (machineSamples M T c).length) :
    (machineCertificate M T hD c).data.weights i j =
      ((machineDescriptor M T hD c).weights.get i).get j := rfl

/-- Use the constructed descriptor's stored data for projection evaluation.
The certificate remains a semantic specification, not the evaluator. -/
theorem machineDescriptor_evaluation (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n))
    (p : Poly n) (a : Assignment n) :
    MvPolynomial.eval (booleanPoint a)
      ((sampledGauge (machineCertificate M T hD c).data).projection p) =
      evaluateDescriptor (machineDescriptor M T hD c)
        (Vector.ofFn (fun j => MvPolynomial.eval
          (booleanPoint ((machineSampleData M T hD c).points.get j)) p)) a :=
  eval_projection_eq_descriptor _ (machineSampleData_rows_linearIndependent M T hD c) p a

theorem machineCertificate_range (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) :
    LinearMap.range (sampledGauge (machineCertificate M T hD c).data).projection =
      wireSpace c :=
  sampledGauge_wire_range _ c (machineCertificate M T hD c).span_eq

theorem machineCertificate_rank (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) :
    Module.finrank ℚ
      (LinearMap.range (sampledGauge (machineCertificate M T hD c).data).projection) =
      wireRank c :=
  sampledGauge_wire_rank _ c (machineCertificate M T hD c).span_eq

/-- Numeric evaluation of the constructed production projection at Boolean
points uses the original shared circuit and supplied sample values of p. -/
theorem machineCertificate_evaluation (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) (p : Poly n)
    (a : Assignment n) :
    MvPolynomial.eval (booleanPoint a)
      ((sampledGauge (machineCertificate M T hD c).data).projection p) =
      reconstructFromCircuit c (machineCertificate M T hD c).wireIndex
        (machineCertificate M T hD c).data.weights
        (fun j => MvPolynomial.eval
          (booleanPoint ((machineCertificate M T hD c).data.samples j)) p) a :=
  eval_projection_from_circuit c (machineCertificate M T hD c) p a

theorem actualSAT_constructed_projection_fixes_decision (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) (L : ℕ) :
    let c := ComposablePpolyDischarge.circuitFor M L (T L)
    (sampledGauge (machineCertificate M T hD c).data).projection (satDecisionTarget L) =
      satDecisionTarget L := by
  dsimp only
  rw [← actualSATCircuit_target M T hD L]
  exact sampledGauge_fixes_target _ _ (machineCertificate M T hD _).span_eq

theorem actualSAT_constructed_projection_rank_le_clock (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) (L : ℕ) :
    let c := ComposablePpolyDischarge.circuitFor M L (T L)
    Module.finrank ℚ
      (LinearMap.range (sampledGauge (machineCertificate M T hD c).data).projection) ≤
      GodMoveCircuitRuntimeCost.circuitConstant M * (L + T L + 1) ^ 4 := by
  dsimp only
  rw [machineCertificate_rank]
  exact unrolled_wireRank_le_clock M L (T L)

end GodMoveConstructedProjection

#print axioms GodMoveConstructedProjection.buildDescriptor_duality
#print axioms GodMoveConstructedProjection.buildDescriptor_operations_le_cubic
#print axioms GodMoveConstructedProjection.buildDescriptor_weight_precision
#print axioms GodMoveConstructedProjection.ofLists_certificate_span
#print axioms GodMoveConstructedProjection.eval_projection_eq_descriptor
#print axioms GodMoveConstructedProjection.machineCertificate_weights_eq_descriptor
#print axioms GodMoveConstructedProjection.machineDescriptor_evaluation
#print axioms GodMoveConstructedProjection.machineCertificate_range
#print axioms GodMoveConstructedProjection.machineCertificate_rank
#print axioms GodMoveConstructedProjection.machineCertificate_evaluation
#print axioms GodMoveConstructedProjection.actualSAT_constructed_projection_fixes_decision
#print axioms GodMoveConstructedProjection.actualSAT_constructed_projection_rank_le_clock
