import GodMoveSampledWireGauge
import GodMoveSamplingBarrier
import GodMoveRankIncrementSAT

/-!
# Sampled gauges whose basis is retained by circuit-wire references

The numeric evaluator below runs the original Boolean circuit once at the
requested Boolean point and reads its selected basis wires. It then applies
the supplied finite rational reconstruction kernel. Its correctness is proved
against the exact production projection, without expanding output polynomials.

The certificate explicitly records both finite matrix duality and the global
semantic assertion that the selected basis spans all computed wires. No
efficient procedure for finding or checking that global assertion is supplied.
Its samples necessarily hit every nonzero target in that space, hence solve
the associated fixed-CNF satisfiability question by ordinary verification.
-/

namespace GodMoveWireSampleCertificate

open GodMoveBooleanInterpolation GodMoveCircuitNormalization
open GodMoveComputedWireRank GodMoveSampledWireGauge GodMoveSamplingBarrier
open GodMoveDirectVerifierCircuit GodMovePinnedSATQueries
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer (CGate runFrom output)
open CookLevinReduction

def sampleList {n r : ℕ} (s : SampleCertificate n r) : List (Assignment n) :=
  List.ofFn s.samples

theorem sampleList_length {n r : ℕ} (s : SampleCertificate n r) :
    (sampleList s).length = r := by simp [sampleList]

/-- The supplied certificate implies the semantic sample-separation property. -/
theorem certificate_separates_wires {n r : ℕ} (s : SampleCertificate n r)
    (c : List (CGate n)) (hspan : basisSpace s = wireSpace c) :
    SeparatesWires c (sampleList s) := by
  intro p hp hzero
  apply samples_determine_on_span s p 0
  · rwa [hspan]
  · exact (basisSpace s).zero_mem
  · intro j
    rw [map_zero]
    exact hzero (s.samples j) (by simp [sampleList])

theorem certificate_size_eq_wireRank {n r : ℕ} (s : SampleCertificate n r)
    (c : List (CGate n)) (hspan : basisSpace s = wireSpace c) : r = wireRank c := by
  rw [← basisSpace_finrank s, hspan]
  rfl

theorem certificate_sample_count_le_length {n r : ℕ} (s : SampleCertificate n r)
    (c : List (CGate n)) (hspan : basisSpace s = wireSpace c) :
    (sampleList s).length ≤ c.length := by
  rw [sampleList_length, certificate_size_eq_wireRank s c hspan]
  exact wireRank_le_length c

/-- Basis polynomials are named by actual emitted wire indices. The polynomial
fields provide semantics; the executable evaluator uses only these references
and the finite numeric weights. Spanning is an explicit unproved-by-the-builder
certificate field, not a polynomial-time validation claim. -/
structure WireCertificate {n : ℕ} (c : List (CGate n)) (r : ℕ) where
  data : SampleCertificate n r
  wireIndex : Fin r → Fin c.length
  basis_eq_wire : ∀ i, data.basis i = (normalizedWires c).getD (wireIndex i).val 0
  span_eq : basisSpace data = wireSpace c

theorem eval_normalizedWires {n : ℕ} (c : List (CGate n)) (a : Assignment n) :
    (normalizedWires c).map (MvPolynomial.eval (booleanPoint a)) =
      (runFrom a [] c).map bit := by
  simp only [normalizedWires, List.map_map, Function.comp_def]
  simp_rw [eval_normalize]
  unfold rawWires
  rw [GodMoveCircuitArithmetization.eval_runArithmetic_poly]
  simp only [List.map_nil]
  exact GodMoveCircuitArithmetization.runArithmetic_compile a [] c

theorem eval_normalizedWire {n : ℕ} (c : List (CGate n)) (a : Assignment n) (j : ℕ) :
    MvPolynomial.eval (booleanPoint a) ((normalizedWires c).getD j 0) =
      bit ((runFrom a [] c).getD j false) := by
  have hp := List.getD_map (l := normalizedWires c) (d := (0 : Poly n)) (n := j)
    (MvPolynomial.eval (booleanPoint a))
  have hb := List.getD_map (l := runFrom a [] c) (d := false) (n := j) bit
  rw [eval_normalizedWires] at hp
  simpa only [map_zero, bit, Bool.false_eq_true, if_false] using hp.symm.trans hb

/-- Numeric evaluation retains the original shared circuit; basis polynomials
are evaluated by reading their Boolean wires. Input polynomial values at the
certificate's samples must be provided by the caller. -/
def reconstructFromCircuit {n r : ℕ} (c : List (CGate n))
    (indices : Fin r → Fin c.length) (weights : Fin r → Fin r → ℚ)
    (sampleValues : Fin r → ℚ) (a : Assignment n) : ℚ :=
  let wires := runFrom a [] c
  reconstructValue weights sampleValues (fun i => bit (wires.getD (indices i).val false))

theorem eval_projection_from_circuit {n r : ℕ} (c : List (CGate n))
    (s : WireCertificate c r) (p : Poly n) (a : Assignment n) :
    MvPolynomial.eval (booleanPoint a) ((sampledGauge s.data).projection p) =
      reconstructFromCircuit c s.wireIndex s.data.weights
        (fun j => MvPolynomial.eval (booleanPoint (s.data.samples j)) p) a := by
  rw [show (sampledGauge s.data).projection = projection s.data from rfl,
    eval_projection_eq_reconstructValue]
  unfold reconstructFromCircuit
  congr 1
  funext i
  rw [s.basis_eq_wire, eval_normalizedWire]

/-- Constructing such a certificate for a direct verifier supplies a list
of candidate assignments to test, with no exponential output expansion. -/
theorem certificate_decides_SAT {n r : ℕ} (φ : Formula) (hvars : VariablesBelow n φ)
    (s : SampleCertificate n r) (hspan : basisSpace s = wireSpace (verifierCircuit n φ)) :
    Satisfiable φ ↔ (sampleList s).any (output (verifierCircuit n φ)) = true :=
  satisfiable_iff_sample_accepts φ hvars (sampleList s)
    (certificate_separates_wires s _ hspan)

/-- Even just the exact dimensions returned by full wire-space certificates
for the two rank-test circuits suffice to decide the original CNF's SAT.
This does not apply to a gauge that merely contains a larger wire-preserving
range and reports its larger dimension. -/
theorem certificate_dimensions_decide_SAT {n r t : ℕ} (φ : Formula)
    (hvars : VariablesBelow n φ) (s : SampleCertificate (n + 2) r)
    (u : SampleCertificate (n + 2) t)
    (hs : basisSpace s = wireSpace (GodMoveRankIncrementSAT.rankPrefix (verifierCircuit n φ)))
    (hu : basisSpace u = wireSpace (GodMoveRankIncrementSAT.rankExtension (verifierCircuit n φ))) :
    Satisfiable φ ↔ r < t := by
  rw [certificate_size_eq_wireRank s _ hs, certificate_size_eq_wireRank u _ hu]
  exact (GodMoveRankIncrementSAT.verifier_rank_increases_iff_satisfiable n φ hvars).symm

end GodMoveWireSampleCertificate

#print axioms GodMoveWireSampleCertificate.certificate_separates_wires
#print axioms GodMoveWireSampleCertificate.certificate_size_eq_wireRank
#print axioms GodMoveWireSampleCertificate.certificate_sample_count_le_length
#print axioms GodMoveWireSampleCertificate.eval_normalizedWires
#print axioms GodMoveWireSampleCertificate.eval_normalizedWire
#print axioms GodMoveWireSampleCertificate.eval_projection_from_circuit
#print axioms GodMoveWireSampleCertificate.certificate_decides_SAT
#print axioms GodMoveWireSampleCertificate.certificate_dimensions_decide_SAT
