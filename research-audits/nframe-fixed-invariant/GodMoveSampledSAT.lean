import GodMoveDirectVerifierCircuit
import GodMoveSamplingBarrier

/-!
# An executable SAT test conditional on a suitable sample selector

Given a selector returning Boolean assignments for a Boolean circuit, the
program below evaluates the direct CNF verifier on those samples and accepts
if any sample satisfies the formula. All program definitions are ordinary
computable Lean definitions; the selector is an explicit argument.

The assignment arity is the existing polynomial witness bound derived from
the faithful formula encoding, so every occurring variable is represented.
Polynomial sample-count bounds transfer to polynomial storage for the actual
sample bit strings. These size results do not prove that the selector can be
computed efficiently, or supply a polynomial-time Turing-machine simulation.
-/

namespace GodMoveSampledSAT

open GodMoveBooleanInterpolation GodMovePinnedSATQueries GodMoveDirectVerifierCircuit
open GodMoveSamplingBarrier
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer CookLevinReduction CookLevinEmitCodec
open SATVerifierSpec SATCircuitSeparationBridge

abbrev SampleSelector := (n : ℕ) → List (CGate n) → List (Assignment n)

/-- The existing unary-coordinate codec's polynomial assignment bound. -/
def witnessArity (φ : Formula) : ℕ := satWb (encodeFormula' φ).length

theorem witnessArity_eq (φ : Formula) :
    witnessArity φ = 3 * (encodeFormula' φ).length * (encodeFormula' φ).length + 3 := rfl

theorem witnessArity_variablesBelow (φ : Formula) : VariablesBelow (witnessArity φ) φ := by
  intro c hc l hl
  have h := lit_var_bound φ c l hc hl
  exact Nat.lt_of_succ_le h

def sampledCircuit (φ : Formula) : List (CGate (witnessArity φ)) :=
  verifierCircuit (witnessArity φ) φ

def selectedSamples (samples : SampleSelector) (φ : Formula) :
    List (Assignment (witnessArity φ)) := samples (witnessArity φ) (sampledCircuit φ)

/-- A concrete Boolean program, with the sample selector supplied explicitly. -/
def sampledSAT (samples : SampleSelector) (φ : Formula) : Bool :=
  (selectedSamples samples φ).any (output (sampledCircuit φ))

theorem sampledSAT_eq_verifier_any (samples : SampleSelector) (φ : Formula) :
    sampledSAT samples φ = (selectedSamples samples φ).any
      (fun a => evalFormula (extendAssignment a) φ) := by
  unfold sampledSAT
  congr 1
  funext a
  exact verifierCircuit_computes (witnessArity φ) φ a

/-- A positive sample is always an actual satisfying assignment. -/
theorem sampledSAT_sound (samples : SampleSelector) (φ : Formula)
    (h : sampledSAT samples φ = true) : Satisfiable φ := by
  rw [sampledSAT_eq_verifier_any, List.any_eq_true] at h
  obtain ⟨a, _, ha⟩ := h
  exact ⟨extendAssignment a, ha⟩

/-- The exact additional property needed by the sampled verifier. -/
def HitsSatisfiableFormulas (samples : SampleSelector) : Prop :=
  ∀ φ : Formula, Satisfiable φ →
    ∃ a ∈ selectedSamples samples φ, evalFormula (extendAssignment a) φ = true

theorem sampledSAT_correct_of_hitting (samples : SampleSelector)
    (h : HitsSatisfiableFormulas samples) (φ : Formula) :
    sampledSAT samples φ = true ↔ Satisfiable φ := by
  constructor
  · exact sampledSAT_sound samples φ
  · intro hsat
    rw [sampledSAT_eq_verifier_any, List.any_eq_true]
    exact h φ hsat

/-- Separating evaluation on the actual computed-wire space supplies the
missing completeness property of this executable sampler. -/
theorem sampledSAT_correct (samples : SampleSelector)
    (hsep : ∀ n (c : List (CGate n)), SeparatesWires c (samples n c))
    (φ : Formula) : sampledSAT samples φ = true ↔ Satisfiable φ :=
  (satisfiable_iff_sample_accepts φ (witnessArity_variablesBelow φ)
    (selectedSamples samples φ) (hsep _ _)).symm

theorem separatingSelector_hits (samples : SampleSelector)
    (hsep : ∀ n (c : List (CGate n)), SeparatesWires c (samples n c)) :
    HitsSatisfiableFormulas samples := by
  intro φ hsat
  have h := (sampledSAT_correct samples hsep φ).mpr hsat
  rw [sampledSAT_eq_verifier_any, List.any_eq_true] at h
  exact h

/-- The same program applied to the repository's formula decoder. -/
def sampledSATWord (samples : SampleSelector) (x : List Bool) : Bool :=
  sampledSAT samples (decodeFormula' x)

theorem sampledSATWord_encode (samples : SampleSelector) (φ : Formula) :
    sampledSATWord samples (encodeFormula' φ) = sampledSAT samples φ := by
  simp [sampledSATWord, decodeFormula'_encodeFormula']

theorem sampledSATWord_eq_SATLang_of_hitting (samples : SampleSelector)
    (h : HitsSatisfiableFormulas samples) (x : List Bool) :
    sampledSATWord samples x = SeparationTarget.SATLang x := by
  have hiff := sampledSAT_correct_of_hitting samples h (decodeFormula' x)
  change sampledSAT samples (decodeFormula' x) = SeparationTarget.SATLang x
  unfold SeparationTarget.SATLang
  split
  · rename_i hsat
    exact hiff.mpr hsat
  · rename_i hunsat
    cases hvalue : sampledSAT samples (decodeFormula' x)
    · rfl
    · exact (hunsat (hiff.mp hvalue)).elim

/-- Exact language-level correctness. No efficient selector or polynomial
machine simulation follows merely from the existence of separating samples. -/
theorem sampledSATWord_eq_SATLang (samples : SampleSelector)
    (hsep : ∀ n (c : List (CGate n)), SeparatesWires c (samples n c))
    (x : List Bool) : sampledSATWord samples x = SeparationTarget.SATLang x :=
  sampledSATWord_eq_SATLang_of_hitting samples (separatingSelector_hits samples hsep) x

/-- The actual sample payload: each finite assignment is written as `n` bits. -/
def storedSamples (samples : SampleSelector) (φ : Formula) : List Bool :=
  ((selectedSamples samples φ).map wordOfFin).flatten

theorem samplePayload_length {n : ℕ} (xs : List (Assignment n)) :
    (xs.map wordOfFin).flatten.length = xs.length * n := by
  induction xs with
  | nil => simp
  | cons a as ih => simp [wordOfFin_length, ih, Nat.add_mul, Nat.add_comm]

theorem storedSamples_length (samples : SampleSelector) (φ : Formula) :
    (storedSamples samples φ).length =
      (selectedSamples samples φ).length * witnessArity φ :=
  samplePayload_length _

theorem sampledCircuit_length_le (φ : Formula) :
    (sampledCircuit φ).length ≤ (encodeFormula' φ).length :=
  verifierCircuit_length_le_encoded _ _

theorem witnessArity_le_quadratic (φ : Formula) :
    witnessArity φ ≤ 3 * ((encodeFormula' φ).length + 1) ^ 2 := by
  rw [witnessArity_eq]
  nlinarith

theorem sampleInputSize_le_quadratic (φ : Formula) :
    witnessArity φ + (sampledCircuit φ).length + 1 ≤
      4 * ((encodeFormula' φ).length + 1) ^ 2 := by
  have h := sampledCircuit_length_le φ
  have hw := witnessArity_eq φ
  nlinarith

/-- A selector whose returned sample count is polynomial in arity and gate
count returns polynomially many assignments on encoded-formula verifier inputs. -/
theorem selectedSamples_length_le (samples : SampleSelector) (C d : ℕ)
    (hsize : ∀ n (c : List (CGate n)), (samples n c).length ≤ C * (n + c.length + 1) ^ d)
    (φ : Formula) :
    (selectedSamples samples φ).length ≤
      (C * 4 ^ d) * ((encodeFormula' φ).length + 1) ^ (2 * d) := by
  calc
    _ ≤ C * (witnessArity φ + (sampledCircuit φ).length + 1) ^ d := hsize _ _
    _ ≤ C * (4 * ((encodeFormula' φ).length + 1) ^ 2) ^ d :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left (sampleInputSize_le_quadratic φ) d)
    _ = _ := by rw [mul_pow, ← pow_mul, mul_assoc]

/-- Explicit polynomial bit storage for the sample assignments. The input
arity is known to the consuming verifier and is not stored in each sample. -/
theorem storedSamples_length_le (samples : SampleSelector) (C d : ℕ)
    (hsize : ∀ n (c : List (CGate n)), (samples n c).length ≤ C * (n + c.length + 1) ^ d)
    (φ : Formula) :
    (storedSamples samples φ).length ≤
      (3 * C * 4 ^ d) * ((encodeFormula' φ).length + 1) ^ (2 * d + 2) := by
  rw [storedSamples_length]
  calc
    _ ≤ ((C * 4 ^ d) * ((encodeFormula' φ).length + 1) ^ (2 * d)) *
        (3 * ((encodeFormula' φ).length + 1) ^ 2) :=
      Nat.mul_le_mul (selectedSamples_length_le samples C d hsize φ)
        (witnessArity_le_quadratic φ)
    _ = _ := by rw [pow_add]; ring

end GodMoveSampledSAT

#print axioms GodMoveSampledSAT.witnessArity_variablesBelow
#print axioms GodMoveSampledSAT.sampledSAT_sound
#print axioms GodMoveSampledSAT.sampledSAT_correct_of_hitting
#print axioms GodMoveSampledSAT.sampledSAT_correct
#print axioms GodMoveSampledSAT.sampledSATWord_encode
#print axioms GodMoveSampledSAT.sampledSATWord_eq_SATLang_of_hitting
#print axioms GodMoveSampledSAT.sampledSATWord_eq_SATLang
#print axioms GodMoveSampledSAT.sampledCircuit_length_le
#print axioms GodMoveSampledSAT.selectedSamples_length_le
#print axioms GodMoveSampledSAT.storedSamples_length_le
