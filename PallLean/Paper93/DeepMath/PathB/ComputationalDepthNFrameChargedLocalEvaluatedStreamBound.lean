import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLiteralWeld

/-!
# Polynomial size of the charged local evaluated verifier stream

The remaining SAT-verifier transducer parses a paired formula/certificate and
emits the nested truth-value stream consumed by `cnfAggregator`.  This file
proves that malformed unary inputs cannot make that semantic output expand
superpolynomially.

Both the number of decoded clauses and the length of every decoded clause are
bounded by the original instance length.  Consequently the evaluated stream
has a uniform quadratic bound in the whole paired input length.  Thus output
capacity is not a hidden obstacle: only the concrete repeated local
parse/lookup/write schedule remains to be implemented.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalEvaluatedStreamBound

open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalNPBridge
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalCNFAggregator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld

/-! ## Decoder shape bounds on all inputs -/

theorem decodeLits_length (k : Nat) (bs : List Bool) :
    (decodeLits k bs).1.length = k := by
  induction k generalizing bs with
  | zero => rfl
  | succ k ih => simp [decodeLits, ih]

theorem decodeClause_length (bs : List Bool) :
    (decodeClause bs).1.length = (decodeNat bs).1 := by
  simp [decodeClause, decodeLits_length]

theorem decodeClauses_length (k : Nat) (bs : List Bool) :
    (decodeClauses k bs).1.length = k := by
  induction k generalizing bs with
  | zero => rfl
  | succ k ih => simp [decodeClauses, ih]

theorem decodeFormula_length_le (bs : List Bool) :
    (decodeFormula bs).length ≤ bs.length := by
  rw [decodeFormula, decodeClauses_length]
  exact decodeNat_value_le_length bs

theorem decodeClauses_clause_length_le (k : Nat) (bs : List Bool)
    {c : Clause} (hc : c ∈ (decodeClauses k bs).1) :
    c.length ≤ bs.length := by
  induction k generalizing bs with
  | zero => simp [decodeClauses] at hc
  | succ k ih =>
      simp only [decodeClauses, List.mem_cons] at hc
      rcases hc with rfl | hc
      · rw [decodeClause_length]
        exact decodeNat_value_le_length bs
      · exact le_trans (ih (decodeClause bs).2 hc)
          (decodeClause_rest_length_le bs)

theorem decodeFormula_clause_length_le (bs : List Bool)
    {c : Clause} (hc : c ∈ decodeFormula bs) :
    c.length ≤ bs.length := by
  simp only [decodeFormula] at hc
  exact le_trans
    (decodeClauses_clause_length_le _ (decodeNat bs).2 hc)
    (decodeNat_rest_length_le bs)

/-! ## Quadratic evaluated-stream bound -/

theorem unpackWitness_instance_length_le (z : List Bool) :
    (unpackWitness z).1.length ≤ z.length := by
  simp only [unpackWitness]
  exact le_trans (List.length_take_le _ _)
    (decodeNat_value_le_length z)

/-- A simple quadratic envelope for the emitted stream. -/
def evaluatedStreamBound (n : Nat) : Nat := 1 + n * (2 * n + 2)

theorem evaluatedStreamBound_poly : PolyBounded evaluatedStreamBound := by
  refine ⟨3, 2, ?_⟩
  intro n
  simp only [evaluatedStreamBound]
  nlinarith [Nat.zero_le n]

theorem evaluatedFormula_shape (w : List Bool) (F : Formula) :
    (evaluatedFormula w F).length = F.length ∧
      (evaluatedFormula w F).map (fun c => 2 * c.length + 2) =
        F.map (fun c => 2 * c.length + 2) := by
  constructor <;> simp [evaluatedFormula]

theorem decoded_formula_weight_le (x : List Bool) :
    ((decodeFormula x).map (fun c => 2 * c.length + 2)).sum ≤
      x.length * (2 * x.length + 2) := by
  have hb : ∀ y ∈ (decodeFormula x).map (fun c => 2 * c.length + 2),
      y ≤ 2 * x.length + 2 := by
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    have := decodeFormula_clause_length_le x hc
    omega
  have hs := List.sum_le_card_nsmul
    ((decodeFormula x).map (fun c => 2 * c.length + 2))
    (2 * x.length + 2) hb
  simp only [List.length_map, nsmul_eq_mul] at hs
  exact le_trans hs (Nat.mul_le_mul_right _ (decodeFormula_length_le x))

/-- On every paired bitstring—including malformed ones—the exact stream
required by the verifier has quadratic length. -/
theorem evaluatedVerifierStream_length_le (z : List Bool) :
    (evaluatedVerifierStream z).length ≤ evaluatedStreamBound z.length := by
  let x := (unpackWitness z).1
  let w := (unpackWitness z).2
  have hx : x.length ≤ z.length := unpackWitness_instance_length_le z
  have hweight := decoded_formula_weight_le x
  have hshape := (evaluatedFormula_shape w (decodeFormula x)).2
  rw [evaluatedVerifierStream, encodeFormulaValues_length, hshape]
  unfold evaluatedStreamBound
  exact Nat.add_le_add_left
    (le_trans hweight (Nat.mul_le_mul hx (by omega))) 1

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalEvaluatedStreamBound

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalEvaluatedStreamBound.decodeFormula_length_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalEvaluatedStreamBound.decodeFormula_clause_length_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalEvaluatedStreamBound.evaluatedStreamBound_poly
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalEvaluatedStreamBound.evaluatedVerifierStream_length_le
