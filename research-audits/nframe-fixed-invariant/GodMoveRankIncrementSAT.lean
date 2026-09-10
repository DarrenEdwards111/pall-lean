import GodMoveDirectVerifierCircuit
import GodMoveComputedWireRank

/-!
# A single computed-wire rank increment detects satisfiability

Two fresh Boolean controls turn the output of a circuit into a new wire
direction exactly when that circuit accepts some input. The construction
copies the original gate list with renamed input indices and appends four
gates. No assignment enumeration or SAT test enters the construction.

This is a reduction to exact rank comparison, not an algorithm for computing
rank and not a superpolynomial lower bound on rank or SAT runtime.
-/

namespace GodMoveRankIncrementSAT

open GodMoveBooleanInterpolation GodMoveCircuitNormalization GodMoveComputedWireRank
open GodMoveSymbolicPinnedInput GodMoveCircuitConnection GodMoveDirectVerifierCircuit
open MvPolynomial MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer CookLevinReduction CookLevinEmitCodec
open GodMovePinnedSATQueries
open GodMoveCircuitArithmetization (AExpr arithGate runArithmetic)
open scoped BigOperators

abbrev QPoly (n : ℕ) := GodMoveBooleanInterpolation.Poly n

def oldIndex {n : ℕ} (i : Fin n) : Fin (n + 2) := ⟨i.val, by omega⟩
def yIndex (n : ℕ) : Fin (n + 2) := ⟨n, by omega⟩
def zIndex (n : ℕ) : Fin (n + 2) := ⟨n + 1, by omega⟩

def liftCircuit {n : ℕ} (c : List (CGate n)) : List (CGate (n + 2)) :=
  specializeCircuit (fun i => CGate.var (oldIndex i)) c

theorem liftCircuit_length {n : ℕ} (c : List (CGate n)) :
    (liftCircuit c).length = c.length := by simp [liftCircuit]

def corner {n : ℕ} (a : Assignment n) (u v : Bool) : Assignment (n + 2) :=
  fun i => if h : i.val < n then a ⟨i.val, h⟩ else if i.val = n then u else v

@[simp] theorem corner_old {n : ℕ} (a : Assignment n) (u v : Bool) (i : Fin n) :
    corner a u v (oldIndex i) = a i := by simp [corner, oldIndex, i.isLt]
@[simp] theorem corner_y {n : ℕ} (a : Assignment n) (u v : Bool) :
    corner a u v (yIndex n) = u := by simp [corner, yIndex]
@[simp] theorem corner_z {n : ℕ} (a : Assignment n) (u v : Bool) :
    corner a u v (zIndex n) = v := by simp [corner, zIndex]

theorem runFrom_lift_corner {n : ℕ} (c : List (CGate n))
    (a : Assignment n) (u v : Bool) :
    runFrom (corner a u v) [] (liftCircuit c) = runFrom a [] c := by
  rw [liftCircuit, runFrom_specialize (fun i : Fin n => CGate.var (oldIndex i)) (fun _ => True.intro)]
  simp only [closedEval, corner_old]

theorem output_lift {n : ℕ} (c : List (CGate n)) (a : Assignment (n + 2)) :
    output (liftCircuit c) a = output c (fun i => a (oldIndex i)) := by
  rw [liftCircuit, output_specialize (fun i : Fin n => CGate.var (oldIndex i)) (fun _ => True.intro)]
  rfl

theorem eval_normalizedWires {n : ℕ} (c : List (CGate n)) (a : Assignment n) :
    (normalizedWires c).map (MvPolynomial.eval (booleanPoint a)) =
      (runFrom a [] c).map bit := by
  unfold normalizedWires rawWires
  simp only [List.map_map, Function.comp_def, eval_normalize]
  rw [GodMoveCircuitArithmetization.eval_runArithmetic_poly]
  exact GodMoveCircuitArithmetization.runArithmetic_compile a [] c

theorem old_wire_corner_eval {n : ℕ} (c : List (CGate n))
    (a : Assignment n) (u v : Bool) (p : QPoly (n + 2))
    (hp : p ∈ normalizedWires (liftCircuit c)) :
    MvPolynomial.eval (booleanPoint (corner a u v)) p =
      MvPolynomial.eval (booleanPoint (corner a false false)) p := by
  apply (List.map_inj_left.mp ?_) p hp
  rw [eval_normalizedWires, eval_normalizedWires,
    runFrom_lift_corner, runFrom_lift_corner]

/-- Add the two controls and their first conjunction with the old output. -/
def rankPrefix {n : ℕ} (c : List (CGate n)) : List (CGate (n + 2)) :=
  ((liftCircuit c ++ [.var (yIndex n)]) ++ [.var (zIndex n)]) ++
    [.bin Bool.and (c.length - 1) c.length]

def lastGate {n : ℕ} (c : List (CGate n)) : CGate (n + 2) :=
  .bin Bool.and (c.length + 2) (c.length + 1)

def rankExtension {n : ℕ} (c : List (CGate n)) : List (CGate (n + 2)) :=
  rankPrefix c ++ [lastGate c]

theorem rankPrefix_length {n : ℕ} (c : List (CGate n)) :
    (rankPrefix c).length = c.length + 3 := by simp [rankPrefix, liftCircuit_length]

theorem rankExtension_length {n : ℕ} (c : List (CGate n)) :
    (rankExtension c).length = c.length + 4 := by
  simp [rankExtension, rankPrefix_length]

noncomputable def oldOutput {n : ℕ} (c : List (CGate n)) : QPoly (n + 2) :=
  GodMoveCircuitArithmetization.rawPoly (liftCircuit c)

private theorem arith_and {n : ℕ} (x : Fin n → QPoly n) (vals : List (QPoly n)) (j k : ℕ) :
    (arithGate (.bin Bool.and j k)).eval x vals = vals.getD j 0 * vals.getD k 0 := by
  simp [arithGate, GodMoveCircuitArithmetization.select, AExpr.eval, mul_comm]

theorem rawWires_prefix {n : ℕ} (c : List (CGate n)) (hc : 0 < c.length) :
    rawWires (rankPrefix c) = rawWires (liftCircuit c) ++
      [X (yIndex n), X (zIndex n), oldOutput c * X (yIndex n)] := by
  have hlen : (rawWires (liftCircuit c)).length = c.length := by
    rw [rawWires_length, liftCircuit_length]
  have hread : ((rawWires (liftCircuit c) ++ [X (yIndex n)]) ++ [X (zIndex n)]).getD
      (c.length - 1) 0 = oldOutput c := by
    rw [List.getD_append _ _ _ _ (by simp [hlen]),
      List.getD_append _ _ _ _ (by rw [hlen]; omega)]
    simp only [oldOutput, GodMoveCircuitArithmetization.rawPoly, liftCircuit_length, rawWires]
  have hyread : ((rawWires (liftCircuit c) ++ [X (yIndex n)]) ++ [X (zIndex n)]).getD
      c.length 0 = X (yIndex n) := by
    rw [List.getD_append _ _ _ _ (by simp [hlen]),
      List.getD_append_right _ _ _ _ (by rw [hlen])]
    simp [hlen]
  unfold rankPrefix
  rw [rawWires_append_gate, rawWires_append_gate, rawWires_append_gate]
  rw [arith_and]
  change rawWires (liftCircuit c) ++ [X (yIndex n)] ++ [X (zIndex n)] ++
    [((rawWires (liftCircuit c) ++ [X (yIndex n)]) ++ [X (zIndex n)]).getD
      (c.length - 1) 0 *
     ((rawWires (liftCircuit c) ++ [X (yIndex n)]) ++ [X (zIndex n)]).getD c.length 0] = _
  rw [hread, hyread]
  simp only [List.append_assoc, List.singleton_append]
  rfl

theorem lastGate_raw {n : ℕ} (c : List (CGate n)) (hc : 0 < c.length) :
    (arithGate (lastGate c)).eval MvPolynomial.X (rawWires (rankPrefix c)) =
      oldOutput c * X (yIndex n) * X (zIndex n) := by
  have hlen : (rawWires (liftCircuit c)).length = c.length := by
    rw [rawWires_length, liftCircuit_length]
  rw [lastGate, arith_and, rawWires_prefix c hc]
  rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega),
    List.getD_append_right _ _ _ _ (by rw [hlen]; omega)]
  simp [hlen]

noncomputable def finalRow {n : ℕ} (c : List (CGate n)) : QPoly (n + 2) :=
  normalize (oldOutput c * X (yIndex n) * X (zIndex n))

theorem extension_space {n : ℕ} (c : List (CGate n)) (hc : 0 < c.length) :
    wireSpace (rankExtension c) = wireSpace (rankPrefix c) ⊔ Submodule.span ℚ {finalRow c} := by
  rw [rankExtension, wireSpace_append_gate, lastGate_raw c hc]
  rfl

noncomputable def evalLinear {n : ℕ} (a : Assignment n) : QPoly n →ₗ[ℚ] ℚ where
  toFun := MvPolynomial.eval (booleanPoint a)
  map_add' := map_add _
  map_smul' := by
    intro r p
    simp [MvPolynomial.smul_eq_C_mul]

@[simp] theorem evalLinear_apply {n : ℕ} (a : Assignment n) (p : QPoly n) :
    evalLinear a p = MvPolynomial.eval (booleanPoint a) p := rfl

noncomputable def cornerFunctional {n : ℕ} (a : Assignment n) : QPoly (n + 2) →ₗ[ℚ] ℚ :=
  (evalLinear (corner a true true) - evalLinear (corner a true false)) -
    evalLinear (corner a false true) + evalLinear (corner a false false)

theorem oldOutput_corner {n : ℕ} (c : List (CGate n)) (a : Assignment n) (u v : Bool) :
    MvPolynomial.eval (booleanPoint (corner a u v)) (oldOutput c) = bit (output c a) := by
  rw [oldOutput, GodMoveCircuitArithmetization.eval_rawPoly, output_lift]
  simp only [corner_old]

theorem cornerFunctional_finalRow {n : ℕ} (c : List (CGate n)) (a : Assignment n) :
    cornerFunctional a (finalRow c) = bit (output c a) := by
  simp [cornerFunctional, finalRow, eval_normalize, oldOutput_corner,
    booleanPoint, bit, map_mul]

theorem cornerFunctional_prefix {n : ℕ} (c : List (CGate n)) (hc : 0 < c.length)
    (a : Assignment n) (p : QPoly (n + 2)) (hp : p ∈ normalizedWires (rankPrefix c)) :
    cornerFunctional a p = 0 := by
  have hzero (u v : Bool) (q : QPoly (n + 2)) (hq : q ∈ normalizedWires (liftCircuit c)) :=
    old_wire_corner_eval c a u v q hq
  unfold normalizedWires at hp
  rw [rawWires_prefix c hc, List.map_append] at hp
  rcases List.mem_append.mp hp with hp | hp
  · change p ∈ normalizedWires (liftCircuit c) at hp
    simp only [cornerFunctional, LinearMap.add_apply, LinearMap.sub_apply,
      evalLinear_apply]
    rw [hzero true true p hp, hzero true false p hp, hzero false true p hp]
    ring
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      simp [cornerFunctional, eval_normalize, oldOutput_corner, booleanPoint, bit, map_mul]

theorem finalRow_not_mem_of_accepts {n : ℕ} (c : List (CGate n)) (hc : 0 < c.length)
    (a : Assignment n) (ha : output c a = true) :
    finalRow c ∉ wireSpace (rankPrefix c) := by
  have hker : wireSpace (rankPrefix c) ≤ LinearMap.ker (cornerFunctional a) := by
    apply Submodule.span_le.mpr
    intro p hp
    exact cornerFunctional_prefix c hc a p (by simpa using hp)
  intro hmem
  have hz := hker hmem
  change cornerFunctional a (finalRow c) = 0 at hz
  rw [cornerFunctional_finalRow, ha] at hz
  norm_num [bit] at hz

theorem rank_increases_of_accepts {n : ℕ} (c : List (CGate n)) (hc : 0 < c.length)
    (a : Assignment n) (ha : output c a = true) :
    wireRank (rankPrefix c) < wireRank (rankExtension c) := by
  apply Submodule.finrank_lt_finrank_of_lt
  have hle : wireSpace (rankPrefix c) ≤ wireSpace (rankExtension c) := by
    rw [extension_space c hc]
    exact le_sup_left
  apply lt_of_le_of_ne hle
  intro heq
  have hmem : finalRow c ∈ wireSpace (rankExtension c) := by
    rw [extension_space c hc]
    exact Submodule.mem_sup_right (Submodule.subset_span (by simp))
  rw [← heq] at hmem
  exact finalRow_not_mem_of_accepts c hc a ha hmem

/-- An identically rejecting output contributes the zero final row. -/
theorem finalRow_eq_zero_of_rejects {n : ℕ} (c : List (CGate n))
    (hfalse : ∀ a, output c a = false) : finalRow c = 0 := by
  apply multilinear_eq_of_boolean_eval _ _ (normalize_isMultilinear _)
    (by intro α hα; simp at hα)
  intro a
  simp only [eval_normalize, map_mul, map_zero]
  rw [oldOutput, GodMoveCircuitArithmetization.eval_rawPoly, output_lift, hfalse]
  simp [bit]

theorem rank_eq_of_rejects {n : ℕ} (c : List (CGate n)) (hc : 0 < c.length)
    (hfalse : ∀ a, output c a = false) :
    wireRank (rankExtension c) = wireRank (rankPrefix c) := by
  unfold wireRank
  rw [extension_space c hc, finalRow_eq_zero_of_rejects c hfalse]
  rw [Submodule.span_zero_singleton, sup_bot_eq]

/-- Exact comparison of two ranks detects whether the original circuit ever
accepts. The two circuits differ by one final legal gate. -/
theorem rank_increases_iff_accepts {n : ℕ} (c : List (CGate n)) (hc : 0 < c.length) :
    wireRank (rankPrefix c) < wireRank (rankExtension c) ↔ ∃ a, output c a = true := by
  constructor
  · intro h
    by_contra hn
    have hfalse : ∀ a, output c a = false := by
      intro a
      cases heq : output c a with
      | false => rfl
      | true => exact False.elim (hn ⟨a, heq⟩)
    rw [rank_eq_of_rejects c hc hfalse] at h
    exact (lt_irrefl _ h)
  · rintro ⟨a, ha⟩
    exact rank_increases_of_accepts c hc a ha

theorem rank_extension_eq_add_one_of_accepts {n : ℕ} (c : List (CGate n))
    (hc : 0 < c.length) (ha : ∃ a, output c a = true) :
    wireRank (rankExtension c) = wireRank (rankPrefix c) + 1 := by
  have hlo := (rank_increases_iff_accepts c hc).mpr ha
  have hhi := wireRank_append_gate_le (rankPrefix c) (lastGate c)
  change wireRank (rankExtension c) ≤ wireRank (rankPrefix c) + 1 at hhi
  omega

/-- The variable bound connects finite circuit inputs to ordinary CNF SAT. -/
theorem verifier_accepts_iff_satisfiable (n : ℕ) (φ : Formula)
    (hvars : VariablesBelow n φ) :
    (∃ a, output (verifierCircuit n φ) a = true) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨extendAssignment a, (verifierCircuit_computes n φ a).symm.trans ha⟩
  · rintro ⟨a, ha⟩
    let b : Assignment n := fun i => a i.val
    refine ⟨b, (verifierCircuit_computes n φ b).trans ?_⟩
    have heq : evalFormula (extendAssignment b) φ = evalFormula a φ := by
      apply SATVerifierSpec.evalFormula_congr
      intro c hc l hl
      have hi := hvars c hc l hl
      simp [extendAssignment, hi, b]
    exact heq.trans ha

/-- A gate-list construction of linear size reduces CNF satisfiability to
one exact rank-increment comparison. It does not compute either rank. -/
theorem verifier_rank_increases_iff_satisfiable (n : ℕ) (φ : Formula)
    (hvars : VariablesBelow n φ) :
    wireRank (rankPrefix (verifierCircuit n φ)) <
      wireRank (rankExtension (verifierCircuit n φ)) ↔ Satisfiable φ := by
  have hc : 0 < (verifierCircuit n φ).length := by
    rw [verifierCircuit_length]
    exact volume_pos _
  exact (rank_increases_iff_accepts _ hc).trans
    (verifier_accepts_iff_satisfiable n φ hvars)

theorem verifier_rank_extension_length_le (n : ℕ) (φ : Formula) :
    (rankExtension (verifierCircuit n φ)).length ≤ (encodeFormula' φ).length + 4 := by
  rw [rankExtension_length]
  exact Nat.add_le_add_right (verifierCircuit_length_le_encoded n φ) 4

/-- An exact-rank subroutine, represented only by its input/output type. No
computability or runtime hypothesis is hidden in this type. -/
abbrev RankSubroutine := (n : ℕ) → List (CGate n) → ℕ

def comparisonArity (φ : Formula) : ℕ :=
  SATVerifierSpec.satWb (encodeFormula' φ).length

theorem comparisonArity_eq (φ : Formula) :
    comparisonArity φ = 3 * (encodeFormula' φ).length * (encodeFormula' φ).length + 3 := rfl

def rankComparisonSAT (ranks : RankSubroutine) (φ : Formula) : Bool :=
  let n := comparisonArity φ
  let c := verifierCircuit n φ
  decide (ranks (n + 2) (rankPrefix c) < ranks (n + 2) (rankExtension c))

/-- Correct exact rank values for the two constructed circuits suffice to
decide SAT. This theorem supplies no exact-rank algorithm or runtime bound. -/
theorem rankComparisonSAT_correct (ranks : RankSubroutine)
    (hranks : ∀ n c, ranks n c = wireRank c) (φ : Formula) :
    rankComparisonSAT ranks φ = true ↔ Satisfiable φ := by
  simp only [rankComparisonSAT, hranks, decide_eq_true_eq]
  apply verifier_rank_increases_iff_satisfiable
  intro c hc l hl
  exact Nat.lt_of_succ_le (SATVerifierSpec.lit_var_bound φ c l hc hl)

end GodMoveRankIncrementSAT

#print axioms GodMoveRankIncrementSAT.rawWires_prefix
#print axioms GodMoveRankIncrementSAT.lastGate_raw
#print axioms GodMoveRankIncrementSAT.cornerFunctional_finalRow
#print axioms GodMoveRankIncrementSAT.cornerFunctional_prefix
#print axioms GodMoveRankIncrementSAT.rank_increases_of_accepts

#print axioms GodMoveRankIncrementSAT.rank_increases_iff_accepts
#print axioms GodMoveRankIncrementSAT.rank_extension_eq_add_one_of_accepts
#print axioms GodMoveRankIncrementSAT.verifier_rank_increases_iff_satisfiable
#print axioms GodMoveRankIncrementSAT.verifier_rank_extension_length_le

#print axioms GodMoveRankIncrementSAT.rankComparisonSAT_correct
