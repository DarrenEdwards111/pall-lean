import GodMoveCircuitConnection

/-!
# Every fixed CNF assignment verifier has a small circuit

A signed literal is a variable or its negation; a clause is an OR; a formula
is an AND. Compiling that tree gives a concrete Boolean circuit, with gate
count at most the coordinate-encoded formula length. The construction works
for every signed CNF, including empty clauses, the empty formula, and indices
outside the assignment domain (which retain the default-false semantics).

Its Boolean-normalized arithmetic output is exactly `verifierCharacteristic`,
without any SAT machine or SAT-correctness premise. Thus the characteristic
already has a small Boolean-circuit representation for every fixed formula.
This is assignment verification: it does not decide whether some satisfying
assignment exists, compute the expanded characteristic, or bound SPDP rank.
-/

namespace GodMoveDirectVerifierCircuit

open GodMovePinnedSATQueries GodMoveFaithfulHandshake GodMoveBooleanInterpolation
open GodMoveCircuitConnection
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer CookLevinReduction CookLevinEmit CookLevinEmitCodec

/-- A signed literal, including the ambient default-false assignment value. -/
def literalTree (n : ℕ) (l : Lit) : Trans n :=
  if h : l.1 < n then
    if l.2 then .var ⟨l.1, h⟩ else .un Bool.not (.var ⟨l.1, h⟩)
  else .cst (!l.2)

def clauseTree (n : ℕ) : Clause → Trans n
  | [] => .cst false
  | l :: ls => .bin Bool.or (literalTree n l) (clauseTree n ls)

def formulaTree (n : ℕ) : Formula → Trans n
  | [] => .cst true
  | c :: cs => .bin Bool.and (clauseTree n c) (formulaTree n cs)

theorem literalTree_eval {n : ℕ} (l : Lit) (a : Fin n → Bool) :
    eval (literalTree n l) a = evalLit (extendAssignment a) l := by
  unfold literalTree evalLit extendAssignment
  by_cases h : l.1 < n
  · cases l.2 <;> simp [h, eval]
  · cases l.2 <;> simp [h, eval]

theorem clauseTree_eval {n : ℕ} (c : Clause) (a : Fin n → Bool) :
    eval (clauseTree n c) a = evalClause (extendAssignment a) c := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
    simpa only [clauseTree, eval, literalTree_eval, evalClause, List.any_cons] using
      congrArg (fun b => evalLit (extendAssignment a) l || b) ih

theorem formulaTree_eval {n : ℕ} (φ : Formula) (a : Fin n → Bool) :
    eval (formulaTree n φ) a = evalFormula (extendAssignment a) φ := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    simpa only [formulaTree, eval, clauseTree_eval, evalFormula, List.all_cons] using
      congrArg (fun b => evalClause (extendAssignment a) c && b) ih

theorem literalTree_volume_le (n : ℕ) (l : Lit) : volume (literalTree n l) ≤ 2 := by
  unfold literalTree
  split
  · split <;> simp [volume]
  · simp [volume]

theorem clauseTree_volume_le (n : ℕ) (c : Clause) :
    volume (clauseTree n c) ≤ 3 * c.length + 1 := by
  induction c with
  | nil => simp [clauseTree, volume]
  | cons l ls ih =>
    have hl := literalTree_volume_le n l
    simp only [clauseTree, volume, List.length_cons]
    omega

/-- Linear gate count in literal occurrences and clause count. -/
theorem formulaTree_volume_le (n : ℕ) (φ : Formula) :
    volume (formulaTree n φ) ≤ 3 * (φ.map List.length).sum + 2 * φ.length + 1 := by
  induction φ with
  | nil => simp [formulaTree, volume]
  | cons c cs ih =>
    have hc := clauseTree_volume_le n c
    simp only [formulaTree, volume, List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem literalTree_volume_le_encoded (n : ℕ) (l : Lit) :
    volume (literalTree n l) ≤ (encodeLit' l).length := by
  have h := literalTree_volume_le n l
  simp only [encodeLit', encodeVar', List.length_append, List.length_singleton,
    encodeNat_length]
  omega

theorem clauseTree_volume_le_encoded (n : ℕ) (c : Clause) :
    volume (clauseTree n c) ≤ (encodeClause' c).length := by
  induction c with
  | nil => simp [clauseTree, volume, encodeClause', encodeNat_length]
  | cons l ls ih =>
    have hl := literalTree_volume_le_encoded n l
    simp only [clauseTree, volume, encodeClause', List.length_append, encodeNat_length,
      List.length_cons, List.map_cons, List.flatten_cons] at *
    omega

/-- The faithful unary coordinate codec already pays for every tree node. -/
theorem formulaTree_volume_le_encoded (n : ℕ) (φ : Formula) :
    volume (formulaTree n φ) ≤ (encodeFormula' φ).length := by
  induction φ with
  | nil => simp [formulaTree, volume, encodeFormula', encodeNat_length]
  | cons c cs ih =>
    have hc := clauseTree_volume_le_encoded n c
    simp only [formulaTree, volume, encodeFormula', List.length_append, encodeNat_length,
      List.length_cons, List.map_cons, List.flatten_cons] at *
    omega

/-- A direct circuit for evaluating a supplied assignment against fixed `φ`. -/
def verifierCircuit (n : ℕ) (φ : Formula) : List (CGate n) :=
  NFrameBoundaryTransducer.compile 0 (formulaTree n φ)

theorem verifierCircuit_computes (n : ℕ) (φ : Formula) :
    computes (verifierCircuit n φ) (fun a => evalFormula (extendAssignment a) φ) := by
  intro a
  exact (compile_computes (formulaTree n φ) a).trans (formulaTree_eval φ a)

theorem verifierCircuit_length (n : ℕ) (φ : Formula) :
    (verifierCircuit n φ).length = volume (formulaTree n φ) :=
  compile_length _ _

theorem verifierCircuit_length_le (n : ℕ) (φ : Formula) :
    (verifierCircuit n φ).length ≤ 3 * (φ.map List.length).sum + 2 * φ.length + 1 := by
  rw [verifierCircuit_length]
  exact formulaTree_volume_le n φ

theorem verifierCircuit_length_le_encoded (n : ℕ) (φ : Formula) :
    (verifierCircuit n φ).length ≤ (encodeFormula' φ).length := by
  rw [verifierCircuit_length]
  exact formulaTree_volume_le_encoded n φ

/-- The same characteristic target has a small circuit before introducing
any SAT decider, clock, or machine-correctness hypothesis. -/
theorem verifierCircuit_target (n : ℕ) (φ : Formula) :
    circuitTarget (verifierCircuit n φ) = verifierCharacteristic n φ := by
  rw [circuitTarget_eq_interpolate, verifierCharacteristic]
  exact interpolate_congr (verifierCircuit_computes n φ)

/-- Consequently the chosen graph-volume minimum of the fixed-formula
assignment predicate is always at most the formula's encoded length. -/
theorem verifier_cbudget_le_encoded (n : ℕ) (φ : Formula) :
    cbudget (fun a : Fin n → Bool => evalFormula (extendAssignment a) φ) ≤
      (encodeFormula' φ).length := by
  have h : cbudget (fun a : Fin n → Bool => evalFormula (extendAssignment a) φ) ≤
      (verifierCircuit n φ).length :=
    Nat.sInf_le ⟨verifierCircuit n φ, verifierCircuit_computes n φ, rfl⟩
  exact h.trans (verifierCircuit_length_le_encoded n φ)

/-- Existence of a compact normalized source for this target is unconditional
for every signed CNF, not evidence of a fast SAT decision procedure. -/
theorem exists_small_circuit_for_characteristic (n : ℕ) (φ : Formula) :
    ∃ c : List (CGate n), c.length ≤ (encodeFormula' φ).length ∧
      circuitTarget c = verifierCharacteristic n φ :=
  ⟨verifierCircuit n φ, verifierCircuit_length_le_encoded n φ, verifierCircuit_target n φ⟩

end GodMoveDirectVerifierCircuit

#print axioms GodMoveDirectVerifierCircuit.literalTree_eval
#print axioms GodMoveDirectVerifierCircuit.formulaTree_eval
#print axioms GodMoveDirectVerifierCircuit.verifierCircuit_computes
#print axioms GodMoveDirectVerifierCircuit.verifierCircuit_length_le
#print axioms GodMoveDirectVerifierCircuit.verifierCircuit_length_le_encoded
#print axioms GodMoveDirectVerifierCircuit.verifierCircuit_target
#print axioms GodMoveDirectVerifierCircuit.verifier_cbudget_le_encoded
#print axioms GodMoveDirectVerifierCircuit.exists_small_circuit_for_characteristic
