import PallLean.Paper93.DeepMath.PathB.ComputationalDepthComposablePpolyDischarge

/-!
# The exact reduction: super-additive composition ⟹ superpolynomial `cbudget(SAT)`

The `+k` codec campaign proves `cbudget(SAT_N) ≥ 2·deps + k` — **additive**, hence linear in
`N` (the AEm testbed pins it exactly: `cbudget(AEm m) = 7m − 1`).  A superpolynomial circuit
lower bound cannot come from additive composition of a bounded number of units.  It needs a
**super-additive** law: composing codec units must *multiply* cost, not add a constant.

This file builds the reduction that turns such a law into the target, so the single open lemma
is stated precisely and everything downstream is discharged around it.

A `SuperAdditiveTower` bundles the hypothetical composition data:
* `cost d` — a `cbudget` floor for the level-`d` self-composite (`realizes`);
* **`cost_super : ∀ d, 2 · cost d ≤ cost (d+1)`** — the super-additive step: each composition at
  least **doubles** the cost.  *This is the entire open content* — the "no-sharing under
  composition" claim, the Valiant-rigidity / Uhlig-sharing wall.  Whether SAT's codec admits
  such a tower is equivalent to an exponential lower bound and is **not** constructed here.
* `arity_le : ∀ d, arity d ≤ d` — the composite's input length grows only linearly, so cost
  outruns any polynomial in the arity.

From these, `cost d ≥ 2^d` (induction), and since `arity d ≤ d`, an exp-beats-poly argument
yields `∀ k, ∃ n, n^k + k < cbudget(SATFamily n)` — exactly the hypothesis of the existing
axiom-clean bridge `sat_superpoly_cbudget_implies_SAT_not_in_P`.  Chaining gives
`SuperAdditiveTower → ¬ InP SATLang`.

**Honest scope.**  The tower is *exponential*-strength — stronger than superpolynomial needs; a
weaker super-additive law would also suffice, this is the clean representative.  Nothing is
constructed: `cost_super` is the open lemma, `T : SuperAdditiveTower` an explicit hypothesis.
This is NOT a proof of `P ≠ NP`; it is the precise statement of what a super-additive
composition would have to deliver, with the surrounding reduction proved.
-/

namespace PallLean.Paper93.DeepMath.PathB.SuperAdditiveComposition

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.SeparationTarget

/-! ### Exponential beats polynomial (elementary, self-contained) -/

/-- `m² < 2^m` for `m ≥ 5` (induction; the step uses `2m+1 ≤ m²`). -/
theorem sq_lt_two_pow (m : ℕ) (hm : 5 ≤ m) : m * m < 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have h5n : 5 * n ≤ n * n := Nat.mul_le_mul hn (le_refl n)
    have h2n : 2 * n + 1 ≤ n * n := by omega
    calc (n + 1) * (n + 1) = n * n + (2 * n + 1) := by ring
      _ < 2 ^ n + 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- For every exponent `e` there is a base `d ≥ 2` with `d^e < 2^d`
(via the substitution `d = e·(e+5)` and `e·m ≤ m² < 2^m`). -/
theorem pow_lt_two_pow_dom (e : ℕ) : ∃ d, 2 ≤ d ∧ d ^ e < 2 ^ d := by
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he; exact ⟨2, le_refl 2, by decide⟩
  · refine ⟨e * (e + 5), ?_, ?_⟩
    · have h1 : 1 * 5 ≤ e * (e + 5) := Nat.mul_le_mul he (by omega)
      omega
    · set m := e + 5 with hm
      have hm5 : 5 ≤ m := by omega
      have hem : e ≤ m := by omega
      have hbase : e * m < 2 ^ m :=
        lt_of_le_of_lt (Nat.mul_le_mul hem (le_refl m)) (sq_lt_two_pow m hm5)
      calc (e * m) ^ e < (2 ^ m) ^ e := Nat.pow_lt_pow_left hbase he.ne'
        _ = 2 ^ (m * e) := by rw [← pow_mul]
        _ = 2 ^ (e * m) := by rw [Nat.mul_comm m e]

/-- `∀ k, ∃ d, d^k + k < 2^d` — exponential dominates polynomial with slack for the `+k`. -/
theorem exp_beats_poly (k : ℕ) : ∃ d, d ^ k + k < 2 ^ d := by
  obtain ⟨d, hd2, hlt⟩ := pow_lt_two_pow_dom (k + 1)
  refine ⟨d, ?_⟩
  have hdk : k < d ^ k :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hd2 k)
  have hpow : d ^ (k + 1) = d ^ k * d := pow_succ d k
  have h2A : d ^ k * 2 ≤ d ^ k * d := Nat.mul_le_mul (le_refl _) hd2
  omega

/-! ### The super-additive composition tower and the reduction -/

/-- A hypothetical **super-additive self-composition tower** on the SAT codec: at level `d`, a
SAT slice on `arity d ≤ d` variables whose `cbudget` is at least `cost d`, where each
composition step at least **doubles** the cost.  The `cost_super` field is the single open
lemma (no-sharing under composition); the tower is never constructed here. -/
structure SuperAdditiveTower where
  /-- Input length of the level-`d` self-composite. -/
  arity : ℕ → ℕ
  /-- A `cbudget` floor for the level-`d` self-composite. -/
  cost : ℕ → ℕ
  /-- The base cost is positive. -/
  cost_pos : 1 ≤ cost 0
  /-- **Super-additivity (the open lemma):** each composition step at least doubles the cost. -/
  cost_super : ∀ d, 2 * cost d ≤ cost (d + 1)
  /-- Arity grows only linearly, so cost outruns any polynomial in the arity. -/
  arity_le : ∀ d, arity d ≤ d
  /-- `cost` is a genuine `cbudget` lower bound for the corresponding SAT slice. -/
  realizes : ∀ d, cost d ≤ cbudget (SATFamily (arity d))

/-- **Cost dominates `2^d` (proved).**  Super-additivity iterated from a positive base. -/
theorem cost_ge_two_pow (T : SuperAdditiveTower) (d : ℕ) : 2 ^ d ≤ T.cost d := by
  induction d with
  | zero => simpa using T.cost_pos
  | succ n ih =>
    calc 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
      _ = 2 * 2 ^ n := Nat.mul_comm _ _
      _ ≤ 2 * T.cost n := by omega
      _ ≤ T.cost (n + 1) := T.cost_super n

/-- **THE REDUCTION (proved).**  A super-additive composition tower forces a superpolynomial
`cbudget` for the exact SAT slices — the hypothesis of the circuit bridge. -/
theorem superAdditiveTower_implies_superpoly (T : SuperAdditiveTower) :
    ∀ k, ∃ n, n ^ k + k < cbudget (SATFamily n) := by
  intro k
  obtain ⟨d, hd⟩ := exp_beats_poly k
  refine ⟨T.arity d, ?_⟩
  have h1 : (T.arity d) ^ k ≤ d ^ k := Nat.pow_le_pow_left (T.arity_le d) k
  have h2 : 2 ^ d ≤ T.cost d := cost_ge_two_pow T d
  have h3 : T.cost d ≤ cbudget (SATFamily (T.arity d)) := T.realizes d
  omega

/-- **Super-additive composition ⟹ `SAT ∉ P` (proved, conditional on the tower).**  Chaining the
reduction with the existing axiom-clean bridge.  The tower is an explicit hypothesis, not an
axiom — `cost_super` is the open no-sharing lemma. -/
theorem superAdditiveTower_implies_SAT_not_in_P (T : SuperAdditiveTower) :
    ¬ InP SATLang :=
  ComposablePpolyDischarge.sat_superpoly_cbudget_implies_SAT_not_in_P
    (superAdditiveTower_implies_superpoly T)

end PallLean.Paper93.DeepMath.PathB.SuperAdditiveComposition

#print axioms PallLean.Paper93.DeepMath.PathB.SuperAdditiveComposition.exp_beats_poly
#print axioms PallLean.Paper93.DeepMath.PathB.SuperAdditiveComposition.superAdditiveTower_implies_superpoly
#print axioms PallLean.Paper93.DeepMath.PathB.SuperAdditiveComposition.superAdditiveTower_implies_SAT_not_in_P
