import GodMoveBooleanInterpolation
import GodMovePinnedSATQueries

/-!
# A constructed semantic handshake for faithfully encoded SAT queries

The source is defined from actual clocked outputs of a `ComposableMachine`
on all assignment-pinned, correctly encoded CNF queries. The target is the
canonical Boolean characteristic polynomial of the signed CNF verifier.
Faithful SAT correctness proves the polynomials equal, hence their actual
strict and inclusive SPDP spaces/ranks agree for the same parameters.
Neither polynomial equality nor a rank bridge is a hypothesis.

This is a truth-table handshake, not the missing efficient God-Move compiler.
It uses `2^n` indexed assignments and provides an explicit common span of
dimension at most `2^n`, not polynomial dimension. The target has the Boolean
values of the signed clause product; it is not identified with an arbitrary
raw nonmultilinear gadget product. No comparison of this source's rank with
the original accumulator energy, or with polynomial runtime, is asserted.
-/

namespace GodMoveFaithfulHandshake

open MvPolynomial MultilinearSPDP SPDP
open GodMoveBooleanInterpolation GodMovePinnedSATQueries
open PallLean.Paper93.DeepMath.PathB
open ComposableMachine CookLevinReduction SeparationTarget

/-- A literal polynomial, including the default-false value outside the
finite assignment domain. The bounded-formula theorem below rules out that
out-of-range case for formulas used by the handshake. -/
noncomputable def literalPolynomial (n : ℕ) (l : Lit) : Poly n :=
  if h : l.1 < n then
    if l.2 then X ⟨l.1, h⟩ else 1 - X ⟨l.1, h⟩
  else if l.2 then 0 else 1

noncomputable def clausePolynomial (n : ℕ) (c : Clause) : Poly n :=
  1 - (c.map (fun l => 1 - literalPolynomial n l)).prod

/-- The ordinary multiplicative CNF verifier polynomial. It can have
nonmultilinear monomials when clauses share variables. -/
noncomputable def clauseProduct (n : ℕ) (φ : Formula) : Poly n :=
  (φ.map (clausePolynomial n)).prod

theorem literalPolynomial_eval {n : ℕ} (a : Assignment n) (l : Lit) :
    MvPolynomial.eval (booleanPoint a) (literalPolynomial n l) =
      bit (evalLit (extendAssignment a) l) := by
  unfold literalPolynomial evalLit extendAssignment
  split
  · rename_i h
    cases l.2 <;> cases ha : a ⟨l.1, h⟩ <;>
      simp [booleanPoint, bit, ha]
  · rename_i h
    cases l.2 <;> simp [bit]

theorem clausePolynomial_eval {n : ℕ} (a : Assignment n) (c : Clause) :
    MvPolynomial.eval (booleanPoint a) (clausePolynomial n c) =
      bit (evalClause (extendAssignment a) c) := by
  induction c with
  | nil => simp [clausePolynomial, evalClause, bit]
  | cons l c ih =>
    have heq : clausePolynomial n (l :: c) =
        1 - (1 - literalPolynomial n l) * (1 - clausePolynomial n c) := by
      simp [clausePolynomial]
    rw [heq, map_sub, map_one, map_mul, map_sub, map_one,
      literalPolynomial_eval, map_sub, map_one, ih]
    change 1 - (1 - bit (evalLit (extendAssignment a) l)) *
        (1 - bit (evalClause (extendAssignment a) c)) =
      bit (evalLit (extendAssignment a) l || evalClause (extendAssignment a) c)
    cases evalLit (extendAssignment a) l <;>
      cases evalClause (extendAssignment a) c <;> norm_num [bit]

theorem clauseProduct_eval {n : ℕ} (a : Assignment n) (φ : Formula) :
    MvPolynomial.eval (booleanPoint a) (clauseProduct n φ) =
      bit (evalFormula (extendAssignment a) φ) := by
  induction φ with
  | nil => simp [clauseProduct, evalFormula, bit]
  | cons c φ ih =>
    have heq : clauseProduct n (c :: φ) = clausePolynomial n c * clauseProduct n φ := by
      simp [clauseProduct]
    rw [heq, map_mul, clausePolynomial_eval, ih]
    change bit (evalClause (extendAssignment a) c) *
        bit (evalFormula (extendAssignment a) φ) =
      bit (evalClause (extendAssignment a) c && evalFormula (extendAssignment a) φ)
    cases evalClause (extendAssignment a) c <;>
      cases evalFormula (extendAssignment a) φ <;> norm_num [bit]

/-- Source coefficients are obtained from actual outputs on all pinned queries. -/
noncomputable def machineQueryPolynomial {n : ℕ}
    (M : Machine) (T : ℕ → ℕ) (φ : Formula) : Poly n :=
  interpolate (fun a : Assignment n => queryOutput M T φ a)

/-- Boolean characteristic polynomial of the signed clause-product verifier. -/
noncomputable def verifierCharacteristic (n : ℕ) (φ : Formula) : Poly n :=
  interpolate (fun a : Assignment n => evalFormula (extendAssignment a) φ)

/-- The Boolean characteristic target agrees with the literal product on the cube.
This is not an equality with the raw product away from the Boolean cube. -/
theorem verifierCharacteristic_eval_eq_clauseProduct {n : ℕ}
    (φ : Formula) (a : Assignment n) :
    MvPolynomial.eval (booleanPoint a) (verifierCharacteristic n φ) =
      MvPolynomial.eval (booleanPoint a) (clauseProduct n φ) := by
  rw [verifierCharacteristic, eval_interpolate, clauseProduct_eval]

/-- The handshake is derived from faithful operational correctness. -/
theorem machineQueryPolynomial_eq_verifierCharacteristic {n : ℕ}
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (φ : Formula) (hvars : VariablesBelow n φ) :
    machineQueryPolynomial (n := n) M T φ = verifierCharacteristic n φ := by
  apply interpolate_congr
  intro a
  exact queryOutput_eq_eval M T hD φ hvars a

/-- Every selected derivative/shift row is identical on the two constructed sides. -/
theorem handshake_row_eq {n : ℕ}
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (φ : Formula) (hvars : VariablesBelow n φ)
    (S : List (Fin n)) (shift : Poly n) :
    mlProj (shift * iterDerivList S (machineQueryPolynomial (n := n) M T φ)) =
      mlProj (shift * iterDerivList S (verifierCharacteristic n φ)) := by
  rw [machineQueryPolynomial_eq_verifierCharacteristic M T hD φ hvars]

theorem handshake_strict_rank_eq {n : ℕ}
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (φ : Formula) (hvars : VariablesBelow n φ)
    (B : BlockPartition n) (kappa ell : ℕ) :
    mlBlockedSpdpRank B kappa ell (machineQueryPolynomial (n := n) M T φ) =
      mlBlockedSpdpRank B kappa ell (verifierCharacteristic n φ) := by
  rw [machineQueryPolynomial_eq_verifierCharacteristic M T hD φ hvars]

theorem handshake_inclusive_rank_eq {n : ℕ}
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (φ : Formula) (hvars : VariablesBelow n φ)
    (B : BlockPartition n) (kappa ell : ℕ) :
    mlBlockedSpdpRankInc B kappa ell (machineQueryPolynomial (n := n) M T φ) =
      mlBlockedSpdpRankInc B kappa ell (verifierCharacteristic n φ) := by
  rw [machineQueryPolynomial_eq_verifierCharacteristic M T hD φ hvars]

/-- Both sides use one explicitly constructed common span. Its verified
budget is exponential, so this is not the missing polynomial common span. -/
theorem handshake_common_span {n : ℕ}
    (M : Machine) (T : ℕ → ℕ) (φ : Formula)
    (B : BlockPartition n) (kappa ell : ℕ) :
    mlBlockedSpdpSubspace B kappa ell (machineQueryPolynomial (n := n) M T φ) ≤
        universalSpan n ∧
      mlBlockedSpdpSubspace B kappa ell (verifierCharacteristic n φ) ≤
        universalSpan n ∧
      Module.finrank ℚ (universalSpan n) ≤ 2 ^ n := by
  exact ⟨strict_subspace_le_universalSpan B kappa ell _,
    strict_subspace_le_universalSpan B kappa ell _, universalSpan_finrank_le_two_pow n⟩

/-- Regression guard: signed contradictory unit clauses are a real UNSAT
example, but their ordinary clause product is not the zero polynomial. -/
def contradictoryUnits : Formula := [[(0, true)], [(0, false)]]

theorem contradictoryUnits_raw_product :
    clauseProduct 1 contradictoryUnits = (X 0 : Poly 1) * (1 - X 0) := by
  simp [clauseProduct, contradictoryUnits, clausePolynomial, literalPolynomial]

theorem contradictoryUnits_characteristic_zero :
    verifierCharacteristic 1 contradictoryUnits = 0 := by
  have hfalse : (fun a : Assignment 1 => evalFormula (extendAssignment a) contradictoryUnits) =
      (fun _ => false) := by
    funext a
    cases ha : a 0 <;>
      simp [evalFormula, contradictoryUnits, evalClause, evalLit, extendAssignment, ha]
  rw [verifierCharacteristic, hfalse]
  simp [interpolate, Step4Compiler.chi_phi]

/-- Boolean agreement must not be promoted to equality with the raw product. -/
theorem characteristic_not_always_raw_product :
    verifierCharacteristic 1 contradictoryUnits ≠ clauseProduct 1 contradictoryUnits := by
  rw [contradictoryUnits_characteristic_zero, contradictoryUnits_raw_product]
  intro h
  have heval := congrArg (MvPolynomial.eval (fun _ : Fin 1 => (2 : ℚ))) h
  norm_num at heval

end GodMoveFaithfulHandshake

#print axioms GodMoveFaithfulHandshake.clauseProduct_eval
#print axioms GodMoveFaithfulHandshake.machineQueryPolynomial_eq_verifierCharacteristic
#print axioms GodMoveFaithfulHandshake.handshake_row_eq
#print axioms GodMoveFaithfulHandshake.handshake_strict_rank_eq
#print axioms GodMoveFaithfulHandshake.handshake_inclusive_rank_eq
#print axioms GodMoveFaithfulHandshake.handshake_common_span
#print axioms GodMoveFaithfulHandshake.characteristic_not_always_raw_product
