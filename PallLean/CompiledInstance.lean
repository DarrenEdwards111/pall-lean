import PallLean.PneqNP_v3
import PallLean.CoupledVerifier

/-!
Instance-aware compiled polynomial scaffold (paper-faithful direction).

Goal: move from `compiledViolationPoly M n` to an object that can carry
instance-dependent clause gadgets.

This file is deliberately conservative: it introduces compile-safe definitions
without changing the existing v3 critical path yet.
-/

open MvPolynomial TuringMachine PneqNP_v3 CoupledVerifier
open scoped BigOperators

namespace PneqNPv3

/-- NP instance used by the clause sheet (currently a disjoint clause system). -/
abbrev SATInstance (N L : ℕ) := DisjointClauseSystem N L

/-- Compiled variable space (same as v3). -/
abbrev CVar (M : DTM) (n : ℕ) := Fin (numVars M n 0)

/-- Data to embed coupled vars into compiled vars. -/
structure ClauseEmbedData (M : DTM) (n N L : ℕ) where
  emb : Fin (N + L) → CVar M n
  emb_injective : Function.Injective emb

/-- Rename map from coupled space into compiled space. -/
noncomputable def renameCoupledIntoCompiled
    {M : DTM} {n N L : ℕ}
    (E : ClauseEmbedData M n N L) :
    MvPolynomial (Fin (N + L)) ℚ →ₐ[ℚ] MvPolynomial (CVar M n) ℚ :=
  MvPolynomial.rename E.emb

/-- Instance-dependent clause factors in compiled variable space. -/
noncomputable def clauseConstraintPolys
    (M : DTM) (n N L : ℕ)
    (inst : SATInstance N L)
    (E : ClauseEmbedData M n N L) :
    List (MvPolynomial (CVar M n) ℚ) :=
  ((Finset.univ : Finset (Fin L)).toList.map fun C =>
    renameCoupledIntoCompiled E (coupledFactor N L inst C))

/-- Existing machine-side constraints as polynomials. -/
noncomputable def tableauConstraintPolys (M : DTM) (n : ℕ) :
    List (MvPolynomial (CVar M n) ℚ) :=
  (constraintList M n ++ transitionConstraints M n).map LocalConstraint.poly

/-- Full instance-aware compiled constraints (tableau ++ clause). -/
noncomputable def compiledConstraintPolys
    (M : DTM) (n N L : ℕ)
    (inst : SATInstance N L)
    (E : ClauseEmbedData M n N L) :
    List (MvPolynomial (CVar M n) ℚ) :=
  tableauConstraintPolys M n ++ clauseConstraintPolys M n N L inst E

/-- Instance-aware compiled violation polynomial (product form scaffold). -/
noncomputable def compiledViolationPolyInst
    (M : DTM) (n N L : ℕ)
    (inst : SATInstance N L)
    (E : ClauseEmbedData M n N L) :
    MvPolynomial (CVar M n) ℚ :=
  (compiledConstraintPolys M n N L inst E).prod

/-- Factorization by construction: tableau part times clause part. -/
theorem compiledViolationPolyInst_factorization
    (M : DTM) (n N L : ℕ)
    (inst : SATInstance N L)
    (E : ClauseEmbedData M n N L) :
    compiledViolationPolyInst M n N L inst E
      = (tableauConstraintPolys M n).prod * (clauseConstraintPolys M n N L inst E).prod := by
  unfold compiledViolationPolyInst compiledConstraintPolys
  simp [List.prod_append]

end PneqNPv3
