import PallLean.PneqNP_v3
import PallLean.CoupledVerifier

/-!
Instance-aware compiled polynomial scaffold (paper-faithful direction).

This file keeps v3 untouched while introducing the instance-parameterized
objects needed by §12.
-/

open MvPolynomial TuringMachine PneqNP_v3 CoupledVerifier
open scoped BigOperators

namespace PneqNPv3

/-- NP instance payload used by the clause sheet. -/
structure SATInstance (N L : ℕ) where
  dcs : DisjointClauseSystem N L

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

/-- Existing machine-side constraints as polynomials. -/
noncomputable def tableauConstraintPolys (M : DTM) (n : ℕ) :
    List (MvPolynomial (CVar M n) ℚ) :=
  (constraintList M n ++ transitionConstraints M n).map LocalConstraint.poly

/-- Instance-dependent clause factors in compiled variable space. -/
noncomputable def clauseConstraintPolys
    (M : DTM) (n N L : ℕ)
    (inst : SATInstance N L)
    (E : ClauseEmbedData M n N L) :
    List (MvPolynomial (CVar M n) ℚ) :=
  ((Finset.univ : Finset (Fin L)).toList.map fun C =>
    renameCoupledIntoCompiled E (coupledFactor N L inst.dcs C))

/-- Full instance-aware compiled constraints (tableau ++ clause). -/
noncomputable def compiledConstraintPolys
    (M : DTM) (n N L : ℕ)
    (inst : SATInstance N L)
    (E : ClauseEmbedData M n N L) :
    List (MvPolynomial (CVar M n) ℚ) :=
  tableauConstraintPolys M n ++ clauseConstraintPolys M n N L inst E

/-- Raw violation polynomial on a list of polynomial constraints. -/
noncomputable def violationPolyRaw {V : Type*} [DecidableEq V]
    (constraints : List (MvPolynomial V ℚ)) : MvPolynomial V ℚ :=
  (constraints.map (fun p => p * p)).sum

/-- Instance-aware compiled violation polynomial (sum of squares). -/
noncomputable def compiledViolationPolyInst
    (M : DTM) (n N L : ℕ)
    (inst : SATInstance N L)
    (E : ClauseEmbedData M n N L) :
    MvPolynomial (CVar M n) ℚ :=
  violationPolyRaw (compiledConstraintPolys M n N L inst E)

/-- Factor-list decomposition by construction (tableau ++ clause). -/
theorem compiledConstraintPolys_append
    (M : DTM) (n N L : ℕ)
    (inst : SATInstance N L)
    (E : ClauseEmbedData M n N L) :
    compiledConstraintPolys M n N L inst E
      = tableauConstraintPolys M n ++ clauseConstraintPolys M n N L inst E := by
  rfl

/-- Clause part is exactly renamed coupled factors list. -/
theorem clauseConstraintPolys_eq_renamed_factors
    (M : DTM) (n N L : ℕ)
    (inst : SATInstance N L)
    (E : ClauseEmbedData M n N L) :
    clauseConstraintPolys M n N L inst E
      = ((Finset.univ : Finset (Fin L)).toList.map fun C =>
          renameCoupledIntoCompiled E (coupledFactor N L inst.dcs C)) := by
  rfl

end PneqNPv3
