import PallLean.Paper93.Paper283.BridgeADiagonalQuadraticRealization

/-!
# Finite-generator rank sandwiches for blocked SPDP subspaces

This file records the linear-algebra equality step behind finite row-polynomial
targets: if the blocked multilinear SPDP subspace is exactly the span of a
finite independent row family, witnessed by two inclusions, then its
`mlBlockedSpdpRank` is the number of rows.

The final section applies the theorem to the checked one-variable Bridge A
local polynomial example from `BridgeADiagonalQuadraticRealization`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open SPDP

attribute [local instance] Classical.dec

/-- A finite independent row family computes the exact blocked multilinear
SPDP rank whenever the blocked SPDP subspace is sandwiched between the span of
the family and the same span. -/
theorem mlBlockedSpdpRank_eq_card_of_span_sandwich
    {n m : Nat} {F : Type*} [Field F]
    (B : BlockPartition n) (kappa ell : Nat)
    (p : MvPolynomial (Fin n) F)
    (rows : Fin m -> MvPolynomial (Fin n) F)
    (hli : LinearIndependent F rows)
    (hspan_le :
      Submodule.span F (Set.range rows) <= mlBlockedSpdpSubspace B kappa ell p)
    (hle_span :
      mlBlockedSpdpSubspace B kappa ell p <= Submodule.span F (Set.range rows)) :
    mlBlockedSpdpRank B kappa ell p = m := by
  unfold mlBlockedSpdpRank
  have hsubspace :
      mlBlockedSpdpSubspace B kappa ell p =
        Submodule.span F (Set.range rows) :=
    le_antisymm hle_span hspan_le
  rw [hsubspace]
  simpa [Fintype.card_fin] using finrank_span_eq_card hli

/-- Bridge A per-vertex normalized local polynomial data from a finite
independent row-polynomial sandwich whose row count is `kappa * gadgetN`. -/
noncomputable def bridgeA_perVertexLocalPolynomialNormalized_of_rowSpanSandwich
    {N d : Nat}
    {alpha beta alpha0 : Real} {kappa gadgetN spdpVars : Nat}
    {G : PallLean.Paper93.Concrete.RegularGraphFixed N d}
    {chi : TseitinCharge N} {Phi : Fin N -> Real} {v : Fin N}
    (partition : BlockPartition spdpVars)
    (Qv : MvPolynomial (Fin spdpVars) Rat)
    (rows : Fin (kappa * gadgetN) -> MvPolynomial (Fin spdpVars) Rat)
    (hli : LinearIndependent Rat rows)
    (hspan_le :
      Submodule.span Rat (Set.range rows) <=
        mlBlockedSpdpSubspace partition kappa kappa Qv)
    (hle_span :
      mlBlockedSpdpSubspace partition kappa kappa Qv <=
        Submodule.span Rat (Set.range rows)) :
    BridgeAPerVertexLocalPolynomialNormalized
      alpha beta alpha0 kappa gadgetN G chi Phi v where
  spdpVars := spdpVars
  partition := partition
  Qv := Qv
  rank_eq_normalized :=
    mlBlockedSpdpRank_eq_card_of_span_sandwich
      partition kappa kappa Qv rows hli hspan_le hle_span

namespace BridgeADiagonalQuadraticRealization

/-- The row-polynomial family for the one-variable diagonal quadratic Bridge A
local target.  It has one row, the derivative row direction `X_0`. -/
noncomputable def oneVarDiagonalQuadratic_rowPolynomialFamily :
    Fin 1 -> MvPolynomial (Fin 1) Rat :=
  fun _ => X (0 : Fin 1)

theorem oneVarDiagonalQuadratic_rowPolynomialFamily_linearIndependent :
    LinearIndependent Rat oneVarDiagonalQuadratic_rowPolynomialFamily := by
  rw [linearIndependent_unique_iff]
  change (X (0 : Fin 1) : MvPolynomial (Fin 1) Rat) ≠ 0
  exact X_one_ne_zero

theorem oneVarDiagonalQuadratic_rowSpan_le_subspace :
    Submodule.span Rat (Set.range oneVarDiagonalQuadratic_rowPolynomialFamily) <=
      mlBlockedSpdpSubspace oneVarPartition 1 1 oneVarDiagonalQuadratic := by
  apply Submodule.span_le.mpr
  rintro q ⟨i, rfl⟩
  fin_cases i
  simpa [oneVarDiagonalQuadratic_rowPolynomialFamily] using
    X_mem_oneVarDiagonalQuadratic_subspace

theorem oneVarDiagonalQuadratic_subspace_le_rowSpan :
    mlBlockedSpdpSubspace oneVarPartition 1 1 oneVarDiagonalQuadratic <=
      Submodule.span Rat (Set.range oneVarDiagonalQuadratic_rowPolynomialFamily) := by
  have hupper := oneVarDiagonalQuadratic_sharpUpperContainment_holds
  intro q hq
  rcases Submodule.mem_span_singleton.mp (hupper hq) with ⟨c, hc⟩
  rw [← hc]
  exact Submodule.smul_mem _
    c (Submodule.subset_span ⟨(0 : Fin 1), by
      simp [oneVarDiagonalQuadratic_rowPolynomialFamily]⟩)

/-- The one-variable Bridge A local target, reproved by the finite-generator
rank-sandwich theorem. -/
theorem oneVarDiagonalQuadratic_exactRank_via_rowSpanSandwich :
    oneVarDiagonalQuadratic_exactRankTarget := by
  unfold oneVarDiagonalQuadratic_exactRankTarget
  simpa using
    mlBlockedSpdpRank_eq_card_of_span_sandwich
      oneVarPartition 1 1 oneVarDiagonalQuadratic
      oneVarDiagonalQuadratic_rowPolynomialFamily
      oneVarDiagonalQuadratic_rowPolynomialFamily_linearIndependent
      oneVarDiagonalQuadratic_rowSpan_le_subspace
      oneVarDiagonalQuadratic_subspace_le_rowSpan

/-- The exact `kappa = 1`, `gadgetN = 1` normalized Bridge A local-polynomial
package, with its rank equality supplied through the finite row sandwich. -/
noncomputable def oneVarDiagonalQuadratic_normalizedLocalPolynomial_via_rowSpanSandwich
    {N d : Nat} (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N) :
    BridgeAPerVertexLocalPolynomialNormalized
      alpha beta alpha0 1 1 G chi Phi v :=
  bridgeA_perVertexLocalPolynomialNormalized_of_rowSpanSandwich
    (alpha := alpha) (beta := beta) (alpha0 := alpha0)
    (kappa := 1) (gadgetN := 1)
    (G := G) (chi := chi) (Phi := Phi) (v := v)
    oneVarPartition oneVarDiagonalQuadratic
    oneVarDiagonalQuadratic_rowPolynomialFamily
    oneVarDiagonalQuadratic_rowPolynomialFamily_linearIndependent
    oneVarDiagonalQuadratic_rowSpan_le_subspace
    oneVarDiagonalQuadratic_subspace_le_rowSpan

end BridgeADiagonalQuadraticRealization

/-! ## Axiom audit anchors -/

#print axioms mlBlockedSpdpRank_eq_card_of_span_sandwich
#print axioms bridgeA_perVertexLocalPolynomialNormalized_of_rowSpanSandwich
#print axioms BridgeADiagonalQuadraticRealization.oneVarDiagonalQuadratic_exactRank_via_rowSpanSandwich
#print axioms BridgeADiagonalQuadraticRealization.oneVarDiagonalQuadratic_normalizedLocalPolynomial_via_rowSpanSandwich

end PallLean.Paper93.Paper283
