import PallLean.Paper93.Paper283.RouteBProjectedPWindowAssembly

/-!
# Route B projected P-window control proof

This file sharpens the remaining projected P-window control obligation for
the PiPhi/head-span gauge.  The broad containment reduces to a pointwise row
identity: every generator row of the selected projected P-window must be the
chosen quotient projection of the corresponding zero-profile shifted
base-product row.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine
open WithinProfileBound
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Minimal remaining row identity for the PiPhi/head-span projected P-window.

For each generator row queried by `mlBlockedSpdpSubspace` at the P-window
parameters, the selected PiPhi/head-span projected row must agree with the
quotient projection of the matching zero-profile shifted base-product row.

This is intentionally pointwise and specific to the PiPhi/head-span gauge; it
does not introduce a broad policy interface for arbitrary gauges. -/
def RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileRowIdentity
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
  (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat) : Prop :=
  ∀ (S : List (Fin n)) (shift : MvPolynomial (Fin n) Rat),
    S.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    shift.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S →
    mlProj
        (shift * SPDP.iterDerivList S
          ((routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) =
      project
        (mlProj
          (shift *
            Finset.univ.prod
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i)))

/-- The factor-list product appearing in the zero-profile row identity is
exactly the local product-form Cook-Levin `compiledPoly`. -/
theorem routeB_cookLevinFactorList_univ_prod_eq_compiledPoly
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Finset.univ.prod
        (fun i : Fin (cookLevinFactorList M n hn2 htb hns).length =>
          (cookLevinFactorList M n hn2 htb hns).get i) =
      compiledPoly (cook_levin_compilation M n hn2 htb hns) := by
  classical
  let factors : List (MvPolynomial (Fin n) Rat) :=
    cookLevinFactorList M n hn2 htb hns
  have hcompiled :
      compiledPoly (cook_levin_compilation M n hn2 htb hns) = factors.prod := by
    simpa [factors, cookLevinFactorList] using
      compiledPoly_eq_constraints_prod M n hn2 htb hns
  have hfin :
      factors.prod =
        Finset.univ.prod (fun i : Fin factors.length => factors.get i) := by
    rw [← Fin.prod_univ_getElem]
    simp [List.get_eq_getElem]
  simpa [factors] using (hcompiled.trans hfin).symm

/-- Compiled form of the remaining PiPhi/head-span row identity.

After rewriting the zero-profile base product, the gate is not a factor-list
bookkeeping issue: it asks the selected projected row of the differentiated
candidate-projected `compiledPoly` to equal the quotient projection of the
undifferentiated shifted `compiledPoly` row. -/
def RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowCompiledDerivativeErasure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat) : Prop :=
  ∀ (S : List (Fin n)) (shift : MvPolynomial (Fin n) Rat),
    S.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    shift.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S →
    mlProj
        (shift * SPDP.iterDerivList S
          ((routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) =
      project
        (mlProj
          (shift * cookLevinZeroProfileBaseProduct M n hn2 htb hns))

/-- The original row identity is equivalent to the compiled derivative-erasure
form.  This isolates the exact algebraic content left after unfolding the
Cook-Levin factor list: the missing step is the derivative-erasure/extraction
identity, not `compiledPoly` bookkeeping. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowZeroProfileRowIdentity_iff_compiledDerivativeErasure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat) :
    RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileRowIdentity
        M n hn2 htb hns project ↔
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowCompiledDerivativeErasure
        M n hn2 htb hns project := by
  constructor
  · intro hrow S shift hSlen hshiftDegree hshiftVars hadm
    rw [hrow S shift hSlen hshiftDegree hshiftVars hadm]
    simp [cookLevinZeroProfileBaseProduct]
  · intro herase S shift hSlen hshiftDegree hshiftVars hadm
    rw [herase S shift hSlen hshiftDegree hshiftVars hadm]
    simp [cookLevinZeroProfileBaseProduct]

/-- Projection-commutation half of the compiled derivative-erasure gate.

This is the part controlled by the PiPhi/head-span retarget package: the
differentiated generator row of the projected Cook-Levin polynomial is the
PiPhi/head-span projection of the differentiated generator row of the
unprojected Cook-Levin polynomial. -/
def RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowCompiledDerivativeProjectionCommutation
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  ∀ (S : List (Fin n)) (shift : MvPolynomial (Fin n) Rat),
    S.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    shift.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S →
    mlProj
        (shift * SPDP.iterDerivList S
          ((routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) =
      (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)
        (mlProj
          (shift * SPDP.iterDerivList S
            (compiledPoly (cook_levin_compilation M n hn2 htb hns))))

/-- Exact remaining unprojected derivative-erasure condition after the
PiPhi/head-span projection has been applied.  Together with the commutation
half above, this is precisely the compiled derivative-erasure row identity. -/
def RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowUnprojectedDerivativeErasureAfterProjection
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  ∀ (S : List (Fin n)) (shift : MvPolynomial (Fin n) Rat),
    S.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    shift.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S →
    (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)
        (mlProj
          (shift * SPDP.iterDerivList S
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) =
      (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)
        (mlProj
          (shift * cookLevinZeroProfileBaseProduct M n hn2 htb hns))

/-- The after-projection derivative-erasure gate is exactly the statement that
the selected PiPhi/head-span projection kills the compiled derivative residual.

This is the smallest algebraic core left after unfolding the zero-profile base
product: for every log-window generator query, the residual row
`mlProj (shift * (∂_S compiledPoly - compiledPoly))` must lie in the kernel of
the chosen PiPhi/head-span projection. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowUnprojectedDerivativeErasureAfterProjection_iff_projectedCompiledDerivativeResidual_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowUnprojectedDerivativeErasureAfterProjection
        M n hn2 htb hns ↔
      ∀ (S : List (Fin n)) (shift : MvPolynomial (Fin n) Rat),
        S.length = Nat.log 2 n →
        shift.totalDegree ≤ Nat.log 2 n →
        shift.vars ⊆ S.toFinset →
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S →
        let p : MvPolynomial (Fin n) Rat :=
          compiledPoly (cook_levin_compilation M n hn2 htb hns)
        (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)
          (mlProj (shift * (SPDP.iterDerivList S p - p))) = 0 := by
  classical
  constructor
  · intro herase S shift hSlen hshiftDegree hshiftVars hadm
    let Pi := routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns
    let p : MvPolynomial (Fin n) Rat :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    have hbase : cookLevinZeroProfileBaseProduct M n hn2 htb hns = p := by
      simpa [p] using cookLevinZeroProfileBaseProduct_eq_compiledPoly M n hn2 htb hns
    have hrow0 := herase S shift hSlen hshiftDegree hshiftVars hadm
    change
      Pi (mlProj (shift * SPDP.iterDerivList S p)) =
        Pi (mlProj (shift * cookLevinZeroProfileBaseProduct M n hn2 htb hns)) at hrow0
    rw [hbase] at hrow0
    have hrow :
        Pi (mlProj (shift * SPDP.iterDerivList S p)) =
          Pi (mlProj (shift * p)) :=
      hrow0
    have hml :
        mlProj (shift * (SPDP.iterDerivList S p - p)) =
          mlProj (shift * SPDP.iterDerivList S p) -
            mlProj (shift * p) := by
      rw [mul_sub]
      change (MultilinearSPDP.mlProjHom Rat)
          (shift * SPDP.iterDerivList S p - shift * p) =
        (MultilinearSPDP.mlProjHom Rat)
            (shift * SPDP.iterDerivList S p) -
          (MultilinearSPDP.mlProjHom Rat) (shift * p)
      rw [map_sub]
    change Pi (mlProj (shift * (SPDP.iterDerivList S p - p))) = 0
    rw [hml, map_sub, hrow, sub_self]
  · intro hres S shift hSlen hshiftDegree hshiftVars hadm
    let Pi := routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns
    let p : MvPolynomial (Fin n) Rat :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    have hbase : cookLevinZeroProfileBaseProduct M n hn2 htb hns = p := by
      simpa [p] using cookLevinZeroProfileBaseProduct_eq_compiledPoly M n hn2 htb hns
    have hml :
        mlProj (shift * (SPDP.iterDerivList S p - p)) =
          mlProj (shift * SPDP.iterDerivList S p) -
            mlProj (shift * p) := by
      rw [mul_sub]
      change (MultilinearSPDP.mlProjHom Rat)
          (shift * SPDP.iterDerivList S p - shift * p) =
        (MultilinearSPDP.mlProjHom Rat)
            (shift * SPDP.iterDerivList S p) -
          (MultilinearSPDP.mlProjHom Rat) (shift * p)
      rw [map_sub]
    have hkernel :
        Pi (mlProj (shift * (SPDP.iterDerivList S p - p))) = 0 := by
      simpa [Pi, p, hml] using
        hres S shift hSlen hshiftDegree hshiftVars hadm
    rw [hml, map_sub] at hkernel
    have hrow :
        Pi (mlProj (shift * SPDP.iterDerivList S p)) -
          Pi (mlProj (shift * p)) = 0 :=
      hkernel
    change
      Pi (mlProj (shift * SPDP.iterDerivList S p)) =
        Pi (mlProj (shift * cookLevinZeroProfileBaseProduct M n hn2 htb hns))
    rw [hbase]
    exact sub_eq_zero.mp hrow

/-- Forward-use form of the residual reduction: it is enough to prove that the
PiPhi/head-span projection kills the compiled derivative residual row. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowUnprojectedDerivativeErasureAfterProjection_of_projectedCompiledDerivativeResidual_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hres :
      ∀ (S : List (Fin n)) (shift : MvPolynomial (Fin n) Rat),
        S.length = Nat.log 2 n →
        shift.totalDegree ≤ Nat.log 2 n →
        shift.vars ⊆ S.toFinset →
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S →
        let p : MvPolynomial (Fin n) Rat :=
          compiledPoly (cook_levin_compilation M n hn2 htb hns)
        (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)
          (mlProj (shift * (SPDP.iterDerivList S p - p))) = 0) :
    RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowUnprojectedDerivativeErasureAfterProjection
      M n hn2 htb hns :=
  (routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowUnprojectedDerivativeErasureAfterProjection_iff_projectedCompiledDerivativeResidual_zero
    M n hn2 htb hns).mpr hres

/-- Empty-generator descent turns a pre-`mlProj` kernel residual into the
projected compiled derivative-residual zero row.

This is the narrowest reduction supplied by the existing head-span retarget
package: `retarget.projection_descent` applied to the empty derivative list and
unit shift says the PiPhi/head-span kernel is stable under `mlProj`.  Therefore
the remaining algebra is not another projection-commutation fact; it is exactly
the pre-`mlProj` kernel membership of
`shift * (∂_S compiledPoly - compiledPoly)`. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_projectedCompiledDerivativeResidual_zero_of_retarget_of_unprojectedResidual_kernel
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (retarget :
      RouteBPaperFaithfulPiPhiHeadSpanProjectionRetarget
        M n hn2 htb hns)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) Rat)
    (hkernel :
      let p : MvPolynomial (Fin n) Rat :=
        compiledPoly (cook_levin_compilation M n hn2 htb hns)
      shift * (SPDP.iterDerivList S p - p) ∈
        LinearMap.ker
          (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)) :
    let p : MvPolynomial (Fin n) Rat :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)
      (mlProj (shift * (SPDP.iterDerivList S p - p))) = 0 := by
  classical
  let Pi := routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns
  let p : MvPolynomial (Fin n) Rat :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let residual : MvPolynomial (Fin n) Rat :=
    shift * (SPDP.iterDerivList S p - p)
  have hkernel' : Pi residual = 0 := by
    simpa [Pi, p, residual, LinearMap.mem_ker] using hkernel
  have hadm_empty :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        ([] : List (Fin n)) := by
    constructor
    · simp
    · intro b
      simp
  let L :=
    routeBSPDPGeneratorRowLinearMap M n hn2 htb hns
      ([] : List (Fin n)) (1 : MvPolynomial (Fin n) Rat)
  have hdesc : Pi.comp L = (Pi.comp L).comp Pi := by
    simpa [Pi, L, routeBPaperFaithfulPiPhiHeadSpanProjection,
      routeBPaperFaithfulPiPhiHeadSpanGauge,
      routeBPaperFaithfulPiPhiHeadSpanTail] using
      retarget.projection_descent
        0 0 ([] : List (Fin n)) (1 : MvPolynomial (Fin n) Rat)
        (by simp)
        (by simp [MvPolynomial.totalDegree_one])
        (by simp)
        (by simp [MvPolynomial.totalDegree_one])
        (by simp [MvPolynomial.vars_one])
        hadm_empty
  have hpoint := congrArg (fun F : _ →ₗ[Rat] _ => F residual) hdesc
  have hpoint' : Pi (L residual) = Pi (L (Pi residual)) := by
    simpa [LinearMap.comp_apply] using hpoint
  have hL_residual : L residual = mlProj residual := by
    simp [L, routeBSPDPGeneratorRowLinearMap_apply, routeBSPDPGeneratorRow,
      SPDP.iterDerivList]
  change Pi (mlProj residual) = 0
  calc
    Pi (mlProj residual) = Pi (L residual) := by rw [hL_residual]
    _ = Pi (L (Pi residual)) := hpoint'
    _ = 0 := by simp [hkernel']

/-- The retarget package closes the projection-commutation half of the
compiled derivative-erasure gate for the intended PiPhi/head-span projection.

Row closure makes the generator row of the projected base fixed by the
finite-row projection, while projection descent identifies that fixed row with
the projection of the unprojected differentiated generator row. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowCompiledDerivativeProjectionCommutation_of_retarget
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (retarget :
      RouteBPaperFaithfulPiPhiHeadSpanProjectionRetarget
        M n hn2 htb hns) :
    RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowCompiledDerivativeProjectionCommutation
      M n hn2 htb hns := by
  classical
  intro S shift hSlen hshiftDegree hshiftVars hadm
  let rows := routeBPaperFaithfulPiPhiHeadSpanRows M n hn2 htb hns
  let Pi := routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns
  let p := compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let L := routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift
  have hSlog : S.length ≤ Nat.log 2 n := le_of_eq hSlen
  have hrowClosure :
      forall i,
        routeBSPDPGeneratorRow M n hn2 htb hns (rows i) S shift
          ∈ finiteRowsSubmodule rows := by
    intro i
    exact
      retarget.row_closure.row_closure
        (Nat.log 2 n) (Nat.log 2 n) S shift
        hSlen hshiftDegree le_rfl le_rfl hshiftVars hadm i
  have hmem :
      L (Pi p) ∈ finiteRowsSubmodule rows := by
    simpa [L, Pi, p, rows, routeBSPDPGeneratorRowLinearMap_apply,
      routeBPaperFaithfulPiPhiHeadSpanProjection,
      routeBPaperFaithfulPiPhiHeadSpanGauge,
      routeBPaperFaithfulPiPhiHeadSpanRows,
      routeBPaperFaithfulPiPhiHeadSpanTail] using
      routeBSPDPGeneratorRow_projected_mem_finiteRowsSubmodule_of_rowClosure
        M n hn2 htb hns rows p S shift hrowClosure
  have hfixed : Pi (L (Pi p)) = L (Pi p) := by
    simpa [Pi, rows, routeBPaperFaithfulPiPhiHeadSpanProjection,
      routeBPaperFaithfulPiPhiHeadSpanGauge,
      routeBPaperFaithfulPiPhiHeadSpanRows,
      routeBPaperFaithfulPiPhiHeadSpanTail] using
      routeBRicherFiniteRowsCandidateGauge_fixed_of_mem
        M n hn2 htb hns rows hmem
  have hdesc :
      Pi.comp L = (Pi.comp L).comp Pi := by
    simpa [Pi, L, routeBPaperFaithfulPiPhiHeadSpanProjection,
      routeBPaperFaithfulPiPhiHeadSpanGauge,
      routeBPaperFaithfulPiPhiHeadSpanTail] using
      retarget.projection_descent
        (Nat.log 2 n) (Nat.log 2 n) S shift
        hSlen hshiftDegree hSlog hshiftDegree hshiftVars hadm
  have hpoint : L (Pi p) = Pi (L p) := by
    have hdescPoint := congrArg (fun F : _ →ₗ[Rat] _ => F p) hdesc
    calc
      L (Pi p) = Pi (L (Pi p)) := hfixed.symm
      _ = Pi (L p) := by
        simpa [LinearMap.comp_apply] using hdescPoint.symm
  simpa [Pi, p, L, routeBSPDPGeneratorRowLinearMap_apply,
    routeBSPDPGeneratorRow] using hpoint

/-- Retarget commutation plus the exact after-projection unprojected
derivative-erasure condition proves the compiled derivative-erasure identity
for the intended PiPhi/head-span projection. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowCompiledDerivativeErasure_of_retarget_of_unprojectedDerivativeErasureAfterProjection
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (retarget :
      RouteBPaperFaithfulPiPhiHeadSpanProjectionRetarget
        M n hn2 htb hns)
    (herase :
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowUnprojectedDerivativeErasureAfterProjection
        M n hn2 htb hns) :
    RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowCompiledDerivativeErasure
      M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns) := by
  intro S shift hSlen hshiftDegree hshiftVars hadm
  calc
    mlProj
        (shift * SPDP.iterDerivList S
          ((routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) =
      (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)
        (mlProj
          (shift * SPDP.iterDerivList S
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) :=
        routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowCompiledDerivativeProjectionCommutation_of_retarget
          M n hn2 htb hns retarget S shift hSlen hshiftDegree hshiftVars hadm
    _ =
      (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)
        (mlProj
          (shift * cookLevinZeroProfileBaseProduct M n hn2 htb hns)) :=
        herase S shift hSlen hshiftDegree hshiftVars hadm

/-- Retarget commutation plus the exact after-projection unprojected
derivative-erasure condition proves the original zero-profile row identity for
the intended PiPhi/head-span projection. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowZeroProfileRowIdentity_of_retarget_of_unprojectedDerivativeErasureAfterProjection
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (retarget :
      RouteBPaperFaithfulPiPhiHeadSpanProjectionRetarget
        M n hn2 htb hns)
    (herase :
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowUnprojectedDerivativeErasureAfterProjection
        M n hn2 htb hns) :
    RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileRowIdentity
      M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns) :=
  (routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowZeroProfileRowIdentity_iff_compiledDerivativeErasure
    M n hn2 htb hns
    (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)).mpr
    (routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowCompiledDerivativeErasure_of_retarget_of_unprojectedDerivativeErasureAfterProjection
      M n hn2 htb hns retarget herase)

/-- Exact generator-membership reduction for the PiPhi/head-span projected
P-window containment. -/
def RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileGeneratorReduction
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat) : Prop :=
  ∀ (S : List (Fin n)) (shift : MvPolynomial (Fin n) Rat),
    S.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    shift.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S →
    mlProj
        (shift * SPDP.iterDerivList S
          ((routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) ∈
      zeroProfileProjectedShiftSpan (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project

/-- The pointwise row identity gives membership of every projected P-window
generator in the projected zero-profile shifted span. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowGenerator_mem_zeroProfileProjection
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)
    (hrow :
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileRowIdentity
        M n hn2 htb hns project)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) Rat)
    (hSlen : S.length = Nat.log 2 n)
    (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
    (hshiftVars : shift.vars ⊆ S.toFinset)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition S) :
    mlProj
        (shift * SPDP.iterDerivList S
          ((routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) ∈
      zeroProfileProjectedShiftSpan (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project := by
  classical
  have hzero :
      mlProj
          (shift *
            Finset.univ.prod
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) ∈
        zeroProfileShiftImageSet (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) := by
    simp only [zeroProfileShiftImageSet, Set.mem_iUnion,
      Set.mem_singleton_iff]
    exact ⟨S, le_of_eq hSlen, shift, hshiftVars, rfl⟩
  have hproject :
      project
          (mlProj
            (shift *
              Finset.univ.prod
                (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) ∈
        zeroProfileProjectedShiftSpan (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
          project := by
    exact Submodule.mem_map_of_mem (Submodule.subset_span hzero)
  rw [hrow S shift hSlen hshiftDegree hshiftVars hadm]
  exact hproject

/-- The original broad containment is exactly the generator-by-generator
zero-profile membership check. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowControlledByZeroProfileProjection_iff_generatorReduction
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat) :
    RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns project ↔
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileGeneratorReduction
        M n hn2 htb hns project := by
  classical
  constructor
  · intro hcontrol S shift hSlen hshiftDegree hshiftVars hadm
    have hle :
        routeBRicherGaugeProjectedPWindowSubspace M n hn2 htb hns
            (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns) ≤
          zeroProfileProjectedShiftSpan (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
            project := by
      simpa [RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowControlledByZeroProfileProjection,
        RouteBProjectedPWindowControlledByZeroProfileProjection] using
        hcontrol
    apply hle
    unfold routeBRicherGaugeProjectedPWindowSubspace
    unfold mlBlockedSpdpSubspace
    exact Submodule.subset_span
      ⟨S, shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩
  · intro hgen
    rw [RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowControlledByZeroProfileProjection,
      RouteBProjectedPWindowControlledByZeroProfileProjection]
    unfold routeBRicherGaugeProjectedPWindowSubspace
    unfold mlBlockedSpdpSubspace
    refine Submodule.span_le.mpr ?_
    intro q hq
    rcases hq with
      ⟨S, shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩
    exact hgen S shift hSlen hshiftDegree hshiftVars hadm

/-- The pointwise row identity proves the full projected P-window containment
needed by the projected zero-profile assembly. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowControlledByZeroProfileProjection_of_rowIdentity
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)
    (hrow :
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileRowIdentity
        M n hn2 htb hns project) :
    RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowControlledByZeroProfileProjection
      M n hn2 htb hns project := by
  exact
    (routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowControlledByZeroProfileProjection_iff_generatorReduction
      M n hn2 htb hns project).mpr
    (fun S shift hSlen hshiftDegree hshiftVars hadm =>
    routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowGenerator_mem_zeroProfileProjection
      M n hn2 htb hns project hrow S shift
      hSlen hshiftDegree hshiftVars hadm)

/-! ## Axiom audit anchors -/

#print axioms RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileRowIdentity
#print axioms routeB_cookLevinFactorList_univ_prod_eq_compiledPoly
#print axioms RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowCompiledDerivativeErasure
#print axioms routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowZeroProfileRowIdentity_iff_compiledDerivativeErasure
#print axioms RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowCompiledDerivativeProjectionCommutation
#print axioms RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowUnprojectedDerivativeErasureAfterProjection
#print axioms routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowUnprojectedDerivativeErasureAfterProjection_iff_projectedCompiledDerivativeResidual_zero
#print axioms routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowUnprojectedDerivativeErasureAfterProjection_of_projectedCompiledDerivativeResidual_zero
#print axioms routeBPaperFaithfulPiPhiHeadSpan_projectedCompiledDerivativeResidual_zero_of_retarget_of_unprojectedResidual_kernel
#print axioms routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowCompiledDerivativeProjectionCommutation_of_retarget
#print axioms routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowCompiledDerivativeErasure_of_retarget_of_unprojectedDerivativeErasureAfterProjection
#print axioms routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowZeroProfileRowIdentity_of_retarget_of_unprojectedDerivativeErasureAfterProjection
#print axioms RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileGeneratorReduction
#print axioms routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowGenerator_mem_zeroProfileProjection
#print axioms routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowControlledByZeroProfileProjection_iff_generatorReduction
#print axioms routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowControlledByZeroProfileProjection_of_rowIdentity

end PallLean.Paper93.Paper283
