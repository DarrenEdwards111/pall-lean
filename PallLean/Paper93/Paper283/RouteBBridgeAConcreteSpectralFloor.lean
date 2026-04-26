import PallLean.Paper93.Paper283.RouteBBridgeASpectralLower
import PallLean.Paper93.Paper283.BridgeAConcreteGadget
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Data.Multiset.Sort

/-!
# Route B Bridge A concrete spectral floors

This file connects the finite-span Bridge A spectral-floor reduction to the
checked concrete matrix data already present for the compiled Cook-Levin
gadget.  The matrix-side input is the decomposition

`compiledGadget eta N = eta • I + L_{K_N}`,

where `L_{K_N}` is positive semidefinite.  A general affine-shift lemma shows
that a positive scalar identity shift of a PSD matrix has every Hermitian
eigenvalue at least the scalar floor.  The remaining Bridge A obligation is
therefore only the explicit budget inequality against the full index set.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.GraphSpectral
open PallLean.Paper93.DeepMath.LPS
open PallLean.Paper93.DeepMath.PathB

private theorem strictMono_const_add (c : Real) :
    StrictMono (fun x : Real => c + x) := by
  intro x y hxy
  linarith

/-- Positive identity shift of a PSD matrix is positive definite. -/
theorem const_smul_one_add_posSemidef_posDef {N : Nat}
    (c : Real) (M : Matrix (Fin N) (Fin N) Real)
    (hM : M.PosSemidef) (hc : 0 < c) :
    (c • (1 : Matrix (Fin N) (Fin N) Real) + M).PosDef := by
  have hshift : (c • (1 : Matrix (Fin N) (Fin N) Real)).PosDef :=
    (Matrix.PosDef.one).smul hc
  exact hshift.add_posSemidef hM

/-- Functional-calculus identity for adding a scalar multiple of the identity
to a Hermitian matrix. -/
theorem cfc_const_add_eq_const_smul_one_add {N : Nat}
    (c : Real) (M : Matrix (Fin N) (Fin N) Real)
    (hM : M.PosSemidef) :
    cfc (fun x : Real => c + x) M =
      c • (1 : Matrix (Fin N) (Fin N) Real) + M := by
  calc
    cfc (fun x : Real => c + x) M
        =
        (algebraMap Real (Matrix (Fin N) (Fin N) Real)) c +
          cfc (fun x : Real => 1 * x) M := by
          rw [show (fun x : Real => c + x) =
              (fun x : Real => c + 1 * x) by
            funext x
            ring]
          rw [cfc_const_add
            (R := Real) (A := Matrix (Fin N) (Fin N) Real)
            (p := IsSelfAdjoint)
            (r := c) (f := fun x : Real => 1 * x) (a := M)
            (ha := hM.1)]
    _ = c • (1 : Matrix (Fin N) (Fin N) Real) + M := by
          rw [cfc_const_mul_id
            (R := Real) (A := Matrix (Fin N) (Fin N) Real)
            (p := IsSelfAdjoint) (r := (1 : Real)) (a := M)
            (ha := hM.1)]
          rw [Algebra.algebraMap_eq_smul_one]
          simp

private theorem const_add_cfc_charpoly_eigenvalues₀ {N : Nat}
    (c : Real) (M : Matrix (Fin N) (Fin N) Real)
    (hM : M.PosSemidef) :
    (cfc (fun x : Real => c + x) M).charpoly =
      ∏ i : Fin (Fintype.card (Fin N)),
        (Polynomial.X -
          Polynomial.C ((c + hM.1.eigenvalues₀ i) : Real)) := by
  let e : Fin (Fintype.card (Fin N)) ≃ Fin N :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  have h :
      (cfc (fun x : Real => c + x) M).charpoly =
        ∏ i : Fin N,
          (Polynomial.X -
            Polynomial.C ((c + hM.1.eigenvalues i) : Real)) := by
    simpa using
      (Matrix.IsHermitian.charpoly_cfc_eq
        (A := M) (𝕜 := Real) hM.1 (fun x : Real => c + x))
  have hp :
      (∏ x : Fin N,
        (Polynomial.X -
          Polynomial.C ((c + hM.1.eigenvalues₀ (e.symm x)) : Real))) =
      ∏ i : Fin (Fintype.card (Fin N)),
        (Polynomial.X -
          Polynomial.C ((c + hM.1.eigenvalues₀ i) : Real)) := by
    simpa using
      (Equiv.prod_comp e.symm
        (fun i : Fin (Fintype.card (Fin N)) =>
          Polynomial.X -
            Polynomial.C ((c + hM.1.eigenvalues₀ i) : Real)))
  simpa [Matrix.IsHermitian.eigenvalues, e] using h.trans hp

private theorem const_add_cfc_roots_re_eigenvalues₀ {N : Nat}
    (c : Real) (M : Matrix (Fin N) (Fin N) Real)
    (hM : M.PosSemidef) :
    (cfc (fun x : Real => c + x) M).charpoly.roots.map
        RCLike.re =
      ((List.ofFn
        (fun i : Fin (Fintype.card (Fin N)) =>
          c + hM.1.eigenvalues₀ i) : List Real) :
        Multiset Real) := by
  have hroots :
      (cfc (fun x : Real => c + x) M).charpoly.roots =
        Multiset.map
          (fun i : Fin (Fintype.card (Fin N)) =>
            (c + hM.1.eigenvalues₀ i : Real)) Finset.univ.val := by
    rw [const_add_cfc_charpoly_eigenvalues₀ c M hM,
      Polynomial.roots_prod]
    · simp_rw [Polynomial.roots_X_sub_C]
      rw [Multiset.bind_singleton]
    · exact Finset.prod_ne_zero_iff.mpr
        (fun i _ => Polynomial.X_sub_C_ne_zero _)
  rw [hroots]
  simp [Fin.univ_val_map, Function.comp_def, RCLike.re]

private theorem const_smul_one_add_posSemidef_eigenvalues₀ {N : Nat}
    (c : Real) (M : Matrix (Fin N) (Fin N) Real)
    (hM : M.PosSemidef) (hc : 0 < c) :
    (const_smul_one_add_posSemidef_posDef c M hM hc).1.eigenvalues₀ =
      fun i : Fin (Fintype.card (Fin N)) =>
        c + hM.1.eigenvalues₀ i := by
  let B : Matrix (Fin N) (Fin N) Real :=
    c • (1 : Matrix (Fin N) (Fin N) Real) + M
  let hB : B.PosDef := const_smul_one_add_posSemidef_posDef c M hM hc
  have hroots :
      B.charpoly.roots.map RCLike.re =
        ((List.ofFn
          (fun i : Fin (Fintype.card (Fin N)) =>
            c + hM.1.eigenvalues₀ i) : List Real) :
          Multiset Real) := by
    change
      ((c • (1 : Matrix (Fin N) (Fin N) Real) + M).charpoly.roots.map
        RCLike.re = _)
    rw [show
        c • (1 : Matrix (Fin N) (Fin N) Real) + M =
          cfc (fun x : Real => c + x) M
        from (cfc_const_add_eq_const_smul_one_add c M hM).symm]
    exact const_add_cfc_roots_re_eigenvalues₀ c M hM
  have hsortB :
      (B.charpoly.roots.map RCLike.re).sort
          (fun x y : Real => x >= y) =
        List.ofFn hB.1.eigenvalues₀ :=
    hB.1.sort_roots_charpoly_eq_eigenvalues₀
  have hsortAff :
      (List.ofFn
        (fun i : Fin (Fintype.card (Fin N)) =>
          c + hM.1.eigenvalues₀ i)).SortedGE := by
    have hf : StrictMono (fun x : Real => c + x) :=
      strictMono_const_add c
    have hsortedM0 : (List.ofFn hM.1.eigenvalues₀).SortedGE :=
      Antitone.sortedGE_ofFn hM.1.eigenvalues₀_antitone
    have hmap := (hf.sortedGE_listMap
      (l := List.ofFn hM.1.eigenvalues₀)).2 hsortedM0
    simpa [List.map_ofFn, Function.comp_def] using hmap
  have hperm :
      (List.ofFn hB.1.eigenvalues₀).Perm
        (List.ofFn
          (fun i : Fin (Fintype.card (Fin N)) =>
            c + hM.1.eigenvalues₀ i)) := by
    apply Multiset.coe_eq_coe.mp
    rw [← hsortB]
    rw [Multiset.sort_eq]
    exact hroots
  have hlist :
      List.ofFn hB.1.eigenvalues₀ =
        List.ofFn
          (fun i : Fin (Fintype.card (Fin N)) =>
            c + hM.1.eigenvalues₀ i) := by
    exact List.Perm.eq_of_sortedGE
      (Antitone.sortedGE_ofFn hB.1.eigenvalues₀_antitone)
      hsortAff hperm
  exact List.ofFn_inj.mp hlist

/-- Eigenvalues of `c • I + M` are the scalar shift of eigenvalues of `M`,
for `M` PSD and `c > 0`. -/
theorem const_smul_one_add_posSemidef_eigenvalues {N : Nat}
    (c : Real) (M : Matrix (Fin N) (Fin N) Real)
    (hM : M.PosSemidef) (hc : 0 < c) :
    ∀ i,
      (const_smul_one_add_posSemidef_posDef c M hM hc).1.eigenvalues i =
        c + hM.1.eigenvalues i := by
  have h0 := const_smul_one_add_posSemidef_eigenvalues₀ c M hM hc
  intro i
  simp [Matrix.IsHermitian.eigenvalues, h0]

/-- Matrix-side eigenvalue floor certificate for a positive identity shift of
a PSD matrix. -/
theorem eigenvalue_floor_const_smul_one_add_posSemidef {N : Nat}
    (c : Real) (M : Matrix (Fin N) (Fin N) Real)
    (hM : M.PosSemidef) (hc : 0 < c) :
    ∀ i,
      c <=
        (const_smul_one_add_posSemidef_posDef c M hM hc).posSemidef.1.eigenvalues i := by
  intro i
  change c <=
    (const_smul_one_add_posSemidef_posDef c M hM hc).1.eigenvalues i
  rw [const_smul_one_add_posSemidef_eigenvalues c M hM hc i]
  exact le_add_of_nonneg_right (Matrix.PosSemidef.eigenvalues_nonneg hM i)

/-- The complete-graph Laplacian used inside `compiledGadget` is PSD. -/
theorem completeAdj_laplacian_posSemidef (N : Nat) :
    (laplacian (completeAdj N)).PosSemidef := by
  exact laplacian_posSemidef_of_symm_nonneg
    (completeAdj N) (completeAdj_symm N) (completeAdj_nonneg_pathB N)

/-- Positive coupling makes the concrete compiled gadget PSD.  This proof is
the one used by the spectral-floor theorem below, via the decomposition
`compiledGadget eta N = eta • I + L_{K_N}`. -/
theorem compiledGadget_posSemidef_of_positive_coupling {N : Nat}
    (eta : Real) (heta : 0 < eta) :
    (compiledGadget eta N).PosSemidef :=
  (const_smul_one_add_posSemidef_posDef
    eta (laplacian (completeAdj N))
    (completeAdj_laplacian_posSemidef N) heta).posSemidef

/-- The concrete compiled gadget has eigenvalue floor equal to its positive
identity-shift coupling. -/
theorem compiledGadget_eigenvalue_floor {N : Nat}
    (eta : Real) (heta : 0 < eta)
    (hA : (compiledGadget eta N).PosSemidef) :
    ∀ i,
      eta <= hA.1.eigenvalues i := by
  let hConcrete : (compiledGadget eta N).PosSemidef :=
    compiledGadget_posSemidef_of_positive_coupling eta heta
  have hproof : hA = hConcrete := Subsingleton.elim hA hConcrete
  rw [hproof]
  exact
    eigenvalue_floor_const_smul_one_add_posSemidef
      eta (laplacian (completeAdj N))
      (completeAdj_laplacian_posSemidef N) heta

/-- Bridge A shifted-logdet lower package for the concrete compiled-gadget
matrix.  The spectral floor is proved from the decomposition
`compiledGadget eta N = eta • I + L_{K_N}`; the only remaining spectral
quantity is the explicit full-span budget. -/
theorem bridgeA_rankLogDetLowerHypotheses_of_compiledGadget_spectral_floor
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    {eta theta rankLogRate delta : Real}
    (heta : 0 < eta) (htheta : 0 < theta)
    (hrate_nonneg : 0 <= rankLogRate)
    (hdelta_rate : delta <= rankLogRate * (kappa : Real))
    (hbudget :
      rankLogRate *
          ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
            (gadgetFamily v).rank) : Real) <=
        (N : Real) * Real.log (1 + theta * eta)) :
    BridgeARankLogDetLowerHypotheses
      alpha beta alpha0 kappa G chi Phi gadgetFamily rankLogRate
      (Real.log
        (((1 : Matrix (Fin N) (Fin N) Real) +
          theta • (compiledGadget eta N)).det))
      delta := by
  let hA : (compiledGadget eta N).PosSemidef :=
    compiledGadget_posSemidef_of_positive_coupling eta heta
  have hfloor :
      ∀ i : Fin N, eta <= hA.1.eigenvalues i := by
    exact compiledGadget_eigenvalue_floor eta heta hA
  exact
    bridgeA_rankLogDetLowerHypotheses_of_shifted_logdet_uniform_eigenvalue_floor
      alpha beta alpha0 kappa G chi Phi gadgetFamily
      (compiledGadget eta N) hA
      htheta hrate_nonneg hdelta_rate heta.le hfloor hbudget

/-- Cook-Levin pocket-gadget specialization of the compiled-gadget spectral
floor package.  The rank sum is unfolded to the uniform pocket rank, leaving
the budget as a fully explicit matrix/rank-side certificate. -/
theorem bridgeA_rankLogDetLowerHypotheses_of_cookLevinPocket_compiledGadget_spectral_floor
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta rankLogRate delta : Real}
    (heta : 0 < eta) (htheta : 0 < theta)
    (hrate_nonneg : 0 <= rankLogRate)
    (hdelta_rate : delta <= rankLogRate * (kappa : Real))
    (hbudget :
      rankLogRate *
          (((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card *
            (PallLean.Paper93.DeepMath.BridgeB.pocketFamily
              alpha kappa gadgetN).rank : Nat) : Real) <=
        (N : Real) * Real.log (1 + theta * eta)) :
    BridgeARankLogDetLowerHypotheses
      alpha beta alpha0 kappa G chi Phi
      (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
      rankLogRate
      (Real.log
        (((1 : Matrix (Fin N) (Fin N) Real) +
          theta • (compiledGadget eta N)).det))
      delta := by
  apply
    bridgeA_rankLogDetLowerHypotheses_of_compiledGadget_spectral_floor
      alpha beta alpha0 kappa G chi Phi
      (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
      heta htheta hrate_nonneg hdelta_rate
  simpa [cookLevinPocketLocalGadgetFamily, cookLevinPocketLocalGadget,
    Finset.sum_const, nsmul_eq_mul, Nat.cast_mul] using hbudget

/-! ## Axiom audit anchors -/

#print axioms const_smul_one_add_posSemidef_posDef
#print axioms cfc_const_add_eq_const_smul_one_add
#print axioms const_smul_one_add_posSemidef_eigenvalues
#print axioms eigenvalue_floor_const_smul_one_add_posSemidef
#print axioms completeAdj_laplacian_posSemidef
#print axioms compiledGadget_posSemidef_of_positive_coupling
#print axioms compiledGadget_eigenvalue_floor
#print axioms bridgeA_rankLogDetLowerHypotheses_of_compiledGadget_spectral_floor
#print axioms bridgeA_rankLogDetLowerHypotheses_of_cookLevinPocket_compiledGadget_spectral_floor

end PallLean.Paper93.Paper283
