import PallLean.Paper93.Paper283.BridgeBShiftedEigenvalueCFC
import Mathlib.Data.Multiset.Sort

/-!
# Route B shifted eigenvalues in sorted order

This file completes the ordered-eigenvalue step for the Route B affine shift.
It uses the CFC characteristic-polynomial calculation from
`BridgeBShiftedEigenvalueCFC` and Mathlib's sorted Hermitian eigenvalue API:
`Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀`.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open Matrix
open Polynomial

/-- The roots of the shifted characteristic polynomial are the affine image of
the roots of the original characteristic polynomial. -/
theorem bridgeB_shifted_roots_map_affine {N : Nat}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    {theta : Real} :
    (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).charpoly.roots.map RCLike.re) =
      ((A.charpoly.roots.map RCLike.re).map (fun x : Real => 1 + theta * x)) := by
  classical
  have hchar :
      (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).charpoly) =
        ∏ i, (Polynomial.X -
          Polynomial.C ((1 + theta * hA.1.eigenvalues i) : Real)) := by
    rw [← bridgeB_affine_cfc_eq_shift theta A hA]
    exact bridgeB_affine_cfc_charpoly theta A hA
  rw [hchar, hA.1.roots_charpoly_eq_eigenvalues]
  rw [Polynomial.roots_prod]
  · have hfactor : ∀ i : Fin N,
        (Polynomial.X - Polynomial.C ((1 + theta * hA.1.eigenvalues i) : Real)).roots =
          ({(1 + theta * hA.1.eigenvalues i)} : Multiset Real) := by
      intro i
      exact Polynomial.roots_X_sub_C _
    simp only [hfactor, Multiset.map_map, Multiset.bind_singleton, Function.comp_apply]
    change Multiset.map (fun x : Fin N => 1 + theta * hA.1.eigenvalues x) Finset.univ.val =
      Multiset.map (fun x : Fin N => 1 + theta * hA.1.eigenvalues x) Finset.univ.val
    rfl
  · exact Finset.prod_ne_zero_iff.mpr (fun _ _ => Polynomial.X_sub_C_ne_zero _)

/-- Sorting the shifted roots agrees with applying the increasing affine map
`x ↦ 1 + theta * x` to the sorted Hermitian eigenvalues of `A`. -/
theorem bridgeB_shifted_sorted_roots_map_affine {N : Nat}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    {theta : Real} (htheta : 0 < theta) :
    ((((1 : Matrix (Fin N) (Fin N) Real) + theta • A).charpoly.roots.map RCLike.re).sort
        (· ≥ ·)) =
      List.ofFn (fun i : Fin (Fintype.card (Fin N)) => 1 + theta * hA.1.eigenvalues₀ i) := by
  classical
  let f : Real → Real := fun x => 1 + theta * x
  have hsort := Multiset.map_sort f (A.charpoly.roots.map RCLike.re)
      (fun a b : Real => a ≥ b) (fun a b : Real => a ≥ b)
      (by
        intro a _ b _
        constructor <;> intro h <;> dsimp [f] at h ⊢ <;> nlinarith [htheta, h])
  calc
    ((((1 : Matrix (Fin N) (Fin N) Real) + theta • A).charpoly.roots.map RCLike.re).sort
        (· ≥ ·))
        = (((A.charpoly.roots.map RCLike.re).map f).sort (· ≥ ·)) := by
            rw [bridgeB_shifted_roots_map_affine (theta := theta) A hA]
    _ = ((A.charpoly.roots.map RCLike.re).sort (· ≥ ·)).map f := by
            exact hsort.symm
    _ = (List.ofFn hA.1.eigenvalues₀).map f := by
            rw [hA.1.sort_roots_charpoly_eq_eigenvalues₀]
    _ = List.ofFn
          (fun i : Fin (Fintype.card (Fin N)) => 1 + theta * hA.1.eigenvalues₀ i) := by
            simp [List.map_ofFn, f, Function.comp_def]

/-- `eigenvalues₀` form of the Route B shifted-eigenvalue identity. -/
theorem one_add_smul_posSemidef_posDef_of_pos_eigenvalues₀ {N : Nat}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    {theta : Real} (htheta : 0 < theta) :
    ∀ i : Fin (Fintype.card (Fin N)),
      (one_add_smul_posSemidef_posDef_of_pos A hA htheta).1.eigenvalues₀ i =
        1 + theta * hA.1.eigenvalues₀ i := by
  intro i
  let hshift := one_add_smul_posSemidef_posDef_of_pos A hA htheta
  have hlist :
      List.ofFn hshift.1.eigenvalues₀ =
        List.ofFn
          (fun i : Fin (Fintype.card (Fin N)) => 1 + theta * hA.1.eigenvalues₀ i) := by
    calc
      List.ofFn hshift.1.eigenvalues₀
          = ((((1 : Matrix (Fin N) (Fin N) Real) + theta • A).charpoly.roots.map RCLike.re).sort
              (· ≥ ·)) := by
              rw [hshift.1.sort_roots_charpoly_eq_eigenvalues₀]
      _ = List.ofFn
            (fun i : Fin (Fintype.card (Fin N)) => 1 + theta * hA.1.eigenvalues₀ i) := by
              exact bridgeB_shifted_sorted_roots_map_affine A hA htheta
  exact congr_fun (List.ofFn_inj.mp hlist) i

/-- Sorted-order sidecar form of the Route B shifted-eigenvalue theorem, in
Mathlib's `Fin N` Hermitian eigenvalue indexing.  The canonical exported
theorem with the shorter name lives in `BridgeBShiftedEigenvalueCFC`. -/
theorem one_add_smul_posSemidef_posDef_of_pos_eigenvalues_sorted {N : Nat}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    {theta : Real} (htheta : 0 < theta) :
    ∀ i,
      (one_add_smul_posSemidef_posDef_of_pos A hA htheta).1.eigenvalues i =
        1 + theta * hA.1.eigenvalues i := by
  intro i
  simpa [Matrix.IsHermitian.eigenvalues] using
    one_add_smul_posSemidef_posDef_of_pos_eigenvalues₀ A hA htheta
      ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin N)))).symm i)

end PallLean.Paper93.Paper283
