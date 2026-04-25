import PallLean.Paper93.Paper283.RouteBEigenvalueNormBound
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Algebra.Polynomial.Roots

/-!
# Route B shifted eigenvalue composition via functional calculus

The remaining Bridge B spectral-composition input is the affine shifted
eigenvalue identity

`eigenvalues(I + theta A) = 1 + theta * eigenvalues(A)`.

Mathlib's Hermitian functional calculus gives the right route: for a Hermitian
matrix `A`, `cfc (fun x => 1 + theta * x) A` has characteristic polynomial
with roots `1 + theta * eigenvalues(A)`.  This file packages that route into
the active Route B certificate vocabulary without importing any SAT/profile
adapter content.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open TuringMachine
open PaperFaithfulSeparation
open PallLean.Paper93.DeepMath.PathB

/-- Witnessed shifted eigenvalue composition statement. -/
def BridgeBShiftedEigenvalueCompositionOfPos {N : Nat}
    (theta : Real) (A : Matrix (Fin N) (Fin N) Real)
    (hA : A.PosSemidef) (htheta : 0 < theta) : Prop :=
  ∀ i,
    (one_add_smul_posSemidef_posDef_of_pos A hA htheta).1.eigenvalues i =
      1 + theta * hA.1.eigenvalues i

/-- The Hermitian functional-calculus characteristic-polynomial target for
the affine shift `x ↦ 1 + theta * x`. -/
theorem bridgeB_affine_cfc_charpoly {N : Nat}
    (theta : Real) (A : Matrix (Fin N) (Fin N) Real)
    (hA : A.PosSemidef) :
    (cfc (fun x : Real => 1 + theta * x) A).charpoly =
      ∏ i, (Polynomial.X -
        Polynomial.C ((1 + theta * hA.1.eigenvalues i) : Real)) := by
  simpa using
      (Matrix.IsHermitian.charpoly_cfc_eq
      (A := A) (𝕜 := Real) hA.1 (fun x : Real => 1 + theta * x))

/-- The matrix-level affine CFC identity for the Bridge B shift. -/
theorem bridgeB_affine_cfc_eq_shift {N : Nat}
    (theta : Real) (A : Matrix (Fin N) (Fin N) Real)
    (hA : A.PosSemidef) :
    cfc (fun x : Real => 1 + theta * x) A =
      (1 : Matrix (Fin N) (Fin N) Real) + theta • A := by
  calc
    cfc (fun x : Real => 1 + theta * x) A
        =
        (algebraMap Real (Matrix (Fin N) (Fin N) Real)) 1 +
          cfc (fun x : Real => theta * x) A := by
          rw [cfc_const_add
            (R := Real) (A := Matrix (Fin N) (Fin N) Real)
            (p := IsSelfAdjoint)
            (r := 1) (f := fun x : Real => theta * x) (a := A)
            (ha := hA.1)]
    _ = (1 : Matrix (Fin N) (Fin N) Real) + theta • A := by
          rw [cfc_const_mul_id
            (R := Real) (A := Matrix (Fin N) (Fin N) Real)
            (p := IsSelfAdjoint) (r := theta) (a := A) (ha := hA.1)]
          simp

private theorem bridgeB_strictMono_one_add_mul {theta : Real}
    (htheta : 0 < theta) :
    StrictMono (fun x : Real => 1 + theta * x) := by
  intro x y hxy
  nlinarith [mul_lt_mul_of_pos_left hxy htheta]

private theorem bridgeB_affine_cfc_charpoly_eigenvalues₀ {N : Nat}
    (theta : Real) (A : Matrix (Fin N) (Fin N) Real)
    (hA : A.PosSemidef) :
    (cfc (fun x : Real => 1 + theta * x) A).charpoly =
      ∏ i : Fin (Fintype.card (Fin N)),
        (Polynomial.X -
          Polynomial.C ((1 + theta * hA.1.eigenvalues₀ i) : Real)) := by
  let e : Fin (Fintype.card (Fin N)) ≃ Fin N :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  have h :
      (cfc (fun x : Real => 1 + theta * x) A).charpoly =
        ∏ i : Fin N,
          (Polynomial.X -
            Polynomial.C ((1 + theta * hA.1.eigenvalues i) : Real)) :=
    bridgeB_affine_cfc_charpoly theta A hA
  have hp :
      (∏ x : Fin N,
        (Polynomial.X -
          Polynomial.C ((1 + theta * hA.1.eigenvalues₀ (e.symm x)) :
            Real))) =
      ∏ i : Fin (Fintype.card (Fin N)),
        (Polynomial.X -
          Polynomial.C ((1 + theta * hA.1.eigenvalues₀ i) : Real)) := by
    simpa using
      (Equiv.prod_comp e.symm
        (fun i : Fin (Fintype.card (Fin N)) =>
          Polynomial.X -
            Polynomial.C ((1 + theta * hA.1.eigenvalues₀ i) : Real)))
  simpa [Matrix.IsHermitian.eigenvalues, e] using h.trans hp

private theorem bridgeB_affine_cfc_roots_re_eigenvalues₀ {N : Nat}
    (theta : Real) (A : Matrix (Fin N) (Fin N) Real)
    (hA : A.PosSemidef) :
    (cfc (fun x : Real => 1 + theta * x) A).charpoly.roots.map
        RCLike.re =
      ((List.ofFn
        (fun i : Fin (Fintype.card (Fin N)) =>
          1 + theta * hA.1.eigenvalues₀ i) : List Real) :
        Multiset Real) := by
  have hroots :
      (cfc (fun x : Real => 1 + theta * x) A).charpoly.roots =
        Multiset.map
          (fun i : Fin (Fintype.card (Fin N)) =>
            (1 + theta * hA.1.eigenvalues₀ i : Real)) Finset.univ.val := by
    rw [bridgeB_affine_cfc_charpoly_eigenvalues₀ theta A hA,
      Polynomial.roots_prod]
    · simp_rw [Polynomial.roots_X_sub_C]
      rw [Multiset.bind_singleton]
    · exact Finset.prod_ne_zero_iff.mpr
        (fun i _ => Polynomial.X_sub_C_ne_zero _)
  rw [hroots]
  simp [Fin.univ_val_map, Function.comp_def, RCLike.re]

private theorem bridgeB_shifted_eigenvalues₀ {N : Nat} {theta : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (htheta : 0 < theta) :
    (one_add_smul_posSemidef_posDef_of_pos A hA htheta).1.eigenvalues₀ =
      fun i : Fin (Fintype.card (Fin N)) =>
        1 + theta * hA.1.eigenvalues₀ i := by
  let B : Matrix (Fin N) (Fin N) Real :=
    (1 : Matrix (Fin N) (Fin N) Real) + theta • A
  let hB : B.PosDef := one_add_smul_posSemidef_posDef_of_pos A hA htheta
  have hroots :
      B.charpoly.roots.map RCLike.re =
        ((List.ofFn
          (fun i : Fin (Fintype.card (Fin N)) =>
            1 + theta * hA.1.eigenvalues₀ i) : List Real) :
          Multiset Real) := by
    change
      (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).charpoly.roots.map
        RCLike.re = _)
    rw [show
        (1 : Matrix (Fin N) (Fin N) Real) + theta • A =
          cfc (fun x : Real => 1 + theta * x) A
        from (bridgeB_affine_cfc_eq_shift theta A hA).symm]
    exact bridgeB_affine_cfc_roots_re_eigenvalues₀ theta A hA
  have hsortB :
      (B.charpoly.roots.map RCLike.re).sort
          (fun x y : Real => x ≥ y) =
        List.ofFn hB.1.eigenvalues₀ :=
    hB.1.sort_roots_charpoly_eq_eigenvalues₀
  have hsortAff :
      (List.ofFn
        (fun i : Fin (Fintype.card (Fin N)) =>
          1 + theta * hA.1.eigenvalues₀ i)).SortedGE := by
    have hf : StrictMono (fun x : Real => 1 + theta * x) :=
      bridgeB_strictMono_one_add_mul htheta
    have hsortedA0 : (List.ofFn hA.1.eigenvalues₀).SortedGE :=
      Antitone.sortedGE_ofFn hA.1.eigenvalues₀_antitone
    have hmap := (hf.sortedGE_listMap
      (l := List.ofFn hA.1.eigenvalues₀)).2 hsortedA0
    simpa [List.map_ofFn, Function.comp_def] using hmap
  have hperm :
      (List.ofFn hB.1.eigenvalues₀).Perm
        (List.ofFn
          (fun i : Fin (Fintype.card (Fin N)) =>
            1 + theta * hA.1.eigenvalues₀ i)) := by
    apply Multiset.coe_eq_coe.mp
    rw [← hsortB]
    rw [Multiset.sort_eq]
    exact hroots
  have hlist :
      List.ofFn hB.1.eigenvalues₀ =
        List.ofFn
          (fun i : Fin (Fintype.card (Fin N)) =>
            1 + theta * hA.1.eigenvalues₀ i) := by
    exact List.Perm.eq_of_sortedGE
      (Antitone.sortedGE_ofFn hB.1.eigenvalues₀_antitone)
      hsortAff hperm
  exact List.ofFn_inj.mp hlist

/-- The Route B shifted-eigenvalue composition theorem.

For PSD `A` and positive `theta`, Mathlib's sorted Hermitian eigenvalues of
`I + theta A` are exactly the affine shift of the sorted eigenvalues of `A`.
The proof goes through CFC characteristic polynomials, root multisets, and
uniqueness of decreasing sorted lists. -/
theorem one_add_smul_posSemidef_posDef_of_pos_eigenvalues {N : Nat}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    {theta : Real} (htheta : 0 < theta) :
    ∀ i,
      (one_add_smul_posSemidef_posDef_of_pos A hA htheta).1.eigenvalues i =
        1 + theta * hA.1.eigenvalues i := by
  have h0 := bridgeB_shifted_eigenvalues₀ A hA htheta
  intro i
  simp [Matrix.IsHermitian.eigenvalues, h0]

/-- The named Bridge B composition proposition is now discharged from PSD
data and `0 < theta`; it is no longer an external spectral field. -/
theorem bridgeB_shiftedEigenvalueComposition_of_pos {N : Nat}
    {theta : Real} (A : Matrix (Fin N) (Fin N) Real)
    (hA : A.PosSemidef) (htheta : 0 < theta) :
    BridgeBShiftedEigenvalueCompositionOfPos theta A hA htheta :=
  one_add_smul_posSemidef_posDef_of_pos_eigenvalues A hA htheta

/-- Bridge B spectral hypotheses with shifted eigenvalue composition and the
finite eigenvalue norm bound both derived from PSD data. -/
theorem bridgeB_spectral_hypotheses_of_posSemidef_autoNorm
    {N : Nat} {theta : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (htheta : 0 < theta) :
    BridgeBSpectralHypotheses theta (routeBEigenvalueSumNormBound A hA)
      (Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det))
      A.rank hA.1.eigenvalues := by
  exact
    bridgeB_spectral_hypotheses_of_posSemidef_with_auto_shiftPosDef_autoNormBound
      A hA htheta
      (one_add_smul_posSemidef_posDef_of_pos_eigenvalues A hA htheta)

/-- Auto-norm Route B matrix certificate after the shifted-eigenvalue theorem
has been discharged.  Compared with `RouteBStrictAutoNormMatrixCertificate`,
this form no longer stores the affine shifted-eigenvalue identity as a field. -/
def RouteBStrictAutoNormDerivedMatrixCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (N d : Nat)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (theta delta rankLogRate : Real)
    (A : Matrix (Fin N) (Fin N) Real)
    (hA : A.PosSemidef)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)),
    ∃ _htheta : 0 < theta,
      0 < alpha ∧ 0 < alpha0 ∧ 2 <= gadgetN ∧
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        rankLogRate
        (Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det))
        delta ∧
      PallLean.Paper93.NFrame.AdmissibleGauge Pi ∧
      RouteBProjectionRankCompatible M n hn2 htb hns A.rank Pi ∧
      RouteBMatrixToSATGaugeFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        (bridgeBLogCapacity theta (routeBEigenvalueSumNormBound A hA))
        delta A.rank Pi

/-- Derived auto-norm certificates supply the existing auto-norm certificate:
the shifted-eigenvalue field is filled by
`one_add_smul_posSemidef_posDef_of_pos_eigenvalues`. -/
theorem routeBStrictAutoNormMatrixCertificate_of_derivedMatrixCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (cert : RouteBStrictAutoNormDerivedMatrixCertificate M n hn2 htb hns) :
    RouteBStrictAutoNormMatrixCertificate M n hn2 htb hns := by
  rcases cert with
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, delta, rankLogRate, A, hA, Pi,
      htheta, halpha, halpha0, hgadgetN,
      hlower, hAdm, hcompat, hfun⟩
  exact
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, delta, rankLogRate, A, hA, Pi,
      htheta, halpha, halpha0, hgadgetN,
      one_add_smul_posSemidef_posDef_of_pos_eigenvalues A hA htheta,
      hlower, hAdm, hcompat, hfun⟩

/-- Per-instance Route B endpoint from the derived certificate form. -/
theorem routeBPerInstanceCertificate_of_derivedMatrixCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (cert : RouteBStrictAutoNormDerivedMatrixCertificate M n hn2 htb hns) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_autoNormMatrixCertificate
    (routeBStrictAutoNormMatrixCertificate_of_derivedMatrixCertificate cert)

/-- Bridge B spectral hypotheses from the named shifted-eigenvalue composition
statement and the automatic finite PSD eigenvalue bound. -/
theorem bridgeB_spectral_hypotheses_of_shiftedEigenvalueComposition_autoNorm
    {N : Nat} {theta : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (htheta : 0 < theta)
    (hcomp : BridgeBShiftedEigenvalueCompositionOfPos theta A hA htheta) :
    BridgeBSpectralHypotheses theta (routeBEigenvalueSumNormBound A hA)
      (Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det))
      A.rank hA.1.eigenvalues := by
  exact
    bridgeB_spectral_hypotheses_of_posSemidef_with_auto_shiftPosDef_autoNormBound
      A hA htheta hcomp

/-- Auto-norm matrix certificate variant that exposes the remaining shifted
eigenvalue composition as a named Route B spectral field. -/
def RouteBStrictAutoNormShiftedMatrixCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (N d : Nat)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (theta delta rankLogRate : Real)
    (A : Matrix (Fin N) (Fin N) Real)
    (hA : A.PosSemidef)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)),
    ∃ htheta : 0 < theta,
      0 < alpha ∧ 0 < alpha0 ∧ 2 <= gadgetN ∧
      BridgeBShiftedEigenvalueCompositionOfPos theta A hA htheta ∧
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        rankLogRate
        (Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det))
        delta ∧
      PallLean.Paper93.NFrame.AdmissibleGauge Pi ∧
      RouteBProjectionRankCompatible M n hn2 htb hns A.rank Pi ∧
      RouteBMatrixToSATGaugeFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        (bridgeBLogCapacity theta (routeBEigenvalueSumNormBound A hA))
        delta A.rank Pi

/-- The named shifted-composition certificate is exactly the auto-norm
certificate expected by the current Route B assembly. -/
theorem routeBStrictAutoNormMatrixCertificate_of_shiftedMatrixCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (cert : RouteBStrictAutoNormShiftedMatrixCertificate M n hn2 htb hns) :
    RouteBStrictAutoNormMatrixCertificate M n hn2 htb hns := by
  rcases cert with
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, delta, rankLogRate, A, hA, Pi,
      htheta, halpha, halpha0, hgadgetN,
      hshift_eigs, hlower, hAdm, hcompat, hfun⟩
  exact
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, delta, rankLogRate, A, hA, Pi,
      htheta, halpha, halpha0, hgadgetN,
      hshift_eigs, hlower, hAdm, hcompat, hfun⟩

/-! ## Axiom audit anchors -/

#print axioms bridgeB_affine_cfc_charpoly
#print axioms bridgeB_affine_cfc_eq_shift
#print axioms one_add_smul_posSemidef_posDef_of_pos_eigenvalues
#print axioms bridgeB_shiftedEigenvalueComposition_of_pos
#print axioms bridgeB_spectral_hypotheses_of_posSemidef_autoNorm
#print axioms routeBStrictAutoNormMatrixCertificate_of_derivedMatrixCertificate
#print axioms routeBPerInstanceCertificate_of_derivedMatrixCertificate
#print axioms bridgeB_spectral_hypotheses_of_shiftedEigenvalueComposition_autoNorm
#print axioms routeBStrictAutoNormMatrixCertificate_of_shiftedMatrixCertificate

end PallLean.Paper93.Paper283
