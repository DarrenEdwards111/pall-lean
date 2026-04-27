import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityTwoResidualActive

/-!
# Residual active closure for identity (4)

Identity (4) uses the same row as identity (2), namely
`u = 3k-1`, `v = 3k`, but takes the left probe
`X_{3k} * X_{3k+1}`.  We reuse identity-(2)'s inert/active partition
of the touched list and compute the residual active coefficient.

No `sorry`.  No new axioms.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP
open BridgeABlockProductRule
open BridgeAKappaTwoTwoFoldLeibnizExpansion
open BridgeAKappaTwoFactorPairLemmas
open BridgeAKappaTwoIdentityOne
open BridgeAKappaTwoIdentityFour
open BridgeAKappaTwoIdentityTwoResidualActive
open BridgeAKappaTwoListInductionHelpers
open MultilinearCoefficientInfrastructure

attribute [local instance] Classical.dec

namespace BridgeAKappaTwoIdentityFourResidualActive

/-! ## Section A: identity-(4) probe in identity-(2) coordinates -/

theorem probeLeft_eq_v_a
    (n k : Nat) (hk2 : 3 * k + 3 < n) :
    probeLeft n k hk2 =
      Finsupp.single (vIdx n k hk2) 1 +
        Finsupp.single (aIdx n k hk2) 1 := by
  unfold probeLeft vIdx aIdx
  rfl

theorem vIdx_ne_aIdx' (n k : Nat) (hk2 : 3 * k + 3 < n) :
    vIdx n k hk2 ≠ aIdx n k hk2 :=
  vIdx_ne_aIdx n k hk2

theorem aIdx_ne_vIdx' (n k : Nat) (hk2 : 3 * k + 3 < n) :
    aIdx n k hk2 ≠ vIdx n k hk2 := by
  exact fun h => vIdx_ne_aIdx n k hk2 h.symm

theorem coeff_single_mul {N : Nat} (v : Fin N)
    (p q : MvPolynomial (Fin N) ℚ) :
    MvPolynomial.coeff (Finsupp.single v 1) (p * q) =
      MvPolynomial.coeff (Finsupp.single v 1) p * MvPolynomial.coeff 0 q +
        MvPolynomial.coeff 0 p *
          MvPolynomial.coeff (Finsupp.single v 1) q := by
  rw [MvPolynomial.coeff_mul, Finsupp.antidiagonal_single]
  have hanti :
      Finset.antidiagonal 1 = ({(0, 1), (1, 0)} : Finset (Nat × Nat)) := by
    decide
  rw [hanti]
  simp [add_comm]

theorem coeff_zero_mul {N : Nat}
    (p q : MvPolynomial (Fin N) ℚ) :
    MvPolynomial.coeff 0 (p * q) =
      MvPolynomial.coeff 0 p * MvPolynomial.coeff 0 q := by
  rw [MvPolynomial.coeff_mul]
  simp

/-! ## Section B: coefficient data for the `UV = (3k-1,3k)` family -/

theorem coeff_zero_uvFactorsFromCoeffs_prod
    (n : Nat) (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff 0 (uvFactorsFromCoeffs n k hk1 hk2 cs).prod = 1 := by
  induction cs with
  | nil =>
      simp
  | cons c cs ih =>
      rw [uvFactorsFromCoeffs_cons, List.prod_cons]
      rw [coeff_zero_mul]
      rw [coeff_zero_cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2)]
      rw [ih]
      ring

theorem coeff_single_a_uvFactorsFromCoeffs_prod
    (n : Nat) (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
        (uvFactorsFromCoeffs n k hk1 hk2 cs).prod = 0 := by
  induction cs with
  | nil =>
      rw [uvFactorsFromCoeffs_nil, List.prod_nil, MvPolynomial.coeff_one]
      rw [if_neg]
      intro h
      have ha := DFunLike.congr_fun h (aIdx n k hk2)
      simp at ha
  | cons c cs ih =>
      rw [uvFactorsFromCoeffs_cons, List.prod_cons]
      rw [coeff_single_mul]
      have hsingle :
          MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
            (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2)) = 0 := by
        exact coeff_X_a_one_sub_C_X_mul_X
          (aIdx n k hk2) (uIdx n k hk1 hk2) (vIdx n k hk2)
          (uIdx_ne_vIdx n k hk1 hk2) c
      rw [hsingle, coeff_zero_cadjFactorPoly, ih]
      ring

theorem coeff_single_v_uvFactorsFromCoeffs_prod
    (n : Nat) (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff (Finsupp.single (vIdx n k hk2) 1)
        (uvFactorsFromCoeffs n k hk1 hk2 cs).prod = 0 := by
  induction cs with
  | nil =>
      rw [uvFactorsFromCoeffs_nil, List.prod_nil, MvPolynomial.coeff_one]
      rw [if_neg]
      intro h
      have hv := DFunLike.congr_fun h (vIdx n k hk2)
      simp at hv
  | cons c cs ih =>
      rw [uvFactorsFromCoeffs_cons, List.prod_cons]
      rw [coeff_single_mul]
      have hsingle :
          MvPolynomial.coeff (Finsupp.single (vIdx n k hk2) 1)
            (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2)) = 0 := by
        exact coeff_X_a_one_sub_C_X_mul_X
          (vIdx n k hk2) (uIdx n k hk1 hk2) (vIdx n k hk2)
          (uIdx_ne_vIdx n k hk1 hk2) c
      rw [hsingle, coeff_zero_cadjFactorPoly, ih]
      ring

theorem coeff_probeLeft_uvFactorsFromCoeffs_prod
    (n : Nat) (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (uvFactorsFromCoeffs n k hk1 hk2 cs).prod = 0 := by
  induction cs with
  | nil =>
      rw [uvFactorsFromCoeffs_nil, List.prod_nil, MvPolynomial.coeff_one]
      rw [if_neg]
      intro h
      have hv := DFunLike.congr_fun h (vIdx n k hk2)
      simp [probeLeft_eq_v_a n k hk2, vIdx_ne_aIdx n k hk2] at hv
  | cons c cs ih =>
      rw [uvFactorsFromCoeffs_cons, List.prod_cons]
      rw [probeLeft_eq_v_a n k hk2]
      rw [coeff_two_mono_mul (vIdx n k hk2) (aIdx n k hk2)
        (vIdx_ne_aIdx n k hk2)]
      have hsingle_v :
          MvPolynomial.coeff (Finsupp.single (vIdx n k hk2) 1)
            (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2)) = 0 := by
        exact coeff_X_a_one_sub_C_X_mul_X
          (vIdx n k hk2) (uIdx n k hk1 hk2) (vIdx n k hk2)
          (uIdx_ne_vIdx n k hk1 hk2) c
      have hsingle_a :
          MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
            (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2)) = 0 := by
        exact coeff_X_a_one_sub_C_X_mul_X
          (aIdx n k hk2) (uIdx n k hk1 hk2) (vIdx n k hk2)
          (uIdx_ne_vIdx n k hk1 hk2) c
      have hprobe :
          MvPolynomial.coeff
              (Finsupp.single (vIdx n k hk2) 1 +
                Finsupp.single (aIdx n k hk2) 1)
              (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2)) = 0 := by
        rw [coeff_X_v_X_w_cadjFactorPoly c
          (uIdx n k hk1 hk2) (vIdx n k hk2)
          (vIdx n k hk2) (aIdx n k hk2)
          (uIdx_ne_vIdx n k hk1 hk2) (vIdx_ne_aIdx n k hk2)]
        simp
        intro h
        have hu := congrArg (fun s : Fin n →₀ Nat => s (uIdx n k hk1 hk2)) h
        simp [uIdx_ne_vIdx n k hk1 hk2, uIdx_ne_aIdx n k hk1 hk2] at hu
      rw [hsingle_v, hsingle_a, hprobe, coeff_zero_cadjFactorPoly]
      rw [probeLeft_eq_v_a n k hk2] at ih
      rw [ih]
      ring

theorem coeff_zero_pderivListProdSum_u_uvFactorsFromCoeffs
    (n : Nat) (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff 0
        (pderivListProdSum (uIdx n k hk1 hk2)
          (uvFactorsFromCoeffs n k hk1 hk2 cs)) = 0 := by
  induction cs with
  | nil =>
      rw [uvFactorsFromCoeffs_nil, pderivListProdSum_nil]
      simp
  | cons c cs ih =>
      rw [uvFactorsFromCoeffs_cons, pderivListProdSum_cons]
      rw [pderiv_one_sub_C_X_mul_X_at_fst c
        (uIdx n k hk1 hk2) (vIdx n k hk2) (uIdx_ne_vIdx n k hk1 hk2)]
      rw [MvPolynomial.coeff_add]
      have hhead :
          MvPolynomial.coeff 0
            ((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
              (uvFactorsFromCoeffs n k hk1 hk2 cs).prod) = 0 := by
        have hreassoc :
            ((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
              (uvFactorsFromCoeffs n k hk1 hk2 cs).prod :
              MvPolynomial (Fin n) ℚ) =
            MvPolynomial.X (vIdx n k hk2) *
              (-(MvPolynomial.C c) *
                (uvFactorsFromCoeffs n k hk1 hk2 cs).prod) := by
          ring
        rw [hreassoc]
        rw [MvPolynomial.coeff_X_mul']
        simp
      have htail :
          MvPolynomial.coeff 0
            (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2) *
              pderivListProdSum (uIdx n k hk1 hk2)
                (uvFactorsFromCoeffs n k hk1 hk2 cs)) = 0 := by
        rw [coeff_zero_mul]
        rw [ih]
        ring
      rw [hhead, htail]
      ring

theorem coeff_single_v_pderivListProdSum_u_uvFactorsFromCoeffs
    (n : Nat) (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff (Finsupp.single (vIdx n k hk2) 1)
        (pderivListProdSum (uIdx n k hk1 hk2)
          (uvFactorsFromCoeffs n k hk1 hk2 cs)) =
      -cs.sum := by
  induction cs with
  | nil =>
      rw [uvFactorsFromCoeffs_nil, pderivListProdSum_nil]
      simp
  | cons c cs ih =>
      rw [uvFactorsFromCoeffs_cons, pderivListProdSum_cons]
      rw [pderiv_one_sub_C_X_mul_X_at_fst c
        (uIdx n k hk1 hk2) (vIdx n k hk2) (uIdx_ne_vIdx n k hk1 hk2)]
      rw [MvPolynomial.coeff_add]
      have hhead :
          MvPolynomial.coeff (Finsupp.single (vIdx n k hk2) 1)
            ((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
              (uvFactorsFromCoeffs n k hk1 hk2 cs).prod) = -c := by
        have hreassoc :
            ((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
              (uvFactorsFromCoeffs n k hk1 hk2 cs).prod :
              MvPolynomial (Fin n) ℚ) =
            MvPolynomial.X (vIdx n k hk2) *
              (-(MvPolynomial.C c) *
                (uvFactorsFromCoeffs n k hk1 hk2 cs).prod) := by
          ring
        rw [hreassoc]
        have hzero :
            (Finsupp.single (vIdx n k hk2) 1 : Fin n →₀ Nat) =
              Finsupp.single (vIdx n k hk2) 1 + 0 := by simp
        conv_lhs => rw [hzero]
        rw [MvPolynomial.coeff_X_mul]
        rw [← map_neg, MvPolynomial.coeff_C_mul,
          coeff_zero_uvFactorsFromCoeffs_prod]
        ring
      have htail :
          MvPolynomial.coeff (Finsupp.single (vIdx n k hk2) 1)
            (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2) *
              pderivListProdSum (uIdx n k hk1 hk2)
                (uvFactorsFromCoeffs n k hk1 hk2 cs)) =
            -cs.sum := by
        rw [coeff_single_mul]
        have hsingle :
            MvPolynomial.coeff (Finsupp.single (vIdx n k hk2) 1)
              (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2)) = 0 := by
          exact coeff_X_a_one_sub_C_X_mul_X
            (vIdx n k hk2) (uIdx n k hk1 hk2) (vIdx n k hk2)
            (uIdx_ne_vIdx n k hk1 hk2) c
        rw [hsingle, coeff_zero_cadjFactorPoly, ih]
        ring
      rw [hhead, htail]
      simp only [List.sum_cons]
      ring

theorem coeff_single_a_pderivListProdSum_u_uvFactorsFromCoeffs
    (n : Nat) (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
        (pderivListProdSum (uIdx n k hk1 hk2)
          (uvFactorsFromCoeffs n k hk1 hk2 cs)) = 0 := by
  induction cs with
  | nil =>
      rw [uvFactorsFromCoeffs_nil, pderivListProdSum_nil]
      simp
  | cons c cs ih =>
      rw [uvFactorsFromCoeffs_cons, pderivListProdSum_cons]
      rw [pderiv_one_sub_C_X_mul_X_at_fst c
        (uIdx n k hk1 hk2) (vIdx n k hk2) (uIdx_ne_vIdx n k hk1 hk2)]
      rw [MvPolynomial.coeff_add]
      have hhead :
          MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
            ((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
              (uvFactorsFromCoeffs n k hk1 hk2 cs).prod) = 0 := by
        have hreassoc :
            ((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
              (uvFactorsFromCoeffs n k hk1 hk2 cs).prod :
              MvPolynomial (Fin n) ℚ) =
            MvPolynomial.X (vIdx n k hk2) *
              (-(MvPolynomial.C c) *
                (uvFactorsFromCoeffs n k hk1 hk2 cs).prod) := by
          ring
        rw [hreassoc, MvPolynomial.coeff_X_mul']
        simp [aIdx_ne_vIdx' n k hk2]
      have htail :
          MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
            (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2) *
              pderivListProdSum (uIdx n k hk1 hk2)
                (uvFactorsFromCoeffs n k hk1 hk2 cs)) = 0 := by
        rw [coeff_single_mul]
        have hsingle :
            MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
              (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2)) = 0 := by
          exact coeff_X_a_one_sub_C_X_mul_X
            (aIdx n k hk2) (uIdx n k hk1 hk2) (vIdx n k hk2)
            (uIdx_ne_vIdx n k hk1 hk2) c
        rw [hsingle, coeff_zero_cadjFactorPoly, ih]
        ring
      rw [hhead, htail]
      ring

theorem coeff_probeLeft_pderivListProdSum_u_uvFactorsFromCoeffs
    (n : Nat) (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (pderivListProdSum (uIdx n k hk1 hk2)
          (uvFactorsFromCoeffs n k hk1 hk2 cs)) = 0 := by
  induction cs with
  | nil =>
      rw [uvFactorsFromCoeffs_nil, pderivListProdSum_nil]
      simp
  | cons c cs ih =>
      rw [uvFactorsFromCoeffs_cons, pderivListProdSum_cons]
      rw [pderiv_one_sub_C_X_mul_X_at_fst c
        (uIdx n k hk1 hk2) (vIdx n k hk2) (uIdx_ne_vIdx n k hk1 hk2)]
      rw [MvPolynomial.coeff_add]
      have hhead :
          MvPolynomial.coeff (probeLeft n k hk2)
            ((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
              (uvFactorsFromCoeffs n k hk1 hk2 cs).prod) = 0 := by
        have hreassoc :
            ((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
              (uvFactorsFromCoeffs n k hk1 hk2 cs).prod :
              MvPolynomial (Fin n) ℚ) =
            MvPolynomial.X (vIdx n k hk2) *
              (-(MvPolynomial.C c) *
                (uvFactorsFromCoeffs n k hk1 hk2 cs).prod) := by
          ring
        rw [hreassoc, probeLeft_eq_v_a n k hk2]
        rw [MvPolynomial.coeff_X_mul]
        rw [← map_neg, MvPolynomial.coeff_C_mul,
          coeff_single_a_uvFactorsFromCoeffs_prod n k hk1 hk2 cs]
        ring
      have htail :
          MvPolynomial.coeff (probeLeft n k hk2)
            (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2) *
              pderivListProdSum (uIdx n k hk1 hk2)
                (uvFactorsFromCoeffs n k hk1 hk2 cs)) = 0 := by
        rw [probeLeft_eq_v_a n k hk2]
        rw [coeff_two_mono_mul (vIdx n k hk2) (aIdx n k hk2)
          (vIdx_ne_aIdx n k hk2)]
        have hsingle_v :
            MvPolynomial.coeff (Finsupp.single (vIdx n k hk2) 1)
              (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2)) = 0 := by
          exact coeff_X_a_one_sub_C_X_mul_X
            (vIdx n k hk2) (uIdx n k hk1 hk2) (vIdx n k hk2)
            (uIdx_ne_vIdx n k hk1 hk2) c
        have hsingle_a :
            MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
              (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2)) = 0 := by
          exact coeff_X_a_one_sub_C_X_mul_X
            (aIdx n k hk2) (uIdx n k hk1 hk2) (vIdx n k hk2)
            (uIdx_ne_vIdx n k hk1 hk2) c
        have hprobe :
            MvPolynomial.coeff
                (Finsupp.single (vIdx n k hk2) 1 +
                  Finsupp.single (aIdx n k hk2) 1)
                (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2)) = 0 := by
          rw [coeff_X_v_X_w_cadjFactorPoly c
            (uIdx n k hk1 hk2) (vIdx n k hk2)
            (vIdx n k hk2) (aIdx n k hk2)
            (uIdx_ne_vIdx n k hk1 hk2) (vIdx_ne_aIdx n k hk2)]
          simp
          intro h
          have hu := congrArg (fun s : Fin n →₀ Nat => s (uIdx n k hk1 hk2)) h
          simp [uIdx_ne_vIdx n k hk1 hk2, uIdx_ne_aIdx n k hk1 hk2] at hu
        rw [hsingle_v, hsingle_a, hprobe, coeff_zero_cadjFactorPoly]
        rw [coeff_single_v_pderivListProdSum_u_uvFactorsFromCoeffs n k hk1 hk2 cs]
        rw [coeff_single_a_pderivListProdSum_u_uvFactorsFromCoeffs n k hk1 hk2 cs]
        rw [probeLeft_eq_v_a n k hk2] at ih
        rw [ih]
        ring
      rw [hhead, htail]
      ring

/-! ## Section C: two-fold coefficient data for the same `UV` family -/

theorem uvFactorsFromCoeffs_pderiv_v_has_X_u_factor
    (n : Nat) (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ uvFactorsFromCoeffs n k hk1 hk2 cs) :
    ∃ q : MvPolynomial (Fin n) ℚ,
      MvPolynomial.pderiv (vIdx n k hk2) f =
        MvPolynomial.X (uIdx n k hk1 hk2) * q := by
  unfold uvFactorsFromCoeffs at hf
  simp only [List.mem_map] at hf
  obtain ⟨c, _hc, rfl⟩ := hf
  refine ⟨-(MvPolynomial.C c), ?_⟩
  rw [pderiv_one_sub_C_X_mul_X_at_snd c
    (uIdx n k hk1 hk2) (vIdx n k hk2)
    (uIdx_ne_vIdx n k hk1 hk2)]
  ring

theorem pderivListProdSum_v_uvFactorsFromCoeffs_has_X_u_factor
    (n : Nat) (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    ∃ q : MvPolynomial (Fin n) ℚ,
      pderivListProdSum (vIdx n k hk2)
          (uvFactorsFromCoeffs n k hk1 hk2 cs) =
        MvPolynomial.X (uIdx n k hk1 hk2) * q :=
  BridgeAKappaTwoIdentityThreeResidualActive.pderivListProdSum_has_X_factor_of_forall
    (uIdx n k hk1 hk2) (vIdx n k hk2)
    (uvFactorsFromCoeffs n k hk1 hk2 cs)
    (uvFactorsFromCoeffs_pderiv_v_has_X_u_factor n k hk1 hk2 cs)

theorem coeff_zero_X_mul {N : Nat} (x : Fin N)
    (p : MvPolynomial (Fin N) ℚ) :
    MvPolynomial.coeff 0 (MvPolynomial.X x * p) = 0 := by
  rw [MvPolynomial.coeff_X_mul']
  simp

theorem coeff_single_X_mul_of_ne {N : Nat} (x y : Fin N)
    (p : MvPolynomial (Fin N) ℚ) (hxy : y ≠ x) :
    MvPolynomial.coeff (Finsupp.single y 1) (MvPolynomial.X x * p) = 0 := by
  rw [MvPolynomial.coeff_X_mul']
  simp [hxy]

theorem coeff_zero_pderivListProdSumTwice_uvFactorsFromCoeffs
    (n : Nat) (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff 0
        (pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
          (uvFactorsFromCoeffs n k hk1 hk2 cs)) =
      -cs.sum := by
  induction cs with
  | nil =>
      rw [uvFactorsFromCoeffs_nil, pderivListProdSumTwice_nil]
      simp
  | cons c cs ih =>
      rw [uvFactorsFromCoeffs_cons, pderivListProdSumTwice_cons]
      rw [pderiv_w_pderiv_v_one_sub_C_X_mul_X_ij c
        (uIdx n k hk1 hk2) (vIdx n k hk2) (uIdx_ne_vIdx n k hk1 hk2)]
      rw [pderiv_one_sub_C_X_mul_X_at_fst c
        (uIdx n k hk1 hk2) (vIdx n k hk2) (uIdx_ne_vIdx n k hk1 hk2)]
      rw [pderiv_one_sub_C_X_mul_X_at_snd c
        (uIdx n k hk1 hk2) (vIdx n k hk2) (uIdx_ne_vIdx n k hk1 hk2)]
      rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add]
      have hdiag :
          MvPolynomial.coeff 0
            (-(MvPolynomial.C c) *
              (uvFactorsFromCoeffs n k hk1 hk2 cs).prod) = -c := by
        rw [← map_neg, MvPolynomial.coeff_C_mul,
          coeff_zero_uvFactorsFromCoeffs_prod]
        ring
      have hcrossV :
          MvPolynomial.coeff 0
            ((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
              MvPolynomial.pderiv (vIdx n k hk2)
                (uvFactorsFromCoeffs n k hk1 hk2 cs).prod) = 0 := by
        rw [pderiv_list_prod]
        obtain ⟨q, hq⟩ :=
          pderivListProdSum_v_uvFactorsFromCoeffs_has_X_u_factor n k hk1 hk2 cs
        rw [hq]
        have hreassoc :
            ((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
              (MvPolynomial.X (uIdx n k hk1 hk2) * q) :
              MvPolynomial (Fin n) ℚ) =
            MvPolynomial.X (uIdx n k hk1 hk2) *
              (-(MvPolynomial.C c) * (MvPolynomial.X (vIdx n k hk2) * q)) := by
          ring
        rw [hreassoc, coeff_zero_X_mul]
      have hcrossU :
          MvPolynomial.coeff 0
            ((-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk1 hk2))) *
              pderivListProdSum (uIdx n k hk1 hk2)
                (uvFactorsFromCoeffs n k hk1 hk2 cs)) = 0 := by
        have hreassoc :
            ((-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk1 hk2))) *
              pderivListProdSum (uIdx n k hk1 hk2)
                (uvFactorsFromCoeffs n k hk1 hk2 cs) :
              MvPolynomial (Fin n) ℚ) =
            MvPolynomial.X (uIdx n k hk1 hk2) *
              (-(MvPolynomial.C c) *
                pderivListProdSum (uIdx n k hk1 hk2)
                  (uvFactorsFromCoeffs n k hk1 hk2 cs)) := by
          ring
        rw [hreassoc, coeff_zero_X_mul]
      have hrec :
          MvPolynomial.coeff 0
            (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2) *
              pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
                (uvFactorsFromCoeffs n k hk1 hk2 cs)) =
            -cs.sum := by
        rw [coeff_zero_mul, coeff_zero_cadjFactorPoly, ih]
        ring
      rw [hdiag, hcrossV, hcrossU, hrec]
      simp only [List.sum_cons]
      ring

theorem coeff_single_v_pderivListProdSumTwice_uvFactorsFromCoeffs
    (n : Nat) (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff (Finsupp.single (vIdx n k hk2) 1)
        (pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
          (uvFactorsFromCoeffs n k hk1 hk2 cs)) = 0 := by
  induction cs with
  | nil =>
      rw [uvFactorsFromCoeffs_nil, pderivListProdSumTwice_nil]
      simp
  | cons c cs ih =>
      rw [uvFactorsFromCoeffs_cons, pderivListProdSumTwice_cons]
      rw [pderiv_w_pderiv_v_one_sub_C_X_mul_X_ij c
        (uIdx n k hk1 hk2) (vIdx n k hk2) (uIdx_ne_vIdx n k hk1 hk2)]
      rw [pderiv_one_sub_C_X_mul_X_at_fst c
        (uIdx n k hk1 hk2) (vIdx n k hk2) (uIdx_ne_vIdx n k hk1 hk2)]
      rw [pderiv_one_sub_C_X_mul_X_at_snd c
        (uIdx n k hk1 hk2) (vIdx n k hk2) (uIdx_ne_vIdx n k hk1 hk2)]
      rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add]
      have hdiag :
          MvPolynomial.coeff (Finsupp.single (vIdx n k hk2) 1)
            (-(MvPolynomial.C c) *
              (uvFactorsFromCoeffs n k hk1 hk2 cs).prod) = 0 := by
        rw [← map_neg, MvPolynomial.coeff_C_mul,
          coeff_single_v_uvFactorsFromCoeffs_prod]
        ring
      have hcrossV :
          MvPolynomial.coeff (Finsupp.single (vIdx n k hk2) 1)
            ((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
              MvPolynomial.pderiv (vIdx n k hk2)
                (uvFactorsFromCoeffs n k hk1 hk2 cs).prod) = 0 := by
        rw [pderiv_list_prod]
        obtain ⟨q, hq⟩ :=
          pderivListProdSum_v_uvFactorsFromCoeffs_has_X_u_factor n k hk1 hk2 cs
        rw [hq]
        have hreassoc :
            ((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
              (MvPolynomial.X (uIdx n k hk1 hk2) * q) :
              MvPolynomial (Fin n) ℚ) =
            MvPolynomial.X (uIdx n k hk1 hk2) *
              (-(MvPolynomial.C c) * (MvPolynomial.X (vIdx n k hk2) * q)) := by
          ring
        rw [hreassoc]
        exact coeff_single_X_mul_of_ne (uIdx n k hk1 hk2) (vIdx n k hk2)
          (-(MvPolynomial.C c) * (MvPolynomial.X (vIdx n k hk2) * q))
          (fun h => uIdx_ne_vIdx n k hk1 hk2 h.symm)
      have hcrossU :
          MvPolynomial.coeff (Finsupp.single (vIdx n k hk2) 1)
            ((-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk1 hk2))) *
              pderivListProdSum (uIdx n k hk1 hk2)
                (uvFactorsFromCoeffs n k hk1 hk2 cs)) = 0 := by
        have hreassoc :
            ((-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk1 hk2))) *
              pderivListProdSum (uIdx n k hk1 hk2)
                (uvFactorsFromCoeffs n k hk1 hk2 cs) :
              MvPolynomial (Fin n) ℚ) =
            MvPolynomial.X (uIdx n k hk1 hk2) *
              (-(MvPolynomial.C c) *
                pderivListProdSum (uIdx n k hk1 hk2)
                  (uvFactorsFromCoeffs n k hk1 hk2 cs)) := by
          ring
        rw [hreassoc]
        exact coeff_single_X_mul_of_ne (uIdx n k hk1 hk2) (vIdx n k hk2)
          (-(MvPolynomial.C c) *
            pderivListProdSum (uIdx n k hk1 hk2)
              (uvFactorsFromCoeffs n k hk1 hk2 cs))
          (fun h => uIdx_ne_vIdx n k hk1 hk2 h.symm)
      have hrec :
          MvPolynomial.coeff (Finsupp.single (vIdx n k hk2) 1)
            (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2) *
              pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
                (uvFactorsFromCoeffs n k hk1 hk2 cs)) = 0 := by
        rw [coeff_single_mul]
        have hsingle :
            MvPolynomial.coeff (Finsupp.single (vIdx n k hk2) 1)
              (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2)) = 0 := by
          exact coeff_X_a_one_sub_C_X_mul_X
            (vIdx n k hk2) (uIdx n k hk1 hk2) (vIdx n k hk2)
            (uIdx_ne_vIdx n k hk1 hk2) c
        rw [hsingle, coeff_zero_cadjFactorPoly, ih]
        ring
      rw [hdiag, hcrossV, hcrossU, hrec]
      ring

/-! ## Section C: coefficient data for the `VA = (3k,3k+1)` family -/

theorem coeff_single_factor_mul_of_coeff_zero_one_of_coeff_single_zero {N : Nat}
    (x : Fin N) (f p : MvPolynomial (Fin N) ℚ)
    (hf0 : MvPolynomial.coeff 0 f = 1)
    (hfx : MvPolynomial.coeff (Finsupp.single x 1) f = 0) :
    MvPolynomial.coeff (Finsupp.single x 1) (f * p) =
      MvPolynomial.coeff (Finsupp.single x 1) p := by
  rw [coeff_single_mul x f p]
  rw [hf0, hfx]
  ring

theorem coeff_single_list_prod_mul_of_forall_preserve {N : Nat}
    (x : Fin N) (fs : List (MvPolynomial (Fin N) ℚ))
    (p : MvPolynomial (Fin N) ℚ)
    (h0 : ∀ f ∈ fs, MvPolynomial.coeff 0 f = 1)
    (hx : ∀ f ∈ fs, MvPolynomial.coeff (Finsupp.single x 1) f = 0) :
    MvPolynomial.coeff (Finsupp.single x 1) (fs.prod * p) =
      MvPolynomial.coeff (Finsupp.single x 1) p := by
  induction fs with
  | nil =>
      simp
  | cons f fs ih =>
      rw [List.prod_cons, mul_assoc]
      rw [coeff_single_factor_mul_of_coeff_zero_one_of_coeff_single_zero x f
        (fs.prod * p) (h0 f (by simp)) (hx f (by simp))]
      exact ih
        (fun g hg => h0 g (List.mem_cons_of_mem f hg))
        (fun g hg => hx g (List.mem_cons_of_mem f hg))

noncomputable def vaFactorsFromCoeffs
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) : List (MvPolynomial (Fin n) ℚ) :=
  cs.map (fun c =>
    cadjFactorPoly c (vIdx n k hk2) (aIdx n k hk2))

@[simp] theorem vaFactorsFromCoeffs_nil
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n) :
    vaFactorsFromCoeffs n k hk2 [] = [] := by
  unfold vaFactorsFromCoeffs
  rfl

@[simp] theorem vaFactorsFromCoeffs_cons
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (c : ℚ) (cs : List ℚ) :
    vaFactorsFromCoeffs n k hk2 (c :: cs) =
      cadjFactorPoly c (vIdx n k hk2) (aIdx n k hk2) ::
        vaFactorsFromCoeffs n k hk2 cs := by
  unfold vaFactorsFromCoeffs
  rfl

theorem activeVAFactorsList_eq_bool_v_vaFactorsFromCoeffs
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    activeVAFactorsList M n k hk1 hk2 =
      [boolFactorPoly n (vIdx n k hk2)] ++
        vaFactorsFromCoeffs n k hk2
          (1 :: (List.finRange M.numStates).map (fun q => transCoeff M q)) := by
  unfold activeVAFactorsList vaFactorsFromCoeffs
  simp only [List.map_cons, List.singleton_append, List.map_map]
  have htail := List.flatMap_pure_eq_map
    (fun q : Fin M.numStates =>
      cadjFactorPoly (transCoeff M q)
        (vIdx n k hk2) (aIdx n k hk2))
    (List.finRange M.numStates)
  simpa [Function.comp_def] using
    congrArg
      (fun t =>
        boolFactorPoly n (vIdx n k hk2) ::
          cadjFactorPoly 1 (vIdx n k hk2) (aIdx n k hk2) :: t)
      htail

theorem vaFactorsFromCoeffs_forall_coeff_zero_one
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ vaFactorsFromCoeffs n k hk2 cs) :
    MvPolynomial.coeff 0 f = 1 := by
  unfold vaFactorsFromCoeffs at hf
  simp only [List.mem_map] at hf
  obtain ⟨c, _hc, rfl⟩ := hf
  exact coeff_zero_cadjFactorPoly c _ _

theorem coeff_zero_vaFactorsFromCoeffs_prod
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff 0 (vaFactorsFromCoeffs n k hk2 cs).prod = 1 :=
  ListProdDerivativeConstantCoeff.coeff_zero_list_prod_eq_one_of_forall
    (vaFactorsFromCoeffs n k hk2 cs)
    (vaFactorsFromCoeffs_forall_coeff_zero_one n k hk2 cs)

theorem vaFactorsFromCoeffs_forall_coeff_single_zero
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) (x : Fin n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ vaFactorsFromCoeffs n k hk2 cs) :
    MvPolynomial.coeff (Finsupp.single x 1) f = 0 := by
  unfold vaFactorsFromCoeffs at hf
  simp only [List.mem_map] at hf
  obtain ⟨c, _hc, rfl⟩ := hf
  exact coeff_X_a_one_sub_C_X_mul_X
    x (vIdx n k hk2) (aIdx n k hk2) (vIdx_ne_aIdx n k hk2) c

theorem coeff_single_vaFactorsFromCoeffs_prod_mul
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) (x : Fin n) (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (Finsupp.single x 1)
        ((vaFactorsFromCoeffs n k hk2 cs).prod * p) =
      MvPolynomial.coeff (Finsupp.single x 1) p := by
  apply coeff_single_list_prod_mul_of_forall_preserve
  · exact vaFactorsFromCoeffs_forall_coeff_zero_one n k hk2 cs
  · exact vaFactorsFromCoeffs_forall_coeff_single_zero n k hk2 cs x

theorem coeff_probeLeft_bool_b_mul
    (n k : Nat) (hk2 : 3 * k + 3 < n)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (boolFactorPoly n (bIdx n k hk2) * p) =
      MvPolynomial.coeff (probeLeft n k hk2) p := by
  rw [probeLeft_eq_v_a n k hk2]
  exact BridgeAKappaTwoIdentityThreeResidualActive.coeff_X_a_X_b_boolFactorPoly_mul
    (vIdx n k hk2) (aIdx n k hk2) (bIdx n k hk2) p
    (fun h => vIdx_ne_bIdx n k hk2 h.symm)
    (fun h => aIdx_ne_bIdx n k hk2 h.symm)

theorem coeff_probeLeft_cadj_a_b_mul
    (n k : Nat) (hk2 : 3 * k + 3 < n)
    (c : ℚ) (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (cadjFactorPoly c (aIdx n k hk2) (bIdx n k hk2) * p) =
      MvPolynomial.coeff (probeLeft n k hk2) p := by
  rw [probeLeft_eq_v_a n k hk2]
  exact BridgeAKappaTwoIdentityThreeResidualActive.coeff_X_a_X_b_cadjFactorPoly_mul_stray_snd
    (vIdx n k hk2) (aIdx n k hk2)
    (aIdx n k hk2) (bIdx n k hk2) c p
    (fun h => vIdx_ne_bIdx n k hk2 h.symm)
    (fun h => aIdx_ne_bIdx n k hk2 h.symm)

theorem coeff_probeLeft_cadj_b_r_mul
    (n k : Nat) (hk2 : 3 * k + 3 < n)
    (c : ℚ) (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (cadjFactorPoly c (bIdx n k hk2) (rIdx n k hk2) * p) =
      MvPolynomial.coeff (probeLeft n k hk2) p := by
  rw [probeLeft_eq_v_a n k hk2]
  exact BridgeAKappaTwoIdentityThreeResidualActive.coeff_X_a_X_b_cadjFactorPoly_mul_stray_fst
    (vIdx n k hk2) (aIdx n k hk2)
    (bIdx n k hk2) (rIdx n k hk2) c p
    (fun h => vIdx_ne_bIdx n k hk2 h.symm)
    (fun h => aIdx_ne_bIdx n k hk2 h.symm)

theorem rightBRFactorsList_forall_probeLeft_preserve
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ rightBRFactorsList M n k hk2)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2) (f * p) =
      MvPolynomial.coeff (probeLeft n k hk2) p := by
  unfold rightBRFactorsList rightBRFactorsListFrom at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with rfl | ⟨q, _hq, rfl⟩
  · exact coeff_probeLeft_cadj_b_r_mul n k hk2 1 p
  · exact coeff_probeLeft_cadj_b_r_mul n k hk2 (transCoeff M q) p

theorem coeff_probeLeft_rightBRFactorsList_prod_mul
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2)
        ((rightBRFactorsList M n k hk2).prod * p) =
      MvPolynomial.coeff (probeLeft n k hk2) p := by
  rw [probeLeft_eq_v_a n k hk2]
  apply BridgeAKappaTwoIdentityThreeResidualActive.coeff_X_a_X_b_list_prod_mul_of_forall_preserve
  intro f hf p'
  rw [← probeLeft_eq_v_a n k hk2]
  exact rightBRFactorsList_forall_probeLeft_preserve M n k hk2 f hf p'

theorem directABFactorsList_forall_probeLeft_preserve
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ directABFactorsList M n k hk2)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2) (f * p) =
      MvPolynomial.coeff (probeLeft n k hk2) p := by
  unfold directABFactorsList transABFactorsListFrom at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with rfl | ⟨q, _hq, rfl⟩
  · exact coeff_probeLeft_cadj_a_b_mul n k hk2 1 p
  · exact coeff_probeLeft_cadj_a_b_mul n k hk2 (transCoeff M q) p

theorem coeff_probeLeft_directABFactorsList_prod_mul
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2)
        ((directABFactorsList M n k hk2).prod * p) =
      MvPolynomial.coeff (probeLeft n k hk2) p := by
  rw [probeLeft_eq_v_a n k hk2]
  apply BridgeAKappaTwoIdentityThreeResidualActive.coeff_X_a_X_b_list_prod_mul_of_forall_preserve
  intro f hf p'
  rw [← probeLeft_eq_v_a n k hk2]
  exact directABFactorsList_forall_probeLeft_preserve M n k hk2 f hf p'

theorem coeff_probeLeft_bool_a_activeVA_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (boolFactorPoly n (aIdx n k hk2) *
          (activeVAFactorsList M n k hk1 hk2).prod) =
      -transCoeffSum M := by
  rw [activeVAFactorsList_eq_bool_v_vaFactorsFromCoeffs M n k hk1 hk2]
  have hdirect :
      vaFactorsFromCoeffs n k hk2
          (1 :: (List.finRange M.numStates).map (fun q => transCoeff M q)) =
        BridgeAKappaTwoIdentityThreeResidualActive.directABFactorsList
          M n k hk2 := by
    unfold vaFactorsFromCoeffs
    unfold BridgeAKappaTwoIdentityThreeResidualActive.directABFactorsList
    unfold BridgeAKappaTwoIdentityThreeResidualActive.transABFactorsListFrom
    unfold BridgeAKappaTwoIdentityThreeAux.aIdx
    unfold BridgeAKappaTwoIdentityThreeAux.bIdx
    unfold vIdx aIdx
    simp only [List.map_cons, List.singleton_append, List.map_map]
    have htail := List.flatMap_pure_eq_map
      (fun q : Fin M.numStates =>
        cadjFactorPoly (transCoeff M q)
          (⟨3 * k, by omega⟩ : Fin n)
          (⟨3 * k + 1, by omega⟩ : Fin n))
      (List.finRange M.numStates)
    simpa [Function.comp_def] using
      congrArg
        (fun t =>
          cadjFactorPoly 1
            (⟨3 * k, by omega⟩ : Fin n)
            (⟨3 * k + 1, by omega⟩ : Fin n) :: t)
        htail.symm
  rw [hdirect]
  have hprod :
      (boolFactorPoly n (aIdx n k hk2) *
          ([boolFactorPoly n (vIdx n k hk2)] ++
            BridgeAKappaTwoIdentityThreeResidualActive.directABFactorsList
              M n k hk2).prod :
        MvPolynomial (Fin n) ℚ) =
      (boolFactorPoly n
          (BridgeAKappaTwoIdentityThreeAux.aIdx n k hk2) *
        boolFactorPoly n
          (BridgeAKappaTwoIdentityThreeAux.bIdx n k hk2)) *
        (BridgeAKappaTwoIdentityThreeResidualActive.directABFactorsList
          M n k hk2).prod := by
    unfold BridgeAKappaTwoIdentityThreeAux.aIdx
    unfold BridgeAKappaTwoIdentityThreeAux.bIdx
    unfold vIdx aIdx
    simp
    ring
  rw [hprod]
  exact BridgeAKappaTwoIdentityThreeResidualActive.coeff_probeLeft_boolPair_directAB_prod
    M n k hk2

theorem coeff_probeLeft_inert_activeVA_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeLeft n k hk2)
        ((inertFactorsList M n k hk1 hk2).prod *
          (activeVAFactorsList M n k hk1 hk2).prod) =
      -transCoeffSum M := by
  have hperm := inertFactorsList_perm_right_base M n k hk1 hk2
  rw [List.Perm.prod_eq hperm]
  rw [List.prod_append]
  have hreassoc₁ :
      ((rightBRFactorsList M n k hk2).prod *
          (([boolFactorPoly n (aIdx n k hk2),
              boolFactorPoly n (bIdx n k hk2)] ++
              directABFactorsList M n k hk2).prod) *
          (activeVAFactorsList M n k hk1 hk2).prod :
        MvPolynomial (Fin n) ℚ) =
      (rightBRFactorsList M n k hk2).prod *
        ((([boolFactorPoly n (aIdx n k hk2),
            boolFactorPoly n (bIdx n k hk2)] ++
            directABFactorsList M n k hk2).prod) *
          (activeVAFactorsList M n k hk1 hk2).prod) := by
    ring
  rw [hreassoc₁]
  rw [coeff_probeLeft_rightBRFactorsList_prod_mul M n k hk2]
  have hbase :
      ((([boolFactorPoly n (aIdx n k hk2),
          boolFactorPoly n (bIdx n k hk2)] ++
          directABFactorsList M n k hk2).prod) *
          (activeVAFactorsList M n k hk1 hk2).prod :
        MvPolynomial (Fin n) ℚ) =
      boolFactorPoly n (bIdx n k hk2) *
        ((directABFactorsList M n k hk2).prod *
          (boolFactorPoly n (aIdx n k hk2) *
            (activeVAFactorsList M n k hk1 hk2).prod)) := by
    simp
    ring
  rw [hbase]
  rw [coeff_probeLeft_bool_b_mul n k hk2]
  rw [coeff_probeLeft_directABFactorsList_prod_mul M n k hk2]
  exact coeff_probeLeft_bool_a_activeVA_prod M n k hk1 hk2

/-! ## Section D: single coefficient of the `VA` derivative -/

theorem rightBRFactorsList_forall_coeff_zero_one
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ rightBRFactorsList M n k hk2) :
    MvPolynomial.coeff 0 f = 1 := by
  unfold rightBRFactorsList rightBRFactorsListFrom at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with rfl | ⟨q, _hq, rfl⟩
  · exact coeff_zero_cadjFactorPoly 1 _ _
  · exact coeff_zero_cadjFactorPoly (transCoeff M q) _ _

theorem rightBRFactorsList_forall_coeff_single_a_zero
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ rightBRFactorsList M n k hk2) :
    MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1) f = 0 := by
  unfold rightBRFactorsList rightBRFactorsListFrom at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with rfl | ⟨q, _hq, rfl⟩
  · exact coeff_X_a_one_sub_C_X_mul_X
      (aIdx n k hk2) (bIdx n k hk2) (rIdx n k hk2)
      (bIdx_ne_rIdx n k hk2) 1
  · exact coeff_X_a_one_sub_C_X_mul_X
      (aIdx n k hk2) (bIdx n k hk2) (rIdx n k hk2)
      (bIdx_ne_rIdx n k hk2) (transCoeff M q)

theorem coeff_single_a_rightBRFactorsList_prod_mul
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
        ((rightBRFactorsList M n k hk2).prod * p) =
      MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1) p := by
  apply coeff_single_list_prod_mul_of_forall_preserve
  · exact rightBRFactorsList_forall_coeff_zero_one M n k hk2
  · exact rightBRFactorsList_forall_coeff_single_a_zero M n k hk2

theorem coeff_single_a_directABFactorsList_prod_mul
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
        ((directABFactorsList M n k hk2).prod * p) =
      MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1) p := by
  apply coeff_single_list_prod_mul_of_forall_preserve
  · exact directABFactorsList_forall_coeff_zero_one M n k hk2
  · exact directABFactorsList_forall_coeff_single_zero
      M n k hk2 (aIdx n k hk2)

theorem coeff_single_a_bool_b_mul
    (n k : Nat) (hk2 : 3 * k + 3 < n)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
        (boolFactorPoly n (bIdx n k hk2) * p) =
      MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1) p := by
  apply coeff_single_factor_mul_of_coeff_zero_one_of_coeff_single_zero
  · exact coeff_zero_boolFactorPoly _
  · rw [BridgeAKappaTwoIdentityThreeResidualActive.coeff_single_boolFactorPoly]
    rw [if_neg (fun h => aIdx_ne_bIdx n k hk2 h)]

theorem coeff_single_a_inertFactorsList_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
        (inertFactorsList M n k hk1 hk2).prod = -1 := by
  have hperm := inertFactorsList_perm_right_base M n k hk1 hk2
  rw [List.Perm.prod_eq hperm]
  rw [List.prod_append]
  rw [coeff_single_a_rightBRFactorsList_prod_mul M n k hk2]
  have hbase :
      ((([boolFactorPoly n (aIdx n k hk2),
          boolFactorPoly n (bIdx n k hk2)] ++
          directABFactorsList M n k hk2).prod) :
        MvPolynomial (Fin n) ℚ) =
      boolFactorPoly n (bIdx n k hk2) *
        ((directABFactorsList M n k hk2).prod *
          boolFactorPoly n (aIdx n k hk2)) := by
    simp
    ring
  rw [hbase]
  rw [coeff_single_a_bool_b_mul n k hk2]
  rw [coeff_single_a_directABFactorsList_prod_mul M n k hk2]
  rw [BridgeAKappaTwoIdentityThreeResidualActive.coeff_single_boolFactorPoly]
  simp

theorem coeff_single_a_inert_va_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
        ((inertFactorsList M n k hk1 hk2).prod *
          (vaFactorsFromCoeffs n k hk2 cs).prod) = -1 := by
  have hreassoc :
      ((inertFactorsList M n k hk1 hk2).prod *
          (vaFactorsFromCoeffs n k hk2 cs).prod :
        MvPolynomial (Fin n) ℚ) =
      (vaFactorsFromCoeffs n k hk2 cs).prod *
        (inertFactorsList M n k hk1 hk2).prod := by
    ring
  rw [hreassoc]
  rw [coeff_single_vaFactorsFromCoeffs_prod_mul n k hk2 cs]
  exact coeff_single_a_inertFactorsList_prod M n k hk1 hk2

theorem coeff_single_a_inert_bool_v_pderivSum_vaFactorsFromCoeffs
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
        ((inertFactorsList M n k hk1 hk2).prod *
          (boolFactorPoly n (vIdx n k hk2) *
            pderivListProdSum (vIdx n k hk2)
              (vaFactorsFromCoeffs n k hk2 cs))) =
      -cs.sum := by
  induction cs with
  | nil =>
      rw [vaFactorsFromCoeffs_nil, pderivListProdSum_nil]
      simp
  | cons c cs ih =>
      rw [vaFactorsFromCoeffs_cons, pderivListProdSum_cons]
      rw [pderiv_one_sub_C_X_mul_X_at_fst c
        (vIdx n k hk2) (aIdx n k hk2) (vIdx_ne_aIdx n k hk2)]
      have hdistrib :
          ((inertFactorsList M n k hk1 hk2).prod *
              (boolFactorPoly n (vIdx n k hk2) *
                ((-(MvPolynomial.C c * MvPolynomial.X (aIdx n k hk2))) *
                    (vaFactorsFromCoeffs n k hk2 cs).prod
                  + cadjFactorPoly c (vIdx n k hk2) (aIdx n k hk2) *
                    pderivListProdSum (vIdx n k hk2)
                      (vaFactorsFromCoeffs n k hk2 cs))) :
            MvPolynomial (Fin n) ℚ) =
          (inertFactorsList M n k hk1 hk2).prod *
            (boolFactorPoly n (vIdx n k hk2) *
              ((-(MvPolynomial.C c * MvPolynomial.X (aIdx n k hk2))) *
                (vaFactorsFromCoeffs n k hk2 cs).prod))
          + cadjFactorPoly c (vIdx n k hk2) (aIdx n k hk2) *
            ((inertFactorsList M n k hk1 hk2).prod *
              (boolFactorPoly n (vIdx n k hk2) *
                pderivListProdSum (vIdx n k hk2)
                  (vaFactorsFromCoeffs n k hk2 cs))) := by
        ring
      rw [hdistrib, MvPolynomial.coeff_add]
      have hhead :
          MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
            ((inertFactorsList M n k hk1 hk2).prod *
              (boolFactorPoly n (vIdx n k hk2) *
                ((-(MvPolynomial.C c * MvPolynomial.X (aIdx n k hk2))) *
                  (vaFactorsFromCoeffs n k hk2 cs).prod))) = -c := by
        have hreassoc :
            ((inertFactorsList M n k hk1 hk2).prod *
              (boolFactorPoly n (vIdx n k hk2) *
                ((-(MvPolynomial.C c * MvPolynomial.X (aIdx n k hk2))) *
                  (vaFactorsFromCoeffs n k hk2 cs).prod)) :
              MvPolynomial (Fin n) ℚ) =
            (MvPolynomial.C (-c)) *
              (MvPolynomial.X (aIdx n k hk2) *
                ((inertFactorsList M n k hk1 hk2).prod *
                  (boolFactorPoly n (vIdx n k hk2) *
                    (vaFactorsFromCoeffs n k hk2 cs).prod))) := by
          rw [map_neg]
          ring
        rw [hreassoc]
        rw [MvPolynomial.coeff_C_mul]
        rw [MvPolynomial.coeff_X_mul']
        have hamem :
            aIdx n k hk2 ∈ (Finsupp.single (aIdx n k hk2) 1 : Fin n →₀ Nat).support := by
          rw [Finsupp.mem_support_iff]
          simp
        rw [if_pos hamem]
        have hsub :
            (Finsupp.single (aIdx n k hk2) 1 -
                Finsupp.single (aIdx n k hk2) 1 : Fin n →₀ Nat) = 0 := by
          ext x
          by_cases hx : x = aIdx n k hk2
          · subst x
            simp
          · simp
        rw [hsub]
        have hzero :
            MvPolynomial.coeff 0
              ((inertFactorsList M n k hk1 hk2).prod *
                (boolFactorPoly n (vIdx n k hk2) *
                  (vaFactorsFromCoeffs n k hk2 cs).prod)) = 1 := by
          have hI := coeff_zero_inertFactorsList_prod M n k hk1 hk2
          have hB := coeff_zero_boolFactorPoly (vIdx n k hk2)
          have hD := coeff_zero_vaFactorsFromCoeffs_prod n k hk2 cs
          rw [coeff_zero_mul]
          rw [hI]
          rw [coeff_zero_mul]
          rw [hB, hD]
          ring
        rw [hzero]
        ring
      have htail :
          MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
            (cadjFactorPoly c (vIdx n k hk2) (aIdx n k hk2) *
              ((inertFactorsList M n k hk1 hk2).prod *
                (boolFactorPoly n (vIdx n k hk2) *
                  pderivListProdSum (vIdx n k hk2)
                    (vaFactorsFromCoeffs n k hk2 cs)))) =
            -cs.sum := by
        rw [coeff_single_factor_mul_of_coeff_zero_one_of_coeff_single_zero]
        · exact ih
        · exact coeff_zero_cadjFactorPoly c _ _
        · exact coeff_X_a_one_sub_C_X_mul_X
            (aIdx n k hk2) (vIdx n k hk2) (aIdx n k hk2)
            (vIdx_ne_aIdx n k hk2) c
      rw [hhead, htail]
      simp
      ring

theorem pderivListProdSum_single
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (i : σ) (f : MvPolynomial σ R) :
    pderivListProdSum i [f] = MvPolynomial.pderiv i f := by
  rw [pderivListProdSum_cons, pderivListProdSum_nil]
  simp

theorem coeff_single_a_inert_pderivSum_v_activeVA
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
        ((inertFactorsList M n k hk1 hk2).prod *
          pderivListProdSum (vIdx n k hk2)
            (activeVAFactorsList M n k hk1 hk2)) =
      -transCoeffSum M := by
  rw [activeVAFactorsList_eq_bool_v_vaFactorsFromCoeffs M n k hk1 hk2]
  rw [pderivListProdSum_append]
  rw [pderivListProdSum_single]
  rw [pderiv_one_sub_boolLC_factor_self (vIdx n k hk2)]
  have hdistrib :
      ((inertFactorsList M n k hk1 hk2).prod *
          ((-1 + 2 * MvPolynomial.X (vIdx n k hk2)) *
              (vaFactorsFromCoeffs n k hk2
                (1 :: (List.finRange M.numStates).map
                  (fun q => transCoeff M q))).prod
            + (boolFactorPoly n (vIdx n k hk2) :: []).prod *
              pderivListProdSum (vIdx n k hk2)
                (vaFactorsFromCoeffs n k hk2
                  (1 :: (List.finRange M.numStates).map
                    (fun q => transCoeff M q)))) :
        MvPolynomial (Fin n) ℚ) =
      (inertFactorsList M n k hk1 hk2).prod *
        ((-1 + 2 * MvPolynomial.X (vIdx n k hk2)) *
          (vaFactorsFromCoeffs n k hk2
            (1 :: (List.finRange M.numStates).map
              (fun q => transCoeff M q))).prod)
      + (inertFactorsList M n k hk1 hk2).prod *
        (boolFactorPoly n (vIdx n k hk2) *
          pderivListProdSum (vIdx n k hk2)
            (vaFactorsFromCoeffs n k hk2
              (1 :: (List.finRange M.numStates).map
                (fun q => transCoeff M q)))) := by
    simp
    ring
  rw [hdistrib, MvPolynomial.coeff_add]
  have hbool :
      MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
        ((inertFactorsList M n k hk1 hk2).prod *
          ((-1 + 2 * MvPolynomial.X (vIdx n k hk2)) *
            (vaFactorsFromCoeffs n k hk2
              (1 :: (List.finRange M.numStates).map
                (fun q => transCoeff M q))).prod)) = 1 := by
    have hreassoc :
        ((inertFactorsList M n k hk1 hk2).prod *
          ((-1 + 2 * MvPolynomial.X (vIdx n k hk2)) *
            (vaFactorsFromCoeffs n k hk2
              (1 :: (List.finRange M.numStates).map
                (fun q => transCoeff M q))).prod) :
          MvPolynomial (Fin n) ℚ) =
        -((inertFactorsList M n k hk1 hk2).prod *
          (vaFactorsFromCoeffs n k hk2
            (1 :: (List.finRange M.numStates).map
              (fun q => transCoeff M q))).prod)
        + MvPolynomial.C (2 : ℚ) *
          (MvPolynomial.X (vIdx n k hk2) *
            ((inertFactorsList M n k hk1 hk2).prod *
              (vaFactorsFromCoeffs n k hk2
                (1 :: (List.finRange M.numStates).map
                  (fun q => transCoeff M q))).prod)) := by
      rw [show (2 : MvPolynomial (Fin n) ℚ) = MvPolynomial.C (2 : ℚ) from by
        simp [map_ofNat]]
      ring
    rw [hreassoc, MvPolynomial.coeff_add, MvPolynomial.coeff_neg,
      MvPolynomial.coeff_C_mul]
    rw [coeff_single_X_mul_of_ne (vIdx n k hk2) (aIdx n k hk2)]
    · rw [coeff_single_a_inert_va_prod M n k hk1 hk2]
      ring
    · exact aIdx_ne_vIdx' n k hk2
  have hdirect :
      MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
        ((inertFactorsList M n k hk1 hk2).prod *
          (boolFactorPoly n (vIdx n k hk2) *
            pderivListProdSum (vIdx n k hk2)
              (vaFactorsFromCoeffs n k hk2
                (1 :: (List.finRange M.numStates).map
                  (fun q => transCoeff M q))))) =
        -(1 :: (List.finRange M.numStates).map
          (fun q => transCoeff M q)).sum :=
    coeff_single_a_inert_bool_v_pderivSum_vaFactorsFromCoeffs
      M n k hk1 hk2 _
  rw [hbool, hdirect]
  simp only [List.sum_cons]
  rw [BridgeAKappaTwoIdentityThreeResidualActive.transCoeff_finRange_list_sum M]
  ring

theorem coeff_single_a_pderivListProdSumTwice_uvFactorsFromCoeffs
    (n : Nat) (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
        (pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
          (uvFactorsFromCoeffs n k hk1 hk2 cs)) = 0 := by
  induction cs with
  | nil =>
      rw [uvFactorsFromCoeffs_nil, pderivListProdSumTwice_nil]
      simp
  | cons c cs ih =>
      rw [uvFactorsFromCoeffs_cons, pderivListProdSumTwice_cons]
      rw [pderiv_w_pderiv_v_one_sub_C_X_mul_X_ij c
        (uIdx n k hk1 hk2) (vIdx n k hk2) (uIdx_ne_vIdx n k hk1 hk2)]
      rw [pderiv_one_sub_C_X_mul_X_at_fst c
        (uIdx n k hk1 hk2) (vIdx n k hk2) (uIdx_ne_vIdx n k hk1 hk2)]
      rw [pderiv_one_sub_C_X_mul_X_at_snd c
        (uIdx n k hk1 hk2) (vIdx n k hk2) (uIdx_ne_vIdx n k hk1 hk2)]
      rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add]
      have hdiag :
          MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
            (-(MvPolynomial.C c) *
              (uvFactorsFromCoeffs n k hk1 hk2 cs).prod) = 0 := by
        rw [← map_neg, MvPolynomial.coeff_C_mul,
          coeff_single_a_uvFactorsFromCoeffs_prod]
        ring
      have hcrossV :
          MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
            ((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
              MvPolynomial.pderiv (vIdx n k hk2)
                (uvFactorsFromCoeffs n k hk1 hk2 cs).prod) = 0 := by
        rw [pderiv_list_prod]
        obtain ⟨q, hq⟩ :=
          pderivListProdSum_v_uvFactorsFromCoeffs_has_X_u_factor n k hk1 hk2 cs
        rw [hq]
        have hreassoc :
            ((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
              (MvPolynomial.X (uIdx n k hk1 hk2) * q) :
              MvPolynomial (Fin n) ℚ) =
            MvPolynomial.X (uIdx n k hk1 hk2) *
              (-(MvPolynomial.C c) * (MvPolynomial.X (vIdx n k hk2) * q)) := by
          ring
        rw [hreassoc]
        exact coeff_single_X_mul_of_ne (uIdx n k hk1 hk2) (aIdx n k hk2)
          (-(MvPolynomial.C c) * (MvPolynomial.X (vIdx n k hk2) * q))
          (fun h => uIdx_ne_aIdx n k hk1 hk2 h.symm)
      have hcrossU :
          MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
            ((-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk1 hk2))) *
              pderivListProdSum (uIdx n k hk1 hk2)
                (uvFactorsFromCoeffs n k hk1 hk2 cs)) = 0 := by
        have hreassoc :
            ((-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk1 hk2))) *
              pderivListProdSum (uIdx n k hk1 hk2)
                (uvFactorsFromCoeffs n k hk1 hk2 cs) :
              MvPolynomial (Fin n) ℚ) =
            MvPolynomial.X (uIdx n k hk1 hk2) *
              (-(MvPolynomial.C c) *
                pderivListProdSum (uIdx n k hk1 hk2)
                  (uvFactorsFromCoeffs n k hk1 hk2 cs)) := by
          ring
        rw [hreassoc]
        exact coeff_single_X_mul_of_ne (uIdx n k hk1 hk2) (aIdx n k hk2)
          (-(MvPolynomial.C c) *
            pderivListProdSum (uIdx n k hk1 hk2)
              (uvFactorsFromCoeffs n k hk1 hk2 cs))
          (fun h => uIdx_ne_aIdx n k hk1 hk2 h.symm)
      have hrec :
          MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
            (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2) *
              pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
                (uvFactorsFromCoeffs n k hk1 hk2 cs)) = 0 := by
        rw [coeff_single_mul]
        have hsingle :
            MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
              (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2)) = 0 := by
          exact coeff_X_a_one_sub_C_X_mul_X
            (aIdx n k hk2) (uIdx n k hk1 hk2) (vIdx n k hk2)
            (uIdx_ne_vIdx n k hk1 hk2) c
        rw [hsingle, coeff_zero_cadjFactorPoly, ih]
        ring
      rw [hdiag, hcrossV, hcrossU, hrec]
      ring

theorem coeff_probeLeft_pderivListProdSumTwice_uvFactorsFromCoeffs
    (n : Nat) (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
          (uvFactorsFromCoeffs n k hk1 hk2 cs)) = 0 := by
  induction cs with
  | nil =>
      rw [uvFactorsFromCoeffs_nil, pderivListProdSumTwice_nil]
      simp
  | cons c cs ih =>
      rw [uvFactorsFromCoeffs_cons, pderivListProdSumTwice_cons]
      rw [pderiv_w_pderiv_v_one_sub_C_X_mul_X_ij c
        (uIdx n k hk1 hk2) (vIdx n k hk2) (uIdx_ne_vIdx n k hk1 hk2)]
      rw [pderiv_one_sub_C_X_mul_X_at_fst c
        (uIdx n k hk1 hk2) (vIdx n k hk2) (uIdx_ne_vIdx n k hk1 hk2)]
      rw [pderiv_one_sub_C_X_mul_X_at_snd c
        (uIdx n k hk1 hk2) (vIdx n k hk2) (uIdx_ne_vIdx n k hk1 hk2)]
      rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add]
      have hdiag :
          MvPolynomial.coeff (probeLeft n k hk2)
            (-(MvPolynomial.C c) *
              (uvFactorsFromCoeffs n k hk1 hk2 cs).prod) = 0 := by
        rw [← map_neg, MvPolynomial.coeff_C_mul,
          coeff_probeLeft_uvFactorsFromCoeffs_prod]
        ring
      have hcrossV :
          MvPolynomial.coeff (probeLeft n k hk2)
            ((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
              MvPolynomial.pderiv (vIdx n k hk2)
                (uvFactorsFromCoeffs n k hk1 hk2 cs).prod) = 0 := by
        rw [pderiv_list_prod]
        obtain ⟨q, hq⟩ :=
          pderivListProdSum_v_uvFactorsFromCoeffs_has_X_u_factor n k hk1 hk2 cs
        rw [hq]
        have hreassoc :
            ((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
              (MvPolynomial.X (uIdx n k hk1 hk2) * q) :
              MvPolynomial (Fin n) ℚ) =
            MvPolynomial.X (uIdx n k hk1 hk2) *
              (-(MvPolynomial.C c) * (MvPolynomial.X (vIdx n k hk2) * q)) := by
          ring
        rw [hreassoc, probeLeft_eq_v_a n k hk2]
        exact BridgeAKappaTwoIdentityThreeAux.coeff_X_a_X_b_X_u_mul_zero
          (vIdx n k hk2) (aIdx n k hk2) (uIdx n k hk1 hk2)
          (-(MvPolynomial.C c) * (MvPolynomial.X (vIdx n k hk2) * q))
          (fun h => uIdx_ne_vIdx n k hk1 hk2 h)
          (fun h => uIdx_ne_aIdx n k hk1 hk2 h)
      have hcrossU :
          MvPolynomial.coeff (probeLeft n k hk2)
            ((-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk1 hk2))) *
              pderivListProdSum (uIdx n k hk1 hk2)
                (uvFactorsFromCoeffs n k hk1 hk2 cs)) = 0 := by
        have hreassoc :
            ((-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk1 hk2))) *
              pderivListProdSum (uIdx n k hk1 hk2)
                (uvFactorsFromCoeffs n k hk1 hk2 cs) :
              MvPolynomial (Fin n) ℚ) =
            MvPolynomial.X (uIdx n k hk1 hk2) *
              (-(MvPolynomial.C c) *
                pderivListProdSum (uIdx n k hk1 hk2)
                  (uvFactorsFromCoeffs n k hk1 hk2 cs)) := by
          ring
        rw [hreassoc, probeLeft_eq_v_a n k hk2]
        exact BridgeAKappaTwoIdentityThreeAux.coeff_X_a_X_b_X_u_mul_zero
          (vIdx n k hk2) (aIdx n k hk2) (uIdx n k hk1 hk2)
          (-(MvPolynomial.C c) *
            pderivListProdSum (uIdx n k hk1 hk2)
              (uvFactorsFromCoeffs n k hk1 hk2 cs))
          (fun h => uIdx_ne_vIdx n k hk1 hk2 h)
          (fun h => uIdx_ne_aIdx n k hk1 hk2 h)
      have hrec :
          MvPolynomial.coeff (probeLeft n k hk2)
            (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2) *
              pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
                (uvFactorsFromCoeffs n k hk1 hk2 cs)) = 0 := by
        rw [probeLeft_eq_v_a n k hk2]
        rw [coeff_two_mono_mul (vIdx n k hk2) (aIdx n k hk2)
          (vIdx_ne_aIdx n k hk2)]
        have hsingle_v :
            MvPolynomial.coeff (Finsupp.single (vIdx n k hk2) 1)
              (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2)) = 0 := by
          exact coeff_X_a_one_sub_C_X_mul_X
            (vIdx n k hk2) (uIdx n k hk1 hk2) (vIdx n k hk2)
            (uIdx_ne_vIdx n k hk1 hk2) c
        have hsingle_a :
            MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
              (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2)) = 0 := by
          exact coeff_X_a_one_sub_C_X_mul_X
            (aIdx n k hk2) (uIdx n k hk1 hk2) (vIdx n k hk2)
            (uIdx_ne_vIdx n k hk1 hk2) c
        have hprobe :
            MvPolynomial.coeff
                (Finsupp.single (vIdx n k hk2) 1 +
                  Finsupp.single (aIdx n k hk2) 1)
                (cadjFactorPoly c (uIdx n k hk1 hk2) (vIdx n k hk2)) = 0 := by
          rw [coeff_X_v_X_w_cadjFactorPoly c
            (uIdx n k hk1 hk2) (vIdx n k hk2)
            (vIdx n k hk2) (aIdx n k hk2)
            (uIdx_ne_vIdx n k hk1 hk2) (vIdx_ne_aIdx n k hk2)]
          simp
          intro h
          have hu := congrArg (fun s : Fin n →₀ Nat => s (uIdx n k hk1 hk2)) h
          simp [uIdx_ne_vIdx n k hk1 hk2, uIdx_ne_aIdx n k hk1 hk2] at hu
        rw [hsingle_v, hsingle_a, hprobe, coeff_zero_cadjFactorPoly]
        rw [coeff_single_v_pderivListProdSumTwice_uvFactorsFromCoeffs n k hk1 hk2 cs]
        rw [coeff_single_a_pderivListProdSumTwice_uvFactorsFromCoeffs n k hk1 hk2 cs]
        rw [probeLeft_eq_v_a n k hk2] at ih
        rw [ih]
        rw [coeff_zero_pderivListProdSumTwice_uvFactorsFromCoeffs n k hk1 hk2 cs]
        ring
      rw [hdiag, hcrossV, hcrossU, hrec]
      ring

/-! ## Section E: self and cross active sums for identity (4) -/

theorem coeff_probeLeft_inert_activeVA_uvFactorsFromCoeffs_twice
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2)
        ((inertFactorsList M n k hk1 hk2).prod *
          (pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
              (uvFactorsFromCoeffs n k hk1 hk2 cs) *
            (activeVAFactorsList M n k hk1 hk2).prod)) =
      cs.sum * transCoeffSum M := by
  have hreassoc :
      ((inertFactorsList M n k hk1 hk2).prod *
          (pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
              (uvFactorsFromCoeffs n k hk1 hk2 cs) *
            (activeVAFactorsList M n k hk1 hk2).prod) :
        MvPolynomial (Fin n) ℚ) =
      pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
          (uvFactorsFromCoeffs n k hk1 hk2 cs) *
        ((inertFactorsList M n k hk1 hk2).prod *
          (activeVAFactorsList M n k hk1 hk2).prod) := by
    ring
  rw [hreassoc, probeLeft_eq_v_a n k hk2]
  rw [coeff_two_mono_mul (vIdx n k hk2) (aIdx n k hk2)
    (vIdx_ne_aIdx n k hk2)]
  have hTprobe :=
    coeff_probeLeft_pderivListProdSumTwice_uvFactorsFromCoeffs
      n k hk1 hk2 cs
  rw [probeLeft_eq_v_a n k hk2] at hTprobe
  have hBprobe := coeff_probeLeft_inert_activeVA_prod M n k hk1 hk2
  rw [probeLeft_eq_v_a n k hk2] at hBprobe
  rw [coeff_single_v_pderivListProdSumTwice_uvFactorsFromCoeffs n k hk1 hk2 cs]
  rw [coeff_single_a_pderivListProdSumTwice_uvFactorsFromCoeffs n k hk1 hk2 cs]
  rw [hTprobe]
  rw [coeff_zero_pderivListProdSumTwice_uvFactorsFromCoeffs n k hk1 hk2 cs]
  rw [hBprobe]
  ring

theorem coeff_probeLeft_inert_cross_uvFactorsFromCoeffs_activeVA
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2)
        ((inertFactorsList M n k hk1 hk2).prod *
          (pderivListProdSum (uIdx n k hk1 hk2)
              (uvFactorsFromCoeffs n k hk1 hk2 cs) *
            pderivListProdSum (vIdx n k hk2)
              (activeVAFactorsList M n k hk1 hk2))) =
      cs.sum * transCoeffSum M := by
  have hreassoc :
      ((inertFactorsList M n k hk1 hk2).prod *
          (pderivListProdSum (uIdx n k hk1 hk2)
              (uvFactorsFromCoeffs n k hk1 hk2 cs) *
            pderivListProdSum (vIdx n k hk2)
              (activeVAFactorsList M n k hk1 hk2)) :
        MvPolynomial (Fin n) ℚ) =
      pderivListProdSum (uIdx n k hk1 hk2)
          (uvFactorsFromCoeffs n k hk1 hk2 cs) *
        ((inertFactorsList M n k hk1 hk2).prod *
          pderivListProdSum (vIdx n k hk2)
            (activeVAFactorsList M n k hk1 hk2)) := by
    ring
  rw [hreassoc, probeLeft_eq_v_a n k hk2]
  rw [coeff_two_mono_mul (vIdx n k hk2) (aIdx n k hk2)
    (vIdx_ne_aIdx n k hk2)]
  have hAprobe :=
    coeff_probeLeft_pderivListProdSum_u_uvFactorsFromCoeffs
      n k hk1 hk2 cs
  rw [probeLeft_eq_v_a n k hk2] at hAprobe
  rw [coeff_single_v_pderivListProdSum_u_uvFactorsFromCoeffs n k hk1 hk2 cs]
  rw [coeff_single_a_pderivListProdSum_u_uvFactorsFromCoeffs n k hk1 hk2 cs]
  rw [hAprobe]
  rw [coeff_zero_pderivListProdSum_u_uvFactorsFromCoeffs n k hk1 hk2 cs]
  rw [coeff_single_a_inert_pderivSum_v_activeVA M n k hk1 hk2]
  ring

/-! ## Section F: residual claim and public per-pair closure -/

def identityFour_residualActiveClaim
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) : Prop :=
  MvPolynomial.coeff (probeLeft n k hk2)
      ((inertFactorsList M n k hk1 hk2).prod *
        pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
          (activeFactorsList M n k hk1 hk2)) =
    2 * crossBlockKValue (transCoeffSum M)

theorem identityFour_residualActiveClaim_holds
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    identityFour_residualActiveClaim M n k hk1 hk2 := by
  unfold identityFour_residualActiveClaim
  rw [pderivListProdSumTwice_activeFactors_decompose M n k hk1 hk2]
  have hdistrib :
      ((inertFactorsList M n k hk1 hk2).prod *
          (pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
              (activeUVFactorsList M n k hk1 hk2) *
            (activeVAFactorsList M n k hk1 hk2).prod
          + pderivListProdSum (uIdx n k hk1 hk2)
              (activeUVFactorsList M n k hk1 hk2) *
            pderivListProdSum (vIdx n k hk2)
              (activeVAFactorsList M n k hk1 hk2)) :
        MvPolynomial (Fin n) ℚ) =
      (inertFactorsList M n k hk1 hk2).prod *
        (pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
            (activeUVFactorsList M n k hk1 hk2) *
          (activeVAFactorsList M n k hk1 hk2).prod)
      + (inertFactorsList M n k hk1 hk2).prod *
        (pderivListProdSum (uIdx n k hk1 hk2)
            (activeUVFactorsList M n k hk1 hk2) *
          pderivListProdSum (vIdx n k hk2)
            (activeVAFactorsList M n k hk1 hk2)) := by
    ring
  rw [hdistrib, MvPolynomial.coeff_add]
  rw [activeUVFactorsList_eq_uvFactorsFromCoeffs M n k hk1 hk2]
  rw [coeff_probeLeft_inert_activeVA_uvFactorsFromCoeffs_twice M n k hk1 hk2]
  rw [coeff_probeLeft_inert_cross_uvFactorsFromCoeffs_activeVA M n k hk1 hk2]
  simp only [List.sum_cons]
  rw [BridgeAKappaTwoIdentityThreeResidualActive.transCoeff_finRange_list_sum M]
  unfold crossBlockKValue
  ring

theorem identityFour_perPairSum_of_decomposition
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (hperm : touchedListPoly_perm_partition_claim M n k hk1 hk2)
    (hres : identityFour_residualActiveClaim M n k hk1 hk2) :
    BridgeAKappaTwoIdentityFour.identityFour_perPairSum
      M n hn htb hns k hk1 hk2 := by
  unfold BridgeAKappaTwoIdentityFour.identityFour_perPairSum
  have hu := rowLeft_first_eq_uIdx n k hk1 hk2
  have hv := rowLeft_second_eq_vIdx n k hk2
  rw [hu, hv]
  have hpermSum :
      pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
        (BridgeAKappaTwoIdentityThreeStructural.touchedListPoly M n k hk1 hk2) =
      pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
        (inertFactorsList M n k hk1 hk2 ++ activeFactorsList M n k hk1 hk2) := by
    apply BridgeAKappaTwoIdentityThreeStructural.pderivListProdSumTwice_perm
    exact hperm
  have hinert :
      pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
        (inertFactorsList M n k hk1 hk2 ++ activeFactorsList M n k hk1 hk2) =
      (inertFactorsList M n k hk1 hk2).prod *
        pderivListProdSumTwice (uIdx n k hk1 hk2) (vIdx n k hk2)
          (activeFactorsList M n k hk1 hk2) := by
    apply pderivListProdSumTwice_append_inert_prefix
    · intro f hf
      exact inertFactorsList_inert_at_u M n k hk1 hk2 f hf
    · intro f hf
      exact inertFactorsList_inert_at_v M n k hk1 hk2 f hf
  rw [← (show
      BridgeAKappaTwoIdentityThreeStructural.touchedListPoly M n k hk1 hk2 =
        (kappaTwoTouchedList_explicit M n k hk1 hk2).map
          (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly) from rfl)]
  rw [hpermSum, hinert]
  exact hres

theorem identityFour_perPairSum
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    BridgeAKappaTwoIdentityFour.identityFour_perPairSum
      M n hn htb hns k hk1 hk2 :=
  identityFour_perPairSum_of_decomposition
    M n hn htb hns k hk1 hk2
    (touchedListPoly_perm_partition M n k hk1 hk2)
    (identityFour_residualActiveClaim_holds M n k hk1 hk2)

theorem kappaTwoIdentityFour
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (mlProj (iterDerivList (rowLeft n k hk1 hk2)
          (cookLevinLocalBlockQ M n hn htb hns
            ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
      2 * crossBlockKValue (transCoeffSum M) :=
  BridgeAKappaTwoIdentityFour.kappaTwoIdentityFour
    M n hn htb hns k hk1 hk2
    (identityFour_perPairSum M n hn htb hns k hk1 hk2)

end BridgeAKappaTwoIdentityFourResidualActive

end PallLean.Paper93.Paper283
