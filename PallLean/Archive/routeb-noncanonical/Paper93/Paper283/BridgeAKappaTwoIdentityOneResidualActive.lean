import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityOneAux
import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityTwoResidualActive
import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityThreeResidualActive

/-!
# Residual active claim for identity (1) per-pair sum

Identity (1) uses the same derivative rows as identity (3), namely
`(3k+2, 3k+3)`, but takes the right probe
`X_{3k+1} * X_{3k+2}`.  We therefore reuse the identity-(3)
inert/active partition and redo only the right-probe coefficient
computation.
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
open BridgeAKappaTwoIdentityThreeAux
open BridgeAKappaTwoIdentityThreeStructural
open BridgeAKappaTwoIdentityThreeResidualActive
open BridgeAKappaTwoListInductionHelpers
open MultilinearCoefficientInfrastructure

attribute [local instance] Classical.dec

namespace BridgeAKappaTwoIdentityOneResidualActive

/-! ## Section A: right-probe preservation lemmas -/

theorem probeRight_eq_b_u
    (n k : Nat) (hk2 : 3 * k + 3 < n) :
    probeRight n k hk2 =
      Finsupp.single (bIdx n k hk2) 1 + Finsupp.single (uIdx n k hk2) 1 := by
  unfold probeRight bIdx uIdx
  rfl

theorem coeff_single_factor_mul_of_coeff_zero_one_of_coeff_single_zero {N : Nat}
    (x : Fin N) (f p : MvPolynomial (Fin N) ℚ)
    (hf0 : MvPolynomial.coeff 0 f = 1)
    (hfx : MvPolynomial.coeff (Finsupp.single x 1) f = 0) :
    MvPolynomial.coeff (Finsupp.single x 1) (f * p) =
      MvPolynomial.coeff (Finsupp.single x 1) p := by
  rw [coeff_single_mul x f p]
  rw [hf0, hfx]
  ring

theorem coeff_zero_mul {N : Nat}
    (p q : MvPolynomial (Fin N) ℚ) :
    MvPolynomial.coeff 0 (p * q) =
      MvPolynomial.coeff 0 p * MvPolynomial.coeff 0 q := by
  rw [MvPolynomial.coeff_mul]
  simp

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

theorem coeff_single_X_mul_of_ne {N : Nat}
    (x y : Fin N) (p : MvPolynomial (Fin N) ℚ) (hyx : y ≠ x) :
    MvPolynomial.coeff (Finsupp.single x 1) (MvPolynomial.X y * p) = 0 := by
  rw [MvPolynomial.coeff_X_mul' (Finsupp.single x 1) y p]
  rw [if_neg]
  intro hmem
  rw [Finsupp.mem_support_iff] at hmem
  apply hmem
  rw [Finsupp.single_apply, if_neg (fun h => hyx h.symm)]

theorem coeff_X_a_X_b_X_b_mul {N : Nat}
    (a b : Fin N) (p : MvPolynomial (Fin N) ℚ) (hab : a ≠ b) :
    MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
        (MvPolynomial.X b * p) =
      MvPolynomial.coeff (Finsupp.single a 1) p := by
  rw [MvPolynomial.coeff_X_mul'
    (Finsupp.single a 1 + Finsupp.single b 1) b p]
  have hbmem :
      b ∈ (Finsupp.single a 1 + Finsupp.single b 1 : Fin N →₀ Nat).support := by
    rw [Finsupp.mem_support_iff]
    rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    rw [if_neg hab, if_pos rfl]
    norm_num
  rw [if_pos hbmem]
  congr 1
  ext x
  by_cases hxa : x = a
  · subst x
    simp
  · by_cases hxb : x = b
    · subst x
      simp [hxa]
    · simp [hxa]

theorem coeff_single_boolFactorPoly_mul_of_ne
    (n k : Nat) (hk2 : 3 * k + 3 < n)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (Finsupp.single (bIdx n k hk2) 1)
        (boolFactorPoly n (aIdx n k hk2) * p) =
      MvPolynomial.coeff (Finsupp.single (bIdx n k hk2) 1) p := by
  apply coeff_single_factor_mul_of_coeff_zero_one_of_coeff_single_zero
  · exact coeff_zero_boolFactorPoly _
  · rw [coeff_single_boolFactorPoly]
    rw [if_neg (fun h => aIdx_ne_bIdx n k hk2 h.symm)]

theorem coeff_probeRight_bool_a_mul
    (n k : Nat) (hk2 : 3 * k + 3 < n)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeRight n k hk2)
        (boolFactorPoly n (aIdx n k hk2) * p) =
      MvPolynomial.coeff (probeRight n k hk2) p := by
  rw [probeRight_eq_b_u]
  exact coeff_X_a_X_b_boolFactorPoly_mul
    (bIdx n k hk2) (uIdx n k hk2) (aIdx n k hk2) p
    (aIdx_ne_bIdx n k hk2)
    (aIdx_ne_uIdx n k hk2)

theorem coeff_probeRight_cadj_a_b_mul
    (n k : Nat) (hk2 : 3 * k + 3 < n)
    (c : ℚ) (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeRight n k hk2)
        (cadjFactorPoly c (aIdx n k hk2) (bIdx n k hk2) * p) =
      MvPolynomial.coeff (probeRight n k hk2) p := by
  rw [probeRight_eq_b_u]
  exact coeff_X_a_X_b_cadjFactorPoly_mul_stray_fst
    (bIdx n k hk2) (uIdx n k hk2)
    (aIdx n k hk2) (bIdx n k hk2) c p
    (aIdx_ne_bIdx n k hk2)
    (aIdx_ne_uIdx n k hk2)

theorem coeff_probeRight_cadj_u_v_mul
    (n k : Nat) (hk2 : 3 * k + 3 < n)
    (c : ℚ) (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeRight n k hk2)
        (cadjFactorPoly c (uIdx n k hk2) (vIdx n k hk2) * p) =
      MvPolynomial.coeff (probeRight n k hk2) p := by
  rw [probeRight_eq_b_u]
  exact coeff_X_a_X_b_cadjFactorPoly_mul_stray_snd
    (bIdx n k hk2) (uIdx n k hk2)
    (uIdx n k hk2) (vIdx n k hk2) c p
    (fun h => bIdx_ne_vIdx n k hk2 h.symm)
    (fun h => uIdx_ne_vIdx n k hk2 h.symm)

theorem coeff_probeRight_cadj_prev_a_mul
    (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (c : ℚ) (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeRight n k hk2)
        (cadjFactorPoly c
          (⟨3 * k - 1, by omega⟩ : Fin n)
          (⟨3 * k - 1 + 1, by omega⟩ : Fin n) * p) =
      MvPolynomial.coeff (probeRight n k hk2) p := by
  rw [probeRight_eq_b_u]
  exact coeff_X_a_X_b_cadjFactorPoly_mul_stray_snd
    (bIdx n k hk2) (uIdx n k hk2)
    (⟨3 * k - 1, by omega⟩ : Fin n)
    (⟨3 * k - 1 + 1, by omega⟩ : Fin n) c p
    (by
      intro h
      have := congr_arg Fin.val h
      unfold bIdx at this
      simp at this
      omega)
    (by
      intro h
      have := congr_arg Fin.val h
      unfold uIdx at this
      simp at this)

theorem coeff_probeRight_prevABFactorsList_prod_mul
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeRight n k hk2)
        ((prevABFactorsList M n k hk1 hk2).prod * p) =
      MvPolynomial.coeff (probeRight n k hk2) p := by
  rw [probeRight_eq_b_u]
  apply coeff_X_a_X_b_list_prod_mul_of_forall_preserve
  intro f hf p'
  rw [← probeRight_eq_b_u]
  unfold prevABFactorsList prevABFactorsListFrom at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with rfl | ⟨q, _hq, rfl⟩
  · exact coeff_probeRight_cadj_prev_a_mul n k hk1 hk2 1 p'
  · exact coeff_probeRight_cadj_prev_a_mul n k hk1 hk2 (transCoeff M q) p'

theorem coeff_probeRight_directLeftABFactorsList_prod_mul
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeRight n k hk2)
        ((directABFactorsList M n k hk2).prod * p) =
      MvPolynomial.coeff (probeRight n k hk2) p := by
  rw [probeRight_eq_b_u]
  apply coeff_X_a_X_b_list_prod_mul_of_forall_preserve
  intro f hf p'
  rw [← probeRight_eq_b_u]
  unfold directABFactorsList transABFactorsListFrom at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with rfl | ⟨q, _hq, rfl⟩
  · exact coeff_probeRight_cadj_a_b_mul n k hk2 1 p'
  · exact coeff_probeRight_cadj_a_b_mul n k hk2 (transCoeff M q) p'

/-! ## Section B: the inert product times `BU` has coefficient `-S` -/

theorem activeBUFactorsList_eq_bool_u_directRightAB
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    activeBUFactorsList M n k hk1 hk2 =
      [boolFactorPoly n (uIdx n k hk2)] ++
        BridgeAKappaTwoIdentityTwoResidualActive.directABFactorsList M n k hk2 := by
  unfold activeBUFactorsList
  unfold BridgeAKappaTwoIdentityTwoResidualActive.directABFactorsList
  unfold BridgeAKappaTwoIdentityTwoResidualActive.transABFactorsListFrom
  unfold BridgeAKappaTwoIdentityTwoResidualActive.aIdx
  unfold BridgeAKappaTwoIdentityTwoResidualActive.bIdx
  unfold bIdx uIdx
  rfl

theorem coeff_probeRight_bool_b_activeBU_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeRight n k hk2)
        (boolFactorPoly n (bIdx n k hk2) *
          (activeBUFactorsList M n k hk1 hk2).prod) =
      -transCoeffSum M := by
  rw [activeBUFactorsList_eq_bool_u_directRightAB M n k hk1 hk2]
  have hprod :
      (boolFactorPoly n (bIdx n k hk2) *
          ([boolFactorPoly n (uIdx n k hk2)] ++
            BridgeAKappaTwoIdentityTwoResidualActive.directABFactorsList
              M n k hk2).prod :
        MvPolynomial (Fin n) ℚ) =
      (boolFactorPoly n
          (BridgeAKappaTwoIdentityTwoResidualActive.aIdx n k hk2) *
        boolFactorPoly n
          (BridgeAKappaTwoIdentityTwoResidualActive.bIdx n k hk2)) *
        (BridgeAKappaTwoIdentityTwoResidualActive.directABFactorsList
          M n k hk2).prod := by
    unfold BridgeAKappaTwoIdentityTwoResidualActive.aIdx
    unfold BridgeAKappaTwoIdentityTwoResidualActive.bIdx
    unfold bIdx uIdx
    simp
    ring
  rw [hprod]
  exact BridgeAKappaTwoIdentityTwoResidualActive.coeff_probeRight_boolPair_directAB_prod
    M n k hk2

theorem coeff_probeRight_inert_activeBU_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeRight n k hk2)
        ((inertFactorsList M n k hk1 hk2).prod *
          (activeBUFactorsList M n k hk1 hk2).prod) =
      -transCoeffSum M := by
  have hperm :=
    inertFactorsList_perm_prev_base M n k hk1 hk2
  rw [List.Perm.prod_eq hperm]
  rw [List.prod_append]
  have hreassoc₁ :
      ((prevABFactorsList M n k hk1 hk2).prod *
          (([boolFactorPoly n (aIdx n k hk2),
              boolFactorPoly n (bIdx n k hk2)] ++
              directABFactorsList M n k hk2).prod) *
          (activeBUFactorsList M n k hk1 hk2).prod :
        MvPolynomial (Fin n) ℚ) =
      (prevABFactorsList M n k hk1 hk2).prod *
        ((([boolFactorPoly n (aIdx n k hk2),
            boolFactorPoly n (bIdx n k hk2)] ++
            directABFactorsList M n k hk2).prod) *
          (activeBUFactorsList M n k hk1 hk2).prod) := by
    ring
  rw [hreassoc₁]
  rw [coeff_probeRight_prevABFactorsList_prod_mul M n k hk1 hk2]
  have hbase :
      ((([boolFactorPoly n (aIdx n k hk2),
          boolFactorPoly n (bIdx n k hk2)] ++
          directABFactorsList M n k hk2).prod) *
          (activeBUFactorsList M n k hk1 hk2).prod :
        MvPolynomial (Fin n) ℚ) =
      boolFactorPoly n (aIdx n k hk2) *
        ((directABFactorsList M n k hk2).prod *
          (boolFactorPoly n (bIdx n k hk2) *
            (activeBUFactorsList M n k hk1 hk2).prod)) := by
    simp
    ring
  rw [hbase]
  rw [coeff_probeRight_bool_a_mul n k hk2]
  rw [coeff_probeRight_directLeftABFactorsList_prod_mul M n k hk2]
  exact coeff_probeRight_bool_b_activeBU_prod M n k hk1 hk2

/-! ## Section C: single coefficient of the `BU` derivative -/

theorem coeff_single_b_prevABFactorsList_prod_mul
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (Finsupp.single (bIdx n k hk2) 1)
        ((prevABFactorsList M n k hk1 hk2).prod * p) =
      MvPolynomial.coeff (Finsupp.single (bIdx n k hk2) 1) p := by
  apply coeff_single_list_prod_mul_of_forall_preserve
  · intro f hf
    unfold prevABFactorsList prevABFactorsListFrom at hf
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatMap, List.mem_finRange] at hf
    rcases hf with rfl | ⟨q, _hq, rfl⟩
    · exact coeff_zero_cadjFactorPoly 1 _ _
    · exact coeff_zero_cadjFactorPoly (transCoeff M q) _ _
  · intro f hf
    unfold prevABFactorsList prevABFactorsListFrom at hf
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatMap, List.mem_finRange] at hf
    rcases hf with rfl | ⟨q, _hq, rfl⟩
    · exact coeff_X_a_one_sub_C_X_mul_X
        (bIdx n k hk2)
        (⟨3 * k - 1, by omega⟩ : Fin n)
        (⟨3 * k - 1 + 1, by omega⟩ : Fin n)
        (by
          intro h
          have := congr_arg Fin.val h
          simp at this)
        1
    · exact coeff_X_a_one_sub_C_X_mul_X
        (bIdx n k hk2)
        (⟨3 * k - 1, by omega⟩ : Fin n)
        (⟨3 * k - 1 + 1, by omega⟩ : Fin n)
        (by
          intro h
          have := congr_arg Fin.val h
          simp at this)
        (transCoeff M q)

theorem coeff_single_b_directLeftABFactorsList_prod_mul
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (Finsupp.single (bIdx n k hk2) 1)
        ((directABFactorsList M n k hk2).prod * p) =
      MvPolynomial.coeff (Finsupp.single (bIdx n k hk2) 1) p := by
  apply coeff_single_list_prod_mul_of_forall_preserve
  · exact directABFactorsList_forall_coeff_zero_one M n k hk2
  · exact directABFactorsList_forall_coeff_single_zero M n k hk2 (bIdx n k hk2)

theorem coeff_single_b_inertFactorsList_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (Finsupp.single (bIdx n k hk2) 1)
        (inertFactorsList M n k hk1 hk2).prod = -1 := by
  have hperm :=
    inertFactorsList_perm_prev_base M n k hk1 hk2
  rw [List.Perm.prod_eq hperm]
  rw [List.prod_append]
  rw [coeff_single_b_prevABFactorsList_prod_mul M n k hk1 hk2]
  have hbase :
      ((([boolFactorPoly n (aIdx n k hk2),
          boolFactorPoly n (bIdx n k hk2)] ++
          directABFactorsList M n k hk2).prod) :
        MvPolynomial (Fin n) ℚ) =
      boolFactorPoly n (aIdx n k hk2) *
        ((directABFactorsList M n k hk2).prod *
          boolFactorPoly n (bIdx n k hk2)) := by
    rw [List.prod_append]
    simp only [List.prod_cons, List.prod_nil, mul_one]
    ring
  rw [hbase]
  rw [coeff_single_boolFactorPoly_mul_of_ne n k hk2]
  rw [coeff_single_b_directLeftABFactorsList_prod_mul M n k hk2]
  rw [coeff_single_boolFactorPoly]
  simp

noncomputable def rightABFactorsFromCoeffs
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) : List (MvPolynomial (Fin n) ℚ) :=
  cs.map (fun c => cadjFactorPoly c (bIdx n k hk2) (uIdx n k hk2))

@[simp] theorem rightABFactorsFromCoeffs_nil
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n) :
    rightABFactorsFromCoeffs n k hk2 [] = [] := by
  unfold rightABFactorsFromCoeffs
  rfl

@[simp] theorem rightABFactorsFromCoeffs_cons
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (c : ℚ) (cs : List ℚ) :
    rightABFactorsFromCoeffs n k hk2 (c :: cs) =
      cadjFactorPoly c (bIdx n k hk2) (uIdx n k hk2) ::
        rightABFactorsFromCoeffs n k hk2 cs := by
  unfold rightABFactorsFromCoeffs
  rfl

theorem directRightABFactorsList_eq_fromCoeffs
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n) :
    BridgeAKappaTwoIdentityTwoResidualActive.directABFactorsList M n k hk2 =
      rightABFactorsFromCoeffs n k hk2
        (1 :: (List.finRange M.numStates).map (fun q => transCoeff M q)) := by
  unfold BridgeAKappaTwoIdentityTwoResidualActive.directABFactorsList
  unfold BridgeAKappaTwoIdentityTwoResidualActive.transABFactorsListFrom
  unfold BridgeAKappaTwoIdentityTwoResidualActive.aIdx
  unfold BridgeAKappaTwoIdentityTwoResidualActive.bIdx
  unfold rightABFactorsFromCoeffs bIdx uIdx
  simp only [List.map_cons, List.singleton_append, List.map_map]
  have htail := List.flatMap_pure_eq_map
    (fun q : Fin M.numStates =>
      cadjFactorPoly (transCoeff M q)
        (⟨3 * k + 1, by omega⟩ : Fin n)
        (⟨3 * k + 2, by omega⟩ : Fin n))
    (List.finRange M.numStates)
  simpa [Function.comp_def] using
    congrArg
      (fun t =>
        cadjFactorPoly 1
          (⟨3 * k + 1, by omega⟩ : Fin n)
          (⟨3 * k + 2, by omega⟩ : Fin n) :: t)
      htail

theorem rightABFactorsFromCoeffs_forall_coeff_zero_one
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ rightABFactorsFromCoeffs n k hk2 cs) :
    MvPolynomial.coeff 0 f = 1 := by
  unfold rightABFactorsFromCoeffs at hf
  simp only [List.mem_map] at hf
  obtain ⟨c, _hc, rfl⟩ := hf
  exact coeff_zero_cadjFactorPoly c _ _

theorem coeff_zero_rightABFactorsFromCoeffs_prod
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff 0 (rightABFactorsFromCoeffs n k hk2 cs).prod = 1 :=
  ListProdDerivativeConstantCoeff.coeff_zero_list_prod_eq_one_of_forall
    (rightABFactorsFromCoeffs n k hk2 cs)
    (rightABFactorsFromCoeffs_forall_coeff_zero_one n k hk2 cs)

theorem rightABFactorsFromCoeffs_forall_coeff_single_zero
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) (x : Fin n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ rightABFactorsFromCoeffs n k hk2 cs) :
    MvPolynomial.coeff (Finsupp.single x 1) f = 0 := by
  unfold rightABFactorsFromCoeffs at hf
  simp only [List.mem_map] at hf
  obtain ⟨c, _hc, rfl⟩ := hf
  exact coeff_X_a_one_sub_C_X_mul_X
    x (bIdx n k hk2) (uIdx n k hk2) (bIdx_ne_uIdx n k hk2) c

theorem coeff_single_rightABFactorsFromCoeffs_prod_mul
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) (x : Fin n) (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (Finsupp.single x 1)
        ((rightABFactorsFromCoeffs n k hk2 cs).prod * p) =
      MvPolynomial.coeff (Finsupp.single x 1) p := by
  apply coeff_single_list_prod_mul_of_forall_preserve
  · exact rightABFactorsFromCoeffs_forall_coeff_zero_one n k hk2 cs
  · exact rightABFactorsFromCoeffs_forall_coeff_single_zero n k hk2 cs x

theorem coeff_single_b_inert_rightAB_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff (Finsupp.single (bIdx n k hk2) 1)
        ((inertFactorsList M n k hk1 hk2).prod *
          (rightABFactorsFromCoeffs n k hk2 cs).prod) = -1 := by
  have hreassoc :
      ((inertFactorsList M n k hk1 hk2).prod *
          (rightABFactorsFromCoeffs n k hk2 cs).prod :
        MvPolynomial (Fin n) ℚ) =
      (rightABFactorsFromCoeffs n k hk2 cs).prod *
        (inertFactorsList M n k hk1 hk2).prod := by
    ring
  rw [hreassoc]
  rw [coeff_single_rightABFactorsFromCoeffs_prod_mul n k hk2 cs]
  exact coeff_single_b_inertFactorsList_prod M n k hk1 hk2

theorem coeff_single_b_inert_bool_u_pderivSum_rightABFactorsFromCoeffs
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff (Finsupp.single (bIdx n k hk2) 1)
        ((inertFactorsList M n k hk1 hk2).prod *
          (boolFactorPoly n (uIdx n k hk2) *
            pderivListProdSum (uIdx n k hk2)
              (rightABFactorsFromCoeffs n k hk2 cs))) =
      -cs.sum := by
  induction cs with
  | nil =>
      rw [rightABFactorsFromCoeffs_nil, pderivListProdSum_nil]
      simp
  | cons c cs ih =>
      rw [rightABFactorsFromCoeffs_cons, pderivListProdSum_cons]
      rw [pderiv_one_sub_C_X_mul_X_at_snd c
        (bIdx n k hk2) (uIdx n k hk2) (bIdx_ne_uIdx n k hk2)]
      have hdistrib :
          ((inertFactorsList M n k hk1 hk2).prod *
              (boolFactorPoly n (uIdx n k hk2) *
                ((-(MvPolynomial.C c * MvPolynomial.X (bIdx n k hk2))) *
                    (rightABFactorsFromCoeffs n k hk2 cs).prod
                  + cadjFactorPoly c (bIdx n k hk2) (uIdx n k hk2) *
                    pderivListProdSum (uIdx n k hk2)
                      (rightABFactorsFromCoeffs n k hk2 cs))) :
            MvPolynomial (Fin n) ℚ) =
          (inertFactorsList M n k hk1 hk2).prod *
            (boolFactorPoly n (uIdx n k hk2) *
              ((-(MvPolynomial.C c * MvPolynomial.X (bIdx n k hk2))) *
                (rightABFactorsFromCoeffs n k hk2 cs).prod))
          + cadjFactorPoly c (bIdx n k hk2) (uIdx n k hk2) *
            ((inertFactorsList M n k hk1 hk2).prod *
              (boolFactorPoly n (uIdx n k hk2) *
                pderivListProdSum (uIdx n k hk2)
                  (rightABFactorsFromCoeffs n k hk2 cs))) := by
        ring
      rw [hdistrib, MvPolynomial.coeff_add]
      have hhead :
          MvPolynomial.coeff (Finsupp.single (bIdx n k hk2) 1)
            ((inertFactorsList M n k hk1 hk2).prod *
              (boolFactorPoly n (uIdx n k hk2) *
                ((-(MvPolynomial.C c * MvPolynomial.X (bIdx n k hk2))) *
                  (rightABFactorsFromCoeffs n k hk2 cs).prod))) = -c := by
        have hreassoc :
            ((inertFactorsList M n k hk1 hk2).prod *
              (boolFactorPoly n (uIdx n k hk2) *
                ((-(MvPolynomial.C c * MvPolynomial.X (bIdx n k hk2))) *
                  (rightABFactorsFromCoeffs n k hk2 cs).prod)) :
              MvPolynomial (Fin n) ℚ) =
            (MvPolynomial.C (-c)) *
              (MvPolynomial.X (bIdx n k hk2) *
                ((inertFactorsList M n k hk1 hk2).prod *
                  (boolFactorPoly n (uIdx n k hk2) *
                    (rightABFactorsFromCoeffs n k hk2 cs).prod))) := by
          rw [map_neg]
          ring
        rw [hreassoc]
        rw [MvPolynomial.coeff_C_mul]
        rw [MvPolynomial.coeff_X_mul']
        have hbmem :
            bIdx n k hk2 ∈ (Finsupp.single (bIdx n k hk2) 1 : Fin n →₀ Nat).support := by
          rw [Finsupp.mem_support_iff]
          simp
        rw [if_pos hbmem]
        have hsub :
            (Finsupp.single (bIdx n k hk2) 1 -
                Finsupp.single (bIdx n k hk2) 1 : Fin n →₀ Nat) = 0 := by
          ext x
          by_cases hx : x = bIdx n k hk2
          · subst x
            simp
          · simp
        rw [hsub]
        have hzero :
            MvPolynomial.coeff 0
              ((inertFactorsList M n k hk1 hk2).prod *
                (boolFactorPoly n (uIdx n k hk2) *
                  (rightABFactorsFromCoeffs n k hk2 cs).prod)) = 1 := by
          have hI := coeff_zero_inertFactorsList_prod M n k hk1 hk2
          have hB := coeff_zero_boolFactorPoly (uIdx n k hk2)
          have hD := coeff_zero_rightABFactorsFromCoeffs_prod n k hk2 cs
          rw [coeff_zero_mul]
          rw [hI]
          rw [coeff_zero_mul]
          rw [hB, hD]
          ring
        rw [hzero]
        ring
      have htail :
          MvPolynomial.coeff (Finsupp.single (bIdx n k hk2) 1)
            (cadjFactorPoly c (bIdx n k hk2) (uIdx n k hk2) *
              ((inertFactorsList M n k hk1 hk2).prod *
                (boolFactorPoly n (uIdx n k hk2) *
                  pderivListProdSum (uIdx n k hk2)
                    (rightABFactorsFromCoeffs n k hk2 cs)))) =
            -cs.sum := by
        rw [coeff_single_factor_mul_of_coeff_zero_one_of_coeff_single_zero]
        · exact ih
        · exact coeff_zero_cadjFactorPoly c _ _
        · exact coeff_X_a_one_sub_C_X_mul_X
            (bIdx n k hk2) (bIdx n k hk2) (uIdx n k hk2)
            (bIdx_ne_uIdx n k hk2) c
      rw [hhead, htail]
      simp
      ring

theorem pderivListProdSum_single
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (i : σ) (f : MvPolynomial σ R) :
    pderivListProdSum i [f] = MvPolynomial.pderiv i f := by
  rw [pderivListProdSum_cons, pderivListProdSum_nil]
  simp

theorem coeff_single_b_inert_pderivSum_u_activeBU
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (Finsupp.single (bIdx n k hk2) 1)
        ((inertFactorsList M n k hk1 hk2).prod *
          pderivListProdSum (uIdx n k hk2)
            (activeBUFactorsList M n k hk1 hk2)) =
      -transCoeffSum M := by
  rw [activeBUFactorsList_eq_bool_u_directRightAB M n k hk1 hk2]
  rw [directRightABFactorsList_eq_fromCoeffs M n k hk2]
  rw [pderivListProdSum_append]
  rw [pderivListProdSum_single]
  rw [pderiv_one_sub_boolLC_factor_self (uIdx n k hk2)]
  have hdistrib :
      ((inertFactorsList M n k hk1 hk2).prod *
          ((-1 + 2 * MvPolynomial.X (uIdx n k hk2)) *
              (rightABFactorsFromCoeffs n k hk2
                (1 :: (List.finRange M.numStates).map
                  (fun q => transCoeff M q))).prod
            + (boolFactorPoly n (uIdx n k hk2) :: []).prod *
              pderivListProdSum (uIdx n k hk2)
                (rightABFactorsFromCoeffs n k hk2
                  (1 :: (List.finRange M.numStates).map
                    (fun q => transCoeff M q)))) :
        MvPolynomial (Fin n) ℚ) =
      (inertFactorsList M n k hk1 hk2).prod *
        ((-1 + 2 * MvPolynomial.X (uIdx n k hk2)) *
          (rightABFactorsFromCoeffs n k hk2
            (1 :: (List.finRange M.numStates).map
              (fun q => transCoeff M q))).prod)
      + (inertFactorsList M n k hk1 hk2).prod *
        (boolFactorPoly n (uIdx n k hk2) *
          pderivListProdSum (uIdx n k hk2)
            (rightABFactorsFromCoeffs n k hk2
              (1 :: (List.finRange M.numStates).map
                (fun q => transCoeff M q)))) := by
    simp
    ring
  rw [hdistrib, MvPolynomial.coeff_add]
  have hbool :
      MvPolynomial.coeff (Finsupp.single (bIdx n k hk2) 1)
        ((inertFactorsList M n k hk1 hk2).prod *
          ((-1 + 2 * MvPolynomial.X (uIdx n k hk2)) *
            (rightABFactorsFromCoeffs n k hk2
              (1 :: (List.finRange M.numStates).map
                (fun q => transCoeff M q))).prod)) = 1 := by
    have hreassoc :
        ((inertFactorsList M n k hk1 hk2).prod *
          ((-1 + 2 * MvPolynomial.X (uIdx n k hk2)) *
            (rightABFactorsFromCoeffs n k hk2
              (1 :: (List.finRange M.numStates).map
                (fun q => transCoeff M q))).prod) :
          MvPolynomial (Fin n) ℚ) =
        -((inertFactorsList M n k hk1 hk2).prod *
          (rightABFactorsFromCoeffs n k hk2
            (1 :: (List.finRange M.numStates).map
              (fun q => transCoeff M q))).prod)
        + (2 : MvPolynomial (Fin n) ℚ) *
          (MvPolynomial.X (uIdx n k hk2) *
            ((inertFactorsList M n k hk1 hk2).prod *
              (rightABFactorsFromCoeffs n k hk2
                (1 :: (List.finRange M.numStates).map
                  (fun q => transCoeff M q))).prod)) := by
      ring
    rw [hreassoc]
    rw [show (2 : MvPolynomial (Fin n) ℚ) = MvPolynomial.C (2 : ℚ) from by
      simp [map_ofNat]]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_neg, MvPolynomial.coeff_C_mul]
    rw [coeff_single_X_mul_of_ne (bIdx n k hk2) (uIdx n k hk2)]
    · rw [coeff_single_b_inert_rightAB_prod M n k hk1 hk2]
      ring
    · intro h
      exact bIdx_ne_uIdx n k hk2 h.symm
  have hdirect :
      MvPolynomial.coeff (Finsupp.single (bIdx n k hk2) 1)
        ((inertFactorsList M n k hk1 hk2).prod *
          (boolFactorPoly n (uIdx n k hk2) *
            pderivListProdSum (uIdx n k hk2)
              (rightABFactorsFromCoeffs n k hk2
                (1 :: (List.finRange M.numStates).map
                  (fun q => transCoeff M q))))) =
        -(1 :: (List.finRange M.numStates).map
          (fun q => transCoeff M q)).sum :=
    coeff_single_b_inert_bool_u_pderivSum_rightABFactorsFromCoeffs
      M n k hk1 hk2 _
  rw [hbool, hdirect]
  simp only [List.sum_cons]
  rw [transCoeff_finRange_list_sum M]
  ring

theorem uvFactorsFromCoeffs_forall_coeff_zero_one_right
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ uvFactorsFromCoeffs n k hk2 cs) :
    MvPolynomial.coeff 0 f = 1 := by
  unfold uvFactorsFromCoeffs at hf
  simp only [List.mem_map] at hf
  obtain ⟨c, _hc, rfl⟩ := hf
  exact coeff_zero_cadjFactorPoly c _ _

theorem coeff_zero_uvFactorsFromCoeffs_prod_right
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff 0 (uvFactorsFromCoeffs n k hk2 cs).prod = 1 :=
  ListProdDerivativeConstantCoeff.coeff_zero_list_prod_eq_one_of_forall
    (uvFactorsFromCoeffs n k hk2 cs)
    (uvFactorsFromCoeffs_forall_coeff_zero_one_right n k hk2 cs)

theorem uvFactorsFromCoeffs_forall_coeff_single_b_zero
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ uvFactorsFromCoeffs n k hk2 cs) :
    MvPolynomial.coeff (Finsupp.single (bIdx n k hk2) 1) f = 0 := by
  unfold uvFactorsFromCoeffs at hf
  simp only [List.mem_map] at hf
  obtain ⟨c, _hc, rfl⟩ := hf
  exact coeff_X_a_one_sub_C_X_mul_X
    (bIdx n k hk2) (uIdx n k hk2) (vIdx n k hk2)
    (uIdx_ne_vIdx n k hk2) c

theorem coeff_single_b_uvFactorsFromCoeffs_prod_mul
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (Finsupp.single (bIdx n k hk2) 1)
        ((uvFactorsFromCoeffs n k hk2 cs).prod * p) =
      MvPolynomial.coeff (Finsupp.single (bIdx n k hk2) 1) p := by
  apply coeff_single_list_prod_mul_of_forall_preserve
  · exact uvFactorsFromCoeffs_forall_coeff_zero_one_right n k hk2 cs
  · exact uvFactorsFromCoeffs_forall_coeff_single_b_zero n k hk2 cs

theorem uvFactorsFromCoeffs_forall_probeRight_preserve
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ uvFactorsFromCoeffs n k hk2 cs)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeRight n k hk2) (f * p) =
      MvPolynomial.coeff (probeRight n k hk2) p := by
  unfold uvFactorsFromCoeffs at hf
  simp only [List.mem_map] at hf
  obtain ⟨c, _hc, rfl⟩ := hf
  exact coeff_probeRight_cadj_u_v_mul n k hk2 c p

theorem coeff_probeRight_uvFactorsFromCoeffs_prod_mul
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeRight n k hk2)
        ((uvFactorsFromCoeffs n k hk2 cs).prod * p) =
      MvPolynomial.coeff (probeRight n k hk2) p := by
  rw [probeRight_eq_b_u]
  apply coeff_X_a_X_b_list_prod_mul_of_forall_preserve
  intro f hf p'
  rw [← probeRight_eq_b_u]
  exact uvFactorsFromCoeffs_forall_probeRight_preserve n k hk2 cs f hf p'

theorem coeff_probeRight_inert_activeBU_cross_uvFactorsFromCoeffs
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff (probeRight n k hk2)
        ((inertFactorsList M n k hk1 hk2).prod *
          (pderivListProdSum (uIdx n k hk2)
              (activeBUFactorsList M n k hk1 hk2) *
            pderivListProdSum (vIdx n k hk2)
              (uvFactorsFromCoeffs n k hk2 cs))) =
      cs.sum * transCoeffSum M := by
  induction cs with
  | nil =>
      rw [uvFactorsFromCoeffs_nil, pderivListProdSum_nil]
      simp
  | cons c cs ih =>
      rw [uvFactorsFromCoeffs_cons, pderivListProdSum_cons]
      rw [cadj_at_3k_plus_2_active_at_v n k hk2 c]
      have hdistrib :
          ((inertFactorsList M n k hk1 hk2).prod *
            (pderivListProdSum (uIdx n k hk2)
                (activeBUFactorsList M n k hk1 hk2) *
              ((-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk2))) *
                  (uvFactorsFromCoeffs n k hk2 cs).prod
                + cadjFactorPoly c
                  (⟨3 * k + 2, by omega⟩ : Fin n)
                  (⟨3 * k + 3, hk2⟩ : Fin n) *
                  pderivListProdSum (vIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs))) :
            MvPolynomial (Fin n) ℚ) =
          (inertFactorsList M n k hk1 hk2).prod *
            (pderivListProdSum (uIdx n k hk2)
                (activeBUFactorsList M n k hk1 hk2) *
              ((-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk2))) *
                (uvFactorsFromCoeffs n k hk2 cs).prod))
          + cadjFactorPoly c
            (⟨3 * k + 2, by omega⟩ : Fin n)
            (⟨3 * k + 3, hk2⟩ : Fin n) *
            ((inertFactorsList M n k hk1 hk2).prod *
              (pderivListProdSum (uIdx n k hk2)
                  (activeBUFactorsList M n k hk1 hk2) *
                pderivListProdSum (vIdx n k hk2)
                  (uvFactorsFromCoeffs n k hk2 cs))) := by
        ring
      rw [hdistrib, MvPolynomial.coeff_add]
      have hhead :
          MvPolynomial.coeff (probeRight n k hk2)
            ((inertFactorsList M n k hk1 hk2).prod *
              (pderivListProdSum (uIdx n k hk2)
                  (activeBUFactorsList M n k hk1 hk2) *
                ((-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk2))) *
                  (uvFactorsFromCoeffs n k hk2 cs).prod))) =
            c * transCoeffSum M := by
        have hreassoc :
            ((inertFactorsList M n k hk1 hk2).prod *
              (pderivListProdSum (uIdx n k hk2)
                  (activeBUFactorsList M n k hk1 hk2) *
                ((-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk2))) *
                  (uvFactorsFromCoeffs n k hk2 cs).prod)) :
              MvPolynomial (Fin n) ℚ) =
            MvPolynomial.C (-c) *
              (MvPolynomial.X (uIdx n k hk2) *
                ((uvFactorsFromCoeffs n k hk2 cs).prod *
                  ((inertFactorsList M n k hk1 hk2).prod *
                    pderivListProdSum (uIdx n k hk2)
                      (activeBUFactorsList M n k hk1 hk2)))) := by
          rw [map_neg]
          ring
        rw [hreassoc, MvPolynomial.coeff_C_mul]
        rw [probeRight_eq_b_u]
        rw [coeff_X_a_X_b_X_b_mul (bIdx n k hk2) (uIdx n k hk2)]
        · rw [coeff_single_b_uvFactorsFromCoeffs_prod_mul]
          rw [coeff_single_b_inert_pderivSum_u_activeBU M n k hk1 hk2]
          ring
        · exact bIdx_ne_uIdx n k hk2
      have htail :
          MvPolynomial.coeff (probeRight n k hk2)
            (cadjFactorPoly c
              (⟨3 * k + 2, by omega⟩ : Fin n)
              (⟨3 * k + 3, hk2⟩ : Fin n) *
              ((inertFactorsList M n k hk1 hk2).prod *
                (pderivListProdSum (uIdx n k hk2)
                    (activeBUFactorsList M n k hk1 hk2) *
                  pderivListProdSum (vIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs)))) =
            cs.sum * transCoeffSum M := by
        change MvPolynomial.coeff (probeRight n k hk2)
            (cadjFactorPoly c (uIdx n k hk2) (vIdx n k hk2) *
              ((inertFactorsList M n k hk1 hk2).prod *
                (pderivListProdSum (uIdx n k hk2)
                    (activeBUFactorsList M n k hk1 hk2) *
                  pderivListProdSum (vIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs)))) =
            cs.sum * transCoeffSum M
        rw [coeff_probeRight_cadj_u_v_mul n k hk2 c]
        exact ih
      rw [hhead, htail]
      simp only [List.sum_cons]
      ring

/-! ## Section D: right-probe self-term and residual active closure -/

theorem uvFactorsFromCoeffs_pderiv_u_has_X_v_factor
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ uvFactorsFromCoeffs n k hk2 cs) :
    ∃ q : MvPolynomial (Fin n) ℚ,
      MvPolynomial.pderiv (uIdx n k hk2) f =
        MvPolynomial.X (vIdx n k hk2) * q := by
  unfold uvFactorsFromCoeffs at hf
  simp only [List.mem_map] at hf
  obtain ⟨c, _hc, rfl⟩ := hf
  refine ⟨-(MvPolynomial.C c), ?_⟩
  change MvPolynomial.pderiv (uIdx n k hk2)
      (cadjFactorPoly c
        (⟨3 * k + 2, by omega⟩ : Fin n)
        (⟨3 * k + 3, hk2⟩ : Fin n)) =
    MvPolynomial.X (vIdx n k hk2) * -(MvPolynomial.C c)
  rw [cadj_at_3k_plus_2_active_at_u n k hk2 c]
  ring

theorem pderivListProdSum_u_uvFactorsFromCoeffs_has_X_v_factor
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    ∃ q : MvPolynomial (Fin n) ℚ,
      pderivListProdSum (uIdx n k hk2)
          (uvFactorsFromCoeffs n k hk2 cs) =
        MvPolynomial.X (vIdx n k hk2) * q :=
  pderivListProdSum_has_X_factor_of_forall
    (vIdx n k hk2) (uIdx n k hk2)
    (uvFactorsFromCoeffs n k hk2 cs)
    (uvFactorsFromCoeffs_pderiv_u_has_X_v_factor n k hk2 cs)

theorem coeff_probeRight_inert_BU_uvFactorsFromCoeffs_twice
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff (probeRight n k hk2)
        ((inertFactorsList M n k hk1 hk2).prod *
          ((activeBUFactorsList M n k hk1 hk2).prod *
            pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
              (uvFactorsFromCoeffs n k hk2 cs))) =
      cs.sum * transCoeffSum M := by
  induction cs with
  | nil =>
      rw [uvFactorsFromCoeffs_nil, pderivListProdSumTwice_nil]
      simp
  | cons c cs ih =>
      rw [uvFactorsFromCoeffs_cons]
      rw [pderivListProdSumTwice_cons]
      rw [cadj_at_3k_plus_2_diagonal n k hk2 c]
      rw [cadj_at_3k_plus_2_active_at_u n k hk2 c]
      rw [cadj_at_3k_plus_2_active_at_v n k hk2 c]
      have hdistrib :
          ((inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                (-(MvPolynomial.C c) *
                    (uvFactorsFromCoeffs n k hk2 cs).prod
                  + (-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
                    MvPolynomial.pderiv (vIdx n k hk2)
                      (uvFactorsFromCoeffs n k hk2 cs).prod
                  + (-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk2))) *
                    pderivListProdSum (uIdx n k hk2)
                      (uvFactorsFromCoeffs n k hk2 cs)
                  + cadjFactorPoly c
                    (⟨3 * k + 2, by omega⟩ : Fin n)
                    (⟨3 * k + 3, hk2⟩ : Fin n) *
                    pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
                      (uvFactorsFromCoeffs n k hk2 cs))) :
            MvPolynomial (Fin n) ℚ) =
          (inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                (-(MvPolynomial.C c) *
                  (uvFactorsFromCoeffs n k hk2 cs).prod))
            + (inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                ((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
                  MvPolynomial.pderiv (vIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs).prod))
            + (inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                ((-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk2))) *
                  pderivListProdSum (uIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs)))
            + (inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                (cadjFactorPoly c
                  (⟨3 * k + 2, by omega⟩ : Fin n)
                  (⟨3 * k + 3, hk2⟩ : Fin n) *
                  pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs))) := by
        ring
      rw [hdistrib]
      rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add]
      have hdiag :
          MvPolynomial.coeff (probeRight n k hk2)
            ((inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                (-(MvPolynomial.C c) *
                  (uvFactorsFromCoeffs n k hk2 cs).prod))) =
            c * transCoeffSum M := by
        have hreassoc :
            ((inertFactorsList M n k hk1 hk2).prod *
                ((activeBUFactorsList M n k hk1 hk2).prod *
                  (-(MvPolynomial.C c) *
                    (uvFactorsFromCoeffs n k hk2 cs).prod)) :
              MvPolynomial (Fin n) ℚ) =
            MvPolynomial.C (-c) *
              ((uvFactorsFromCoeffs n k hk2 cs).prod *
                ((inertFactorsList M n k hk1 hk2).prod *
                  (activeBUFactorsList M n k hk1 hk2).prod)) := by
          rw [map_neg]
          ring
        rw [hreassoc, MvPolynomial.coeff_C_mul]
        rw [coeff_probeRight_uvFactorsFromCoeffs_prod_mul n k hk2 cs]
        rw [coeff_probeRight_inert_activeBU_prod M n k hk1 hk2]
        ring
      have hcrossV :
          MvPolynomial.coeff (probeRight n k hk2)
            ((inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                ((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
                  MvPolynomial.pderiv (vIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs).prod))) = 0 := by
        have hreassoc :
            ((inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                ((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
                  MvPolynomial.pderiv (vIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs).prod)) :
              MvPolynomial (Fin n) ℚ) =
            MvPolynomial.X (vIdx n k hk2) *
              (-(MvPolynomial.C c) *
                ((inertFactorsList M n k hk1 hk2).prod *
                  ((activeBUFactorsList M n k hk1 hk2).prod *
                    MvPolynomial.pderiv (vIdx n k hk2)
                      (uvFactorsFromCoeffs n k hk2 cs).prod))) := by
          ring
        rw [hreassoc, probeRight_eq_b_u]
        exact coeff_X_a_X_b_X_u_mul_zero
          (bIdx n k hk2) (uIdx n k hk2) (vIdx n k hk2)
          (-(MvPolynomial.C c) *
            ((inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                MvPolynomial.pderiv (vIdx n k hk2)
                  (uvFactorsFromCoeffs n k hk2 cs).prod)))
          (fun h => bIdx_ne_vIdx n k hk2 h.symm)
          (fun h => uIdx_ne_vIdx n k hk2 h.symm)
      have hcrossU :
          MvPolynomial.coeff (probeRight n k hk2)
            ((inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                ((-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk2))) *
                  pderivListProdSum (uIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs)))) = 0 := by
        obtain ⟨q, hq⟩ :=
          pderivListProdSum_u_uvFactorsFromCoeffs_has_X_v_factor n k hk2 cs
        rw [hq]
        have hreassoc :
            ((inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                ((-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk2))) *
                  (MvPolynomial.X (vIdx n k hk2) * q))) :
              MvPolynomial (Fin n) ℚ) =
            MvPolynomial.X (vIdx n k hk2) *
              (-(MvPolynomial.C c) *
                ((inertFactorsList M n k hk1 hk2).prod *
                  ((activeBUFactorsList M n k hk1 hk2).prod *
                    (MvPolynomial.X (uIdx n k hk2) * q)))) := by
          ring
        rw [hreassoc, probeRight_eq_b_u]
        exact coeff_X_a_X_b_X_u_mul_zero
          (bIdx n k hk2) (uIdx n k hk2) (vIdx n k hk2)
          (-(MvPolynomial.C c) *
            ((inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                (MvPolynomial.X (uIdx n k hk2) * q))))
          (fun h => bIdx_ne_vIdx n k hk2 h.symm)
          (fun h => uIdx_ne_vIdx n k hk2 h.symm)
      have hrec :
          MvPolynomial.coeff (probeRight n k hk2)
            ((inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                (cadjFactorPoly c
                  (⟨3 * k + 2, by omega⟩ : Fin n)
                  (⟨3 * k + 3, hk2⟩ : Fin n) *
                  pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs)))) =
            cs.sum * transCoeffSum M := by
        have hreassoc :
            ((inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                (cadjFactorPoly c
                  (⟨3 * k + 2, by omega⟩ : Fin n)
                  (⟨3 * k + 3, hk2⟩ : Fin n) *
                  pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs))) :
              MvPolynomial (Fin n) ℚ) =
            cadjFactorPoly c
              (⟨3 * k + 2, by omega⟩ : Fin n)
              (⟨3 * k + 3, hk2⟩ : Fin n) *
              ((inertFactorsList M n k hk1 hk2).prod *
                ((activeBUFactorsList M n k hk1 hk2).prod *
                  pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs))) := by
          ring
        rw [hreassoc]
        change MvPolynomial.coeff (probeRight n k hk2)
            (cadjFactorPoly c (uIdx n k hk2) (vIdx n k hk2) *
              ((inertFactorsList M n k hk1 hk2).prod *
                ((activeBUFactorsList M n k hk1 hk2).prod *
                  pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs)))) =
          cs.sum * transCoeffSum M
        rw [coeff_probeRight_cadj_u_v_mul n k hk2 c]
        exact ih
      rw [hdiag, hcrossV, hcrossU, hrec]
      simp only [List.sum_cons]
      ring

theorem coeff_probeRight_activeFactors_residual
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeRight n k hk2)
        ((inertFactorsList M n k hk1 hk2).prod *
          pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
            (activeFactorsList M n k hk1 hk2)) =
      2 * crossBlockKValue (transCoeffSum M) := by
  rw [pderivListProdSumTwice_activeFactors_decompose M n k hk1 hk2]
  rw [activeUVFactorsList_eq_uvFactorsFromCoeffs M n k hk1 hk2]
  have hdistrib :
      ((inertFactorsList M n k hk1 hk2).prod *
          (pderivListProdSum (uIdx n k hk2)
              (activeBUFactorsList M n k hk1 hk2) *
            pderivListProdSum (vIdx n k hk2)
              (uvFactorsFromCoeffs n k hk2
                (1 :: (List.finRange M.numStates).map
                  (fun q => transCoeff M q)))
          + (activeBUFactorsList M n k hk1 hk2).prod *
            pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
              (uvFactorsFromCoeffs n k hk2
                (1 :: (List.finRange M.numStates).map
                  (fun q => transCoeff M q)))) :
        MvPolynomial (Fin n) ℚ) =
      (inertFactorsList M n k hk1 hk2).prod *
          (pderivListProdSum (uIdx n k hk2)
              (activeBUFactorsList M n k hk1 hk2) *
            pderivListProdSum (vIdx n k hk2)
              (uvFactorsFromCoeffs n k hk2
                (1 :: (List.finRange M.numStates).map
                  (fun q => transCoeff M q))))
        + (inertFactorsList M n k hk1 hk2).prod *
          ((activeBUFactorsList M n k hk1 hk2).prod *
            pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
              (uvFactorsFromCoeffs n k hk2
                (1 :: (List.finRange M.numStates).map
                  (fun q => transCoeff M q))) ) := by
    ring
  rw [hdistrib, MvPolynomial.coeff_add]
  rw [coeff_probeRight_inert_activeBU_cross_uvFactorsFromCoeffs M n k hk1 hk2]
  rw [coeff_probeRight_inert_BU_uvFactorsFromCoeffs_twice M n k hk1 hk2]
  simp only [List.sum_cons]
  rw [transCoeff_finRange_list_sum M]
  unfold crossBlockKValue
  ring

/-! ## Section E: structural bridge to the identity (1) statement -/

theorem identityOne_perPairSum
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    BridgeAKappaTwoIdentityOne.identityOne_perPairSum
      M n hn htb hns k hk1 hk2 := by
  unfold BridgeAKappaTwoIdentityOne.identityOne_perPairSum
  have hperm :=
    BridgeAKappaTwoIdentityThreeStructural.touchedListPoly_perm_partition
      M n k hk1 hk2
  have hpermSum :
      pderivListProdSumTwice
          (⟨3 * k + 2, by omega⟩ : Fin n)
          (⟨3 * k + 3, hk2⟩ : Fin n)
          (touchedListPoly M n k hk1 hk2) =
        pderivListProdSumTwice
          (⟨3 * k + 2, by omega⟩ : Fin n)
          (⟨3 * k + 3, hk2⟩ : Fin n)
          (inertFactorsList M n k hk1 hk2 ++ activeFactorsList M n k hk1 hk2) := by
    apply pderivListProdSumTwice_perm
    exact hperm
  have htlp : touchedListPoly M n k hk1 hk2 =
      (kappaTwoTouchedList_explicit M n k hk1 hk2).map
        (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly) := rfl
  have hinert :
      pderivListProdSumTwice
          (⟨3 * k + 2, by omega⟩ : Fin n)
          (⟨3 * k + 3, hk2⟩ : Fin n)
          (inertFactorsList M n k hk1 hk2 ++ activeFactorsList M n k hk1 hk2) =
        (inertFactorsList M n k hk1 hk2).prod *
          pderivListProdSumTwice
            (⟨3 * k + 2, by omega⟩ : Fin n)
            (⟨3 * k + 3, hk2⟩ : Fin n)
            (activeFactorsList M n k hk1 hk2) := by
    apply pderivListProdSumTwice_append_inert_prefix
    · intro f hf
      have h := inertFactorsList_inert_at_u M n k hk1 hk2 f hf
      change MvPolynomial.pderiv (uIdx n k hk2) f = 0 at h
      unfold uIdx at h
      exact h
    · intro f hf
      have h := inertFactorsList_inert_at_v M n k hk1 hk2 f hf
      change MvPolynomial.pderiv (vIdx n k hk2) f = 0 at h
      unfold vIdx at h
      exact h
  rw [← htlp]
  rw [hpermSum, hinert]
  change MvPolynomial.coeff (probeRight n k hk2)
      ((inertFactorsList M n k hk1 hk2).prod *
        pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
          (activeFactorsList M n k hk1 hk2)) =
    2 * crossBlockKValue (transCoeffSum M)
  exact coeff_probeRight_activeFactors_residual M n k hk1 hk2

end BridgeAKappaTwoIdentityOneResidualActive

end PallLean.Paper93.Paper283
