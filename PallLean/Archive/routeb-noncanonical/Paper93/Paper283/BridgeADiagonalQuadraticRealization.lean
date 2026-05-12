import PallLean.MlProjFar
import PallLean.IterDerivHelpers
import PallLean.Paper93.Paper283.BridgeACompilerLocalPolynomial

/-!
# Bridge A diagonal quadratic local realization

This file isolates the smallest nonzero local-polynomial instance of the
normalized Bridge A target.  The candidate is the one-variable diagonal
quadratic `X 0 * X 0`; at `kappa = 1` its derivative row is a nonzero
multiple of `X 0`, while the allowed degree-one shift by `X 0` is killed by
`mlProj`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open SPDP

namespace BridgeADiagonalQuadraticRealization

attribute [local instance] Classical.dec

/-- The singleton-block local partition for the one-coordinate test gadget. -/
noncomputable def oneVarPartition : BlockPartition 1 where
  numBlocks := 1
  assign := fun _ => 0

/-- The one-variable diagonal quadratic candidate `X_0^2`. -/
noncomputable def oneVarDiagonalQuadratic : MvPolynomial (Fin 1) Rat :=
  X (0 : Fin 1) * X (0 : Fin 1)

/-- The only length-one row is block-admissible for the singleton partition. -/
theorem oneVar_singleton_admissible :
    isBlockAdmissible oneVarPartition [(0 : Fin 1)] := by
  constructor
  · simp
  · intro b
    fin_cases b
    simp [oneVarPartition]

/-- `mlProj` fixes the lone linear monomial. -/
theorem mlProj_X_one :
    mlProj (X (0 : Fin 1) : MvPolynomial (Fin 1) Rat) =
      X (0 : Fin 1) := by
  change mlProj (MvPolynomial.monomial (Finsupp.single (0 : Fin 1) 1) (1 : Rat)) =
    MvPolynomial.monomial (Finsupp.single (0 : Fin 1) 1) (1 : Rat)
  have hml : Finsupp.IsMultilinear (Finsupp.single (0 : Fin 1) 1) := by
    intro i
    fin_cases i
    simp
  rw [mlProj_monomial, if_pos hml]

/-- `mlProj` kills the lone square monomial. -/
theorem mlProj_X_sq_zero_one :
    mlProj (X (0 : Fin 1) * X (0 : Fin 1) :
      MvPolynomial (Fin 1) Rat) = 0 := by
  have hmon :
      (X (0 : Fin 1) : MvPolynomial (Fin 1) Rat) * X (0 : Fin 1) =
        MvPolynomial.monomial
          (Finsupp.single (0 : Fin 1) 1 + Finsupp.single (0 : Fin 1) 1)
          (1 * 1 : Rat) := by
    rw [MvPolynomial.X, MvPolynomial.monomial_mul]
  rw [hmon, mul_one]
  have hadd :
      Finsupp.single (0 : Fin 1) 1 + Finsupp.single (0 : Fin 1) 1 =
        Finsupp.single (0 : Fin 1) 2 := by
    apply Finsupp.ext
    intro i
    fin_cases i
    simp
  have hnot : ¬ Finsupp.IsMultilinear (Finsupp.single (0 : Fin 1) 2) := by
    intro hml
    have := hml (0 : Fin 1)
    simp at this
  rw [hadd, mlProj_monomial, if_neg hnot]

/-- The first derivative of the one-variable diagonal quadratic is `2 * X_0`. -/
theorem pderiv_oneVarDiagonalQuadratic :
    pderiv (0 : Fin 1) oneVarDiagonalQuadratic =
      (2 : Rat) • X (0 : Fin 1) := by
  rw [oneVarDiagonalQuadratic, pderiv_mul, MvPolynomial.pderiv_X_self]
  simp only [one_mul, mul_one]
  rw [two_smul]

/-- The corresponding singleton iterated derivative is the same row. -/
theorem iterDerivList_oneVarDiagonalQuadratic :
    iterDerivList [(0 : Fin 1)] oneVarDiagonalQuadratic =
      (2 : Rat) • X (0 : Fin 1) := by
  rw [IterDerivHelpers.iterDerivList_single, pderiv_oneVarDiagonalQuadratic]

/-- `mlProj` preserves the unshifted derivative row. -/
theorem mlProj_iterDerivList_oneVarDiagonalQuadratic :
    mlProj (iterDerivList [(0 : Fin 1)] oneVarDiagonalQuadratic) =
      (2 : Rat) • X (0 : Fin 1) := by
  rw [iterDerivList_oneVarDiagonalQuadratic, mlProj_smul, mlProj_X_one]

/-- The degree-one self-shifted row vanishes after multilinear projection. -/
theorem mlProj_X_mul_iterDerivList_oneVarDiagonalQuadratic :
    mlProj (X (0 : Fin 1) *
        iterDerivList [(0 : Fin 1)] oneVarDiagonalQuadratic) = 0 := by
  rw [iterDerivList_oneVarDiagonalQuadratic]
  rw [show X (0 : Fin 1) * ((2 : Rat) • X (0 : Fin 1)) =
      (2 : Rat) • (X (0 : Fin 1) * X (0 : Fin 1)) by
    simp [MvPolynomial.smul_eq_C_mul, mul_assoc, mul_comm]]
  rw [mlProj_smul, mlProj_X_sq_zero_one, smul_zero]

/-- The linear row `X_0` lies in the `kappa = ell = 1` blocked multilinear
SPDP subspace of the one-variable diagonal quadratic. -/
theorem X_mem_oneVarDiagonalQuadratic_subspace :
    X (0 : Fin 1) ∈
      mlBlockedSpdpSubspace oneVarPartition 1 1 oneVarDiagonalQuadratic := by
  have hrow :
      (2 : Rat) • X (0 : Fin 1) ∈
        mlBlockedSpdpSubspace oneVarPartition 1 1 oneVarDiagonalQuadratic := by
    have hgen :=
      mlProj_deriv_mem oneVarPartition 1 1 oneVarDiagonalQuadratic
        [(0 : Fin 1)] (by simp) oneVar_singleton_admissible
    have hgen' :
        mlProj (iterDerivList [(0 : Fin 1)] oneVarDiagonalQuadratic) ∈
          mlBlockedSpdpSubspace oneVarPartition 1 1 oneVarDiagonalQuadratic := by
      simpa [one_mul] using hgen
    rwa [mlProj_iterDerivList_oneVarDiagonalQuadratic] at hgen'
  have hscale :
      ((1 / 2 : Rat) •
          ((2 : Rat) • (X (0 : Fin 1) : MvPolynomial (Fin 1) Rat))) =
        (X (0 : Fin 1) : MvPolynomial (Fin 1) Rat) := by
    rw [smul_smul]
    norm_num
  rw [← hscale]
  exact Submodule.smul_mem _ (1 / 2 : Rat) hrow

/-- The coordinate polynomial `X_0` is nonzero. -/
theorem X_one_ne_zero :
    (X (0 : Fin 1) : MvPolynomial (Fin 1) Rat) ≠ 0 := by
  intro hx
  have hcoeff := congrArg
    (fun p => coeff (Finsupp.single (0 : Fin 1) 1) p) hx
  simp at hcoeff

/-- The nonzero lower bound already forced by the diagonal row. -/
theorem one_le_rank_oneVarDiagonalQuadratic :
    1 ≤ mlBlockedSpdpRank oneVarPartition 1 1 oneVarDiagonalQuadratic := by
  unfold mlBlockedSpdpRank
  by_contra h
  have hzero :
      Module.finrank Rat
        (mlBlockedSpdpSubspace oneVarPartition 1 1 oneVarDiagonalQuadratic) = 0 := by
    omega
  have hbot :
      mlBlockedSpdpSubspace oneVarPartition 1 1 oneVarDiagonalQuadratic = ⊥ := by
    rw [← Submodule.finrank_eq_zero (R := Rat)]
    exact hzero
  have hxbot :
      X (0 : Fin 1) ∈
        (⊥ : Submodule Rat (MvPolynomial (Fin 1) Rat)) := by
    simpa [hbot] using X_mem_oneVarDiagonalQuadratic_subspace
  have hx : X (0 : Fin 1) = (0 : MvPolynomial (Fin 1) Rat) := by
    change X (0 : Fin 1) = (0 : MvPolynomial (Fin 1) Rat) at hxbot
    exact hxbot
  exact X_one_ne_zero hx

/-- Every row lies in the two-dimensional multilinear monomial envelope
`span {1, X_0}`.  This is the currently checked upper containment; sharpening
it to the line `span {X_0}` is exactly the remaining equality step below. -/
theorem oneVarDiagonalQuadratic_subspace_le_multilinearBasis :
    mlBlockedSpdpSubspace oneVarPartition 1 1 oneVarDiagonalQuadratic ≤
      Submodule.span Rat
        (↑(MlProjFar.mlMonomialBasis (Finset.univ : Finset (Fin 1))) :
          Set (MvPolynomial (Fin 1) Rat)) := by
  unfold mlBlockedSpdpSubspace
  apply Submodule.span_le.mpr
  rintro q ⟨S, m, _hlen, _hdeg, _hvars, _hadm, hq⟩
  rw [hq]
  apply MlProjFar.mlProj_in_span_of_vars_subset
  · intro α hα
    change α ∈
      (Finsupp.filter (fun α => Finsupp.IsMultilinear α)
        (m * iterDerivList S oneVarDiagonalQuadratic)).support at hα
    rw [Finsupp.support_filter] at hα
    exact (Finset.mem_filter.mp hα).2
  · intro i _hi
    exact Finset.mem_univ i

/-- The checked finite upper bound following from the multilinear envelope. -/
theorem oneVarDiagonalQuadratic_rank_le_two :
    mlBlockedSpdpRank oneVarPartition 1 1 oneVarDiagonalQuadratic ≤ 2 := by
  unfold mlBlockedSpdpRank
  have h :=
    MlProjFar.finrank_le_of_vars_bounded
      (W := mlBlockedSpdpSubspace oneVarPartition 1 1 oneVarDiagonalQuadratic)
      (V := (Finset.univ : Finset (Fin 1)))
      oneVarDiagonalQuadratic_subspace_le_multilinearBasis
  simpa using h

/-- In one variable, the multilinear monomial envelope is contained in
`span {1, X_0}`. -/
theorem oneVar_multilinearBasis_le_span_one_X :
    Submodule.span Rat
        (↑(MlProjFar.mlMonomialBasis (Finset.univ : Finset (Fin 1))) :
          Set (MvPolynomial (Fin 1) Rat)) ≤
      Submodule.span Rat
        ({(1 : MvPolynomial (Fin 1) Rat),
          X (0 : Fin 1)} : Set (MvPolynomial (Fin 1) Rat)) := by
  apply Submodule.span_mono
  intro p hp
  simp only [MlProjFar.mlMonomialBasis, Finset.coe_image, Set.mem_image] at hp
  rcases hp with ⟨T, _hT, rfl⟩
  by_cases h0 : (0 : Fin 1) ∈ T
  · have hT : T = {(0 : Fin 1)} := by
      ext i
      fin_cases i
      simp [h0]
    rw [hT]
    simp
  · have hT : T = ∅ := by
      ext i
      fin_cases i
      simp [h0]
    rw [hT]
    simp

/-- The constant coefficient is unchanged by multilinear projection. -/
theorem constantCoeff_mlProj_oneVar
    (q : MvPolynomial (Fin 1) Rat) :
    MvPolynomial.constantCoeff (mlProj q) =
      MvPolynomial.constantCoeff q := by
  change coeff (0 : Fin 1 →₀ Nat) (mlProj q) = coeff 0 q
  exact coeff_mlProj_of_isMultilinear_mono q 0 (by intro i; simp)

/-- Any length-one derivative list over `Fin 1` is the singleton row. -/
theorem iterDerivList_oneVarDiagonalQuadratic_of_length_one
    (S : List (Fin 1)) (hlen : S.length = 1) :
    iterDerivList S oneVarDiagonalQuadratic =
      (2 : Rat) • X (0 : Fin 1) := by
  cases S with
  | nil =>
      simp at hlen
  | cons a rest =>
      have hrest_len : rest.length = 0 := by
        have hlen' : Nat.succ rest.length = Nat.succ 0 := by
          simpa using hlen
        exact Nat.succ.inj hlen'
      have hrest : rest = [] := List.length_eq_zero_iff.mp hrest_len
      subst hrest
      fin_cases a
      exact iterDerivList_oneVarDiagonalQuadratic

/-- Every raw generator has zero constant coefficient. -/
theorem constantCoeff_oneVarDiagonalQuadratic_generator_zero
    (S : List (Fin 1)) (m : MvPolynomial (Fin 1) Rat)
    (hlen : S.length = 1) :
    MvPolynomial.constantCoeff
        (mlProj (m * iterDerivList S oneVarDiagonalQuadratic)) = 0 := by
  rw [constantCoeff_mlProj_oneVar]
  rw [iterDerivList_oneVarDiagonalQuadratic_of_length_one S hlen]
  rw [map_mul]
  simp [MvPolynomial.constantCoeff_eq]

/-- The whole one-variable diagonal subspace has zero constant coefficient. -/
theorem oneVarDiagonalQuadratic_subspace_le_constantCoeffKer :
    mlBlockedSpdpSubspace oneVarPartition 1 1 oneVarDiagonalQuadratic ≤
      LinearMap.ker (MvPolynomial.lcoeff Rat (0 : Fin 1 →₀ Nat)) := by
  unfold mlBlockedSpdpSubspace
  apply Submodule.span_le.mpr
  rintro q ⟨S, m, hlen, _hdeg, _hvars, _hadm, hq⟩
  change coeff (0 : Fin 1 →₀ Nat) q = 0
  rw [hq]
  simpa [MvPolynomial.constantCoeff_eq] using
    constantCoeff_oneVarDiagonalQuadratic_generator_zero S m hlen

/-- Inside `span {1, X_0}`, zero constant coefficient forces membership in
the line `span {X_0}`. -/
theorem mem_span_X_of_mem_span_one_X_of_constantCoeff_zero
    {q : MvPolynomial (Fin 1) Rat}
    (hspan :
      q ∈ Submodule.span Rat
        ({(1 : MvPolynomial (Fin 1) Rat),
          X (0 : Fin 1)} : Set (MvPolynomial (Fin 1) Rat)))
    (hconst : MvPolynomial.constantCoeff q = 0) :
    q ∈ (Rat ∙ (X (0 : Fin 1) : MvPolynomial (Fin 1) Rat) :
      Submodule Rat (MvPolynomial (Fin 1) Rat)) := by
  rw [Submodule.mem_span_pair] at hspan
  rcases hspan with ⟨a, b, hq⟩
  have ha : a = 0 := by
    have hc := congrArg MvPolynomial.constantCoeff hq
    rw [hconst] at hc
    simpa [MvPolynomial.constantCoeff_eq] using hc
  rw [← hq, ha, zero_smul, zero_add]
  exact Submodule.smul_mem _ b (Submodule.mem_span_singleton_self _)

/-- The sharp upper-containment subgoal left by the exact one-variable rank
calculation.  It says that the constant row in the checked two-dimensional
envelope never appears. -/
def oneVarDiagonalQuadratic_sharpUpperContainment : Prop :=
  mlBlockedSpdpSubspace oneVarPartition 1 1 oneVarDiagonalQuadratic ≤
    (Rat ∙ (X (0 : Fin 1) : MvPolynomial (Fin 1) Rat) :
      Submodule Rat (MvPolynomial (Fin 1) Rat))

/-- The sharp upper-containment subgoal is in fact discharged for the
one-variable diagonal quadratic. -/
theorem oneVarDiagonalQuadratic_sharpUpperContainment_holds :
    oneVarDiagonalQuadratic_sharpUpperContainment := by
  intro q hq
  apply mem_span_X_of_mem_span_one_X_of_constantCoeff_zero
  · exact oneVar_multilinearBasis_le_span_one_X
      (oneVarDiagonalQuadratic_subspace_le_multilinearBasis hq)
  · have hker := oneVarDiagonalQuadratic_subspace_le_constantCoeffKer hq
    simpa [LinearMap.mem_ker, MvPolynomial.lcoeff_apply,
      MvPolynomial.constantCoeff_eq] using hker

/-- The exact normalized `kappa = 1`, `gadgetN = 1` Bridge A local target. -/
def oneVarDiagonalQuadratic_exactRankTarget : Prop :=
  mlBlockedSpdpRank oneVarPartition 1 1 oneVarDiagonalQuadratic = 1

/-- Once the remaining sharp containment is proved, the normalized rank target
for `kappa = 1`, `gadgetN = 1` follows immediately. -/
theorem oneVarDiagonalQuadratic_exactRank_of_sharpUpper
    (hupper : oneVarDiagonalQuadratic_sharpUpperContainment) :
    oneVarDiagonalQuadratic_exactRankTarget := by
  have hle : mlBlockedSpdpRank oneVarPartition 1 1 oneVarDiagonalQuadratic ≤ 1 := by
    unfold mlBlockedSpdpRank
    calc
      Module.finrank Rat
          (mlBlockedSpdpSubspace oneVarPartition 1 1 oneVarDiagonalQuadratic)
          ≤ Module.finrank Rat
              (Rat ∙ (X (0 : Fin 1) : MvPolynomial (Fin 1) Rat) :
                Submodule Rat (MvPolynomial (Fin 1) Rat)) :=
            Submodule.finrank_mono hupper
      _ = 1 := by
            rw [finrank_span_singleton X_one_ne_zero]
  unfold oneVarDiagonalQuadratic_exactRankTarget
  exact le_antisymm hle one_le_rank_oneVarDiagonalQuadratic

/-- The kernel-checked nonzero normalized local polynomial realization for
`kappa = 1` and `gadgetN = 1`. -/
theorem oneVarDiagonalQuadratic_exactRank :
    oneVarDiagonalQuadratic_exactRankTarget :=
  oneVarDiagonalQuadratic_exactRank_of_sharpUpper
    oneVarDiagonalQuadratic_sharpUpperContainment_holds

/-- The exact `gadgetN = 1` normalized Bridge A local-polynomial package:
`kappa = 1`, one local variable, and `Q_v = X_0^2`. -/
noncomputable def oneVarDiagonalQuadratic_normalizedLocalPolynomial
    {N d : Nat} (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N → Real) (v : Fin N) :
    BridgeAPerVertexLocalPolynomialNormalized
      alpha beta alpha0 1 1 G chi Phi v where
  spdpVars := 1
  partition := oneVarPartition
  Qv := oneVarDiagonalQuadratic
  rank_eq_normalized := by
    simpa [oneVarDiagonalQuadratic_exactRankTarget] using
      oneVarDiagonalQuadratic_exactRank

/-!
The exact equality target for this file is:

`mlBlockedSpdpRank oneVarPartition 1 1 oneVarDiagonalQuadratic = 1`.

The lemmas above prove the kernel-checked nonzero lower bound and the key
row computations: the unshifted row spans `X_0`, and the only nonconstant
degree-one shift candidate `X_0 * ∂_0 Q` is killed by `mlProj`.
-/

#print axioms pderiv_oneVarDiagonalQuadratic
#print axioms iterDerivList_oneVarDiagonalQuadratic
#print axioms mlProj_iterDerivList_oneVarDiagonalQuadratic
#print axioms mlProj_X_mul_iterDerivList_oneVarDiagonalQuadratic
#print axioms X_mem_oneVarDiagonalQuadratic_subspace
#print axioms one_le_rank_oneVarDiagonalQuadratic
#print axioms oneVarDiagonalQuadratic_subspace_le_multilinearBasis
#print axioms oneVarDiagonalQuadratic_rank_le_two
#print axioms oneVarDiagonalQuadratic_exactRank_of_sharpUpper
#print axioms oneVarDiagonalQuadratic_sharpUpperContainment_holds
#print axioms oneVarDiagonalQuadratic_exactRank
#print axioms oneVarDiagonalQuadratic_normalizedLocalPolynomial

end BridgeADiagonalQuadraticRealization

end PallLean.Paper93.Paper283
