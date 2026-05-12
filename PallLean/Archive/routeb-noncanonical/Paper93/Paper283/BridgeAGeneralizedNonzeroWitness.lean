import PallLean.BlockedBoolRank
import PallLean.MlProjFar
import PallLean.Paper93.Paper283.BridgeACompilerLocalPolynomial

/-!
# Generalized nonzero Bridge A local-polynomial witness attempt

This file records a nonzero generalized Bridge A construction attempt
extending `BridgeADiagonalQuadraticRealization`.

The intended exact candidate has one payload variable and `kappa` squared
helper variables for each row `r : Fin (kappa * gadgetN)`.  Differentiating
once in every helper for one row should leave a single multilinear row
monomial; mixed or incomplete strict-`kappa` derivative lists should retain
a square and be killed by `mlProj`.

The exact rank theorem for that square-helper polynomial is isolated below as
a target.  The checked progress theorem in this file is a Boolean
helper-product lower-bound model: the strict derivative rows indexed by
`Fin (kappa * gadgetN)` already force rank at least `kappa * gadgetN` for a
concrete nonzero polynomial.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open SPDP

namespace BridgeAGeneralizedNonzeroWitness

attribute [local instance] Classical.dec

/-- A discrete partition: each local variable is its own block. -/
noncomputable def discretePartition (n : Nat) : BlockPartition n where
  numBlocks := n
  assign := fun i => i

/-- In the discrete partition, every nodup list is block-admissible. -/
theorem discretePartition_admissible_of_nodup {n : Nat}
    {S : List (Fin n)} (hS : S.Nodup) :
    isBlockAdmissible (discretePartition n) S := by
  constructor
  · exact hS
  · intro b
    change (List.filter (fun i => decide (i = b)) S).length ≤ 1
    simpa [List.count, List.countP_eq_length_filter] using
      (List.nodup_iff_count_le_one.mp hS b)

/-- Number of target rows in the normalized Bridge A local rank target. -/
def rowCount (kappa gadgetN : Nat) : Nat :=
  kappa * gadgetN

/-! ## Exact square-helper candidate -/

/-- Variables for the exact candidate: one payload slot plus `kappa` helper
slots for each row. -/
def squareHelperVarCount (kappa gadgetN : Nat) : Nat :=
  rowCount kappa gadgetN * (kappa + 1)

/-- Payload variable for a row in the exact square-helper candidate. -/
def squarePayloadIndex (kappa gadgetN : Nat)
    (r : Fin (rowCount kappa gadgetN)) :
    Fin (squareHelperVarCount kappa gadgetN) :=
  finProdFinEquiv (r, (0 : Fin (kappa + 1)))

/-- The `j`th squared helper variable for row `r`. -/
def squareHelperIndex (kappa gadgetN : Nat)
    (r : Fin (rowCount kappa gadgetN)) (j : Fin kappa) :
    Fin (squareHelperVarCount kappa gadgetN) :=
  finProdFinEquiv (r, j.succ)

/-- One row term: payload times the product of squared helper variables. -/
noncomputable def squareHelperRowTerm (kappa gadgetN : Nat)
    (r : Fin (rowCount kappa gadgetN)) :
    MvPolynomial (Fin (squareHelperVarCount kappa gadgetN)) Rat :=
  X (squarePayloadIndex kappa gadgetN r) *
    ∏ j : Fin kappa,
      (X (squareHelperIndex kappa gadgetN r j) *
        X (squareHelperIndex kappa gadgetN r j))

/-- The intended exact generalized local polynomial candidate. -/
noncomputable def squareHelperQ (kappa gadgetN : Nat) :
    MvPolynomial (Fin (squareHelperVarCount kappa gadgetN)) Rat :=
  ∑ r : Fin (rowCount kappa gadgetN), squareHelperRowTerm kappa gadgetN r

/-! ## Square-helper derivative rows -/

/-- The `kappa` squared-helper variables belonging to one square-helper row. -/
noncomputable def squareRowHelperSet (kappa gadgetN : Nat)
    (r : Fin (rowCount kappa gadgetN)) :
    Finset (Fin (squareHelperVarCount kappa gadgetN)) :=
  (Finset.univ : Finset (Fin kappa)).image
    (fun j => squareHelperIndex kappa gadgetN r j)

/-- The multilinear row monomial expected after differentiating a square row
once in every helper variable. -/
noncomputable def squareRowLinearMonomial (kappa gadgetN : Nat)
    (r : Fin (rowCount kappa gadgetN)) :
    MvPolynomial (Fin (squareHelperVarCount kappa gadgetN)) Rat :=
  X (squarePayloadIndex kappa gadgetN r) *
    ∏ j : Fin kappa, X (squareHelperIndex kappa gadgetN r j)

/-- Exponent vector for the expected multilinear row monomial. -/
noncomputable def squareRowLinearExponent (kappa gadgetN : Nat)
    (r : Fin (rowCount kappa gadgetN)) :
    Fin (squareHelperVarCount kappa gadgetN) →₀ Nat :=
  Finsupp.single (squarePayloadIndex kappa gadgetN r) 1 +
    (Finset.univ : Finset (Fin kappa)).sum
      (fun j => Finsupp.single (squareHelperIndex kappa gadgetN r j) 1)

/-- The square-helper row space predicted by the exact arbitrary-`kappa`
candidate. -/
noncomputable def squareHelperRowSpace (kappa gadgetN : Nat) :
    Submodule Rat (MvPolynomial (Fin (squareHelperVarCount kappa gadgetN)) Rat) :=
  Submodule.span Rat
    (Set.range (squareRowLinearMonomial kappa gadgetN))

/-- The exact upper-containment still needed for the arbitrary-`kappa`
equality: every blocked multilinear SPDP generator of `squareHelperQ` lies in
the predicted row space. -/
def squareHelperExactUpperContainment (kappa gadgetN : Nat) : Prop :=
  mlBlockedSpdpSubspace
      (discretePartition (squareHelperVarCount kappa gadgetN))
      kappa kappa (squareHelperQ kappa gadgetN) ≤
    squareHelperRowSpace kappa gadgetN

/-- The exact normalized rank target for the intended square-helper
polynomial candidate. -/
def squareHelperExactRankTarget (kappa gadgetN : Nat) : Prop :=
  mlBlockedSpdpRank (discretePartition (squareHelperVarCount kappa gadgetN))
      kappa kappa (squareHelperQ kappa gadgetN) =
    kappa * gadgetN

/-- The concrete lower-bound Kronecker obligation for `squareHelperQ`.
Differentiating row `t` in all its squared helpers should have coefficient
`2^kappa` on row monomial `t` and zero on every other row monomial. -/
def squareHelperDerivativeRowKronecker (kappa gadgetN : Nat) : Prop :=
  ∀ s t : Fin (rowCount kappa gadgetN),
    coeff (squareRowLinearExponent kappa gadgetN s)
      (mlProj (iterDerivList (squareRowHelperSet kappa gadgetN t).toList
        (squareHelperQ kappa gadgetN))) =
      if s = t then (2 : Rat) ^ kappa else 0

/-- For a fixed row, square-helper indices are injective in the helper slot. -/
theorem squareHelperIndex_injective_right {kappa gadgetN : Nat}
    (r : Fin (rowCount kappa gadgetN)) :
    Function.Injective (squareHelperIndex kappa gadgetN r) := by
  intro a b h
  apply Fin.ext
  exact Nat.succ.inj
    (congrArg Fin.val (congrArg Prod.snd (finProdFinEquiv.injective h)))

/-- Each square row-helper set has exactly `kappa` variables. -/
theorem squareRowHelperSet_card (kappa gadgetN : Nat)
    (r : Fin (rowCount kappa gadgetN)) :
    (squareRowHelperSet kappa gadgetN r).card = kappa := by
  unfold squareRowHelperSet
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro a _ b _ h
    exact squareHelperIndex_injective_right (kappa := kappa)
      (gadgetN := gadgetN) r h

/-- Square row-helper derivative lists are admissible for the discrete
partition. -/
theorem squareRowHelperSet_toList_admissible (kappa gadgetN : Nat)
    (r : Fin (rowCount kappa gadgetN)) :
    isBlockAdmissible
      (discretePartition (squareHelperVarCount kappa gadgetN))
      (squareRowHelperSet kappa gadgetN r).toList :=
  discretePartition_admissible_of_nodup
    (squareRowHelperSet kappa gadgetN r).nodup_toList

/-- The square-helper derivative rows are linearly independent as soon as the
Kronecker coefficient obligation is discharged. -/
theorem linearIndependent_squareHelper_derivativeRows_of_kronecker
    {kappa gadgetN : Nat}
    (hgap : squareHelperDerivativeRowKronecker kappa gadgetN) :
    LinearIndependent Rat
      (fun r : Fin (rowCount kappa gadgetN) =>
        mlProj (iterDerivList (squareRowHelperSet kappa gadgetN r).toList
          (squareHelperQ kappa gadgetN))) := by
  classical
  rw [linearIndependent_iff']
  intro s w hw i hi
  have hcoeff_zero :
      coeff (squareRowLinearExponent kappa gadgetN i)
        (∑ j ∈ s, w j •
          mlProj (iterDerivList
            (squareRowHelperSet kappa gadgetN j).toList
            (squareHelperQ kappa gadgetN))) = 0 := by
    rw [hw]
    simp
  simp only [coeff_sum, coeff_smul, smul_eq_mul] at hcoeff_zero
  have hsum :
      (∑ j ∈ s,
        w j *
          coeff (squareRowLinearExponent kappa gadgetN i)
            (mlProj (iterDerivList
              (squareRowHelperSet kappa gadgetN j).toList
              (squareHelperQ kappa gadgetN)))) =
        w i * (2 : Rat) ^ kappa := by
    rw [Finset.sum_eq_single i]
    · rw [hgap i i, if_pos rfl]
    · intro j hj hji
      rw [hgap i j, if_neg (fun hij => hji hij.symm), mul_zero]
    · intro hnot
      exact (hnot hi).elim
  have hpow_ne : (2 : Rat) ^ kappa ≠ 0 := pow_ne_zero _ (by norm_num)
  exact (mul_eq_zero.mp (hsum ▸ hcoeff_zero)).resolve_right hpow_ne

/-- Conditional checked lower bound for the intended square-helper candidate:
the only remaining lower-bound obligation is the explicit row-Kronecker
coefficient statement above. -/
theorem squareHelper_rank_lower_of_derivativeRowKronecker
    {kappa gadgetN : Nat}
    (hgap : squareHelperDerivativeRowKronecker kappa gadgetN) :
    kappa * gadgetN ≤
      mlBlockedSpdpRank
        (discretePartition (squareHelperVarCount kappa gadgetN))
        kappa kappa (squareHelperQ kappa gadgetN) := by
  classical
  have hli :=
    linearIndependent_squareHelper_derivativeRows_of_kronecker
      (kappa := kappa) (gadgetN := gadgetN) hgap
  have hmem : ∀ r : Fin (rowCount kappa gadgetN),
      mlProj (iterDerivList (squareRowHelperSet kappa gadgetN r).toList
        (squareHelperQ kappa gadgetN)) ∈
        mlBlockedSpdpSubspace
          (discretePartition (squareHelperVarCount kappa gadgetN))
          kappa kappa (squareHelperQ kappa gadgetN) := by
    intro r
    refine Submodule.subset_span ?_
    refine ⟨(squareRowHelperSet kappa gadgetN r).toList,
      (1 : MvPolynomial (Fin (squareHelperVarCount kappa gadgetN)) Rat),
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.length_toList]
      exact squareRowHelperSet_card kappa gadgetN r
    · simp
    · simp
    · exact squareRowHelperSet_toList_admissible kappa gadgetN r
    · simp
  unfold mlBlockedSpdpRank
  set row :
      Fin (rowCount kappa gadgetN) →
        mlBlockedSpdpSubspace
          (discretePartition (squareHelperVarCount kappa gadgetN))
          kappa kappa (squareHelperQ kappa gadgetN) :=
    fun r => ⟨mlProj (iterDerivList
        (squareRowHelperSet kappa gadgetN r).toList
        (squareHelperQ kappa gadgetN)), hmem r⟩ with hrow
  have hli_sub : LinearIndependent Rat row := by
    rw [linearIndependent_iff'] at hli ⊢
    intro s w hw i hi
    apply hli s w ?_ i hi
    have hval : (∑ j ∈ s, w j • row j).val =
        (0 :
          mlBlockedSpdpSubspace
            (discretePartition (squareHelperVarCount kappa gadgetN))
            kappa kappa (squareHelperQ kappa gadgetN)).val :=
      congrArg Subtype.val hw
    simpa [hrow] using hval
  simpa [rowCount] using hli_sub.fintype_card_le_finrank

/-- The isolated exact upper-containment would give the matching
`kappa * gadgetN` upper bound. -/
theorem squareHelper_rank_upper_of_exactUpperContainment
    {kappa gadgetN : Nat}
    (hupper : squareHelperExactUpperContainment kappa gadgetN) :
    mlBlockedSpdpRank
        (discretePartition (squareHelperVarCount kappa gadgetN))
        kappa kappa (squareHelperQ kappa gadgetN) ≤
      kappa * gadgetN := by
  classical
  haveI : Module.Finite Rat (squareHelperRowSpace kappa gadgetN) := by
    unfold squareHelperRowSpace
    exact Module.Finite.span_of_finite Rat (Set.finite_range _)
  unfold mlBlockedSpdpRank
  calc
    Module.finrank Rat
        (mlBlockedSpdpSubspace
          (discretePartition (squareHelperVarCount kappa gadgetN))
          kappa kappa (squareHelperQ kappa gadgetN))
        ≤ Module.finrank Rat (squareHelperRowSpace kappa gadgetN) :=
          Submodule.finrank_mono hupper
    _ ≤ (Set.range (squareRowLinearMonomial kappa gadgetN)).toFinset.card := by
          unfold squareHelperRowSpace
          exact finrank_span_le_card _
    _ ≤ Fintype.card (Fin (rowCount kappa gadgetN)) := by
          rw [Set.toFinset_range]
          exact Finset.card_image_le
    _ = kappa * gadgetN := by
          simp [rowCount]

/-- Exact arbitrary-`kappa` equality follows from the concrete square-row
Kronecker lower calculation and the exact upper-containment into the predicted
row space. -/
theorem squareHelperExactRankTarget_of_derivativeRowKronecker_and_exactUpperContainment
    {kappa gadgetN : Nat}
    (hgap : squareHelperDerivativeRowKronecker kappa gadgetN)
    (hupper : squareHelperExactUpperContainment kappa gadgetN) :
    squareHelperExactRankTarget kappa gadgetN := by
  unfold squareHelperExactRankTarget
  exact le_antisymm
    (squareHelper_rank_upper_of_exactUpperContainment
      (kappa := kappa) (gadgetN := gadgetN) hupper)
    (squareHelper_rank_lower_of_derivativeRowKronecker
      (kappa := kappa) (gadgetN := gadgetN) hgap)

/-! ## Checked helper-row lower-bound model -/

/-- Helper-only variable count for the checked lower-bound model. -/
def helperVarCount (kappa gadgetN : Nat) : Nat :=
  rowCount kappa gadgetN * kappa

/-- Helper variable `(row, derivative-slot)` in the checked lower-bound model. -/
def helperIndex (kappa gadgetN : Nat)
    (r : Fin (rowCount kappa gadgetN)) (j : Fin kappa) :
    Fin (helperVarCount kappa gadgetN) :=
  finProdFinEquiv (r, j)

/-- The `kappa` helpers belonging to one row. -/
noncomputable def rowHelperSet (kappa gadgetN : Nat)
    (r : Fin (rowCount kappa gadgetN)) :
    Finset (Fin (helperVarCount kappa gadgetN)) :=
  (Finset.univ : Finset (Fin kappa)).image
    (fun j => helperIndex kappa gadgetN r j)

/-- The family of row helper sets, one strict-derivative row per target row. -/
noncomputable def rowHelperFamily (kappa gadgetN : Nat) :
    Finset (Finset (Fin (helperVarCount kappa gadgetN))) :=
  (Finset.univ : Finset (Fin (rowCount kappa gadgetN))).image
    (rowHelperSet kappa gadgetN)

/-- Each row-helper set has exactly `kappa` variables. -/
theorem rowHelperSet_card (kappa gadgetN : Nat)
    (r : Fin (rowCount kappa gadgetN)) :
    (rowHelperSet kappa gadgetN r).card = kappa := by
  unfold rowHelperSet helperIndex
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro a _ b _ h
    exact congrArg Prod.snd (finProdFinEquiv.injective h)

/-- For positive `kappa`, different rows give different helper sets. -/
theorem rowHelperSet_injective {kappa gadgetN : Nat}
    (hkappa : 1 ≤ kappa) :
    Function.Injective (rowHelperSet kappa gadgetN) := by
  intro r s hset
  have hkpos : 0 < kappa := by omega
  let j0 : Fin kappa := ⟨0, hkpos⟩
  have hmem :
      helperIndex kappa gadgetN r j0 ∈ rowHelperSet kappa gadgetN s := by
    rw [← hset]
    simp [rowHelperSet, helperIndex, j0]
  simp only [rowHelperSet, Finset.mem_image, Finset.mem_univ, true_and] at hmem
  rcases hmem with ⟨j, hj⟩
  exact (congrArg Prod.fst (finProdFinEquiv.injective hj)).symm

/-- The row-helper family has exactly `kappa * gadgetN` rows. -/
theorem rowHelperFamily_card {kappa gadgetN : Nat}
    (hkappa : 1 ≤ kappa) :
    (rowHelperFamily kappa gadgetN).card = kappa * gadgetN := by
  unfold rowHelperFamily rowCount
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro a _ b _ h
    exact rowHelperSet_injective (gadgetN := gadgetN) hkappa h

/-- Row-helper derivative lists are admissible for the discrete partition. -/
theorem rowHelperSet_toList_admissible (kappa gadgetN : Nat)
    (S : Finset (Fin (helperVarCount kappa gadgetN))) :
    isBlockAdmissible (discretePartition (helperVarCount kappa gadgetN))
      S.toList :=
  discretePartition_admissible_of_nodup S.nodup_toList

/-- The checked helper-product polynomial used to prove the row lower bound. -/
noncomputable def helperBoolProductQ (kappa gadgetN : Nat) :
    MvPolynomial (Fin (helperVarCount kappa gadgetN)) Rat :=
  SymmetricPower.boolFactorFullProd (helperVarCount kappa gadgetN)

/-- The target exact normalized rank statement for the checked helper-product
model.  The lower bound below is proved; exactness is not claimed here because
mixed admissible helper sets may contribute extra rows. -/
def helperBoolProductExactRankTarget (kappa gadgetN : Nat) : Prop :=
  mlBlockedSpdpRank (discretePartition (helperVarCount kappa gadgetN))
      kappa kappa (helperBoolProductQ kappa gadgetN) =
    kappa * gadgetN

/-- Checked progress: the strict-`kappa` row-helper derivatives force at least
`kappa * gadgetN` multilinearly independent rows. -/
theorem helperBoolProduct_rank_lower {kappa gadgetN : Nat}
    (hkappa : 1 ≤ kappa) :
    kappa * gadgetN ≤
      mlBlockedSpdpRank (discretePartition (helperVarCount kappa gadgetN))
        kappa kappa (helperBoolProductQ kappa gadgetN) := by
  classical
  have hcard :
      ∀ S ∈ rowHelperFamily kappa gadgetN, S.card = kappa := by
    intro S hS
    simp only [rowHelperFamily, Finset.mem_image, Finset.mem_univ, true_and] at hS
    rcases hS with ⟨r, rfl⟩
    exact rowHelperSet_card kappa gadgetN r
  have hadm :
      ∀ S ∈ rowHelperFamily kappa gadgetN,
        isBlockAdmissible (discretePartition (helperVarCount kappa gadgetN))
          S.toList := by
    intro S _hS
    exact rowHelperSet_toList_admissible kappa gadgetN S
  have h :=
    BlockedBoolRank.mlBlockedSpdpRank_ge_of_general_family_any_ell
      (N := helperVarCount kappa gadgetN) (κ := kappa) (ℓ := kappa)
      hkappa (discretePartition (helperVarCount kappa gadgetN))
      (F := rowHelperFamily kappa gadgetN) hcard hadm
  simpa [helperBoolProductQ, rowHelperFamily_card hkappa] using h

/-- Nonzero corollary of the checked lower bound. -/
theorem helperBoolProduct_rank_pos {kappa gadgetN : Nat}
    (hkappa : 1 ≤ kappa) (hgadgetN : 1 ≤ gadgetN) :
    0 <
      mlBlockedSpdpRank (discretePartition (helperVarCount kappa gadgetN))
        kappa kappa (helperBoolProductQ kappa gadgetN) := by
  have hlower := helperBoolProduct_rank_lower
    (kappa := kappa) (gadgetN := gadgetN) hkappa
  have htarget : 0 < kappa * gadgetN := Nat.mul_pos
    (by omega) (by omega)
  exact lt_of_lt_of_le htarget hlower

/-- Bridge-A-shaped consequence of the checked helper-product lower bound:
under the energy trigger, the concrete helper-product polynomial has SPDP rank
at least `kappa`.  This is a lower-bound local-polynomial realization, not the
stronger exact normalized `kappa * gadgetN` equality target. -/
theorem helperBoolProduct_energy_trigger_spdpRank_lower {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N)
    (hkappa : 1 ≤ kappa) (hgadgetN : 1 ≤ gadgetN)
    (_hE : alpha0 <= localEnergy alpha beta G chi Phi v) :
    kappa <=
      mlBlockedSpdpRank (discretePartition (helperVarCount kappa gadgetN))
        kappa kappa (helperBoolProductQ kappa gadgetN) := by
  have hrow :
      kappa * gadgetN <=
        mlBlockedSpdpRank (discretePartition (helperVarCount kappa gadgetN))
          kappa kappa (helperBoolProductQ kappa gadgetN) :=
    helperBoolProduct_rank_lower
      (kappa := kappa) (gadgetN := gadgetN) hkappa
  exact le_trans (Nat.le_mul_of_pos_right kappa (by omega)) hrow

/-! ## General finite upper envelopes -/

/-- Any strict blocked SPDP subspace is contained in the multilinear monomial
span over all ambient variables. -/
theorem mlBlockedSpdpSubspace_le_allMultilinearBasis {n : Nat}
    (B : BlockPartition n) (kappa ell : Nat)
    (p : MvPolynomial (Fin n) Rat) :
    mlBlockedSpdpSubspace B kappa ell p ≤
      Submodule.span Rat
        (↑(MlProjFar.mlMonomialBasis (Finset.univ : Finset (Fin n))) :
          Set (MvPolynomial (Fin n) Rat)) := by
  unfold mlBlockedSpdpSubspace
  apply Submodule.span_le.mpr
  rintro q ⟨S, m, _hlen, _hdeg, _hvars, _hadm, hq⟩
  rw [hq]
  apply MlProjFar.mlProj_in_span_of_vars_subset
  · intro α hα
    change α ∈
      (Finsupp.filter (fun α => Finsupp.IsMultilinear α)
        (m * iterDerivList S p)).support at hα
    rw [Finsupp.support_filter] at hα
    exact (Finset.mem_filter.mp hα).2
  · intro i _hi
    exact Finset.mem_univ i

/-- Ambient multilinear-envelope upper bound for every blocked SPDP rank. -/
theorem mlBlockedSpdpRank_le_allVarsPow {n : Nat}
    (B : BlockPartition n) (kappa ell : Nat)
    (p : MvPolynomial (Fin n) Rat) :
    mlBlockedSpdpRank B kappa ell p ≤ 2 ^ n := by
  unfold mlBlockedSpdpRank
  have h :=
    MlProjFar.finrank_le_of_vars_bounded
      (W := mlBlockedSpdpSubspace B kappa ell p)
      (V := (Finset.univ : Finset (Fin n)))
      (mlBlockedSpdpSubspace_le_allMultilinearBasis B kappa ell p)
  simpa using h

/-- Checked finite upper envelope for the helper-product model. -/
theorem helperBoolProduct_rank_upper (kappa gadgetN : Nat) :
    mlBlockedSpdpRank (discretePartition (helperVarCount kappa gadgetN))
        kappa kappa (helperBoolProductQ kappa gadgetN) ≤
      2 ^ helperVarCount kappa gadgetN :=
  mlBlockedSpdpRank_le_allVarsPow
    (discretePartition (helperVarCount kappa gadgetN))
    kappa kappa (helperBoolProductQ kappa gadgetN)

/-- Checked finite upper envelope for the intended square-helper candidate. -/
theorem squareHelper_rank_upper (kappa gadgetN : Nat) :
    mlBlockedSpdpRank (discretePartition (squareHelperVarCount kappa gadgetN))
        kappa kappa (squareHelperQ kappa gadgetN) ≤
      2 ^ squareHelperVarCount kappa gadgetN :=
  mlBlockedSpdpRank_le_allVarsPow
    (discretePartition (squareHelperVarCount kappa gadgetN))
    kappa kappa (squareHelperQ kappa gadgetN)

/-! ## Axiom audit anchors -/

#print axioms rowHelperFamily_card
#print axioms helperBoolProduct_rank_lower
#print axioms helperBoolProduct_energy_trigger_spdpRank_lower
#print axioms squareHelper_rank_lower_of_derivativeRowKronecker
#print axioms squareHelper_rank_upper_of_exactUpperContainment
#print axioms squareHelperExactRankTarget_of_derivativeRowKronecker_and_exactUpperContainment
#print axioms mlBlockedSpdpRank_le_allVarsPow
#print axioms squareHelper_rank_upper

end BridgeAGeneralizedNonzeroWitness

end PallLean.Paper93.Paper283
