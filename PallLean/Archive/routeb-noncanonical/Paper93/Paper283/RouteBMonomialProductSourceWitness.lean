import PallLean.BlockedBoolRank
import PallLean.GodMoveReal
import PallLean.IterDerivHelpers
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeMapPiPhi
import PallLean.Paper93.DeepMath.PathB.ProjectedIdentityMinorPaperFaithful
import PallLean.ProductDeriv

/-!
# Route B monomial-product source witness

This file isolates a non-compiled source-side `CoupledSheetPoly` for the flat
Cook-Levin split.  The source polynomial is the single multilinear monomial
over the first variable in each Cook-Levin locality block:

`Q = ∏_{i : Fin (n / 3)} X_{3 i}`.

The proved part is the complete rank-lower-bound reduction from a concrete
Kronecker coefficient matrix for the derivative rows.  The remaining
mathematical gap is named as `DerivativeRowKroneckerGap`: proving that gap for
the monomial product discharges the paper-faithful
`SourceIdentityMinorLowerBound` without using `compiledPoly` or
`lemma124_compiledPoly_identity_minor_lower_bound`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open PallLean.Paper93.DeepMath.PathB
open SPDP
open TuringMachine

namespace RouteBMonomialProductSourceWitness

attribute [local instance] Classical.dec

/-- The flat Cook-Levin split used by the paper-faithful source side. -/
noncomputable abbrev flatSplit
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : UVSplit :=
  flatCookLevinUVSplit M n hn2 htb hns

/-- The Cook-Levin locality partition, viewed as a partition of the flat split. -/
noncomputable abbrev cookPartition
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    BlockPartition (flatSplit M n hn2 htb hns).total :=
  (cook_levin_compilation M n hn2 htb hns).partition

/-- The first variable in Cook-Levin locality block `i`, as a source `u` index. -/
noncomputable def spacedU
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : Fin (n / 3)) : Fin (flatSplit M n hn2 htb hns).numU :=
  ⟨3 * i.val, by
    show 3 * i.val < (cook_levin_compilation M n hn2 htb hns).numVars
    rw [cook_levin_numVars M n hn2 htb hns]
    omega⟩

/-- The spaced source variables as a finset in the flat source variable space. -/
noncomputable def spacedVarSet
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Finset (Fin (flatSplit M n hn2 htb hns).numU) :=
  (Finset.univ : Finset (Fin (n / 3))).map
    ⟨spacedU M n hn2 htb hns, by
      intro i j hij
      apply Fin.ext
      have := congrArg Fin.val hij
      dsimp [spacedU] at this
      omega⟩

/-- The non-compiled monomial-product coupled sheet:
`Q = ∏_{i : Fin (n / 3)} X_{3 i}`. -/
noncomputable def spacedMonomialProduct
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    CoupledSheetPoly (flatSplit M n hn2 htb hns) :=
  (spacedVarSet M n hn2 htb hns).prod (fun i => X i)

/-- The first-of-block family, typed in the flat source variable space. -/
noncomputable abbrev spacedKappaFamily
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (κ : Nat) :
    Finset (Finset (Fin (flatSplit M n hn2 htb hns).numU)) :=
  GodMoveReal.fobFamily n κ

theorem spacedKappaFamily_card
    (M : DTM) (n κ : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    (spacedKappaFamily M n hn2 htb hns κ).card = Nat.choose (n / 3) κ := by
  simpa [spacedKappaFamily] using GodMoveReal.fobFamily_card n κ

theorem spacedKappaFamily_mem_card
    (M : DTM) (n κ : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (flatSplit M n hn2 htb hns).numU))
    (hS : S ∈ spacedKappaFamily M n hn2 htb hns κ) :
    S.card = κ := by
  simpa [spacedKappaFamily] using
    GodMoveReal.fobFamily_mem_card n κ S hS

/-- Spaced variables are block-admissible for the pulled-back flat Cook-Levin
source partition. -/
theorem spacedKappaFamily_blockAdmissible
    (M : DTM) (n κ : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (flatSplit M n hn2 htb hns).numU))
    (hS : S ∈ spacedKappaFamily M n hn2 htb hns κ) :
    isBlockAdmissible
      (pullbackPartition (cookPartition M n hn2 htb hns)
        (flatSplit M n hn2 htb hns).inlU) S.toList := by
  simpa [spacedKappaFamily, cookPartition, flatSplit, pullbackPartition, UVSplit.inlU] using
    GodMoveReal.fobFamily_mem_blockAdmissible n hn2 κ M htb hns S hS

/-- Every selected row subset in the first-of-block family is contained in the
base support of the monomial product. -/
theorem spacedKappaFamily_subset_spacedVarSet
    (M : DTM) (n κ : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (flatSplit M n hn2 htb hns).numU))
    (hS : S ∈ spacedKappaFamily M n hn2 htb hns κ) :
    S ⊆ spacedVarSet M n hn2 htb hns := by
  intro v hv
  simp only [spacedKappaFamily, GodMoveReal.fobFamily, Finset.mem_map] at hS
  obtain ⟨T, _, rfl⟩ := hS
  change v ∈ GodMoveReal.firstOfBlockSubset n T at hv
  simp only [GodMoveReal.firstOfBlockSubset, Finset.mem_map] at hv
  obtain ⟨i, _, rfl⟩ := hv
  simp only [spacedVarSet, Finset.mem_map, Finset.mem_univ, true_and]
  refine ⟨i, ?_⟩
  apply Fin.ext
  rfl

/-- Exponent vector for the monomial supported on a finset. -/
noncomputable abbrev supportMonomial {N : Nat} (S : Finset (Fin N)) : Fin N →₀ Nat :=
  SymmetricPower.tagMonomial S

/-- The product of variables over a finset is the corresponding support monomial. -/
theorem prod_X_eq_monomial_support {N : Nat} (S : Finset (Fin N)) :
    S.prod (fun i => (X i : MvPolynomial (Fin N) ℚ)) =
      monomial (supportMonomial S) (1 : ℚ) := by
  rw [supportMonomial, SymmetricPower.tagMonomial, MvPolynomial.monomial_sum_one]
  simp [MvPolynomial.X]

/-- Coefficients of a pure multilinear variable product are Kronecker in the support. -/
theorem coeff_support_prod_X {N : Nat} (S T : Finset (Fin N)) :
    coeff (supportMonomial S) (T.prod (fun i => (X i : MvPolynomial (Fin N) ℚ))) =
      if S = T then (1 : ℚ) else 0 := by
  rw [prod_X_eq_monomial_support]
  rw [MvPolynomial.coeff_monomial]
  by_cases hST : S = T
  · subst hST
    simp
  · have hmono : supportMonomial T ≠ supportMonomial S := by
      intro h
      exact hST (SymmetricPower.tagMonomial_injective h.symm)
    simp [hST, hmono]

/-- Differentiating a product of distinct variables by one variable erases that
factor. -/
theorem pderiv_prod_X_of_mem {N : Nat} (base : Finset (Fin N)) {i : Fin N}
    (hi : i ∈ base) :
    pderiv i (base.prod (fun j => (X j : MvPolynomial (Fin N) ℚ))) =
      (base.erase i).prod (fun j => (X j : MvPolynomial (Fin N) ℚ)) := by
  rw [ProductDeriv.pderiv_prod_single (s := base)
    (f := fun j => (X j : MvPolynomial (Fin N) ℚ)) (i := i) (k := i) hi]
  · simp
  · intro j _ hj
    exact MvPolynomial.pderiv_X_of_ne hj

/-- Iterated differentiation by a subset of the product support erases exactly
that subset. -/
theorem iterDerivList_toList_prod_X_of_subset {N : Nat} (T : Finset (Fin N)) :
    ∀ base : Finset (Fin N), T ⊆ base →
      iterDerivList T.toList (base.prod (fun i => (X i : MvPolynomial (Fin N) ℚ))) =
        ((base \ T).prod (fun i => (X i : MvPolynomial (Fin N) ℚ))) := by
  classical
  refine Finset.induction_on T ?_ ?_
  · intro base _
    simp [iterDerivList]
  · intro a T ha ih base hsub
    have hperm : (insert a T).toList.Perm (a :: T.toList) :=
      Finset.toList_insert ha
    rw [IterDerivHelpers.iterDerivList_perm hperm]
    rw [IterDerivHelpers.iterDerivList_cons]
    have ha_base : a ∈ base := hsub (Finset.mem_insert_self a T)
    rw [pderiv_prod_X_of_mem base ha_base]
    have hsub_erase : T ⊆ base.erase a := by
      intro x hx
      exact Finset.mem_erase.mpr ⟨fun hxa => ha (hxa ▸ hx), hsub (Finset.mem_insert_of_mem hx)⟩
    rw [ih (base.erase a) hsub_erase]
    have hset : base.erase a \ T = base \ insert a T := by
      ext x
      by_cases hxa : x = a
      · subst hxa
        simp
      · simp [Finset.mem_sdiff, hxa]
    rw [hset]

/-- Removing subsets from the same base is injective on subsets of that base. -/
theorem sdiff_right_injective_on_subsets {N : Nat} {base S T : Finset (Fin N)}
    (hS : S ⊆ base) (hT : T ⊆ base) :
    base \ S = base \ T ↔ S = T := by
  constructor
  · intro h
    ext x
    constructor
    · intro hxS
      have hxbase : x ∈ base := hS hxS
      by_contra hxT
      have hx_left : x ∉ base \ S := by simp [Finset.mem_sdiff, hxS]
      have hx_right : x ∈ base \ T := by simp [Finset.mem_sdiff, hxbase, hxT]
      exact hx_left (h ▸ hx_right)
    · intro hxT
      have hxbase : x ∈ base := hT hxT
      by_contra hxS
      have hx_left : x ∈ base \ S := by simp [Finset.mem_sdiff, hxbase, hxS]
      have hx_right : x ∉ base \ T := by simp [Finset.mem_sdiff, hxT]
      exact hx_right (h ▸ hx_left)
  · intro h
    subst h
    rfl

/-- The precise derivative-row Kronecker gap left for the monomial product.

Rows are indexed by κ-subsets `T` of the spaced variables, and columns by the
complement monomials `spacedVarSet \ S`.  For the monomial product, the
expected matrix is the identity: differentiating by `T` leaves exactly the
complement monomial for `T`. -/
def DerivativeRowKroneckerGap
    {N : Nat} (F : Finset (Finset (Fin N)))
    (base : Finset (Fin N)) (Q : MvPolynomial (Fin N) ℚ) : Prop :=
  ∀ ⦃S⦄, S ∈ F → ∀ ⦃T⦄, T ∈ F →
    coeff (supportMonomial (base \ S))
      (mlProj (iterDerivList T.toList Q)) =
        if S = T then (1 : ℚ) else 0

/-- Generic Kronecker gap for a monomial product, for any row family contained
in the product support. -/
theorem derivativeRowKroneckerGap_prod_X_of_subset
    {N : Nat} {F : Finset (Finset (Fin N))} {base : Finset (Fin N)}
    (hsub : ∀ ⦃S⦄, S ∈ F → S ⊆ base) :
    DerivativeRowKroneckerGap F base
      (base.prod (fun i => (X i : MvPolynomial (Fin N) ℚ))) := by
  intro S hS T hT
  have hmono :
      Finsupp.IsMultilinear (supportMonomial (base \ S)) := by
    simpa [supportMonomial] using
      SymmetricPower.tagMonomial_isMultilinear (base \ S)
  rw [coeff_mlProj_of_isMultilinear_mono _ _ hmono]
  rw [iterDerivList_toList_prod_X_of_subset T base (hsub hT)]
  rw [coeff_support_prod_X]
  have hSsub : S ⊆ base := hsub hS
  have hTsub : T ⊆ base := hsub hT
  by_cases hST : S = T
  · subst hST
    simp
  · have hdiff : base \ S ≠ base \ T := by
      intro hdiff
      exact hST ((sdiff_right_injective_on_subsets hSsub hTsub).mp hdiff)
    simp [hST, hdiff]

/-- Linear independence from a derivative-row Kronecker coefficient matrix. -/
theorem linearIndependent_derivativeRows_of_kroneckerGap
    {N : Nat} {F : Finset (Finset (Fin N))}
    {base : Finset (Fin N)} {Q : MvPolynomial (Fin N) ℚ}
    (hgap : DerivativeRowKroneckerGap F base Q) :
    LinearIndependent ℚ
      (fun S : F => mlProj (iterDerivList (S : Finset (Fin N)).toList Q)) := by
  rw [linearIndependent_iff']
  intro s w hw i hi
  have hcoeff_zero :
      coeff (supportMonomial (base \ (i : Finset (Fin N))))
        (∑ j ∈ s, w j • mlProj (iterDerivList (j : Finset (Fin N)).toList Q)) = 0 := by
    rw [hw]
    simp
  simp only [coeff_sum, coeff_smul, smul_eq_mul] at hcoeff_zero
  have hsum :
      (∑ j ∈ s,
        w j *
          coeff (supportMonomial (base \ (i : Finset (Fin N))))
            (mlProj (iterDerivList (j : Finset (Fin N)).toList Q))) = w i := by
    rw [Finset.sum_eq_single i]
    · rw [hgap i.2 i.2, if_pos rfl, mul_one]
    · intro j hj hji
      have hne : (i : Finset (Fin N)) ≠ (j : Finset (Fin N)) := by
        intro hij
        exact hji (Subtype.ext hij.symm)
      rw [hgap i.2 j.2, if_neg hne, mul_zero]
    · intro hnot
      exact (hnot hi).elim
  exact hsum ▸ hcoeff_zero

/-- Rank lower bound from the Kronecker gap and block-admissibility of the
chosen derivative rows. -/
theorem mlBlockedSpdpRank_ge_card_of_kroneckerGap
    {N κ ℓ : Nat} (B : BlockPartition N)
    {F : Finset (Finset (Fin N))} {base : Finset (Fin N)}
    {Q : MvPolynomial (Fin N) ℚ}
    (hcard : ∀ S ∈ F, S.card = κ)
    (hadm : ∀ S ∈ F, isBlockAdmissible B S.toList)
    (hgap : DerivativeRowKroneckerGap F base Q) :
    F.card ≤ mlBlockedSpdpRank B κ ℓ Q := by
  have hli := linearIndependent_derivativeRows_of_kroneckerGap hgap
  have hmem : ∀ (S : F),
      mlProj (iterDerivList (S : Finset (Fin N)).toList Q) ∈
        mlBlockedSpdpSubspace B κ ℓ Q := by
    intro S
    refine Submodule.subset_span ?_
    refine ⟨(S : Finset (Fin N)).toList, (1 : MvPolynomial (Fin N) ℚ), ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.length_toList]
      exact hcard S S.2
    · simp
    · simp
    · exact hadm S S.2
    · simp
  unfold mlBlockedSpdpRank
  set row : F → mlBlockedSpdpSubspace B κ ℓ Q :=
    fun S => ⟨mlProj (iterDerivList (S : Finset (Fin N)).toList Q), hmem S⟩ with hrow
  have hli_sub : LinearIndependent ℚ row := by
    rw [linearIndependent_iff'] at hli ⊢
    intro s w hw i hi
    apply hli s w ?_ i hi
    have hval : (∑ j ∈ s, w j • row j).val =
        (0 : mlBlockedSpdpSubspace B κ ℓ Q).val :=
      congrArg Subtype.val hw
    simpa [hrow] using hval
  rw [show F.card = Fintype.card F from (Fintype.card_coe F).symm]
  exact hli_sub.fintype_card_le_finrank

/-- The monomial-product source lower bound, conditional only on the explicit
derivative-row Kronecker gap. -/
theorem sourceIdentityMinorLowerBound_spacedMonomialProduct_of_kroneckerGap
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hgap :
      DerivativeRowKroneckerGap
        (spacedKappaFamily M n hn2 htb hns (Nat.log 2 n))
        (spacedVarSet M n hn2 htb hns)
        (spacedMonomialProduct M n hn2 htb hns)) :
    SourceIdentityMinorLowerBound n (flatSplit M n hn2 htb hns)
      (cookPartition M n hn2 htb hns)
      (Nat.log 2 n) (Nat.log 2 n)
      (spacedMonomialProduct M n hn2 htb hns) := by
  unfold SourceIdentityMinorLowerBound
  rw [← spacedKappaFamily_card M n (Nat.log 2 n) hn2 htb hns]
  exact mlBlockedSpdpRank_ge_card_of_kroneckerGap
    (pullbackPartition (cookPartition M n hn2 htb hns)
      (flatSplit M n hn2 htb hns).inlU)
    (fun S hS =>
      spacedKappaFamily_mem_card M n (Nat.log 2 n) hn2 htb hns S hS)
    (fun S hS =>
      spacedKappaFamily_blockAdmissible M n (Nat.log 2 n) hn2 htb hns S hS)
    hgap

/-- The concrete derivative-row Kronecker gap for the spaced monomial product. -/
theorem derivativeRowKroneckerGap_spacedMonomialProduct
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    DerivativeRowKroneckerGap
      (spacedKappaFamily M n hn2 htb hns (Nat.log 2 n))
      (spacedVarSet M n hn2 htb hns)
      (spacedMonomialProduct M n hn2 htb hns) := by
  simpa [spacedMonomialProduct] using
    derivativeRowKroneckerGap_prod_X_of_subset
      (F := spacedKappaFamily M n hn2 htb hns (Nat.log 2 n))
      (base := spacedVarSet M n hn2 htb hns)
      (fun S hS =>
        spacedKappaFamily_subset_spacedVarSet
          M n (Nat.log 2 n) hn2 htb hns S hS)

/-- The monomial-product source lower bound with the Kronecker gap discharged. -/
theorem sourceIdentityMinorLowerBound_spacedMonomialProduct
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SourceIdentityMinorLowerBound n (flatSplit M n hn2 htb hns)
      (cookPartition M n hn2 htb hns)
      (Nat.log 2 n) (Nat.log 2 n)
      (spacedMonomialProduct M n hn2 htb hns) :=
  sourceIdentityMinorLowerBound_spacedMonomialProduct_of_kroneckerGap
    M n hn2 htb hns
    (derivativeRowKroneckerGap_spacedMonomialProduct M n hn2 htb hns)

/-- Backwards-compatible certificate for the non-compiled monomial-product
Route B source witness.  The concrete value
`monomialProductSourceCertificate` below now discharges the derivative-row
Kronecker payload. -/
structure MonomialProductSourceCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Type where
  derivative_row_kronecker_gap :
    DerivativeRowKroneckerGap
      (spacedKappaFamily M n hn2 htb hns (Nat.log 2 n))
      (spacedVarSet M n hn2 htb hns)
      (spacedMonomialProduct M n hn2 htb hns)

theorem sourceIdentityMinorLowerBound_spacedMonomialProduct_of_certificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (cert : MonomialProductSourceCertificate M n hn2 htb hns) :
    SourceIdentityMinorLowerBound n (flatSplit M n hn2 htb hns)
      (cookPartition M n hn2 htb hns)
      (Nat.log 2 n) (Nat.log 2 n)
      (spacedMonomialProduct M n hn2 htb hns) :=
  sourceIdentityMinorLowerBound_spacedMonomialProduct_of_kroneckerGap
    M n hn2 htb hns cert.derivative_row_kronecker_gap

/-- A certificate value whose proof payload is the concrete monomial-product
Kronecker theorem above. -/
noncomputable def monomialProductSourceCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    MonomialProductSourceCertificate M n hn2 htb hns where
  derivative_row_kronecker_gap :=
    derivativeRowKroneckerGap_spacedMonomialProduct M n hn2 htb hns

/-! ## Axiom audit anchors -/

#print axioms prod_X_eq_monomial_support
#print axioms coeff_support_prod_X
#print axioms pderiv_prod_X_of_mem
#print axioms iterDerivList_toList_prod_X_of_subset
#print axioms derivativeRowKroneckerGap_prod_X_of_subset
#print axioms derivativeRowKroneckerGap_spacedMonomialProduct
#print axioms linearIndependent_derivativeRows_of_kroneckerGap
#print axioms mlBlockedSpdpRank_ge_card_of_kroneckerGap
#print axioms sourceIdentityMinorLowerBound_spacedMonomialProduct_of_kroneckerGap
#print axioms sourceIdentityMinorLowerBound_spacedMonomialProduct
#print axioms sourceIdentityMinorLowerBound_spacedMonomialProduct_of_certificate
#print axioms monomialProductSourceCertificate

end RouteBMonomialProductSourceWitness
end PallLean.Paper93.Paper283
