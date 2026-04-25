import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeKeepFOB
import PallLean.CrossTermVanishing
import Mathlib.Tactic

/-!
# Linear independence after the keep-FOB projection

This file keeps the proof local to the coefficient pattern already established
in `CrossTermVanishing.linearIndependent_mlProj_compiled_fob`.  The only new
ingredient is that `piZero keepFOB` preserves coefficients at first-of-block
tag monomials, while all first-of-block derivative lists commute through the
projection.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial SPDP MultilinearSPDP SymmetricPower
open PaperFaithfulSeparation TuringMachine

attribute [local instance] Classical.dec

/-- A kept-supported monomial coefficient is unchanged by `piZero`. -/
theorem coeff_piZero_eq_of_support_kept {N : Nat}
    (keep : Fin N → Prop) [DecidablePred keep]
    (α : Fin N →₀ Nat)
    (hα : ∀ i, ¬ keep i → α i = 0)
    (p : MvPolynomial (Fin N) Rat) :
    coeff α (PiStarConcrete.piZero keep p) = coeff α p := by
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
  rw [map_sum]
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
  rw [coeff_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro β hβ
  rw [PiStarConcrete.piZero_monomial]
  by_cases hβkeep : ∀ i, ¬ keep i → β i = 0
  · rw [if_pos hβkeep]
  · rw [if_neg hβkeep, coeff_zero]
    have hβα : β ≠ α := by
      intro hEq
      exact hβkeep (fun i hi => by rw [hEq]; exact hα i hi)
    rw [coeff_monomial, if_neg hβα]

/-- First-of-block tag monomials are supported only on `keepFOB` variables. -/
theorem tagMonomial_keepFOB_supported {n : Nat} (S : Finset (Fin n))
    (hfob : ∀ v ∈ S, 3 ∣ v.val) :
    ∀ i, ¬ PiStarConcrete.keepFOB i → tagMonomial S i = 0 := by
  intro i hnot
  rw [tagMonomial_apply]
  by_cases hi : i ∈ S
  · exact (hnot (by simpa [PiStarConcrete.keepFOB] using hfob i hi)).elim
  · simp [hi]

/-- The projected keep-FOB compiled generators have the same FOB tag
coefficient matrix as the unprojected compiled generators. -/
theorem coeff_mlProj_keepFOBProjected_compiled_samesize
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S T : Finset (Fin n))
    (hcardST : S.card = T.card)
    (hS_fob : ∀ v ∈ S, 3 ∣ v.val)
    (hT_fob : ∀ v ∈ T, 3 ∣ v.val) :
    coeff (tagMonomial S)
      (mlProj (iterDerivList T.toList
        (satDeciderGaugeKeepFOBProjection M n hn htb hns
          (compiledPoly (cook_levin_compilation M n hn htb hns))))) =
    (2 : Rat) ^ (S ∩ T).card := by
  unfold satDeciderGaugeKeepFOBProjection
  have hT_kept : ∀ i ∈ T.toList, PiStarConcrete.keepFOB i :=
    PiStarConcrete.fobList_allKept T hT_fob
  change coeff (tagMonomial S)
      (mlProj (iterDerivList T.toList
        (PiStarConcrete.piSubst PiStarConcrete.keepFOB (0 : Fin n → Rat)
          (compiledPoly (cook_levin_compilation M n hn htb hns))))) =
    (2 : Rat) ^ (S ∩ T).card
  rw [PiStarConcrete.iterDerivList_piSubst_allKept
    PiStarConcrete.keepFOB (0 : Fin n → Rat) T.toList hT_kept]
  change coeff (tagMonomial S)
      (mlProj (PiStarConcrete.piZero PiStarConcrete.keepFOB
        (iterDerivList T.toList
          (compiledPoly (cook_levin_compilation M n hn htb hns))))) =
    (2 : Rat) ^ (S ∩ T).card
  rw [PiStarConcrete.mlProj_piZero_comm PiStarConcrete.keepFOB]
  rw [coeff_piZero_eq_of_support_kept PiStarConcrete.keepFOB (tagMonomial S)
    (tagMonomial_keepFOB_supported S hS_fob)]
  exact CrossTermVanishing.coeff_mlProj_compiled_samesize
    M n hn htb hns S T hcardST hS_fob hT_fob

/-- Generic Gram-matrix bridge: any family whose FOB tag coefficient matrix is
`2 ^ |T ∩ S|` is linearly independent. -/
theorem linearIndependent_of_tag_coeff_gram {N κ : Nat} (_hκ : κ ≥ 1)
    {F : Finset (Finset (Fin N))}
    (hcard : ∀ S ∈ F, S.card = κ)
    (v : Finset (Fin N) → MvPolynomial (Fin N) Rat)
    (hcoeff : ∀ T ∈ F, ∀ S ∈ F,
      coeff (tagMonomial T) (v S) = (2 : Rat) ^ (T ∩ S).card) :
    LinearIndependent Rat (fun S : F => v (S : Finset (Fin N))) := by
  rw [linearIndependent_iff']
  intro s w hw i hi
  set c : Finset (Fin N) → Rat := fun S =>
    if h : S ∈ F then
      if ⟨S, h⟩ ∈ s then w ⟨S, h⟩ else 0
    else 0 with hc_def
  have hzero_F : ∑ S ∈ F, c S • v S = 0 := by
    have : ∑ S ∈ F, c S • v S =
        ∑ S ∈ s, w S • v (S : Finset (Fin N)) := by
      conv_lhs => rw [← Finset.sum_attach F (fun S => c S • v S)]
      rw [← Finset.sum_filter_add_sum_filter_not F.attach (fun S => S ∈ s)]
      have hzero_part :
          ∑ S ∈ F.attach.filter (fun S => S ∉ s),
            c (S : Finset (Fin N)) • v (S : Finset (Fin N)) = 0 := by
        apply Finset.sum_eq_zero
        intro ⟨S, hSF⟩ hmem
        simp only [Finset.mem_filter, Finset.mem_attach, true_and] at hmem
        rw [show c S = 0 from by simp [hc_def, dif_pos hSF, if_neg hmem], zero_smul]
      rw [hzero_part, add_zero]
      apply Finset.sum_nbij (fun S => S)
      · intro ⟨S, hSF⟩ hmem
        simp only [Finset.mem_filter, Finset.mem_attach, true_and] at hmem
        exact hmem
      · intro ⟨S₁, _⟩ _ ⟨S₂, _⟩ _ heq
        exact heq
      · intro ⟨S, hSF⟩ hmem
        exact ⟨⟨S, hSF⟩, by simp [hmem], rfl⟩
      · intro ⟨S, hSF⟩ hmem
        simp only [Finset.mem_filter, Finset.mem_attach, true_and] at hmem
        simp only [hc_def, dif_pos hSF, if_pos hmem]
    rw [this, hw]
  have hextract : ∀ T ∈ F, ∑ S ∈ F, c S * (2 : Rat) ^ (T ∩ S).card = 0 := by
    intro T hTF
    have hcoeff_T : coeff (tagMonomial T) (∑ S ∈ F, c S • v S) = 0 := by
      rw [hzero_F]
      simp [coeff_zero]
    simp only [coeff_sum, coeff_smul, smul_eq_mul] at hcoeff_T
    convert hcoeff_T using 1
    apply Finset.sum_congr rfl
    intro S hS
    rw [hcoeff T hTF S hS]
  set g : Finset (Fin N) → Rat :=
    fun U => ∑ S ∈ F, c S * BlockedBoolRank.zetaIndicator S U with hg_def
  set allSubsets := (Finset.univ : Finset (Fin N)).powerset with hall_def
  have hg_sq_eq : ∑ U ∈ allSubsets, g U ^ 2 =
      ∑ T ∈ F, ∑ S ∈ F, c T * c S * (2 : Rat) ^ (T ∩ S).card := by
    simp only [hg_def, sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm (s := allSubsets) (t := F)]
    congr 1
    funext T
    rw [Finset.sum_comm (s := allSubsets) (t := F)]
    congr 1
    funext S
    rw [show ∑ U ∈ allSubsets,
        (c T * BlockedBoolRank.zetaIndicator T U) *
          (c S * BlockedBoolRank.zetaIndicator S U) =
        c T * c S * ∑ U ∈ allSubsets,
          BlockedBoolRank.zetaIndicator T U * BlockedBoolRank.zetaIndicator S U from by
      rw [Finset.mul_sum]
      congr 1
      funext U
      ring]
    rw [BlockedBoolRank.zetaIndicator_inner_product]
  have hquad_zero :
      ∑ T ∈ F, ∑ S ∈ F, c T * c S * (2 : Rat) ^ (T ∩ S).card = 0 := by
    apply Finset.sum_eq_zero
    intro T hT
    rw [show ∑ S ∈ F, c T * c S * (2 : Rat) ^ (T ∩ S).card =
        c T * ∑ S ∈ F, c S * (2 : Rat) ^ (T ∩ S).card from by
      rw [Finset.mul_sum]
      congr 1
      ext S
      ring]
    rw [hextract T hT, mul_zero]
  have hg_sq_zero : ∑ U ∈ allSubsets, g U ^ 2 = 0 := by
    rw [hg_sq_eq, hquad_zero]
  have hg_zero : ∀ U ∈ allSubsets, g U = 0 :=
    BlockedBoolRank.sum_sq_eq_zero_imp hg_sq_zero
  have hg_eval : ∀ T ∈ F, g T = c T := by
    intro T hTF
    show ∑ S ∈ F, c S * BlockedBoolRank.zetaIndicator S T = c T
    rw [show ∑ S ∈ F, c S * BlockedBoolRank.zetaIndicator S T =
        c T * BlockedBoolRank.zetaIndicator T T +
          ∑ S ∈ F.erase T, c S * BlockedBoolRank.zetaIndicator S T from by
      rw [← Finset.add_sum_erase F _ hTF]]
    rw [show BlockedBoolRank.zetaIndicator T T = 1 from by
      simp [BlockedBoolRank.zetaIndicator], mul_one]
    suffices h : ∑ S ∈ F.erase T, c S * BlockedBoolRank.zetaIndicator S T = 0 by
      linarith
    apply Finset.sum_eq_zero
    intro S hS
    have hSF := Finset.mem_of_mem_erase hS
    have hne := Finset.ne_of_mem_erase hS
    rw [show BlockedBoolRank.zetaIndicator S T = 0 from by
      simp only [BlockedBoolRank.zetaIndicator]
      rw [if_neg]
      intro hsub
      exact hne
        (BlockedBoolRank.Finset.eq_of_subset_of_card_eq hsub
          (by rw [hcard T hTF, hcard S hSF])).symm]
    exact mul_zero _
  have hci : c (i : Finset (Fin N)) = 0 := by
    have hT_mem : (i : Finset (Fin N)) ∈ allSubsets := by
      simp [hall_def]
    rw [← hg_eval _ i.2]
    exact hg_zero _ hT_mem
  simp only [hc_def, dif_pos i.2, if_pos hi] at hci
  exact hci

/-- Linear independence of the keep-FOB projected compiled generators for any
family of first-of-block equal-cardinality subsets. -/
theorem linearIndependent_mlProj_keepFOBProjected_compiled_fob
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (κ : Nat) (hκ : κ ≥ 1)
    {F : Finset (Finset (Fin n))}
    (hcard : ∀ S ∈ F, S.card = κ)
    (hfob : ∀ S ∈ F, ∀ v ∈ S, 3 ∣ v.val) :
    LinearIndependent Rat (fun S : F =>
      mlProj (iterDerivList (S : Finset (Fin n)).toList
        (satDeciderGaugeKeepFOBProjection M n hn htb hns
          (compiledPoly (cook_levin_compilation M n hn htb hns))))) := by
  refine linearIndependent_of_tag_coeff_gram hκ hcard
    (fun S => mlProj (iterDerivList S.toList
      (satDeciderGaugeKeepFOBProjection M n hn htb hns
        (compiledPoly (cook_levin_compilation M n hn htb hns))))) ?_
  intro T hT S hS
  exact coeff_mlProj_keepFOBProjected_compiled_samesize
    M n hn htb hns T S
    (by rw [hcard T hT, hcard S hS])
    (hfob T hT) (hfob S hS)

end PallLean.Paper93.DeepMath.PathB
