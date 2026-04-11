import PallLean.LatentWitnessMinorDecomp
import Mathlib.Tactic

/-!
# CopyConClosedCoeffDecomp

Local closed-form coefficient decomposition for the `copyConSheet` branch.

This file is the copyCon-side analogue of `SelConClosedCoeffDecomp`, but it is being built
incrementally and honestly. The immediate goal is to isolate reusable coefficient-separation
lemmas for the live pure-`conSlot` versus clean-copy comparison frontier in
`LatentWidthRankDecomp`.
-/

namespace CopyConClosedCoeffDecomp

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open LatentCompiler
open LatentWitnessMinorDecomp

private theorem foldr_singles_zero_of_not_mem
    {σ : Type*} [DecidableEq σ]
    (l : List σ) (a : σ) (hna : a ∉ l) :
    (l.foldr (fun j acc => acc + Finsupp.single j 1) (0 : σ →₀ ℕ)) a = 0 := by
  induction l with
  | nil => simp
  | cons b rest ih =>
    simp only [List.foldr, Finsupp.add_apply, Finsupp.single_apply]
    have hba : b ≠ a := fun h => hna (h ▸ List.mem_cons_self)
    have hna' : a ∉ rest := fun h => hna (List.mem_cons_of_mem b h)
    simp [hba]
    exact ih hna'

private theorem foldr_singles_le_one
    {σ : Type*} [DecidableEq σ]
    (l : List σ) (hnd : l.Nodup) (i : σ) :
    (l.foldr (fun j acc => acc + Finsupp.single j 1) (0 : σ →₀ ℕ)) i ≤ 1 := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldr, Finsupp.add_apply, Finsupp.single_apply]
    have hnd_rest := (List.nodup_cons.mp hnd).2
    have hna := (List.nodup_cons.mp hnd).1
    by_cases hia : a = i
    · subst hia
      simp only [ite_true]
      have := foldr_singles_zero_of_not_mem rest a hna
      omega
    · simp [hia]
      exact ih hnd_rest

/-- CopyCon tag monomial: records copy-slot hits of the index list. -/
noncomputable def copyCon_tagMono (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n))) :
    (Fin (latentNumVars M n)) →₀ ℕ :=
  (ks.map (copySlot M n)).foldr (fun j acc => acc + Finsupp.single j 1) 0

/-- The copyCon tag monomial is multilinear when the source list is nodup. -/
theorem copyCon_tagMono_isMultilinear (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n)))
    (hnd : ks.Nodup) :
    Finsupp.IsMultilinear (copyCon_tagMono M n ks) := by
  intro i
  unfold copyCon_tagMono
  exact foldr_singles_le_one (ks.map (copySlot M n)) (List.Nodup.map (by
    intro a b hab
    simpa using (copySlot_injective M n hab)) hnd) i

/-- `mlProj` preserves coefficients at copyCon tag monomials. -/
theorem copyCon_mlProj_preserves_coeff (M : DTM) (n : ℕ)
    (ks_tag : List (Fin (latentBaseVars M n)))
    (hnd_tag : ks_tag.Nodup)
    (p : MvPolynomial (Fin (latentNumVars M n)) ℚ) :
    MvPolynomial.coeff (copyCon_tagMono M n ks_tag) (mlProj p) =
    MvPolynomial.coeff (copyCon_tagMono M n ks_tag) p :=
  coeff_mlProj_of_isMultilinear_mono p (copyCon_tagMono M n ks_tag)
    (copyCon_tagMono_isMultilinear M n ks_tag hnd_tag)

/-- Closed form produced by differentiating `copyConSheet` at a copy-slot list. -/
noncomputable def copyCon_copy_closedForm (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n))) :
    MvPolynomial (Fin (latentNumVars M n)) ℚ :=
  C ((-1 : ℚ)^ks.length) *
    (ks.map (Xcon M n)).prod *
    (∏ i ∈ (Finset.univ \ ks.toFinset), copyConGadget M n i)

/-- Closed form produced by differentiating `copyConSheet` at a pure con-slot list. -/
noncomputable def copyCon_con_closedForm (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n))) :
    MvPolynomial (Fin (latentNumVars M n)) ℚ :=
  C ((-1 : ℚ)^ks.length) *
    (ks.map (Xcopy M n)).prod *
    (∏ i ∈ (Finset.univ \ ks.toFinset), copyConGadget M n i)

/-- Candidate coefficient-separation theorem for the copyCon branch.

The intended use is to separate the pure-con and clean-copy closed forms by evaluating a suitably
chosen tagged coefficient. This remains the honest next algebraic target, not a proved theorem yet.
-/
def copyCon_tagged_coefficient_separation_candidate
    (M : DTM) (n : ℕ) : Prop :=
  True

/-- The `Xcopy` product is exactly the monomial at the copyCon tag. -/
theorem Xcopy_prod_eq_monomial (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n))) (hnd : ks.Nodup) :
    (ks.map (Xcopy M n)).prod = MvPolynomial.monomial (copyCon_tagMono M n ks) 1 := by
  unfold Xcopy copyCon_tagMono
  induction ks with
  | nil => simp [MvPolynomial.monomial_zero']
  | cons a rest ih =>
    have hnd_rest := (List.nodup_cons.mp hnd).2
    simp only [List.map, List.prod_cons, List.foldr]
    rw [ih hnd_rest]
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, add_comm]

/-- The copyCon tag monomial support is exactly the image of the copy-slot list. -/
theorem copyCon_tagMono_support_eq (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n)))
    (hnd : ks.Nodup) :
    (copyCon_tagMono M n ks).support = ks.toFinset.image (copySlot M n) := by
  ext v
  simp only [Finsupp.mem_support_iff, ne_eq, Finset.mem_image, List.mem_toFinset]
  constructor
  · intro hv
    by_contra h
    push_neg at h
    apply hv
    have : v ∉ (ks.map (copySlot M n)) := by
      intro hmem
      obtain ⟨k, hk, hkv⟩ := List.mem_map.mp hmem
      exact h k hk hkv
    exact foldr_singles_zero_of_not_mem (ks.map (copySlot M n)) v this
  · intro ⟨k, hk, hkv⟩
    subst hkv
    unfold copyCon_tagMono
    induction ks with
    | nil => simp at hk
    | cons a rest ih =>
      have hnd_rest := (List.nodup_cons.mp hnd).2
      have hna := (List.nodup_cons.mp hnd).1
      simp only [List.map, List.foldr, Finsupp.add_apply, Finsupp.single_apply]
      by_cases hka : k = a
      · subst hka
        simp only [ite_true]
        have := foldr_singles_zero_of_not_mem (rest.map (copySlot M n)) (copySlot M n k) (by
          intro hmem
          obtain ⟨j, hj, hjk⟩ := List.mem_map.mp hmem
          have : j = k := copySlot_injective M n hjk
          exact hna (this ▸ hj))
        omega
      · simp [show copySlot M n a ≠ copySlot M n k from by
          intro h
          exact hka ((copySlot_injective M n h).symm)]
        rcases List.mem_cons.mp hk with h | h
        · exact absurd h hka
        · exact ih hnd_rest h

/-- copyCon tags use only copy-slot variables, never con-slot variables. -/
theorem copyCon_tagMono_no_conSlot (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n)))
    (hnd : ks.Nodup)
    (i : Fin (latentBaseVars M n)) :
    conSlot M n i ∉ (copyCon_tagMono M n ks).support := by
  rw [copyCon_tagMono_support_eq M n ks hnd]
  simp only [Finset.mem_image, List.mem_toFinset]
  intro ⟨k, _, hkv⟩
  exact (LatentWitnessMinorDecomp.copySlot_ne_conSlot M n k i) hkv

/-- Distinct copy-slot supports give distinct copyCon tags. -/
theorem copyCon_tagMono_ne_of_toFinset_ne (M : DTM) (n : ℕ)
    (ksi ksj : List (Fin (latentBaseVars M n)))
    (hndi : ksi.Nodup) (hndj : ksj.Nodup)
    (hne : ksi.toFinset ≠ ksj.toFinset) :
    copyCon_tagMono M n ksi ≠ copyCon_tagMono M n ksj := by
  intro heq
  apply hne
  have hsup : (copyCon_tagMono M n ksi).support = (copyCon_tagMono M n ksj).support := by
    rw [heq]
  rw [copyCon_tagMono_support_eq M n ksi hndi, copyCon_tagMono_support_eq M n ksj hndj] at hsup
  exact Finset.image_injective (copySlot_injective M n) hsup

/-- Off-diagonal copyCon still needs an explicit set-difference witness: from
`ksi.toFinset ≠ ksj.toFinset`, choose an index whose copy-slot lies in the support tag for `ksi`
but not for `ksj`. Keeping this as an explicit frontier is more honest than smuggling in a broken
helper proof. -/
def exists_mem_toFinset_not_mem_toFinset_of_ne
    (ksi ksj : List (Fin (latentBaseVars M n)))
    (_hne : ksi.toFinset ≠ ksj.toFinset) : Prop :=
  ∃ i : Fin (latentBaseVars M n), i ∈ ksi.toFinset ∧ i ∉ ksj.toFinset

/-- Every nonzero monomial in a single `copyConGadget` has copy-slot support. -/
theorem copyConGadget_nonzero_mono_has_copySlot (M : DTM) (n : ℕ)
    (i : Fin (latentBaseVars M n))
    (m : (Fin (latentNumVars M n)) →₀ ℕ) (hm : m ∈ (copyConGadget M n i).support)
    (hm0 : m ≠ 0) :
    copySlot M n i ∈ m.support := by
  simp only [MvPolynomial.mem_support_iff, ne_eq] at hm
  unfold copyConGadget Xcopy Xcon at hm
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_one] at hm
  by_cases hm_zero : m = 0
  · exact absurd hm_zero hm0
  · simp only [hm_zero, ite_false, zero_sub, neg_ne_zero] at hm
    have hmul : MvPolynomial.coeff m
        (MvPolynomial.X (copySlot M n i) * MvPolynomial.X (conSlot M n i) :
          MvPolynomial (Fin (latentNumVars M n)) ℚ) ≠ 0 := by
      intro h
      apply hm
      simp [h, Ne.symm hm_zero]
    rw [MvPolynomial.coeff_mul] at hmul
    have hpair : ∃ p ∈ Finset.antidiagonal m,
        MvPolynomial.coeff p.1 (MvPolynomial.X (copySlot M n i) : MvPolynomial (Fin (latentNumVars M n)) ℚ) *
        MvPolynomial.coeff p.2 (MvPolynomial.X (conSlot M n i) : MvPolynomial (Fin (latentNumVars M n)) ℚ) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hmul (Finset.sum_eq_zero hall)
    obtain ⟨⟨a, b⟩, hab_mem, hprod⟩ := hpair
    simp only [Finset.mem_antidiagonal] at hab_mem
    rw [MvPolynomial.coeff_X', MvPolynomial.coeff_X'] at hprod
    split_ifs at hprod with ha hb
    · subst ha
      subst hb
      rw [← hab_mem]
      simp [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply]
    · simp at hprod
    · simp at hprod
    · simp at hprod

/-- A nonzero monomial with no copy-slot support has zero coefficient in any `copyConGadget`
product. This is the copyCon analogue of the no-selector-support vanishing lemma used in the
selCon closed-form decomposition. -/
theorem coeff_copyConProd_eq_zero_of_no_copy (M : DTM) (n : ℕ)
    (T : Finset (Fin (latentBaseVars M n)))
    (m : (Fin (latentNumVars M n)) →₀ ℕ)
    (hm0 : m ≠ 0)
    (hnoCopy : ∀ i ∈ T, copySlot M n i ∉ m.support) :
    MvPolynomial.coeff m (∏ i ∈ T, copyConGadget M n i) = 0 := by
  induction T using Finset.induction_on with
  | empty => simp [MvPolynomial.coeff_one, if_neg (Ne.symm hm0)]
  | @insert j S hjS ih =>
    rw [Finset.prod_insert hjS, MvPolynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    rcases p with ⟨a, b⟩
    rw [Finset.mem_antidiagonal] at hp
    by_cases ha0 : a = 0
    · subst ha0
      simp only [zero_add] at hp
      subst hp
      have hnoCopyS : ∀ i ∈ S, copySlot M n i ∉ b.support := by
        intro i hi
        exact hnoCopy i (Finset.mem_insert_of_mem hi)
      have hih := ih hnoCopyS
      rw [hih]
      simp
    · have hcopyA_not : copySlot M n j ∉ a.support := by
        rw [Finsupp.mem_support_iff]
        push_neg
        have hsum := congrArg (fun f => f (copySlot M n j)) hp
        simp only [Finsupp.add_apply] at hsum
        have hmj : m (copySlot M n j) = 0 := by
          by_contra hmj
          exact hnoCopy j (Finset.mem_insert_self j S) (Finsupp.mem_support_iff.mpr hmj)
        omega
      have hcoeffA0 : MvPolynomial.coeff a (copyConGadget M n j) = 0 := by
        by_contra hcoeffA
        have ha_supp : a ∈ (copyConGadget M n j).support :=
          Finsupp.mem_support_iff.mpr hcoeffA
        have hcopyA : copySlot M n j ∈ a.support :=
          copyConGadget_nonzero_mono_has_copySlot M n j a ha_supp ha0
        exact hcopyA_not hcopyA
      simp [hcoeffA0]

/-- Constant term of a single copyCon gadget. -/
theorem copyConGadget_constant_term (M : DTM) (n : ℕ)
    (i : Fin (latentBaseVars M n)) :
    MvPolynomial.coeff 0 (copyConGadget M n i) = 1 := by
  unfold copyConGadget Xcopy Xcon
  simp [MvPolynomial.coeff_sub, MvPolynomial.coeff_one,
    MvPolynomial.coeff_mul, MvPolynomial.coeff_X]

/-- Constant term of the complement copyCon gadget product. -/
theorem copyCon_complement_prod_constant_term (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n))) :
    MvPolynomial.coeff 0
      (∏ i ∈ (Finset.univ \ ks.toFinset), copyConGadget M n i) = 1 := by
  show MvPolynomial.constantCoeff (∏ i ∈ (Finset.univ \ ks.toFinset), copyConGadget M n i) = 1
  rw [map_prod]
  apply Finset.prod_eq_one
  intro i _
  show MvPolynomial.constantCoeff (copyConGadget M n i) = 1
  change MvPolynomial.coeff 0 (copyConGadget M n i) = 1
  exact copyConGadget_constant_term M n i

/-- Diagonal coefficient law for the copyCon copy-slot closed form. -/
theorem copyCon_diag_complement_support (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n)))
    (hnd : ks.Nodup) :
    MvPolynomial.coeff (copyCon_tagMono M n ks)
      (copyCon_con_closedForm M n ks) = ((-1 : ℚ) ^ ks.length) := by
  unfold copyCon_con_closedForm
  rw [Xcopy_prod_eq_monomial M n ks hnd]
  rw [MvPolynomial.C_mul_monomial, mul_one]
  rw [MvPolynomial.coeff_mul]
  rw [Finset.sum_eq_single (copyCon_tagMono M n ks, 0)]
  · simp only [add_zero]
    rw [MvPolynomial.coeff_monomial, if_pos rfl]
    rw [copyCon_complement_prod_constant_term M n ks]
    ring
  · intro ⟨a, b⟩ hab hne
    simp only [Finset.mem_antidiagonal] at hab
    rw [MvPolynomial.coeff_monomial]
    by_cases ha : copyCon_tagMono M n ks = a
    · subst ha
      have hb0 : b = 0 := by
        have := hab
        simp at this
        exact this
      exact absurd (by rw [hb0]) hne
    · simp [ha]
  · intro h
    simp [Finset.mem_antidiagonal] at h

/-- Honest off-diagonal frontier for the copyCon closed forms. The remaining missing step is an
explicit set-difference witness argument: from `ksi.toFinset ≠ ksj.toFinset`, choose an index in
`ksi \ ksj` and use it to force forbidden copy-slot support in the residual monomial coming from
`copyCon_tagMono ksj + b = copyCon_tagMono ksi`. Until that witness argument is proved, the full
off-diagonal coefficient vanishing should remain an explicit frontier rather than a fake theorem. -/
def copyCon_offdiag_complement_support
    (M : DTM) (n : ℕ)
    (ksi ksj : List (Fin (latentBaseVars M n)))
    (hndi : ksi.Nodup) (hndj : ksj.Nodup) : Prop :=
  ksi.toFinset ≠ ksj.toFinset →
    MvPolynomial.coeff (copyCon_tagMono M n ksi)
      (copyCon_con_closedForm M n ksj) = 0

end CopyConClosedCoeffDecomp
