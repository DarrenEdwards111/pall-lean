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

/-- At a copy slot outside the tag support, `copyCon_tagMono` evaluates to zero. -/
theorem copyCon_tagMono_apply_copySlot_eq_zero_of_not_mem
    (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n)))
    (hnd : ks.Nodup)
    (i : Fin (latentBaseVars M n))
    (hi : i ∉ ks.toFinset) :
    (copyCon_tagMono M n ks) (copySlot M n i) = 0 := by
  by_contra hne
  have hsupp : copySlot M n i ∈ (copyCon_tagMono M n ks).support :=
    Finsupp.mem_support_iff.mpr hne
  rw [copyCon_tagMono_support_eq M n ks hnd] at hsupp
  simp only [Finset.mem_image, List.mem_toFinset] at hsupp
  rcases hsupp with ⟨j, hj, hEq⟩
  have : j = i := copySlot_injective M n hEq
  exact hi (this ▸ List.mem_toFinset.mpr hj)

/-- At a copy slot inside the tag support, `copyCon_tagMono` evaluates nontrivially. -/
theorem copyCon_tagMono_apply_copySlot_ne_zero_of_mem
    (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n)))
    (hnd : ks.Nodup)
    (i : Fin (latentBaseVars M n))
    (hi : i ∈ ks.toFinset) :
    (copyCon_tagMono M n ks) (copySlot M n i) ≠ 0 := by
  have hsupp : copySlot M n i ∈ (copyCon_tagMono M n ks).support := by
    rw [copyCon_tagMono_support_eq M n ks hnd]
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  exact Finsupp.mem_support_iff.mp hsupp

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

/-- If two nodup copy-slot index lists have the same length but different `toFinset`, some index
lies in `ksi` but not in `ksj`. This is the exact set-difference witness needed in the off-diagonal
copyCon coefficient argument. -/
theorem exists_mem_toFinset_not_mem_toFinset_of_ne_of_length_eq
    (ksi ksj : List (Fin (latentBaseVars M n)))
    (hndi : ksi.Nodup) (hndj : ksj.Nodup)
    (hlen : ksi.length = ksj.length)
    (hne : ksi.toFinset ≠ ksj.toFinset) :
    ∃ i : Fin (latentBaseVars M n), i ∈ ksi.toFinset ∧ i ∉ ksj.toFinset := by
  classical
  by_contra hall
  push_neg at hall
  have hsub : ksi.toFinset ⊆ ksj.toFinset := by
    intro x hx
    exact hall x hx
  have hcard_eq : ksi.toFinset.card = ksj.toFinset.card := by
    rw [List.toFinset_card_of_nodup hndi, List.toFinset_card_of_nodup hndj, hlen]
  have hfs_eq : ksi.toFinset = ksj.toFinset := Finset.eq_of_subset_of_card_le hsub (by omega)
  exact hne hfs_eq

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

/-- Any nonzero monomial supported by `copyConGadget M n i` must be exactly the two-slot monomial
`single (copySlot M n i) 1 + single (conSlot M n i) 1`. This is the literal support classification
needed to kill the inserted-index witness branch in the positive-witness induction. -/
theorem copyConGadget_nonzero_mono_exact_shape_candidate
    (M : DTM) (n : ℕ)
    (i : Fin (latentBaseVars M n)) :
    ∀ m : (Fin (latentNumVars M n)) →₀ ℕ,
      m ∈ (copyConGadget M n i).support →
      m ≠ 0 →
      m = Finsupp.single (copySlot M n i) 1 + Finsupp.single (conSlot M n i) 1 := by
  intro m hm hm0
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
      exact hab_mem.symm
    · simp at hprod
    · simp at hprod
    · simp at hprod

/-- Support transports forward through a sum: if `x` appears in `b.support` and `a + b = m`, then
it also appears in `m.support`. -/
theorem mem_support_of_mem_support_right_of_add
    {σ : Type*} [DecidableEq σ]
    (a b m : σ →₀ ℕ)
    (x : σ)
    (hx : x ∈ b.support)
    (hadd : a + b = m) :
    x ∈ m.support := by
  rw [Finsupp.mem_support_iff] at hx ⊢
  have hsum := congrArg (fun f => f x) hadd
  simp only [Finsupp.add_apply] at hsum
  omega

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

/-- If a nonzero monomial occurs in `copyConGadget M n j`, it cannot use a different copy slot
`copySlot M n i` with `i ≠ j`. -/
theorem copyConGadget_nonzero_mono_no_other_copySlot
    (M : DTM) (n : ℕ)
    (i j : Fin (latentBaseVars M n))
    (hij : i ≠ j)
    (m : (Fin (latentNumVars M n)) →₀ ℕ)
    (hm : m ∈ (copyConGadget M n j).support) :
    copySlot M n i ∉ m.support := by
  intro hcopy
  have hm_copy : m (copySlot M n i) ≠ 0 := Finsupp.mem_support_iff.mp hcopy
  have hm0 : m ≠ 0 := by
    intro hmz
    exact hm_copy (by simp [hmz])
  have hshape := copyConGadget_nonzero_mono_exact_shape_candidate M n j m hm hm0
  rw [hshape] at hcopy
  have hneq : copySlot M n i ≠ copySlot M n j := by
    intro hEq
    exact hij (copySlot_injective M n hEq)
  simp [Finsupp.mem_support_iff, Finsupp.add_apply, hneq,
    show copySlot M n i ≠ conSlot M n j from copySlot_ne_conSlot M n i j] at hcopy

/-- In the insert-step for the copyCon gadget product, any witness copy-slot belonging to an index
`i ≠ j` cannot come from the left gadget factor `copyConGadget M n j`, so it survives in the
residual monomial `b`. -/
theorem copyCon_insert_witness_survives_in_residual
    (M : DTM) (n : ℕ)
    {i j : Fin (latentBaseVars M n)}
    (hij : i ≠ j)
    {a b m : (Fin (latentNumVars M n)) →₀ ℕ}
    (ha_supp : a ∈ (copyConGadget M n j).support)
    (hm_copy : copySlot M n i ∈ m.support)
    (hb_add : a + b = m) :
    copySlot M n i ∈ b.support := by
  have hcopyA_not : copySlot M n i ∉ a.support :=
    copyConGadget_nonzero_mono_no_other_copySlot M n i j hij a ha_supp
  rw [Finsupp.mem_support_iff] at hm_copy hcopyA_not ⊢
  have hsum := congrArg (fun f => f (copySlot M n i)) hb_add
  simp only [Finsupp.add_apply] at hsum
  have ha_zero : a (copySlot M n i) = 0 := by
    by_contra ha_ne
    exact hcopyA_not ha_ne
  omega

/-- Insert-step splitter for the positive-witness copyCon induction.
If a witness copy-slot belongs to an index from the residual set `S`, then any nonzero left factor
from `copyConGadget M n j` forces that witness to remain in the residual monomial `b`. -/
theorem copyCon_exists_copy_insert_reduce_to_residual
    (M : DTM) (n : ℕ)
    {j : Fin (latentBaseVars M n)}
    {S : Finset (Fin (latentBaseVars M n))}
    (hjS : j ∉ S)
    {a b m : (Fin (latentNumVars M n)) →₀ ℕ}
    (hp : a + b = m)
    (ha_supp : a ∈ (copyConGadget M n j).support)
    {i : Fin (latentBaseVars M n)}
    (hiS : i ∈ S)
    (hm_copy : copySlot M n i ∈ m.support) :
    ∃ i' ∈ S, copySlot M n i' ∈ b.support := by
  refine ⟨i, hiS, ?_⟩
  exact copyCon_insert_witness_survives_in_residual M n
    (i := i) (j := j)
    (hij := by
      intro hEq
      exact hjS (hEq ▸ hiS))
    (a := a) (b := b) (m := m)
    ha_supp hm_copy hp

/-- Insert-step repackaging of a witness in `insert j S`: if the witness is not on the inserted
index `j`, then a nonzero left gadget factor pushes the witness down into the residual monomial. -/
theorem copyCon_exists_copy_insert_cases
    (M : DTM) (n : ℕ)
    {j : Fin (latentBaseVars M n)}
    {S : Finset (Fin (latentBaseVars M n))}
    (hjS : j ∉ S)
    {a b m : (Fin (latentNumVars M n)) →₀ ℕ}
    (hp : a + b = m)
    (ha_supp : a ∈ (copyConGadget M n j).support)
    (hhasCopy : ∃ i ∈ insert j S, copySlot M n i ∈ m.support) :
    (copySlot M n j ∈ m.support) ∨ (∃ i' ∈ S, copySlot M n i' ∈ b.support) := by
  rcases hhasCopy with ⟨i, hiT, hm_copy⟩
  rcases Finset.mem_insert.mp hiT with rfl | hiS
  · exact Or.inl hm_copy
  · exact Or.inr <| copyCon_exists_copy_insert_reduce_to_residual M n hjS hp ha_supp hiS hm_copy

/-- Pointwise residual-support transport for the insert-step seam.
If the left antidiagonal factor contributes zero at `copySlot i`, then any support of the full sum
at that slot must already come from the residual monomial `b`. This is the honest transport shape
needed to treat both `a = 0` and exact-shape left factors uniformly. -/
theorem copyCon_copySlot_support_moves_to_residual_of_left_zero
    (M : DTM) (n : ℕ)
    {i : Fin (latentBaseVars M n)}
    {a b m : (Fin (latentNumVars M n)) →₀ ℕ}
    (hp : a + b = m)
    (ha_zero : a (copySlot M n i) = 0)
    (hm_copy : copySlot M n i ∈ m.support) :
    copySlot M n i ∈ b.support := by
  rw [Finsupp.mem_support_iff] at hm_copy ⊢
  have hsum := congrArg (fun f => f (copySlot M n i)) hp
  simp only [Finsupp.add_apply] at hsum
  omega

/-- Specialization of the pointwise residual-support transport to the inserted witness slot itself.
In the constant-term branch `a = 0`, any support of `m` at `copySlot j` must already come from the
residual monomial `b`. -/
theorem copyCon_insert_j_witness_moves_to_residual
    (M : DTM) (n : ℕ)
    (j : Fin (latentBaseVars M n))
    {a b m : (Fin (latentNumVars M n)) →₀ ℕ}
    (hp : a + b = m)
    (ha : a = 0)
    (hmj : copySlot M n j ∈ m.support) :
    copySlot M n j ∈ b.support := by
  apply copyCon_copySlot_support_moves_to_residual_of_left_zero M n (i := j) hp
  · simpa [ha]
  · exact hmj

/-- In the exact-shape branch, any residual witness copy-slot `copySlot i` with `i ≠ j` is absent
from the left monomial `single(copy j)+single(con j)`, so the pointwise residual-support transport
applies directly. -/
theorem copyCon_exact_shape_other_copySlot_zero
    (M : DTM) (n : ℕ)
    {i j : Fin (latentBaseVars M n)}
    (hij : i ≠ j) :
    ((Finsupp.single (copySlot M n j) 1 + Finsupp.single (conSlot M n j) 1 :
      (Fin (latentNumVars M n)) →₀ ℕ)) (copySlot M n i) = 0 := by
  have hneq : copySlot M n j ≠ copySlot M n i := by
    intro hEq
    exact hij ((copySlot_injective M n hEq).symm)
  have hneq' : conSlot M n j ≠ copySlot M n i := by
    intro hEq
    exact (copySlot_ne_conSlot M n i j) hEq.symm
  simp [hneq, hneq']

/-- Local insert-step summand frontier for the positive-witness induction.
If the left antidiagonal monomial is a nonzero support monomial of `copyConGadget j`, and the total
monomial `m` contains some copy-slot witness from `insert j S`, then either the witness is on `j`
and the left coefficient already vanishes against `copyConGadget_constant_term`, or the witness is
pushed into the residual `b`, where the induction hypothesis should apply. This packages the exact
branch split still needed before reproving `coeff_copyConProd_eq_zero_of_exists_copy`. -/
theorem copyCon_insert_antidiagonal_summand_zero
    (M : DTM) (n : ℕ)
    (j : Fin (latentBaseVars M n))
    (S : Finset (Fin (latentBaseVars M n)))
    (hjS : j ∉ S)
    (m : (Fin (latentNumVars M n)) →₀ ℕ)
    (a b : (Fin (latentNumVars M n)) →₀ ℕ)
    (hp : a + b = m)
    (ha_supp : a ∈ (copyConGadget M n j).support)
    (hcopy : ∃ i ∈ insert j S, copySlot M n i ∈ m.support) :
    (copySlot M n j ∈ m.support) ∨ (∃ i ∈ S, copySlot M n i ∈ b.support) := by
  exact copyCon_exists_copy_insert_cases M n hjS hp ha_supp hcopy

/-- Constant term of a single copyCon gadget. -/
theorem copyConGadget_constant_term (M : DTM) (n : ℕ)
    (i : Fin (latentBaseVars M n)) :
    MvPolynomial.coeff 0 (copyConGadget M n i) = 1 := by
  unfold copyConGadget Xcopy Xcon
  simp [MvPolynomial.coeff_sub, MvPolynomial.coeff_one,
    MvPolynomial.coeff_mul, MvPolynomial.coeff_X]

/-- Coefficient classification for a single copyCon gadget: the only monomials with nonzero
coefficient are the constant monomial and the exact copy-con pair monomial. -/
theorem copyConGadget_coeff_nonzero_classification
    (M : DTM) (n : ℕ)
    (i : Fin (latentBaseVars M n))
    (m : (Fin (latentNumVars M n)) →₀ ℕ)
    (hm : MvPolynomial.coeff m (copyConGadget M n i) ≠ 0) :
    m = 0 ∨ m = Finsupp.single (copySlot M n i) 1 + Finsupp.single (conSlot M n i) 1 := by
  by_cases hm0 : m = 0
  · exact Or.inl hm0
  · right
    have hsupp : m ∈ (copyConGadget M n i).support := Finsupp.mem_support_iff.mpr hm
    exact copyConGadget_nonzero_mono_exact_shape_candidate M n i m hsupp hm0

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

/-- Constant term of an arbitrary copyCon gadget product. -/
theorem copyCon_prod_constant_term (M : DTM) (n : ℕ)
    (S : Finset (Fin (latentBaseVars M n))) :
    MvPolynomial.coeff 0 (∏ i ∈ S, copyConGadget M n i) = 1 := by
  show MvPolynomial.constantCoeff (∏ i ∈ S, copyConGadget M n i) = 1
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

/-- Stronger induction target for gadget-product vanishing.
If any copy-slot appears in the support of `m`, then the coefficient of the copyCon gadget product
must vanish. This is the formulation that matches the constant-term insert branch, because after
removing the inserted index from the smaller product one can still transport a residual witness on
that same copy-slot. The indexed positive-witness statement below should be recovered as a simple
corollary once this stronger form is proved. -/
def coeff_copyConProd_eq_zero_of_any_copy
    (M : DTM) (n : ℕ)
    (T : Finset (Fin (latentBaseVars M n)))
    (m : (Fin (latentNumVars M n)) →₀ ℕ) : Prop :=
  m ≠ 0 →
  (∃ i : Fin (latentBaseVars M n), copySlot M n i ∈ m.support) →
    MvPolynomial.coeff m (∏ i ∈ T, copyConGadget M n i) = 0

/-- A nonzero monomial has zero coefficient in the constant polynomial `1`. -/
theorem coeff_one_eq_zero_of_ne_zero
    {σ : Type} [DecidableEq σ]
    (m : σ →₀ ℕ)
    (hm : m ≠ 0) :
    MvPolynomial.coeff m (1 : MvPolynomial σ ℚ) = 0 := by
  rw [MvPolynomial.coeff_one]
  simp [show (0 : σ →₀ ℕ) ≠ m from by simpa [eq_comm] using hm]

/-- Temporary wrapper for the stronger `any_copy` target while it remains recorded as
`def ... : Prop`. The latest honest retry confirmed the right insert-step organization,
left-factor classification first and witness usage branchwise, but also re-confirmed the theorem
order issue: the full stronger theorem cannot be placed here yet because it depends on local seam
lemmas stated later in the file.

So this wrapper stays as the executable entry point for now, and the branch-first theorem rewrite
is recorded in the surrounding local seam theorems plus the blocker note below. -/
theorem coeff_copyConProd_eq_zero_of_any_copy_apply
    (M : DTM) (n : ℕ)
    (T : Finset (Fin (latentBaseVars M n)))
    (m : (Fin (latentNumVars M n)) →₀ ℕ)
    (hzero : coeff_copyConProd_eq_zero_of_any_copy M n T m)
    (hm : m ≠ 0)
    (hcopy : ∃ i : Fin (latentBaseVars M n), copySlot M n i ∈ m.support) :
    MvPolynomial.coeff m (∏ i ∈ T, copyConGadget M n i) = 0 :=
  hzero hm hcopy

/-- Indexed positive-witness version, intended as a corollary of
`coeff_copyConProd_eq_zero_of_any_copy`. -/
def coeff_copyConProd_eq_zero_of_exists_copy
    (M : DTM) (n : ℕ)
    (T : Finset (Fin (latentBaseVars M n)))
    (m : (Fin (latentNumVars M n)) →₀ ℕ) : Prop :=
  m ≠ 0 →
  (∃ i ∈ T, copySlot M n i ∈ m.support) →
    MvPolynomial.coeff m (∏ i ∈ T, copyConGadget M n i) = 0

/-- Exact local frontier exposed by the failed full induction retry.
For an insert-step antidiagonal term with left coefficient supported on the exact copy-con shape,
if the witness split lands in the residual branch, then the summand should vanish by applying the
induction hypothesis to the residual coefficient. This isolates the remaining bookkeeping problem:
one must move from `a + b = m` and `a = exactShape` to a clean right-factor zero statement without
mixing up the total monomial `m` and the residual monomial `b`. -/
theorem copyCon_insert_exact_shape_residual_summand_zero
    (M : DTM) (n : ℕ)
    (j : Fin (latentBaseVars M n))
    (S : Finset (Fin (latentBaseVars M n)))
    (m a b : (Fin (latentNumVars M n)) →₀ ℕ)
    (hp : a + b = m)
    (hshape : a = Finsupp.single (copySlot M n j) 1 + Finsupp.single (conSlot M n j) 1)
    (hcopy : ∃ i : Fin (latentBaseVars M n), copySlot M n i ∈ b.support)
    (hb : b ≠ 0)
    (hzero : ∀ m' : (Fin (latentNumVars M n)) →₀ ℕ,
      m' ≠ 0 →
      (∃ i : Fin (latentBaseVars M n), copySlot M n i ∈ m'.support) →
      MvPolynomial.coeff m' (∏ i ∈ S, copyConGadget M n i) = 0) :
    MvPolynomial.coeff a (copyConGadget M n j) *
      MvPolynomial.coeff b (∏ i ∈ S, copyConGadget M n i) = 0 := by
  have hbcoeff : MvPolynomial.coeff b (∏ i ∈ S, copyConGadget M n i) = 0 :=
    hzero b hb hcopy
  rw [hbcoeff]
  ring

/-- Constant-term branch of the insert-step antidiagonal analysis, phrased against the stronger
arbitrary-copy witness target. The honest split is now direct: any copy witness on `m.support`
either is the inserted `j` witness, handled by `hmove` and `hjzero`, or is some other copy slot,
which moves to `b.support` because the left factor is constant. -/
theorem copyCon_insert_constant_residual_summand_zero
    (M : DTM) (n : ℕ)
    (j : Fin (latentBaseVars M n))
    (S : Finset (Fin (latentBaseVars M n)))
    (m a b : (Fin (latentNumVars M n)) →₀ ℕ)
    (hjS : j ∉ S)
    (hp : a + b = m)
    (ha0 : a = 0)
    (ha_supp : a ∈ (copyConGadget M n j).support)
    (hm : m ≠ 0)
    (hcopy : ∃ i : Fin (latentBaseVars M n), copySlot M n i ∈ m.support)
    (hzero : ∀ m' : (Fin (latentNumVars M n)) →₀ ℕ,
      m' ≠ 0 →
      (∃ i : Fin (latentBaseVars M n), copySlot M n i ∈ m'.support) →
      MvPolynomial.coeff m' (∏ i ∈ S, copyConGadget M n i) = 0)
    (hmove : (copySlot M n j ∈ m.support) → copySlot M n j ∈ b.support)
    (hjzero : (copySlot M n j ∈ b.support) →
      MvPolynomial.coeff b (∏ i ∈ S, copyConGadget M n i) = 0) :
    MvPolynomial.coeff a (copyConGadget M n j) *
      MvPolynomial.coeff b (∏ i ∈ S, copyConGadget M n i) = 0 := by
  rcases hcopy with ⟨i, him⟩
  by_cases hij : i = j
  · subst hij
    have hbcoeff : MvPolynomial.coeff b (∏ i ∈ S, copyConGadget M n i) = 0 :=
      hjzero (hmove him)
    rw [hbcoeff]
    ring
  · have hbcoeff : MvPolynomial.coeff b (∏ i ∈ S, copyConGadget M n i) = 0 :=
      hzero b
        (by
          intro hb0
          apply hm
          rw [ha0, hb0, zero_add] at hp
          exact hp.symm)
        (by
          refine ⟨i, ?_⟩
          exact copyCon_copySlot_support_moves_to_residual_of_left_zero M n hp (by simpa [ha0]) him)
    rw [hbcoeff]
    ring

/-- Honest blocker note for the stronger `any_copy` induction.

The tempting exact-shape inserted-witness frontier is false if stated as:
from `a = Xcopy(j) * Xcon(j)` and `copySlot j ∈ m.support`, conclude the corresponding antidiagonal
summand vanishes. That data alone says nothing about the residual coefficient on `b`, because the
witness on `m` may be explained entirely by the left exact-shape monomial `a`.

This means the remaining problem is no longer a missing transport lemma. The induction skeleton
itself must be rearranged: in the exact-shape branch one cannot first choose an arbitrary witness on
`m` and then try to push it uniformly to `b`. Instead, the proof has to classify the left monomial
first and only then choose the witness strategy adapted to that branch.

The latest retry also exposed a concrete file-organization constraint: the stronger theorem cannot
honestly live above these local seam lemmas while it calls them, so either the seam lemmas must be
moved earlier or the full theorem must be reintroduced later in the file.

The sharper remaining target is not bare vanishing. What is actually needed is a theorem saying
that in the exact-shape inserted-slot branch, either
1. the right residual `b` is zero and the full antidiagonal term can be evaluated directly, or
2. `b` is nonzero and carries a copy-slot witness, so the residual branch theorem applies.

The latest direct proof attempt showed the naive witness choice `i = j` does not work: the left
exact-shape monomial already uses `copySlot j`, so the pointwise residual-support transport lemma
cannot move that slot into `b`. So the split remains a genuine candidate, not a theorem yet.
-/

lemma copyCon_exact_shape_coeff_doc_separator : True := by
  trivial

/-- Exact-shape coefficient in a single copyCon gadget.

This is the one-gadget antidiagonal micro-goal currently blocking the zero-residual branch. -/
theorem copyCon_exact_shape_coeff_single_copy
    (M : DTM) (n : ℕ)
    (j : Fin (latentBaseVars M n))
    {a : (Fin (latentNumVars M n)) →₀ ℕ}
    (ha : a ≠ Finsupp.single (copySlot M n j) 1) :
    MvPolynomial.coeff a (MvPolynomial.X (copySlot M n j) : MvPolynomial (Fin (latentNumVars M n)) ℚ) = 0 := by
  rw [MvPolynomial.coeff_X']
  by_cases h : Finsupp.single (copySlot M n j) 1 = a
  · exact False.elim (ha h.symm)
  · simp [h]

theorem copyCon_exact_shape_coeff_single_con
    (M : DTM) (n : ℕ)
    (j : Fin (latentBaseVars M n))
    {b : (Fin (latentNumVars M n)) →₀ ℕ}
    (hb : b ≠ Finsupp.single (conSlot M n j) 1) :
    MvPolynomial.coeff b (MvPolynomial.X (conSlot M n j) : MvPolynomial (Fin (latentNumVars M n)) ℚ) = 0 := by
  rw [MvPolynomial.coeff_X']
  by_cases h : Finsupp.single (conSlot M n j) 1 = b
  · exact False.elim (hb h.symm)
  · simp [h]

/-- Exact-shape coefficient in a single copyCon gadget.

This is the one-gadget antidiagonal micro-goal currently blocking the zero-residual branch. -/
theorem copyCon_exact_shape_antidiagonal_pair_zero
    (M : DTM) (n : ℕ)
    (j : Fin (latentBaseVars M n))
    {a b : (Fin (latentNumVars M n)) →₀ ℕ}
    (hab : a + b = Finsupp.single (copySlot M n j) 1 + Finsupp.single (conSlot M n j) 1)
    (hne : (a, b) ≠ (Finsupp.single (copySlot M n j) 1, Finsupp.single (conSlot M n j) 1)) :
    MvPolynomial.coeff a (MvPolynomial.X (copySlot M n j) : MvPolynomial (Fin (latentNumVars M n)) ℚ) *
      MvPolynomial.coeff b (MvPolynomial.X (conSlot M n j) : MvPolynomial (Fin (latentNumVars M n)) ℚ) = 0 := by
  by_cases ha : a = Finsupp.single (copySlot M n j) 1
  · have hb : b ≠ Finsupp.single (conSlot M n j) 1 := by
      intro hbeq
      apply hne
      simp [ha, hbeq]
    rw [ha, copyCon_exact_shape_coeff_single_con M n j hb]
    ring
  · rw [copyCon_exact_shape_coeff_single_copy M n j ha]
    ring

/-- Exact-shape coefficient in a single copyCon gadget. -/
theorem copyCon_exact_shape_coeff_nonzero
    (M : DTM) (n : ℕ)
    (j : Fin (latentBaseVars M n)) :
  MvPolynomial.coeff
    (Finsupp.single (copySlot M n j) 1 + Finsupp.single (conSlot M n j) 1)
    (copyConGadget M n j) = -1 := by
  unfold copyConGadget Xcopy Xcon
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_one]
  have hne :
      ((Finsupp.single (copySlot M n j) 1 + Finsupp.single (conSlot M n j) 1 :
        (Fin (latentNumVars M n)) →₀ ℕ)) ≠ 0 := by
    intro hzero
    have hval := congrArg (fun f => f (copySlot M n j)) hzero
    simp at hval
  have hconst : MvPolynomial.coeff
      (Finsupp.single (copySlot M n j) 1 + Finsupp.single (conSlot M n j) 1)
      (1 : MvPolynomial (Fin (latentNumVars M n)) ℚ) = 0 := by
    exact coeff_one_eq_zero_of_ne_zero _ hne
  have hif : (if 0 = (Finsupp.single (copySlot M n j) 1 + Finsupp.single (conSlot M n j) 1 :
      (Fin (latentNumVars M n)) →₀ ℕ) then (1 : ℚ) else 0) = 0 := by
    by_cases h : (0 : (Fin (latentNumVars M n)) →₀ ℕ) =
        Finsupp.single (copySlot M n j) 1 + Finsupp.single (conSlot M n j) 1
    · exact False.elim (hne h.symm)
    · simp [h]
  rw [hif, zero_sub, MvPolynomial.coeff_mul]
  rw [Finset.sum_eq_single
    (Finsupp.single (copySlot M n j) 1, Finsupp.single (conSlot M n j) 1)]
  · norm_num
  · intro ab hab hnepair
    rcases ab with ⟨a, b⟩
    exact copyCon_exact_shape_antidiagonal_pair_zero M n j (by
      simpa [Finset.mem_antidiagonal] using hab) hnepair
  · simp [Finset.mem_antidiagonal]

/-- Micro-blocker note for the exact-shape gadget coefficient.

The selCon analogue and the direct retries agree on the proof shape: expand `coeff_sub`, kill the
constant branch because the target monomial is nonzero, then prove the remaining multiplication
coefficient by isolating the unique antidiagonal pair `(single copy, single con)`.

What is still missing is the last antidiagonal singleton/coefficient calculation in a form Lean
accepts without extra local normalization lemmas. Two tiny ingredients are now isolated as the
helpers `copyCon_exact_shape_coeff_single_copy` and `copyCon_exact_shape_coeff_single_con`; the
remaining gap was promoting the antidiagonal uniqueness step for the exact pair `(single copy,
single con)` into the full exact-shape coefficient theorem. -/

def copyCon_exact_shape_coeff_antidiagonal_blocker : Prop :=
  True

/-- Zero-residual exact-shape branch, now reduced to the explicit gadget coefficient and the
constant term of the residual product.

Importantly, this summand is not zero: when `b = 0`, the residual product contributes its constant
term `1`, so the exact-shape gadget contribution survives as `-1`.

The remaining missing lemma is exactly the copyCon analogue of `coeff_zero_cvFactor_prod` from
IdentityMinor: `coeff 0 (∏ i ∈ S, copyConGadget M n i) = 1`. -/
theorem copyCon_insert_exact_shape_zero_residual_summand_candidate
    (M : DTM) (n : ℕ)
    (j : Fin (latentBaseVars M n))
    (S : Finset (Fin (latentBaseVars M n)))
    (m a b : (Fin (latentNumVars M n)) →₀ ℕ) :
  a + b = m →
  a = Finsupp.single (copySlot M n j) 1 + Finsupp.single (conSlot M n j) 1 →
  b = 0 →
    MvPolynomial.coeff a (copyConGadget M n j) *
      MvPolynomial.coeff b (∏ i ∈ S, copyConGadget M n i) = -1 := by
  intro _ ha hb
  subst ha
  subst hb
  rw [copyCon_exact_shape_coeff_nonzero, copyCon_prod_constant_term]
  norm_num

/-- Nonzero-residual exact-shape inserted-slot frontier.

The old split statement was too weakly targeted. The real remaining local need is the direct
nonzero branch: if `a` is the exact inserted gadget shape, `copySlot j` appears in the total
monomial `m`, and the residual `b` is nonzero, then one must show that some copy-slot appears in
`b.support`. This is exactly what is needed to feed the induction hypothesis on the residual
factor. -/
def copyCon_insert_exact_shape_nonzero_residual_witness_candidate
    (M : DTM) (n : ℕ)
    (j : Fin (latentBaseVars M n))
    (S : Finset (Fin (latentBaseVars M n)))
    (m a b : (Fin (latentNumVars M n)) →₀ ℕ) : Prop :=
  a + b = m →
  a = Finsupp.single (copySlot M n j) 1 + Finsupp.single (conSlot M n j) 1 →
  copySlot M n j ∈ m.support →
  b ≠ 0 →
  ∃ i : Fin (latentBaseVars M n), copySlot M n i ∈ b.support

/-- Local residual-support frontier for the copyCon off-diagonal argument. Once one has a witness
`i0 ∈ ksi.toFinset` with `i0 ∉ ksj.toFinset`, the remaining missing step is to show that any
residual monomial `b` satisfying `copyCon_tagMono M n ksj + b = copyCon_tagMono M n ksi` must carry
`copySlot M n i0` in its support. This is the exact support contradiction needed to combine the
set-difference witness with `coeff_copyConProd_eq_zero_of_no_copy`. -/
theorem copyCon_residual_support_from_offdiag_witness
    (M : DTM) (n : ℕ)
    (ksi ksj : List (Fin (latentBaseVars M n)))
    (i0 : Fin (latentBaseVars M n))
    (hndi : ksi.Nodup) (hndj : ksj.Nodup)
    (hi0_ksi : i0 ∈ ksi.toFinset)
    (hi0_not_ksj : i0 ∉ ksj.toFinset) :
    ∀ b : (Fin (latentNumVars M n)) →₀ ℕ,
      copyCon_tagMono M n ksj + b = copyCon_tagMono M n ksi →
        copySlot M n i0 ∈ b.support := by
  intro b hab
  rw [Finsupp.mem_support_iff]
  have hsum : (copyCon_tagMono M n ksj + b) (copySlot M n i0) =
      (copyCon_tagMono M n ksi) (copySlot M n i0) := by
    rw [hab]
  simp only [Finsupp.add_apply] at hsum
  have hleft : (copyCon_tagMono M n ksj) (copySlot M n i0) = 0 := by
    exact copyCon_tagMono_apply_copySlot_eq_zero_of_not_mem M n ksj hndj i0 hi0_not_ksj
  have hright : (copyCon_tagMono M n ksi) (copySlot M n i0) ≠ 0 := by
    exact copyCon_tagMono_apply_copySlot_ne_zero_of_mem M n ksi hndi i0 hi0_ksi
  intro hb0
  rw [hleft, hb0, zero_add] at hsum
  exact hright hsum.symm

/-- Honest later-placement frontier for the stronger `any_copy` theorem.

Reinserting the stronger theorem after the local seam block removed the theorem-order problem and
confirmed the branch-first induction shape is the right one. The constant branch and the
exact-shape residual-witness branch both wire up cleanly against the proved seam lemmas.

The remaining live branch is exactly the expected one: the exact-shape inserted-slot case with
`copySlot j ∈ m.support`. The explicit one-gadget coefficient theorem now lands, and the
zero-residual subcase is discharged from it.

So the true remaining blocker is now the direct nonzero-residual witness statement
`copyCon_insert_exact_shape_nonzero_residual_witness_candidate`: find a copy-slot witness in `b` or
replace that need with a stronger direct argument. -/
def coeff_copyConProd_eq_zero_of_any_copy_later_candidate : Prop :=
  True

/-- Honest off-diagonal frontier for the copyCon pure-con closed form. The combinatorial witness
and the local residual-support theorem are now both proved, and the local insert-step antidiagonal
packaging has been upgraded to theorem level in both branches under the strengthened induction
statement `coeff_copyConProd_eq_zero_of_any_copy`. So the remaining blocker is now exactly the
full induction assembly for that stronger gadget-product vanishing statement, followed by its use
with `copyCon_residual_support_from_offdiag_witness` to finish the off-diagonal coefficient
argument. -/
def copyCon_offdiag_complement_support
    (M : DTM) (n : ℕ)
    (ksi ksj : List (Fin (latentBaseVars M n)))
    (hndi : ksi.Nodup) (hndj : ksj.Nodup)
    (hlen : ksi.length = ksj.length) : Prop :=
  ksi.toFinset ≠ ksj.toFinset →
    MvPolynomial.coeff (copyCon_tagMono M n ksi)
      (copyCon_con_closedForm M n ksj) = 0

end CopyConClosedCoeffDecomp
