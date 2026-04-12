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

/-- Variables of a single copyCon gadget are exactly its copy-slot and con-slot variables. -/
theorem copyConGadget_vars_subset_copy_or_con
    (M : DTM) (n : ℕ)
    (i : Fin (latentBaseVars M n)) :
    (copyConGadget M n i).vars ⊆
      (Finset.univ.image (copySlot M n) ∪ Finset.univ.image (conSlot M n)) := by
  intro v hv
  unfold copyConGadget at hv
  have hvsub := MvPolynomial.vars_sub_subset (p := (1 : MvPolynomial (Fin (latentNumVars M n)) ℚ)) (q := Xcopy M n i * Xcon M n i)
  have hv' := Finset.mem_of_subset hvsub hv
  rw [Finset.mem_union] at hv'
  rcases hv' with hv1 | hvmul
  · rw [MvPolynomial.vars_one] at hv1
    simp at hv1
  · have hvmul_sub := MvPolynomial.vars_mul (φ := Xcopy M n i) (ψ := Xcon M n i)
    have hvmul' := Finset.mem_of_subset hvmul_sub hvmul
    rw [Finset.mem_union] at hvmul'
    unfold Xcopy Xcon at hvmul'
    rcases hvmul' with hvc | hvs
    · rw [MvPolynomial.vars_X] at hvc
      rw [Finset.mem_singleton.mp hvc]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    · rw [MvPolynomial.vars_X] at hvs
      rw [Finset.mem_singleton.mp hvs]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

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

/-- If a nonzero monomial occurs in `copyConGadget M n j`, it cannot use a different con slot
`conSlot M n i` with `i ≠ j`. -/
theorem copyConGadget_nonzero_mono_no_other_conSlot
    (M : DTM) (n : ℕ)
    (i j : Fin (latentBaseVars M n))
    (hij : i ≠ j)
    (m : (Fin (latentNumVars M n)) →₀ ℕ)
    (hm : m ∈ (copyConGadget M n j).support) :
    conSlot M n i ∉ m.support := by
  intro hcon
  have hm_con : m (conSlot M n i) ≠ 0 := Finsupp.mem_support_iff.mp hcon
  have hm0 : m ≠ 0 := by
    intro hmz
    exact hm_con (by simp [hmz])
  have hshape := copyConGadget_nonzero_mono_exact_shape_candidate M n j m hm hm0
  rw [hshape] at hcon
  have hneq : conSlot M n i ≠ conSlot M n j := by
    intro hEq
    have : i = j := by
      simp [conSlot, slot] at hEq
      exact Fin.ext (by omega)
    exact hij this
  simp [Finsupp.mem_support_iff, Finsupp.add_apply, hneq,
    show conSlot M n i ≠ copySlot M n j from by
      intro hEq
      exact (copySlot_ne_conSlot M n j i) hEq.symm] at hcon

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

/-- Con-slot analogue of residual support transport in the insert step.
If a con-slot belonging to an index `i ≠ j` appears in the total monomial `m`, then a nonzero left
factor from `copyConGadget M n j` cannot account for it, so that con-slot support survives in the
residual monomial `b`.
-/
theorem copyCon_insert_con_witness_survives_in_residual
    (M : DTM) (n : ℕ)
    {i j : Fin (latentBaseVars M n)}
    (hij : i ≠ j)
    {a b m : (Fin (latentNumVars M n)) →₀ ℕ}
    (ha_supp : a ∈ (copyConGadget M n j).support)
    (hm_con : conSlot M n i ∈ m.support)
    (hb_add : a + b = m) :
    conSlot M n i ∈ b.support := by
  have hconA_not : conSlot M n i ∉ a.support :=
    copyConGadget_nonzero_mono_no_other_conSlot M n i j hij a ha_supp
  rw [Finsupp.mem_support_iff] at hm_con hconA_not ⊢
  have hsum := congrArg (fun f => f (conSlot M n i)) hb_add
  simp only [Finsupp.add_apply] at hsum
  have ha_zero : a (conSlot M n i) = 0 := by
    by_contra ha_ne
    exact hconA_not ha_ne
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

/-- If a coefficient in a product is nonzero, some antidiagonal summand is nonzero. -/
theorem copyCon_coeff_mul_nonzero_witness
    {m : (Fin (latentNumVars M n)) →₀ ℕ}
    {p q : MvPolynomial (Fin (latentNumVars M n)) ℚ}
    (h : MvPolynomial.coeff m (p * q) ≠ 0) :
    ∃ ab ∈ Finset.antidiagonal m,
      MvPolynomial.coeff ab.1 p * MvPolynomial.coeff ab.2 q ≠ 0 := by
  rw [MvPolynomial.coeff_mul] at h
  by_contra hall
  push_neg at hall
  exact h (Finset.sum_eq_zero hall)

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

So the true remaining blocker is now the direct nonzero-residual part of the exact-shape insert
branch. One route would still be to prove
`copyCon_insert_exact_shape_nonzero_residual_witness_candidate`, but a cleaner replacement may be
a stronger direct residual-vanishing theorem, recorded here as
`copyCon_exact_shape_nonzero_residual_direct_zero_candidate`.

A direct retry confirms again that the naive witness `i = j` is false here: evaluating
`a + b = m` at `copySlot j` only shows that `m(copySlot j)` can already be supplied by the left
exact-shape monomial, so it does not force `b(copySlot j) ≠ 0`.

The most plausible remaining bridge now looks like a product-level nonzero-monomial classification,
recorded as `copyCon_prod_nonzero_mono_classification_candidate`, which could then feed the direct
residual-zero route. -/

theorem copyCon_prod_nonzero_mono_classification_candidate
    (M : DTM) (n : ℕ)
    (S : Finset (Fin (latentBaseVars M n)))
    (m : (Fin (latentNumVars M n)) →₀ ℕ) :
  MvPolynomial.coeff m (∏ i ∈ S, copyConGadget M n i) ≠ 0 →
  ∃ U : Finset (Fin (latentBaseVars M n)),
    U ⊆ S ∧
    (∀ i ∈ U,
      copySlot M n i ∈ m.support ∧
      conSlot M n i ∈ m.support) := by
  intro hm_nonzero
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨∅, Finset.empty_subset _, fun i hi => absurd hi (by simp)⟩
  | @insert j S hjS ih =>
      have hw := copyCon_coeff_mul_nonzero_witness (M := M) (n := n)
        (m := m) (p := copyConGadget M n j) (q := ∏ i ∈ S, copyConGadget M n i)
        (by simpa [Finset.prod_insert hjS] using hm_nonzero)
      rcases hw with ⟨ab, hab, hmul_ne⟩
      rcases ab with ⟨a, b⟩
      have hab_add : a + b = m := by simpa [Finset.mem_antidiagonal] using hab
      have hcoeff_a : MvPolynomial.coeff a (copyConGadget M n j) ≠ 0 := by
        intro h0
        apply hmul_ne
        simp [h0]
      rcases copyConGadget_coeff_nonzero_classification M n j a hcoeff_a with ha0 | hshape
      · subst ha0
        have hbm : b = m := by simpa using hab_add
        have hcoeff_b : MvPolynomial.coeff b (∏ i ∈ S, copyConGadget M n i) ≠ 0 := by
          intro h0
          apply hmul_ne
          simp [h0]
        rw [hbm] at hcoeff_b
        rcases ih hcoeff_b with ⟨U, hUS, hUshape⟩
        refine ⟨U, Finset.Subset.trans hUS (Finset.subset_insert _ _), ?_⟩
        intro i hi
        exact hUshape i hi
      · refine ⟨insert j ∅, ?_, ?_⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact Finset.mem_insert_self _ _
          · simp at hi
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · have hab_eq := hab_add
            rw [hshape] at hab_eq
            -- hab_eq : Finsupp.single (copySlot M n i) 1 + Finsupp.single (conSlot M n i) 1 + b = m
            -- For the copy-slot value:
            have hab_copy : Finsupp.single (copySlot M n i) 1 (copySlot M n i) +
                Finsupp.single (conSlot M n i) 1 (copySlot M n i) +
                b (copySlot M n i) = m (copySlot M n i) := by
              have := congr_arg (· (copySlot M n i)) hab_eq
              simp only [Finsupp.add_apply] at this
              exact this
            rw [Finsupp.single_apply, Finsupp.single_apply] at hab_copy
            simp [copySlot_ne_conSlot M n i i] at hab_copy
            -- For the con-slot value:
            have hab_con : Finsupp.single (copySlot M n i) 1 (conSlot M n i) +
                Finsupp.single (conSlot M n i) 1 (conSlot M n i) +
                b (conSlot M n i) = m (conSlot M n i) := by
              have := congr_arg (· (conSlot M n i)) hab_eq
              simp only [Finsupp.add_apply] at this
              exact this
            rw [Finsupp.single_apply, Finsupp.single_apply] at hab_con
            have hne : conSlot M n i ≠ copySlot M n i := by
              intro hEq
              exact (copySlot_ne_conSlot M n i i) hEq.symm
            simp [hne] at hab_con
            constructor
            · rw [Finsupp.mem_support_iff]
              omega
            · rw [Finsupp.mem_support_iff]
              omega
          · simp at hi

-- Sharpened pointwise support classification for nonzero copyCon product coefficients.
--
-- The previous classification only recovered some contributing subset `U ⊆ S`. For the residual-kill
-- step, what is really needed is a per-index statement: every copy-slot or con-slot seen in
-- `m.support` must come from an actual gadget index in `S`, and any such supporting index is forced to
-- contribute both local atoms. This is the bookkeeping shape needed to turn the residual step into a
-- support contradiction rather than a subset-existence argument.

/-- Recorded frontier alias for the pointwise-support theorem shape. -/
def copyCon_prod_nonzero_mono_pointwise_support_candidate
    (M : DTM) (n : ℕ)
    (S : Finset (Fin (latentBaseVars M n)))
    (m : (Fin (latentNumVars M n)) →₀ ℕ) : Prop :=
  MvPolynomial.coeff m (∏ i ∈ S, copyConGadget M n i) ≠ 0 →
    (∀ i : Fin (latentBaseVars M n),
      copySlot M n i ∈ m.support →
        i ∈ S ∧ conSlot M n i ∈ m.support) ∧
    (∀ i : Fin (latentBaseVars M n),
      conSlot M n i ∈ m.support →
        i ∈ S ∧ copySlot M n i ∈ m.support)
-- Copy-slot support control for nonzero monomials of a copyCon product.
--
-- This is the positive form of the factor-support exclusion theorem: if a monomial has nonzero
-- coefficient in `∏ i ∈ S, copyConGadget M n i`, then every copy-slot in its support comes from an
-- index already in `S`.
--
-- Deferred to after both exclusion theorems are proved. See below.

-- Structural frontier: direct factor-level support exclusion for the copyCon product.
--
-- This is the antidiagonal/product analogue of the single-gadget exact-shape classification. Rather
-- than packaging contradictions through `coeff_copyConProd_eq_zero_of_no_copy`, it states directly
-- that indices outside `S` cannot contribute copy-slot support to a nonzero monomial of the product.
--
-- This is essentially the negated form of copy-slot support control, and may be the cleaner induction
-- target: prove exclusion for `i ∉ S` first, then recover support control by contraposition.

/-- Micro-lemma: a nonzero product summand over `ℚ` forces the right factor coefficient to be
nonzero.

This is the scalar part of the insert-step exclusion seam. Once the antidiagonal witness provides a
nonzero product
`coeff a (copyConGadget j) * coeff b (∏ k ∈ S, copyConGadget k) ≠ 0`, the only remaining issue is to
separate that into nonvanishing of the right residual coefficient.
-/
theorem copyCon_nonzero_mul_right_of_mul_ne_zero
    {x y : ℚ}
    (hxy : x * y ≠ 0) :
    y ≠ 0 := by
  intro hy
  apply hxy
  simp [hy]

/-- A nonzero coefficient on the left factor of a product witness puts the left monomial in the
support of that factor. This is the tiny support-extraction bridge needed when unpacking a nonzero
antidiagonal summand in the insert step. -/
theorem copyCon_left_factor_support_of_nonzero_coeff
    (M : DTM) (n : ℕ)
    (j : Fin (latentBaseVars M n))
    (a : (Fin (latentNumVars M n)) →₀ ℕ)
    (ha_coeff : MvPolynomial.coeff a (copyConGadget M n j) ≠ 0) :
    a ∈ (copyConGadget M n j).support := by
  exact Finsupp.mem_support_iff.mpr ha_coeff

/-- If a monomial has nonzero coefficient in a polynomial, every atom in that monomial support lies
in the polynomial's variable set. -/
theorem copyCon_support_atom_mem_vars_of_nonzero_coeff_candidate
    (p : MvPolynomial (Fin (latentNumVars M n)) ℚ)
    (m : (Fin (latentNumVars M n)) →₀ ℕ) :
  MvPolynomial.coeff m p ≠ 0 →
    ∀ v ∈ m.support,
      v ∈ p.vars := by
  intro hm_nonzero v hv
  have hm_supp : m ∈ p.support := Finsupp.mem_support_iff.mpr hm_nonzero
  by_contra hv_not
  have hz : m v = 0 := MvPolynomial.mem_support_notMem_vars_zero hm_supp hv_not
  have hv_ne : m v ≠ 0 := Finsupp.mem_support_iff.mp hv
  exact hv_ne hz

/-- Insert-step reduction surface for the factor-support exclusion induction.

A direct first proof attempt of `copyCon_prod_nonzero_mono_factor_support_exclusion_candidate`
exposed the real live seam: after extracting a nonzero antidiagonal witness `(a,b)` for the insert
step, outside-index copy-slot support does transport from `m` to the residual `b` via
`copyCon_insert_witness_survives_in_residual`, and the scalar nonvanishing of the residual
coefficient should follow from `copyCon_nonzero_mul_right_of_mul_ne_zero`.

So this insert-step reduction is now the honest next theorem surface for the exclusion route.
-/
theorem copyCon_prod_nonzero_mono_factor_support_exclusion_insert_reduce
    (M : DTM) (n : ℕ)
    (j : Fin (latentBaseVars M n))
    (S : Finset (Fin (latentBaseVars M n)))
    (m a b : (Fin (latentNumVars M n)) →₀ ℕ) :
  a + b = m →
  a ∈ (copyConGadget M n j).support →
  MvPolynomial.coeff a (copyConGadget M n j) *
      MvPolynomial.coeff b (∏ k ∈ S, copyConGadget M n k) ≠ 0 →
  ∀ i : Fin (latentBaseVars M n),
    i ∉ insert j S →
    copySlot M n i ∈ m.support →
    MvPolynomial.coeff b (∏ k ∈ S, copyConGadget M n k) ≠ 0 ∧
      copySlot M n i ∈ b.support := by
  intro hab_add ha_supp hab_coeff i hi_notin hcopy_m
  have hij : i ≠ j := by
    intro hEq
    exact hi_notin (hEq ▸ Finset.mem_insert_self _ _)
  have hiS : i ∉ S := by
    intro hiS
    exact hi_notin (Finset.mem_insert_of_mem hiS)
  have hcopy_b : copySlot M n i ∈ b.support :=
    copyCon_insert_witness_survives_in_residual M n
      (i := i) (j := j) (a := a) (b := b) (m := m)
      hij ha_supp hcopy_m hab_add
  have hcoeff_b_ne : MvPolynomial.coeff b (∏ k ∈ S, copyConGadget M n k) ≠ 0 := by
    exact copyCon_nonzero_mul_right_of_mul_ne_zero hab_coeff
  exact ⟨hcoeff_b_ne, hcopy_b⟩

/-- Structural exclusion theorem for copy-slot support in nonzero copyCon product monomials.

This is the antidiagonal/product analogue of the single-gadget exact-shape classification. If a
monomial has nonzero coefficient in `∏ i ∈ S, copyConGadget M n i`, then no copy-slot indexed
outside `S` can occur in its support.
-/
theorem copyCon_prod_nonzero_mono_factor_support_exclusion_candidate
    (M : DTM) (n : ℕ)
    (S : Finset (Fin (latentBaseVars M n)))
    (m : (Fin (latentNumVars M n)) →₀ ℕ) :
  MvPolynomial.coeff m (∏ i ∈ S, copyConGadget M n i) ≠ 0 →
    ∀ i : Fin (latentBaseVars M n),
      i ∉ S →
      copySlot M n i ∉ m.support := by
  revert m
  induction S using Finset.induction_on with
  | empty =>
      intro m hm_nonzero i hi_empty hcopy
      have hm0 : m ≠ 0 := by
        intro hmz
        rw [hmz] at hcopy
        simp at hcopy
      have hcoeff0 : MvPolynomial.coeff m (1 : MvPolynomial (Fin (latentNumVars M n)) ℚ) = 0 :=
        coeff_one_eq_zero_of_ne_zero _ hm0
      exact hm_nonzero hcoeff0
  | @insert j S hjS ih =>
      intro m hm_nonzero i hi_notin hcopy
      have hw := copyCon_coeff_mul_nonzero_witness (M := M) (n := n)
        (m := m) (p := copyConGadget M n j) (q := ∏ k ∈ S, copyConGadget M n k)
        (by simpa [Finset.prod_insert hjS] using hm_nonzero)
      rcases hw with ⟨ab, hab, hab_coeff⟩
      rcases ab with ⟨a, b⟩
      have hab_add : a + b = m := by
        simpa [Finset.mem_antidiagonal] using hab
      have hcoeff_a : MvPolynomial.coeff a (copyConGadget M n j) ≠ 0 := by
        intro h0
        apply hab_coeff
        simp [h0]
      have ha_supp : a ∈ (copyConGadget M n j).support :=
        copyCon_left_factor_support_of_nonzero_coeff M n j a hcoeff_a
      have hred := copyCon_prod_nonzero_mono_factor_support_exclusion_insert_reduce
        M n j S m a b hab_add ha_supp hab_coeff i hi_notin hcopy
      exact ih b hred.1 i (by
        intro hiS
        exact hi_notin (Finset.mem_insert_of_mem hiS)) hred.2

/-- Structural exclusion theorem for con-slot support in nonzero copyCon product monomials.

This is the exact con-slot analogue of
`copyCon_prod_nonzero_mono_factor_support_exclusion_candidate`. If a monomial has nonzero
coefficient in `∏ i ∈ S, copyConGadget M n i`, then no con-slot indexed outside `S` can occur in its
support.
-/
theorem copyCon_prod_nonzero_mono_con_factor_support_exclusion_candidate
    (M : DTM) (n : ℕ)
    (S : Finset (Fin (latentBaseVars M n)))
    (m : (Fin (latentNumVars M n)) →₀ ℕ) :
  MvPolynomial.coeff m (∏ i ∈ S, copyConGadget M n i) ≠ 0 →
    ∀ i : Fin (latentBaseVars M n),
      i ∉ S →
      conSlot M n i ∉ m.support := by
  revert m
  induction S using Finset.induction_on with
  | empty =>
      intro m hm_nonzero i hi_empty hcon
      have hm0 : m ≠ 0 := by
        intro hmz
        rw [hmz] at hcon
        simp at hcon
      have hcoeff0 : MvPolynomial.coeff m (1 : MvPolynomial (Fin (latentNumVars M n)) ℚ) = 0 :=
        coeff_one_eq_zero_of_ne_zero _ hm0
      exact hm_nonzero hcoeff0
  | @insert j S hjS ih =>
      intro m hm_nonzero i hi_notin hcon
      have hw := copyCon_coeff_mul_nonzero_witness (M := M) (n := n)
        (m := m) (p := copyConGadget M n j) (q := ∏ k ∈ S, copyConGadget M n k)
        (by simpa [Finset.prod_insert hjS] using hm_nonzero)
      rcases hw with ⟨ab, hab, hab_coeff⟩
      rcases ab with ⟨a, b⟩
      have hab_add : a + b = m := by
        simpa [Finset.mem_antidiagonal] using hab
      have hcoeff_a : MvPolynomial.coeff a (copyConGadget M n j) ≠ 0 := by
        intro h0
        apply hab_coeff
        simp [h0]
      have ha_supp : a ∈ (copyConGadget M n j).support :=
        copyCon_left_factor_support_of_nonzero_coeff M n j a hcoeff_a
      have hij : i ≠ j := by
        intro hEq
        exact hi_notin (hEq ▸ Finset.mem_insert_self _ _)
      have hcon_b : conSlot M n i ∈ b.support :=
        copyCon_insert_con_witness_survives_in_residual M n
          (i := i) (j := j) (a := a) (b := b) (m := m)
          hij ha_supp hcon hab_add
      have hcoeff_b : MvPolynomial.coeff b (∏ k ∈ S, copyConGadget M n k) ≠ 0 :=
        copyCon_nonzero_mul_right_of_mul_ne_zero hab_coeff
      exact ih b hcoeff_b i (by
        intro hiS
        exact hi_notin (Finset.mem_insert_of_mem hiS)) hcon_b

/-- Copy-slot support control for nonzero monomials of a copyCon product.

This is the positive form of the factor-support exclusion theorem: if a monomial has nonzero
coefficient in `∏ i ∈ S, copyConGadget M n i`, then every copy-slot in its support comes from an
index already in `S`, and the paired con-slot is also in support.
-/
theorem copyCon_prod_nonzero_mono_copy_support_control_candidate
    (M : DTM) (n : ℕ)
    (S : Finset (Fin (latentBaseVars M n)))
    (m : (Fin (latentNumVars M n)) →₀ ℕ) :
  MvPolynomial.coeff m (∏ i ∈ S, copyConGadget M n i) ≠ 0 →
    ∀ i : Fin (latentBaseVars M n),
      copySlot M n i ∈ m.support →
      i ∈ S ∧ conSlot M n i ∈ m.support := by
  intro hm_nonzero i hcopy
  have hiS : i ∈ S := by
    by_contra hi_notin
    exact copyCon_prod_nonzero_mono_factor_support_exclusion_candidate M n S m hm_nonzero i hi_notin hcopy
  refine ⟨hiS, ?_⟩
  by_contra hcon_not
  have hcon_notin : conSlot M n i ∉ m.support := hcon_not
  -- Since i ∈ S and coeff m ≠ 0, write S = insert i S' with i ∉ S'.
  -- Then ∏ k ∈ S, ... = copyConGadget M n i * ∏ k ∈ S', ...
  -- Antidiagonal decomposition of m gives (a, b) with a+b = m and
  -- coeff a (copyConGadget i) * coeff b (∏ k ∈ S', ...) ≠ 0.
  -- From copyConGadget_coeff_nonzero_classification: a = 0 or a = single(copySlot i) + single(conSlot i).
  -- If a = single(copySlot i) + single(conSlot i), then a(conSlot i) = 1, so m(conSlot i) ≥ 1,
  -- contradicting conSlot i ∉ m.support.
  -- If a = 0, then b = m, and coeff m (∏ k ∈ S', ...) ≠ 0.
  -- But copySlot M n i ∈ m.support and i ∉ S', so by copy_exclusion on S',
  -- copySlot M n i ∉ m.support, contradiction.
  have hiS' := hiS
  rw [show S = insert i (S.erase i) from (Finset.insert_erase hiS).symm] at hm_nonzero
  have hi_not_erase : i ∉ S.erase i := by simp [Finset.mem_erase]
  have hw := copyCon_coeff_mul_nonzero_witness (M := M) (n := n)
    (m := m) (p := copyConGadget M n i) (q := ∏ k ∈ S.erase i, copyConGadget M n k)
    (by simpa [Finset.prod_insert hi_not_erase] using hm_nonzero)
  rcases hw with ⟨ab, hab, hab_coeff⟩
  rcases ab with ⟨a, b⟩
  have hab_add : a + b = m := by simpa [Finset.mem_antidiagonal] using hab
  have hcoeff_a : MvPolynomial.coeff a (copyConGadget M n i) ≠ 0 := by
    intro h0
    apply hab_coeff
    simp [h0]
  rcases copyConGadget_coeff_nonzero_classification M n i a hcoeff_a with ha0 | hshape
  · subst ha0
    have hbm : b = m := by simpa using hab_add
    have hcoeff_b : MvPolynomial.coeff b (∏ k ∈ S.erase i, copyConGadget M n k) ≠ 0 :=
      copyCon_nonzero_mul_right_of_mul_ne_zero hab_coeff
    have hcopy_b : copySlot M n i ∈ b.support := by rw [hbm]; exact hcopy
    exact copyCon_prod_nonzero_mono_factor_support_exclusion_candidate M n (S.erase i) b
      hcoeff_b i hi_not_erase hcopy_b
  · have hab_ext : ∀ v, (a + b) v = m v := Finsupp.ext_iff.mp hab_add
    have hcon_val := hab_ext (conSlot M n i)
    rw [Finsupp.add_apply, hshape] at hcon_val
    simp only [Finsupp.add_apply, Finsupp.single_apply] at hcon_val
    have hcon_ne : conSlot M n i ≠ copySlot M n i := by
      intro hEq
      exact (copySlot_ne_conSlot M n i i) hEq.symm
    simp [hcon_ne] at hcon_val
    have hm_con_ne : m (conSlot M n i) ≠ 0 := by omega
    exact hcon_notin (Finsupp.mem_support_iff.mpr hm_con_ne)

/-- Con-slot support control for nonzero monomials of a copyCon product.

This is the positive form of the con-slot exclusion theorem: if a monomial has nonzero coefficient
in `∏ i ∈ S, copyConGadget M n i`, then every con-slot in its support comes from an index already in
`S`, and the paired copy-slot is also in support.
-/
theorem copyCon_prod_nonzero_mono_con_support_control_candidate
    (M : DTM) (n : ℕ)
    (S : Finset (Fin (latentBaseVars M n)))
    (m : (Fin (latentNumVars M n)) →₀ ℕ) :
  MvPolynomial.coeff m (∏ i ∈ S, copyConGadget M n i) ≠ 0 →
    ∀ i : Fin (latentBaseVars M n),
      conSlot M n i ∈ m.support →
      i ∈ S ∧ copySlot M n i ∈ m.support := by
  intro hm_nonzero i hcon
  have hiS : i ∈ S := by
    by_contra hi_notin
    exact copyCon_prod_nonzero_mono_con_factor_support_exclusion_candidate M n S m hm_nonzero i hi_notin hcon
  refine ⟨hiS, ?_⟩
  by_contra hcopy_not
  have hcopy_notin : copySlot M n i ∉ m.support := hcopy_not
  have hiS' := hiS
  rw [show S = insert i (S.erase i) from (Finset.insert_erase hiS).symm] at hm_nonzero
  have hi_not_erase : i ∉ S.erase i := by simp [Finset.mem_erase]
  have hw := copyCon_coeff_mul_nonzero_witness (M := M) (n := n)
    (m := m) (p := copyConGadget M n i) (q := ∏ k ∈ S.erase i, copyConGadget M n k)
    (by simpa [Finset.prod_insert hi_not_erase] using hm_nonzero)
  rcases hw with ⟨ab, hab, hab_coeff⟩
  rcases ab with ⟨a, b⟩
  have hab_add : a + b = m := by simpa [Finset.mem_antidiagonal] using hab
  have hcoeff_a : MvPolynomial.coeff a (copyConGadget M n i) ≠ 0 := by
    intro h0
    apply hab_coeff
    simp [h0]
  rcases copyConGadget_coeff_nonzero_classification M n i a hcoeff_a with ha0 | hshape
  · subst ha0
    have hbm : b = m := by simpa using hab_add
    have hcoeff_b : MvPolynomial.coeff b (∏ k ∈ S.erase i, copyConGadget M n k) ≠ 0 :=
      copyCon_nonzero_mul_right_of_mul_ne_zero hab_coeff
    have hcon_b : conSlot M n i ∈ b.support := by rw [hbm]; exact hcon
    exact copyCon_prod_nonzero_mono_con_factor_support_exclusion_candidate M n (S.erase i) b
      hcoeff_b i hi_not_erase hcon_b
  · have hab_ext : ∀ v, (a + b) v = m v := Finsupp.ext_iff.mp hab_add
    have hcopy_val := hab_ext (copySlot M n i)
    rw [Finsupp.add_apply, hshape] at hcopy_val
    simp only [Finsupp.add_apply, Finsupp.single_apply] at hcopy_val
    have hcopy_ne : copySlot M n i ≠ conSlot M n i := copySlot_ne_conSlot M n i i
    simp [hcopy_ne] at hcopy_val
    have hm_copy_ne : m (copySlot M n i) ≠ 0 := by omega
    exact hcopy_notin (Finsupp.mem_support_iff.mpr hm_copy_ne)

/-- Product-level variable-support frontier for copyCon gadget products.

This is the cleanest route to the final atom-shape classification theorem. Rather than reason first
about coefficients of individual monomials, prove directly that the product
`∏ i ∈ S, copyConGadget M n i` contains no variables except copy-slot and con-slot variables. Then
any monomial with nonzero coefficient in that product automatically has support atoms of one of those
two forms.
-/
theorem copyCon_prod_vars_subset_copy_or_con_candidate
    (M : DTM) (n : ℕ)
    (S : Finset (Fin (latentBaseVars M n))) :
  (∏ i ∈ S, copyConGadget M n i).vars ⊆
    (Finset.univ.image (copySlot M n) ∪ Finset.univ.image (conSlot M n)) := by
  intro v hv
  induction S using Finset.induction_on generalizing v with
  | empty =>
      simp at hv
  | @insert j S hjS ih =>
      rw [Finset.prod_insert hjS] at hv
      have hvmul := Finset.mem_of_subset (MvPolynomial.vars_mul (φ := copyConGadget M n j) (ψ := ∏ k ∈ S, copyConGadget M n k)) hv
      rw [Finset.mem_union] at hvmul
      rcases hvmul with hv' | hv'
      · exact copyConGadget_vars_subset_copy_or_con M n j hv'
      · exact ih hv'

/-- Final atom-shape classification for nonzero copyCon product monomials. -/
theorem copyCon_prod_nonzero_mono_support_atoms_are_copy_or_con_candidate
    (M : DTM) (n : ℕ)
    (S : Finset (Fin (latentBaseVars M n)))
    (m : (Fin (latentNumVars M n)) →₀ ℕ) :
  MvPolynomial.coeff m (∏ i ∈ S, copyConGadget M n i) ≠ 0 →
    ∀ v ∈ m.support,
      (∃ i : Fin (latentBaseVars M n), v = copySlot M n i) ∨
      (∃ i : Fin (latentBaseVars M n), v = conSlot M n i) := by
  intro hm_nonzero v hv
  have hvars : v ∈ (∏ i ∈ S, copyConGadget M n i).vars :=
    copyCon_support_atom_mem_vars_of_nonzero_coeff_candidate
      (p := ∏ i ∈ S, copyConGadget M n i) (m := m) hm_nonzero v hv
  have hsubset := copyCon_prod_vars_subset_copy_or_con_candidate M n S hvars
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hsubset
  rcases hsubset with hcopy | hcon
  · rcases hcopy with ⟨i, _, rfl⟩
    exact Or.inl ⟨i, rfl⟩
  · rcases hcon with ⟨i, _, rfl⟩
    exact Or.inr ⟨i, rfl⟩

/-- Fully generic pointwise factor extraction for nonzero copyCon product monomials. -/
theorem copyCon_prod_nonzero_mono_pointwise_factor_extraction_candidate
    (M : DTM) (n : ℕ)
    (S : Finset (Fin (latentBaseVars M n)))
    (m : (Fin (latentNumVars M n)) →₀ ℕ) :
  MvPolynomial.coeff m (∏ i ∈ S, copyConGadget M n i) ≠ 0 →
    (∀ v ∈ m.support,
      (∃ i ∈ S,
        v = copySlot M n i ∧ conSlot M n i ∈ m.support) ∨
      (∃ i ∈ S,
        v = conSlot M n i ∧ copySlot M n i ∈ m.support)) := by
  intro hm_nonzero v hv
  rcases copyCon_prod_nonzero_mono_support_atoms_are_copy_or_con_candidate M n S m hm_nonzero v hv with
    ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rcases copyCon_prod_nonzero_mono_copy_support_control_candidate M n S m hm_nonzero i hv with
      ⟨hiS, hcon⟩
    exact Or.inl ⟨i, hiS, rfl, hcon⟩
  · rcases copyCon_prod_nonzero_mono_con_support_control_candidate M n S m hm_nonzero i hv with
      ⟨hiS, hcopy⟩
    exact Or.inr ⟨i, hiS, rfl, hcopy⟩

/-- Dependency note for the live residual-branch frontier.

The exact-shape nonzero-residual branch below should not be attacked first anymore. Its former
parent frontiers are now complete: we have copy-slot support control, con-slot support control, atom
shape classification, and the fully generic pointwise factor-extraction theorem for nonzero monomials
of `∏ i ∈ S, copyConGadget M n i`.

What this now buys downstream is a concrete way to attack the residual branch: given any support atom
of a nonzero residual monomial, extract the specific index `i ∈ S` witnessing the paired local
copy/con contribution, instead of reasoning via an undirected existential subset.
-/
def copyCon_prod_support_control_feeds_residual_branch_note : Prop :=
  True

def copyCon_exact_shape_nonzero_residual_direct_zero_candidate : Prop :=
  ∀ (M : DTM) (n : ℕ)
    (j : Fin (latentBaseVars M n))
    (S : Finset (Fin (latentBaseVars M n)))
    (b : (Fin (latentNumVars M n)) →₀ ℕ),
    MvPolynomial.coeff b (∏ i ∈ S, copyConGadget M n i) ≠ 0 →
    copySlot M n j ∉ b.support →
    j ∉ S

/-- Honest later-placement frontier for the stronger `any_copy` theorem. -/
def coeff_copyConProd_eq_zero_of_any_copy_later_candidate : Prop :=
  True

-- Honest off-diagonal frontier for the copyCon pure-con closed form. The combinatorial witness
-- and the local residual-support theorem are now both proved, and the local insert-step antidiagonal
-- packaging has been upgraded to theorem level in both branches under the strengthened induction
-- statement `coeff_copyConProd_eq_zero_of_any_copy`. So the remaining blocker is now exactly the
-- full induction assembly for that stronger gadget-product vanishing statement, followed by its use
-- with `copyCon_residual_support_from_offdiag_witness` to finish the off-diagonal coefficient
-- argument.

-- Honest remaining off-diagonal contradiction frontier for copyCon closed forms.
--
-- The infrastructure below is now substantially stronger than when this surface was first introduced:
-- - an off-diagonal set-difference witness is available,
-- - residual support transport is proved,
-- - and nonzero monomials of copyCon gadget products now admit full pointwise factor extraction.
--
-- So the live gap is no longer vague support bookkeeping. The remaining issue is the final coefficient
-- kill: from an alleged nonzero tagged coefficient on the off-diagonal closed form, extract a concrete
-- copy/con index witness in the residual gadget product and contradict the set-difference witness
-- coming from `ksi.toFinset ≠ ksj.toFinset`.

-- Final local witness-extraction frontier for the copyCon off-diagonal coefficient kill.
--
-- The previous first pass was too loose about which witness should be produced. The actual coefficient
-- shape is this: if the tagged coefficient of the residual gadget product is nonzero, then the
-- pointwise extraction theorem must produce an index from the residual factor set whose copy-slot (and
-- paired con-slot) occur in the tagged monomial `copyCon_tagMono M n ksi`. Since that tag monomial has
-- no con-slot support at all, this should force the contradiction.

/-- Empty-tag nuisance isolated for the copyCon off-diagonal kill.

The residual-pair extraction theorem wants an actual copy-slot witness in the tag monomial, so the
empty-tag case should be split off explicitly instead of being smuggled through a bogus proof by
cases on `ksi`.
-/
-- Note: the original statement without the `ksi.toFinset ⊆ ksj.toFinset → False` guard is false
-- because coeff 0 (∏ ...) = 1 ≠ 0 when ksi = []. We add the guard to make it provable.
theorem copyCon_tagMono_nonzero_coeff_forces_nonempty_candidate
    (M : DTM) (n : ℕ)
    (ksi : List (Fin (latentBaseVars M n)))
    (ksj : List (Fin (latentBaseVars M n)))
    (hnd : ksi.Nodup)
    (hsub : ∃ k ∈ ksi, k ∉ ksj) :
  MvPolynomial.coeff (copyCon_tagMono M n ksi)
      (∏ i ∈ (Finset.univ \ ksj.toFinset), copyConGadget M n i) ≠ 0 →
    ksi ≠ [] := by
  intro _hcoeff hnil
  subst hnil
  rcases hsub with ⟨k, hk, _⟩
  simp at hk

/-- Final local witness-extraction frontier for the copyCon off-diagonal coefficient kill,
with the empty-tag nuisance separated out. -/
theorem copyCon_offdiag_nonzero_coeff_forces_residual_pair_candidate
    (M : DTM) (n : ℕ)
    (ksi ksj : List (Fin (latentBaseVars M n)))
    (hnd : ksi.Nodup) :
  ksi ≠ [] →
  MvPolynomial.coeff (copyCon_tagMono M n ksi)
      (∏ i ∈ (Finset.univ \ ksj.toFinset), copyConGadget M n i) ≠ 0 →
    ∃ j_idx ∈ (Finset.univ \ ksj.toFinset),
      copySlot M n j_idx ∈ (copyCon_tagMono M n ksi).support ∧
      conSlot M n j_idx ∈ (copyCon_tagMono M n ksi).support := by
  intro hne hcoeff
  cases' ksi with i0 rest
  · exfalso
    exact hne rfl
  · have hpair := copyCon_prod_nonzero_mono_pointwise_factor_extraction_candidate
      M n (Finset.univ \ ksj.toFinset) (copyCon_tagMono M n (i0 :: rest)) hcoeff
    have hcopy0 : copySlot M n i0 ∈ (copyCon_tagMono M n (i0 :: rest)).support := by
      rw [copyCon_tagMono_support_eq M n (i0 :: rest) hnd]
      exact Finset.mem_image.mpr ⟨i0, by simp, rfl⟩
    have hex := hpair (copySlot M n i0) hcopy0
    rcases hex with (⟨j_idx, hj_idx, hEq, hcon⟩ | ⟨j_idx, hj_idx, hEq, _hcopyj_idx⟩)
    · have hij : i0 = j_idx := by exact copySlot_injective M n hEq
      subst hij
      exact ⟨i0, hj_idx, hcopy0, hcon⟩
    · exfalso
      exact (copySlot_ne_conSlot M n i0 j_idx) hEq

-- Honest remaining off-diagonal contradiction frontier for copyCon closed forms.
--
-- The infrastructure below is now substantially stronger than when this surface was first introduced:
-- - an off-diagonal set-difference witness is available,
-- - residual support transport is proved,
-- - and nonzero monomials of copyCon gadget products now admit full pointwise factor extraction.
--
-- So the live gap is no longer vague support bookkeeping. The remaining issue is the final coefficient
-- kill: from an alleged nonzero tagged coefficient on the off-diagonal closed form, extract a concrete
-- copy/con index witness in the residual gadget product and contradict the set-difference witness
-- coming from `ksi.toFinset ≠ ksj.toFinset`.

/-- Honest remaining check on the off-diagonal contradiction proof.

The contradiction core is now explicit and concentrated: set-difference witness, nonempty-tag
reduction, residual pair extraction, and `copyCon_tagMono_no_conSlot` close the logic. The only
remaining uncertainty is the coefficient normalization on `copyCon_con_closedForm`, namely the exact
Lean-compatible route from a nonzero tagged coefficient on the closed form to a nonzero tagged
coefficient on the residual gadget product.

Concretely, the proof now depends only on verifying the expected coefficient identities for:
- scalar extraction through `MvPolynomial.coeff_C_mul`, and
- the `Xcopy`-product/monomial rewrite in the tagged coefficient.
-/
theorem copyCon_offdiag_complement_support
    (M : DTM) (n : ℕ)
    (ksi ksj : List (Fin (latentBaseVars M n)))
    (hndi : ksi.Nodup) (hndj : ksj.Nodup)
    (hlen : ksi.length = ksj.length) :
  ksi.toFinset ≠ ksj.toFinset →
    MvPolynomial.coeff (copyCon_tagMono M n ksi)
      (copyCon_con_closedForm M n ksj) = 0 := by
  intro hne
  by_contra hcoeff
  rcases exists_mem_toFinset_not_mem_toFinset_of_ne_of_length_eq
    (n := n) ksi ksj hndi hndj hlen hne with ⟨i0, hi0_ksi, hi0_not_ksj⟩
  have hsub : ∃ k ∈ ksi, k ∉ ksj := by
    refine ⟨i0, ?_, ?_⟩
    · simpa [List.mem_toFinset] using hi0_ksi
    · simpa [List.mem_toFinset] using hi0_not_ksj
  unfold copyCon_con_closedForm at hcoeff
  have hscalar_ne : ((-1 : ℚ) ^ ksj.length) ≠ 0 := by
    exact pow_ne_zero _ (by norm_num)
  have hcoeff' : MvPolynomial.coeff (copyCon_tagMono M n ksi)
      (C ((-1 : ℚ) ^ ksj.length) *
        ((ksj.map (Xcopy M n)).prod * ∏ i ∈ (Finset.univ \ ksj.toFinset), copyConGadget M n i)) ≠ 0 := by
    simpa [mul_assoc] using hcoeff
  rw [MvPolynomial.coeff_C_mul] at hcoeff'
  have hresid_copy : MvPolynomial.coeff (copyCon_tagMono M n ksi)
      ((ksj.map (Xcopy M n)).prod * ∏ i ∈ (Finset.univ \ ksj.toFinset), copyConGadget M n i) ≠ 0 := by
    intro hzero
    apply hcoeff'
    simp [hzero, hscalar_ne]
  rw [Xcopy_prod_eq_monomial M n ksj hndj] at hresid_copy
  have htag_diff : copyCon_tagMono M n ksi ≠ copyCon_tagMono M n ksj :=
    copyCon_tagMono_ne_of_toFinset_ne M n ksi ksj hndi hndj hne
  rw [MvPolynomial.coeff_mul] at hresid_copy
  have hsum_nonzero :
      ∃ ab ∈ (Finset.antidiagonal (copyCon_tagMono M n ksi)),
        MvPolynomial.coeff ab.1 (MvPolynomial.monomial (copyCon_tagMono M n ksj) 1) *
          MvPolynomial.coeff ab.2 (∏ i ∈ (Finset.univ \ ksj.toFinset), copyConGadget M n i) ≠ 0 := by
    by_contra hnone
    apply hresid_copy
    rw [Finset.sum_eq_zero]
    intro ab hab
    have hmem : ab ∈ Finset.antidiagonal (copyCon_tagMono M n ksi) := hab
    have := hnone ab hmem
    simpa [Finset.mem_antidiagonal] using this
  rcases hsum_nonzero with ⟨⟨a, b⟩, hab, habnz⟩
  have hab_add : a + b = copyCon_tagMono M n ksi := by
    simpa [Finset.mem_antidiagonal] using hab
  have ha_coeff_ne : MvPolynomial.coeff a (MvPolynomial.monomial (copyCon_tagMono M n ksj) 1) ≠ 0 := by
    intro hzero
    apply habnz
    simp [hzero]
  have ha_eq : a = copyCon_tagMono M n ksj := by
    by_cases hEq : a = copyCon_tagMono M n ksj
    · exact hEq
    · have hEq' : copyCon_tagMono M n ksj ≠ a := by simpa [eq_comm] using hEq
      have : MvPolynomial.coeff a (MvPolynomial.monomial (copyCon_tagMono M n ksj) 1) = 0 := by
        rw [MvPolynomial.coeff_monomial]
        simp [hEq']
      exact (ha_coeff_ne this).elim
  subst ha_eq
  have hb_ne_zero : b ≠ 0 := by
    intro hb0
    subst hb0
    have : copyCon_tagMono M n ksi = copyCon_tagMono M n ksj := by
      simpa [zero_add] using hab_add.symm
    exact htag_diff this
  have hb_coeff_ne :
      MvPolynomial.coeff b (∏ i ∈ (Finset.univ \ ksj.toFinset), copyConGadget M n i) ≠ 0 := by
    intro hzero
    apply habnz
    simp [hzero]
  have hcopy_missing : copySlot M n i0 ∈ b.support := by
    have hsum := congrArg (fun f => f (copySlot M n i0)) hab_add
    have hksi_one : (copyCon_tagMono M n ksi) (copySlot M n i0) ≠ 0 :=
      copyCon_tagMono_apply_copySlot_ne_zero_of_mem M n ksi hndi i0 hi0_ksi
    have hksj_zero : (copyCon_tagMono M n ksj) (copySlot M n i0) = 0 :=
      copyCon_tagMono_apply_copySlot_eq_zero_of_not_mem M n ksj hndj i0 hi0_not_ksj
    simp [Finsupp.add_apply, hksj_zero] at hsum
    exact Finsupp.mem_support_iff.mpr (by exact hsum.trans_ne hksi_one)
  have hpair := copyCon_prod_nonzero_mono_copy_support_control_candidate M n
    (Finset.univ \ ksj.toFinset) b hb_coeff_ne i0 hcopy_missing
  rcases hpair with ⟨hi0_resid, hcon_resid⟩
  exact hi0_not_ksj hi0_resid

end CopyConClosedCoeffDecomp
