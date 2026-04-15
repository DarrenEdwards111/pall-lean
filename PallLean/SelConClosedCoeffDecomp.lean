import PallLean.SelConCoeffReduction
import Mathlib.Tactic

/-!
# SelConClosedCoeffDecomp

Further decomposition of the remaining NP coefficient core.

After `SelConCoeffReduction`, the remaining frontier is to prove diagonal and
off-diagonal coefficients for one explicit closed form. This file splits that
again into two concrete sub-obligations:

1. `mlProj` does not disturb the target coefficient for the tagged monomial;
2. the complementary product of `selConGadget`s contributes no extra copies of the tag.

That leaves only bare monomial-support bookkeeping on the closed form.
-/

namespace SelConClosedCoeffDecomp

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open LatentCompiler
open LatentWitnessMinorDecomp
open SelConCoeffReduction

/-- The bare closed form before `mlProj` is applied. -/
noncomputable def selCon_closedForm (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n))) :
    MvPolynomial (Fin (latentNumVars M n)) ℚ :=
  C ((-1 : ℚ)^ks.length) *
    (ks.map (Xcon M n)).prod *
    (∏ i ∈ (Finset.univ \ ks.toFinset), selConGadget M n i)

/-- Helper: if a ∉ l, foldr of singles at position a is 0. -/
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
    simp [hba]; exact ih hna'

/-- Helper: foldr of distinct singles produces multilinear result. -/
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
    · simp [hia]; exact ih hnd_rest

/-- selCon_tagMono produces a multilinear monomial when the input list has nodup conSlot images. -/
theorem selCon_tagMono_isMultilinear (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n)))
    (hnd : ks.Nodup) :
    Finsupp.IsMultilinear (selCon_tagMono M n ks) := by
  intro i
  unfold selCon_tagMono
  exact foldr_singles_le_one (ks.map (conSlot M n)) (List.Nodup.map (by
    intro a b hab; simp [conSlot, slot, Fin.ext_iff] at hab; omega) hnd) i

/-- mlProj preserves coefficients at selCon_tagMono monomials (which are multilinear). -/
theorem selCon_mlProj_preserves_coeff (M : DTM) (n : ℕ)
    (ks_tag : List (Fin (latentBaseVars M n)))
    (hnd_tag : ks_tag.Nodup)
    (p : MvPolynomial (Fin (latentNumVars M n)) ℚ) :
    MvPolynomial.coeff (selCon_tagMono M n ks_tag) (mlProj p) =
    MvPolynomial.coeff (selCon_tagMono M n ks_tag) p :=
  coeff_mlProj_of_isMultilinear_mono p (selCon_tagMono M n ks_tag)
    (selCon_tagMono_isMultilinear M n ks_tag hnd_tag)

/-- Reduction of the diagonal coefficient statement to the raw closed form (proved). -/
theorem selCon_diag_mlProj_preserves_coeff (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n)))
    (hnd : ks.Nodup) :
    MvPolynomial.coeff (selCon_tagMono M n ks)
      (mlProj (selCon_closedForm M n ks)) =
    MvPolynomial.coeff (selCon_tagMono M n ks)
      (selCon_closedForm M n ks) :=
  selCon_mlProj_preserves_coeff M n ks hnd (selCon_closedForm M n ks)

/-- Reduction of the off-diagonal coefficient statement to the raw closed form (proved). -/
theorem selCon_offdiag_mlProj_preserves_coeff (M : DTM) (n : ℕ)
    (ksi ksj : List (Fin (latentBaseVars M n)))
    (hndi : ksi.Nodup) :
    MvPolynomial.coeff (selCon_tagMono M n ksi)
      (mlProj (selCon_closedForm M n ksj)) =
    MvPolynomial.coeff (selCon_tagMono M n ksi)
      (selCon_closedForm M n ksj) :=
  selCon_mlProj_preserves_coeff M n ksi hndi (selCon_closedForm M n ksj)

/-- The Xcon product for ks is the monomial at tagMono ks. -/
theorem Xcon_prod_eq_monomial (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n))) (hnd : ks.Nodup) :
    (ks.map (Xcon M n)).prod = MvPolynomial.monomial (selCon_tagMono M n ks) 1 := by
  unfold Xcon selCon_tagMono
  induction ks with
  | nil => simp [MvPolynomial.monomial_zero']
  | cons a rest ih =>
    have hnd_rest := (List.nodup_cons.mp hnd).2
    simp only [List.map, List.prod_cons, List.foldr]
    rw [ih hnd_rest]
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, add_comm]

/-- Each selConGadget uses only selSlot and conSlot variables. -/
theorem selConGadget_constant_term (M : DTM) (n : ℕ)
    (i : Fin (latentBaseVars M n)) :
    MvPolynomial.coeff 0 (selConGadget M n i) = 1 := by
  unfold selConGadget Xsel Xcon
  simp [MvPolynomial.coeff_sub, MvPolynomial.coeff_one,
    MvPolynomial.coeff_mul, MvPolynomial.coeff_X]

/-- The complement product of selConGadgets has constant term 1. -/
theorem complement_prod_constant_term (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n))) :
    MvPolynomial.coeff 0
      (∏ i ∈ (Finset.univ \ ks.toFinset), selConGadget M n i) = 1 := by
  -- coeff 0 = constantCoeff (definitional), which is a ring hom
  show MvPolynomial.constantCoeff (∏ i ∈ (Finset.univ \ ks.toFinset), selConGadget M n i) = 1
  rw [map_prod]
  apply Finset.prod_eq_one
  intro i _
  show MvPolynomial.constantCoeff (selConGadget M n i) = 1
  change MvPolynomial.coeff 0 (selConGadget M n i) = 1
  exact selConGadget_constant_term M n i

/-- The selCon tag monomial at a member is nonzero. -/
theorem tagMono_mem_eq_one (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n))) (hnd : ks.Nodup)
    (k : Fin (latentBaseVars M n)) (hk : k ∈ ks) :
    (selCon_tagMono M n ks) (conSlot M n k) = 1 := by
  unfold selCon_tagMono
  induction ks with
  | nil => simp at hk
  | cons a rest ih =>
    have hnd_rest := (List.nodup_cons.mp hnd).2
    have hna := (List.nodup_cons.mp hnd).1
    simp only [List.map, List.foldr, Finsupp.add_apply, Finsupp.single_apply]
    by_cases hka : k = a
    · subst hka
      simp only [ite_true]
      have := foldr_singles_zero_of_not_mem (rest.map (conSlot M n)) (conSlot M n k) (by
        intro hmem
        obtain ⟨j, hj, hjk⟩ := List.mem_map.mp hmem
        have : k = j := by simp [conSlot, slot, Fin.ext_iff] at hjk; omega
        exact hna (this ▸ hj))
      omega
    · simp [show conSlot M n a ≠ conSlot M n k from by
        intro h; simp [conSlot, slot, Fin.ext_iff] at h; omega]
      rcases List.mem_cons.mp hk with h | h
      · exact absurd h hka
      · exact ih hnd_rest h

/-- The tag monomial's support is exactly {conSlot k | k ∈ ks}. -/
theorem tagMono_support_eq (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n)))
    (hnd : ks.Nodup) :
    (selCon_tagMono M n ks).support = ks.toFinset.image (conSlot M n) := by
  ext v
  simp only [Finsupp.mem_support_iff, ne_eq, Finset.mem_image, List.mem_toFinset]
  constructor
  · intro hv
    by_contra h
    push_neg at h
    apply hv
    have : v ∉ (ks.map (conSlot M n)) := by
      intro hmem
      obtain ⟨k, hk, hkv⟩ := List.mem_map.mp hmem
      exact h k hk hkv
    exact foldr_singles_zero_of_not_mem (ks.map (conSlot M n)) v this
  · intro ⟨k, hk, hkv⟩
    subst hkv
    intro h0
    have := tagMono_mem_eq_one M n ks hnd k hk
    omega

theorem selCon_diag_complement_support (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n)))
    (hnd : ks.Nodup) :
    MvPolynomial.coeff (selCon_tagMono M n ks)
      (selCon_closedForm M n ks) = selCon_signOfList ks := by
  unfold selCon_closedForm selCon_signOfList
  rw [Xcon_prod_eq_monomial M n ks hnd]
  rw [MvPolynomial.C_mul_monomial, mul_one]
  -- Goal: coeff τ (monomial(τ, (-1)^|ks|) * complement) = if Even len then 1 else -1
  -- By coeff_mul: sum over antidiagonal. Only (τ, 0) contributes.
  rw [MvPolynomial.coeff_mul]
  -- The antidiagonal of τ: all pairs (a, b) with a + b = τ
  -- Only (τ, 0) contributes: monomial(τ, s) contributes at τ (coeff τ = s)
  -- complement contributes at 0 (coeff 0 = 1)
  -- All other pairs: monomial(τ, s) has coeff 0 at anything ≠ τ
  rw [Finset.sum_eq_single (selCon_tagMono M n ks, 0)]
  · -- Main contribution: coeff τ (monomial(τ, s)) * coeff 0 (complement)
    simp only [add_zero]
    rw [MvPolynomial.coeff_monomial, if_pos rfl]
    rw [complement_prod_constant_term M n ks]
    by_cases heven : Even ks.length
    · have : ((-1 : ℚ) ^ ks.length) = 1 :=
        (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℚ) ≠ 1)).mpr heven
      simp [selCon_signOfList, heven, this]
    · have : ((-1 : ℚ) ^ ks.length) = -1 := by
        exact (neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℚ) ≠ 1)).mpr
          ((Nat.even_or_odd ks.length).resolve_left heven)
      simp [selCon_signOfList, heven, this]
  · -- All other pairs (a, b) contribute 0
    intro ⟨a, b⟩ hab hne
    simp only [Finset.mem_antidiagonal] at hab
    rw [MvPolynomial.coeff_monomial]
    by_cases ha : selCon_tagMono M n ks = a
    · subst ha
      -- If a = τ, then b = 0 from antidiagonal, contradicting hne
      have hb0 : b = 0 := by
        have := hab; simp at this; exact this
      exact absurd (by rw [hb0]) hne
    · simp [ha]
  · -- (τ, 0) is in the antidiagonal
    intro h
    simp [Finset.mem_antidiagonal] at h

/-- Every nonzero monomial in a single selConGadget has selSlot support.
selConGadget i = 1 - X(selSlot i) * X(conSlot i), so its support is
{0, e_{selSlot} + e_{conSlot}}, and the nonzero monomial e_{sel}+e_{con}
has selSlot i in its Finsupp support. -/
theorem selConGadget_nonzero_mono_has_selSlot (M : DTM) (n : ℕ)
    (i : Fin (latentBaseVars M n))
    (m : (Fin (latentNumVars M n)) →₀ ℕ) (hm : m ∈ (selConGadget M n i).support)
    (hm0 : m ≠ 0) :
    selSlot M n i ∈ m.support := by
  -- selConGadget i = 1 - X(selSlot i) * X(conSlot i)
  -- coeff m (1 - X_s * X_c) ≠ 0 forces m = 0 or m = e_s + e_c
  -- Since m ≠ 0, m = e_s + e_c, and selSlot i ∈ (e_s + e_c).support
  simp only [MvPolynomial.mem_support_iff, ne_eq] at hm
  unfold selConGadget Xsel Xcon at hm
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_one] at hm
  -- coeff m (1 - X_s * X_c) = (if m=0 then 1 else 0) - coeff m (X_s * X_c)
  by_cases hm_zero : m = 0
  · exact absurd hm_zero hm0
  · -- m ≠ 0, so (if m=0 then 1 else 0) = 0
    simp only [hm_zero, ite_false, zero_sub, neg_ne_zero] at hm
    -- hm : coeff m (X sel * X con) ≠ 0 (after negation of sub = 0)
    have hmul : MvPolynomial.coeff m
        (MvPolynomial.X (selSlot M n i) * MvPolynomial.X (conSlot M n i) :
          MvPolynomial (Fin (latentNumVars M n)) ℚ) ≠ 0 := by
      intro h; apply hm; simp [h, Ne.symm hm_zero]
    rw [MvPolynomial.coeff_mul] at hmul
    -- The only contributing antidiagonal pair is (e_sel, e_con)
    have hpair : ∃ p ∈ Finset.antidiagonal m,
        MvPolynomial.coeff p.1 (MvPolynomial.X (selSlot M n i) : MvPolynomial (Fin (latentNumVars M n)) ℚ) *
        MvPolynomial.coeff p.2 (MvPolynomial.X (conSlot M n i) : MvPolynomial (Fin (latentNumVars M n)) ℚ) ≠ 0 := by
      by_contra hall; push_neg at hall
      exact hmul (Finset.sum_eq_zero hall)
    obtain ⟨⟨a, b⟩, hab_mem, hprod⟩ := hpair
    simp only [Finset.mem_antidiagonal] at hab_mem
    rw [MvPolynomial.coeff_X', MvPolynomial.coeff_X'] at hprod
    split_ifs at hprod with ha hb
    · -- a = e_sel, b = e_con → m = e_sel + e_con
      subst ha; subst hb
      rw [← hab_mem]
      simp [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply]
    · simp at hprod
    · simp at hprod
    · simp at hprod

/-- A nonzero monomial with no selSlot support has zero coefficient in any selConGadget product. -/
theorem coeff_selConProd_eq_zero_of_no_sel (M : DTM) (n : ℕ)
    (T : Finset (Fin (latentBaseVars M n)))
    (m : (Fin (latentNumVars M n)) →₀ ℕ)
    (hm0 : m ≠ 0)
    (hnoSel : ∀ i ∈ T, selSlot M n i ∉ m.support) :
    MvPolynomial.coeff m (∏ i ∈ T, selConGadget M n i) = 0 := by
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
      have hnoSelS : ∀ i ∈ S, selSlot M n i ∉ b.support := by
        intro i hi
        exact hnoSel i (Finset.mem_insert_of_mem hi)
      have hih := ih hnoSelS
      rw [hih]
      simp
    · have hselA_not : selSlot M n j ∉ a.support := by
        rw [Finsupp.mem_support_iff]
        push_neg
        have hsum := congrArg (fun f => f (selSlot M n j)) hp
        simp only [Finsupp.add_apply] at hsum
        have hmj : m (selSlot M n j) = 0 := by
          by_contra hmj
          exact hnoSel j (Finset.mem_insert_self j S) (Finsupp.mem_support_iff.mpr hmj)
        omega
      have hcoeffA0 : MvPolynomial.coeff a (selConGadget M n j) = 0 := by
        by_contra hcoeffA
        have ha_supp : a ∈ (selConGadget M n j).support :=
          Finsupp.mem_support_iff.mpr hcoeffA
        have hselA : selSlot M n j ∈ a.support :=
          selConGadget_nonzero_mono_has_selSlot M n j a ha_supp ha0
        exact hselA_not hselA
      simp [hcoeffA0]

/-- tagMono only has conSlot variables (no selSlot). -/
theorem tagMono_no_selSlot (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n)))
    (hnd : ks.Nodup)
    (i : Fin (latentBaseVars M n)) :
    selSlot M n i ∉ (selCon_tagMono M n ks).support := by
  rw [tagMono_support_eq M n ks hnd]
  simp only [Finset.mem_image, List.mem_toFinset]
  intro ⟨k, _, hkv⟩
  -- selSlot M n i = conSlot M n k is impossible: different layer indices
  simp [selSlot, conSlot, slot, Fin.ext_iff] at hkv
  omega

/-- For nodup lists, different toFinsets imply different tagMonos. -/
theorem tagMono_ne_of_toFinset_ne (M : DTM) (n : ℕ)
    (ksi ksj : List (Fin (latentBaseVars M n)))
    (hndi : ksi.Nodup) (hndj : ksj.Nodup)
    (hne : ksi.toFinset ≠ ksj.toFinset) :
    selCon_tagMono M n ksi ≠ selCon_tagMono M n ksj := by
  intro heq
  apply hne
  -- If tagMono ksi = tagMono ksj, then their supports are equal
  have hsup : (selCon_tagMono M n ksi).support = (selCon_tagMono M n ksj).support := by
    rw [heq]
  rw [tagMono_support_eq M n ksi hndi, tagMono_support_eq M n ksj hndj] at hsup
  -- Finset.image conSlot ksi.toFinset = Finset.image conSlot ksj.toFinset
  -- conSlot is injective, so this implies ksi.toFinset = ksj.toFinset
  exact Finset.image_injective (by
    intro a b hab; simp [conSlot, slot, Fin.ext_iff] at hab; omega) hsup

theorem selCon_offdiag_complement_support (M : DTM) (n : ℕ)
    (ksi ksj : List (Fin (latentBaseVars M n)))
    (hndi : ksi.Nodup) (hndj : ksj.Nodup) :
    ksi.toFinset ≠ ksj.toFinset →
    MvPolynomial.coeff (selCon_tagMono M n ksi)
      (selCon_closedForm M n ksj) = 0 := by
  intro hneq
  unfold selCon_closedForm
  rw [Xcon_prod_eq_monomial M n ksj hndj]
  rw [MvPolynomial.C_mul_monomial, mul_one]
  -- Goal: coeff τ_ksi (monomial(τ_ksj, (-1)^|ksj|) * complement_ksj) = 0
  -- Use antidiagonal: every contributing pair (a,b) needs coeff a (monomial(τ_ksj, s)) ≠ 0
  -- which forces a = τ_ksj. Then b = τ_ksi - τ_ksj.
  -- But τ_ksi ≠ τ_ksj, so b ≠ 0, meaning complement must supply nonzero monomial mass.
  -- The complement only introduces conSlot vars paired with selSlot vars,
  -- but τ_ksi has no selSlot components, contradiction.
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro ⟨a, b⟩ hab
  simp only [Finset.mem_antidiagonal] at hab
  rw [MvPolynomial.coeff_monomial]
  by_cases ha : selCon_tagMono M n ksj = a
  · -- a = τ_ksj, so b = τ_ksi - τ_ksj
    subst ha
    simp only [if_pos rfl, ite_true, one_mul, mul_comm]
    -- Need: coeff b (complement) = 0
    -- b satisfies: τ_ksj + b = τ_ksi (from antidiagonal)
    -- If b = 0, then τ_ksi = τ_ksj, contradiction
    have htne := tagMono_ne_of_toFinset_ne M n ksi ksj hndi hndj hneq
    have hb0 : b ≠ 0 := by
      intro h; subst h; simp at hab; exact htne hab.symm
    -- b has no selSlot vars: from hab, b(v) = τ_ksi(v) - τ_ksj(v) for all v
    -- Both τ's have 0 at selSlot positions, so b(selSlot i) = 0
    -- Therefore selSlot i ∉ b.support for any i
    have hb_no_sel : ∀ i : Fin (latentBaseVars M n), selSlot M n i ∉ b.support := by
      intro i
      rw [Finsupp.mem_support_iff]; push_neg
      -- From hab: (τ_ksj + b)(selSlot i) = τ_ksi(selSlot i)
      have hsum : (selCon_tagMono M n ksj + b) (selSlot M n i) =
          (selCon_tagMono M n ksi) (selSlot M n i) := by
        rw [hab]
      simp only [Finsupp.add_apply] at hsum
      -- τ_ksi(selSlot i) = 0 (tag has no selSlot)
      have h1 : (selCon_tagMono M n ksi) (selSlot M n i) = 0 := by
        by_contra hne
        exact tagMono_no_selSlot M n ksi hndi i (Finsupp.mem_support_iff.mpr hne)
      -- τ_ksj(selSlot i) = 0
      have h2 : (selCon_tagMono M n ksj) (selSlot M n i) = 0 := by
        by_contra hne
        exact tagMono_no_selSlot M n ksj hndj i (Finsupp.mem_support_iff.mpr hne)
      omega
    -- b has no selSlot support and b ≠ 0, so its coefficient in complement is 0
    have hcoeff0 : MvPolynomial.coeff b (∏ i ∈ (Finset.univ \ ksj.toFinset), selConGadget M n i) = 0 :=
      coeff_selConProd_eq_zero_of_no_sel M n (Finset.univ \ ksj.toFinset) b hb0
        (by intro i _; exact hb_no_sel i)
    simpa [hcoeff0]
  · simp [ha]

/-- Assembled diagonal closed-form statement. -/
theorem selCon_diag_closed_form_from_decomp (M : DTM) (n : ℕ) :
    selCon_diag_closed_form_statement M n := by
  intro ks hnd hlen
  change MvPolynomial.coeff (selCon_tagMono M n ks)
    (mlProj (selCon_closedForm M n ks)) = selCon_signOfList ks
  rw [selCon_diag_mlProj_preserves_coeff M n ks hnd]
  exact selCon_diag_complement_support M n ks hnd

/-- Assembled off-diagonal closed-form statement. -/
theorem selCon_offdiag_closed_form_from_decomp (M : DTM) (n : ℕ) :
    selCon_offdiag_closed_form_statement M n := by
  intro ksi ksj hndi hndj hleni hlenj hneq
  change MvPolynomial.coeff (selCon_tagMono M n ksi)
    (mlProj (selCon_closedForm M n ksj)) = 0
  rw [selCon_offdiag_mlProj_preserves_coeff M n ksi ksj hndi]
  exact selCon_offdiag_complement_support M n ksi ksj hndi hndj hneq

/-- Therefore the original Kronecker coefficient law follows from the finer decomposition. -/
theorem selCon_kronecker_coeff_law_logscale_from_finer_decomp
    (M : DTM) (n : ℕ) (hn804 : n ≥ 2 ^ 804)
    (idxList : Fin (Nat.choose (latentBaseVars M n) (Nat.log 2 n)) →
      List (Fin (latentBaseVars M n)))
    (hnd : ∀ i, (idxList i).Nodup)
    (hlen : ∀ i, (idxList i).length = Nat.log 2 n)
    (hfinj : ∀ i j, (idxList i).toFinset = (idxList j).toFinset → i = j) :
    selCon_kronecker_coeff_law_logscale M n hn804 := by
  exact selCon_kronecker_coeff_law_logscale_from_closed_forms
    M n hn804 idxList hnd hlen hfinj
    (selCon_diag_closed_form_from_decomp M n)
    (selCon_offdiag_closed_form_from_decomp M n)

/-! ## Canonical choose-indexed list family (Item 1)

We instantiate idxList from `sublistsLen` over `List.finRange (latentBaseVars M n)`.
This provides explicit witnesses for:
- nodup rows (`hnd`)
- κ-length rows (`hlen`)
- toFinset-level injectivity (`hfinj`)
-/

noncomputable def selCon_baseList (M : DTM) (n : ℕ) :
    List (Fin (latentBaseVars M n)) :=
  List.finRange (latentBaseVars M n)

noncomputable def selCon_subsetList (M : DTM) (n : ℕ) :
    List (List (Fin (latentBaseVars M n))) :=
  (selCon_baseList M n).sublistsLen (Nat.log 2 n)

theorem selCon_subsetList_length (M : DTM) (n : ℕ) :
    (selCon_subsetList M n).length =
      Nat.choose (latentBaseVars M n) (Nat.log 2 n) := by
  unfold selCon_subsetList selCon_baseList
  simpa using List.length_sublistsLen (Nat.log 2 n) (List.finRange (latentBaseVars M n))

noncomputable def selCon_idxList (M : DTM) (n : ℕ) :
    Fin (Nat.choose (latentBaseVars M n) (Nat.log 2 n)) →
      List (Fin (latentBaseVars M n)) :=
  fun i => (selCon_subsetList M n).get (i.cast (selCon_subsetList_length M n).symm)

private theorem sublistsLen_get_sublist {α : Type*} (l : List α) (k : ℕ)
    (i : Fin (l.sublistsLen k).length) :
    ((l.sublistsLen k).get i).Sublist l := by
  have hmem := List.get_mem (l.sublistsLen k) i
  exact List.mem_sublists'.mp (List.sublistsLen_sublist_sublists' k l |>.subset hmem)

private theorem fin_eq_of_get_eq_of_nodup {α : Type*} {l : List α}
    (hnd : l.Nodup) {i j : Fin l.length} (hget : l.get i = l.get j) : i = j := by
  apply Fin.ext
  have hopt : l[i.1]? = l[j.1]? := by
    simpa [List.getElem?_eq_getElem i.2, List.getElem?_eq_getElem j.2] using congrArg some hget
  exact List.getElem?_inj i.2 hnd hopt

theorem selCon_idxList_nodup (M : DTM) (n : ℕ)
    (i : Fin (Nat.choose (latentBaseVars M n) (Nat.log 2 n))) :
    (selCon_idxList M n i).Nodup := by
  unfold selCon_idxList
  have hsub : (((selCon_baseList M n).sublistsLen (Nat.log 2 n)).get
      (i.cast (selCon_subsetList_length M n).symm)).Sublist (selCon_baseList M n) :=
    sublistsLen_get_sublist (selCon_baseList M n) (Nat.log 2 n)
      (i.cast (selCon_subsetList_length M n).symm)
  exact hsub.nodup (by unfold selCon_baseList; exact List.nodup_finRange _)

theorem selCon_idxList_length (M : DTM) (n : ℕ)
    (i : Fin (Nat.choose (latentBaseVars M n) (Nat.log 2 n))) :
    (selCon_idxList M n i).length = Nat.log 2 n := by
  unfold selCon_idxList
  have hmem : ((selCon_baseList M n).sublistsLen (Nat.log 2 n)).get
      (i.cast (selCon_subsetList_length M n).symm) ∈
      (selCon_baseList M n).sublistsLen (Nat.log 2 n) :=
    List.get_mem _ _
  exact List.length_of_sublistsLen hmem

theorem selCon_idxList_toFinset_injective (M : DTM) (n : ℕ) :
    ∀ i j : Fin (Nat.choose (latentBaseVars M n) (Nat.log 2 n)),
      (selCon_idxList M n i).toFinset = (selCon_idxList M n j).toFinset → i = j := by
  intro i j hfs
  have hsub_i : (selCon_idxList M n i).Sublist (selCon_baseList M n) := by
    unfold selCon_idxList
    exact sublistsLen_get_sublist (selCon_baseList M n) (Nat.log 2 n)
      (i.cast (selCon_subsetList_length M n).symm)
  have hsub_j : (selCon_idxList M n j).Sublist (selCon_baseList M n) := by
    unfold selCon_idxList
    exact sublistsLen_get_sublist (selCon_baseList M n) (Nat.log 2 n)
      (j.cast (selCon_subsetList_length M n).symm)
  have hnd_base : (selCon_baseList M n).Nodup := by
    unfold selCon_baseList
    exact List.nodup_finRange _
  have hlist_eq : selCon_idxList M n i = selCon_idxList M n j :=
    IdentityMinor.sublist_eq_of_nodup_toFinset_eq hnd_base hsub_i hsub_j hfs
  -- Convert list equality back to index equality via nodup of sublistsLen + get-injectivity
  have hnodup_subs : (selCon_subsetList M n).Nodup := by
    unfold selCon_subsetList selCon_baseList
    exact List.nodup_sublistsLen (Nat.log 2 n) (List.nodup_finRange _)
  have hget_eq : (selCon_subsetList M n).get (i.cast (selCon_subsetList_length M n).symm) =
      (selCon_subsetList M n).get (j.cast (selCon_subsetList_length M n).symm) := by
    simpa [selCon_idxList] using hlist_eq
  have hcast_eq : i.cast (selCon_subsetList_length M n).symm =
      j.cast (selCon_subsetList_length M n).symm :=
    fin_eq_of_get_eq_of_nodup hnodup_subs hget_eq
  exact Fin.ext (by simpa using congrArg Fin.val hcast_eq)

/-- Item 1 completed: canonical idxList package immediately discharges the
finer decomposition theorem assumptions. -/
theorem selCon_kronecker_coeff_law_logscale_from_canonical_idxList
    (M : DTM) (n : ℕ) (hn804 : n ≥ 2 ^ 804) :
    selCon_kronecker_coeff_law_logscale M n hn804 := by
  exact selCon_kronecker_coeff_law_logscale_from_finer_decomp
    M n hn804
    (selCon_idxList M n)
    (selCon_idxList_nodup M n)
    (selCon_idxList_length M n)
    (selCon_idxList_toFinset_injective M n)

/-- Canonical choose-indexed family immediately yields the bundled Kronecker data. -/
theorem selCon_kronecker_data_logscale_from_canonical_idxList
    (M : DTM) (n : ℕ) (hn804 : n ≥ 2 ^ 804) :
    selCon_kronecker_data_logscale M n hn804 := by
  exact selCon_kronecker_coeff_law_logscale_from_canonical_idxList M n hn804

/-- The NP-side Kronecker linear-independence package is now canonical:
no external selector-list indexing data is required. -/
theorem selCon_kronecker_linear_independence_logscale_from_canonical_idxList
    (M : DTM) (n : ℕ) (hn804 : n ≥ 2 ^ 804) :
    selCon_kronecker_linear_independence_logscale M n hn804 := by
  exact selCon_kronecker_linear_independence_logscale_from_data
    M n hn804 (selCon_kronecker_data_logscale_from_canonical_idxList M n hn804)

end SelConClosedCoeffDecomp
