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

/-- The selConGadget complement uses only variables from {selSlot i, conSlot i | i ∉ ks}. -/
theorem selConGadget_usesOnly_outsideSlots (M : DTM) (n : ℕ)
    (i : Fin (latentBaseVars M n)) :
    CoeffDisjoint.usesOnly (selConGadget M n i)
      ({selSlot M n i, conSlot M n i} : Set (Fin (latentNumVars M n))) := by
  sorry

/-- The tag monomial's support is exactly {conSlot k | k ∈ ks}. -/
theorem tagMono_support_eq (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n)))
    (hnd : ks.Nodup) :
    (selCon_tagMono M n ks).support = ks.toFinset.image (conSlot M n) := by
  sorry

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

/-- Off-diagonal: coeff of one tag at another's closed form = 0.

Strategy: ksi ≠ ksj implies τ_ksi ≠ τ_ksj (injective conSlot).
The monomial part contributes only τ_ksj. The complement cannot supply the
difference because it pairs every conSlot with a selSlot, but τ_ksi uses only conSlot vars.
-/
theorem selCon_offdiag_complement_support (M : DTM) (n : ℕ)
    (ksi ksj : List (Fin (latentBaseVars M n)))
    (hndi : ksi.Nodup) (hndj : ksj.Nodup) :
    ksi ≠ ksj →
    MvPolynomial.coeff (selCon_tagMono M n ksi)
      (selCon_closedForm M n ksj) = 0 := by
  intro hneq
  unfold selCon_closedForm
  rw [Xcon_prod_eq_monomial M n ksj hndj]
  rw [MvPolynomial.C_mul_monomial, mul_one]
  sorry

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
    (hinj : Function.Injective idxList) :
    selCon_kronecker_coeff_law_logscale M n hn804 := by
  exact selCon_kronecker_coeff_law_logscale_from_closed_forms
    M n hn804 idxList hnd hlen hinj
    (selCon_diag_closed_form_from_decomp M n)
    (selCon_offdiag_closed_form_from_decomp M n)

end SelConClosedCoeffDecomp
