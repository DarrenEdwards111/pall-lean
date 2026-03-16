/-
  RankLowerBound.lean — Prove restrictedRank_ge_of_top_coeff_ne_zero.
-/
import PallLean.LiveVarsDefs
import PallLean.SpanDim
import PallLean.TopCoeffExtract
import PallLean.RestrictedSPDP
import PallLean.MultilinearRestrict
import PallLean.DegreeBounds
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

open MvPolynomial Finset Restriction BoolEval Depth4Simulation PneqNP_Defs
  UniversalRestriction SPDP LiveVarsDefs RestrictedSPDP

namespace RankLowerBound

variable {n : ℕ}

noncomputable def expMapN (T : Finset (Fin n)) : Fin n →₀ ℕ :=
  ∑ i ∈ T, Finsupp.single i 1

lemma expMapN_injective : Function.Injective (@expMapN n) := by
  intro S T hST; ext j
  have := Finsupp.ext_iff.mp hST j
  simp only [expMapN, Finsupp.finset_sum_apply, Finsupp.single_apply, sum_ite_eq'] at this
  constructor
  · intro hj; by_contra hjT; simp [hj, hjT] at this
  · intro hj; by_contra hjS; simp [hj, hjS] at this

lemma prod_X_eq_monomial_N (T : Finset (Fin n)) :
    (∏ i ∈ T, X i : MvPolynomial (Fin n) ℚ) = monomial (expMapN T) 1 := by
  unfold expMapN; induction T using Finset.induction with
  | empty => simp only [prod_empty, sum_empty]; exact one_def.symm
  | @insert j T hj ih =>
    rw [prod_insert hj, ih, MvPolynomial.X, monomial_mul, one_mul, sum_insert hj]

lemma monomial_eq_mul_C_N (s : Fin n →₀ ℕ) (c : ℚ) :
    (monomial s c : MvPolynomial (Fin n) ℚ) = monomial s 1 * C c := by
  rw [C_apply, monomial_mul, add_zero, one_mul]

lemma vars_prod_X_subset (T : Finset (Fin n)) (v : Fin n)
    (hv : v ∈ (∏ i ∈ T, X i : MvPolynomial (Fin n) ℚ).vars) : v ∈ T := by
  have h := vars_prod (fun i : Fin n => (X i : MvPolynomial (Fin n) ℚ)) hv
  rw [Finset.mem_biUnion] at h; obtain ⟨i, hi, hvi⟩ := h
  rw [vars_X, Finset.mem_singleton] at hvi; rwa [hvi]

/-- Scaled monomials indexed by subsets of L are LI. -/
lemma li_scaled_subsets (L : Finset (Fin n)) (c : ℚ) (hc : c ≠ 0) :
    LinearIndependent ℚ (fun T : {T : Finset (Fin n) // T ⊆ L} =>
      (monomial (expMapN T.1) c : MvPolynomial (Fin n) ℚ)) := by
  rw [linearIndependent_iff]; intro l hl; ext ⟨S, hS⟩
  have h0 : ∑ T ∈ l.support, l T • monomial (expMapN T.1) c = 0 := by
    have := hl; rwa [Finsupp.linearCombination_apply, Finsupp.sum] at this
  have key : ∑ T ∈ l.support, (coeffAddMonoidHom (R := ℚ) (expMapN S))
      (l T • monomial (expMapN T.1) c) = 0 := by
    rw [← map_sum (coeffAddMonoidHom (expMapN S)), h0, map_zero]
  simp only [coeffAddMonoidHom_apply, coeff_smul, coeff_monomial, smul_eq_mul] at key
  rw [sum_eq_single ⟨S, hS⟩] at key
  · simp only [↓reduceIte] at key; simp only [Finsupp.coe_zero, Pi.zero_apply]
    exact (mul_eq_zero.mp key).resolve_right hc
  · intro ⟨T, hT⟩ _ hne
    have : expMapN T ≠ expMapN S := fun h => hne (Subtype.ext (expMapN_injective h))
    simp [this]
  · intro hS'; simp [show l ⟨S, hS⟩ = 0 from by rwa [Finsupp.mem_support_iff, not_not] at hS']

/-- Card of subsets of L = 2^|L| -/
lemma card_powerset_subtype (L : Finset (Fin n)) :
    Fintype.card {T : Finset (Fin n) // T ⊆ L} = 2 ^ L.card := by
  rw [← Finset.card_powerset L]
  have : {T : Finset (Fin n) // T ⊆ L} ≃ ↥L.powerset :=
    Equiv.subtypeEquivRight (fun T => Finset.mem_powerset.symm)
  rw [Fintype.card_congr this, Fintype.card_coe]

/-- Each scaled monomial is in the SPDP generating set. -/
lemma in_spdp_set (f : BoolFun n)
    (T : Finset (Fin n)) (hT : T ⊆ liveVars (universalRestriction n)) :
    let ρ := universalRestriction n
    let q := restrictPoly ρ (multilinearInterp f)
    let κ := Nat.log 2 n
    let c := coeff (liveTopMonomial n) q
    monomial (expMapN T) c ∈
    { q' : MvPolynomial (Fin n) ℚ | ∃ (S : List (Fin n)) (m : MvPolynomial (Fin n) ℚ),
        S.length = κ ∧ m.totalDegree ≤ κ ∧
        (∀ i ∈ S, i ∈ liveVars ρ) ∧
        (∀ v ∈ m.vars, v ∈ liveVars ρ) ∧
        q' = m * iterDerivList S q } := by
  refine ⟨(liveVars (universalRestriction n)).toList, ∏ i ∈ T, X i, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.length_toList]; exact liveVars_card_eq_log n
  · calc (∏ i ∈ T, X i : MvPolynomial (Fin n) ℚ).totalDegree
        ≤ ∑ i ∈ T, (X i : MvPolynomial (Fin n) ℚ).totalDegree :=
          totalDegree_finset_prod T (fun i => X i)
      _ = T.card := by simp [totalDegree_X]
      _ ≤ (liveVars (universalRestriction n)).card := card_le_card hT
      _ = Nat.log 2 n := liveVars_card_eq_log n
  · intro i hi; exact Finset.mem_toList.mp hi
  · intro v hv; exact hT (vars_prod_X_subset T v hv)
  · rw [iterDerivList_allLive_eq_topCoeff n f, prod_X_eq_monomial_N, monomial_eq_mul_C_N]

/-- The SPDP span for the restricted polynomial. -/
noncomputable def spdpSpan (n : ℕ) (f : BoolFun n) : Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  Submodule.span ℚ
    { q' : MvPolynomial (Fin n) ℚ | ∃ (S : List (Fin n)) (m : MvPolynomial (Fin n) ℚ),
      S.length = Nat.log 2 n ∧ m.totalDegree ≤ Nat.log 2 n ∧
      (∀ i ∈ S, i ∈ liveVars (universalRestriction n)) ∧
      (∀ v ∈ m.vars, v ∈ liveVars (universalRestriction n)) ∧
      q' = m * iterDerivList S (restrictPoly (universalRestriction n) (multilinearInterp f)) }

/-- Each scaled monomial is in the SPDP span. -/
lemma monomial_mem_spdpSpan (f : BoolFun n)
    (T : {T : Finset (Fin n) // T ⊆ liveVars (universalRestriction n)}) :
    monomial (expMapN T.1) (coeff (liveTopMonomial n)
      (restrictPoly (universalRestriction n) (multilinearInterp f))) ∈
    spdpSpan n f :=
  Submodule.subset_span (in_spdp_set f T.1 T.2)

/-- LI family in the SPDP span. -/
lemma li_in_spdpSpan (f : BoolFun n)
    (h_ne : coeff (liveTopMonomial n)
      (restrictPoly (universalRestriction n) (multilinearInterp f)) ≠ 0) :
    LinearIndependent ℚ (fun T : {T : Finset (Fin n) // T ⊆ liveVars (universalRestriction n)} =>
      (⟨monomial (expMapN T.1) (coeff (liveTopMonomial n)
        (restrictPoly (universalRestriction n) (multilinearInterp f))),
        monomial_mem_spdpSpan f T⟩ : spdpSpan n f)) := by
  apply LinearIndependent.of_comp (spdpSpan n f).subtype
  convert li_scaled_subsets (liveVars (universalRestriction n)) _ h_ne

/-- The SPDP span is finite-dimensional (generators have bounded degree). -/
instance spdpSpan_finite (n : ℕ) (f : BoolFun n) : Module.Finite ℚ (spdpSpan n f) := by
  apply Module.Finite.of_injective
    (Submodule.inclusion (show spdpSpan n f ≤ restrictDegree (Fin n) ℚ (2 * n) from ?_))
    (Submodule.inclusion_injective _)
  apply Submodule.span_le.mpr; intro q' hq'
  obtain ⟨S, m, _, hdeg, _, _, rfl⟩ := hq'
  rw [SetLike.mem_coe, mem_restrictDegree]; intro s hs i
  have hsi : s i ≤ s.sum (fun _ e => e) := by
    by_cases hi : i ∈ s.support
    · exact single_le_sum (fun j _ => Nat.zero_le (s j)) hi
    · rw [Finsupp.mem_support_iff, not_not] at hi; omega
  let q := restrictPoly (universalRestriction n) (multilinearInterp f)
  have htd : (m * iterDerivList S q).totalDegree ≤ 2 * n :=
    calc (m * iterDerivList S q).totalDegree
        ≤ m.totalDegree + (iterDerivList S q).totalDegree := totalDegree_mul m _
      _ ≤ m.totalDegree + q.totalDegree :=
          Nat.add_le_add_left (DegreeBounds.totalDegree_iterDerivList_le S q) _
      _ ≤ m.totalDegree + (multilinearInterp f).totalDegree :=
          Nat.add_le_add_left (DegreeBounds.totalDegree_restrictPoly_le _ _) _
      _ ≤ Nat.log 2 n + n :=
          Nat.add_le_add hdeg (Depth4Simulation.totalDegree_multilinearInterp_le f)
      _ ≤ 2 * n := by linarith [Nat.log_le_self 2 n]
  exact le_trans hsi (le_trans (le_totalDegree hs) htd)

set_option maxHeartbeats 1600000 in
/-- finrank of spdpSpan ≥ 2^|liveVars|. -/
lemma finrank_spdpSpan_ge (n : ℕ) (f : BoolFun n)
    (h_ne : coeff (liveTopMonomial n)
      (restrictPoly (universalRestriction n) (multilinearInterp f)) ≠ 0) :
    Module.finrank ℚ (spdpSpan n f) ≥ 2 ^ (liveVars (universalRestriction n)).card := by
  have hli := li_in_spdpSpan f h_ne
  have hle := hli.fintype_card_le_finrank
  rw [card_powerset_subtype] at hle
  omega

set_option maxHeartbeats 800000 in
/-- SPDP rank ≥ 2^|liveVars| when top coefficient is nonzero. -/
theorem restrictedRank_ge_proved (n : ℕ) (hn : n ≥ 2) (f : BoolFun n)
    (h_ne : coeff (liveTopMonomial n)
      (restrictPoly (universalRestriction n) (multilinearInterp f)) ≠ 0) :
    restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n)
      (multilinearInterp f) (universalRestriction n) ≥
    2 ^ (liveVars (universalRestriction n)).card := by
  simp only [restrictedSpdpRank]
  -- The goal is now: Module.finrank ℚ (span ...) ≥ 2^|L|
  -- This span equals spdpSpan n f by definition
  change Module.finrank ℚ (spdpSpan n f) ≥ _
  exact finrank_spdpSpan_ge n f h_ne

end RankLowerBound
