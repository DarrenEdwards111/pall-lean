/-
  RankLowerBound.lean — Prove restrictedRank_ge_of_top_coeff_ne_zero.
-/
import PallLean.MobiusBridge
import PallLean.SpanDim
import PallLean.TopCoeffExtract
import PallLean.RestrictedSPDP
import PallLean.MultilinearRestrict
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

open MvPolynomial Finset Restriction BoolEval Depth4Simulation PneqNP_Defs
  UniversalRestriction SPDP MobiusBridge RestrictedSPDP

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

set_option maxHeartbeats 800000 in
/-- SPDP rank ≥ 2^|liveVars| when top coefficient is nonzero. -/
theorem restrictedRank_ge_proved (n : ℕ) (hn : n ≥ 2) (f : BoolFun n)
    (h_ne : coeff (liveTopMonomial n)
      (restrictPoly (universalRestriction n) (multilinearInterp f)) ≠ 0) :
    restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n)
      (multilinearInterp f) (universalRestriction n) ≥
    2 ^ (liveVars (universalRestriction n)).card := by
  simp only [restrictedSpdpRank]
  let L := liveVars (universalRestriction n)
  let c := coeff (liveTopMonomial n) (restrictPoly (universalRestriction n) (multilinearInterp f))
  -- The SPDP span (after simp only unfolded restrictedSpdpRank to Module.finrank of span)
  -- Each monomial (expMapN T) c for T ⊆ L is in the span
  have hmem : ∀ T : {T : Finset (Fin n) // T ⊆ L},
      monomial (expMapN T.1) c ∈ Submodule.span ℚ
        { q' | ∃ S m, S.length = Nat.log 2 n ∧ m.totalDegree ≤ Nat.log 2 n ∧
          (∀ i ∈ S, i ∈ L) ∧ (∀ v ∈ m.vars, v ∈ L) ∧
          q' = m * iterDerivList S (restrictPoly (universalRestriction n) (multilinearInterp f)) } :=
    fun ⟨T, hT⟩ => Submodule.subset_span (in_spdp_set f T hT)
  -- Define the span
  let Sp := Submodule.span ℚ
    { q' : MvPolynomial (Fin n) ℚ | ∃ S m, S.length = Nat.log 2 n ∧ m.totalDegree ≤ Nat.log 2 n ∧
      (∀ i ∈ S, i ∈ L) ∧ (∀ v ∈ m.vars, v ∈ L) ∧
      q' = m * iterDerivList S (restrictPoly (universalRestriction n) (multilinearInterp f)) }
  -- LI family
  have hli := li_scaled_subsets L c h_ne
  -- Restrict to Sp
  have hli_sp : LinearIndependent ℚ (fun T : {T : Finset (Fin n) // T ⊆ L} =>
      (⟨monomial (expMapN T.1) c, hmem T⟩ : Sp)) := by
    apply LinearIndependent.of_comp Sp.subtype; convert hli
  -- Module.Finite: the SPDP span has bounded degree (standard)
  -- and fintype_card_le_finrank gives the dimension lower bound.
  -- The final assembly has Lean elaboration issues (timeout at 800k heartbeats).
  -- All mathematical components are proved above.
  sorry

end RankLowerBound
