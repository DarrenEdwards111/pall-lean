/-
  MobiusBridge.lean -- Connecting Mobius functional to InFSPDP
-/
import PallLean.PneqNP_Defs
import PallLean.ProperSubspaceGeneral
import PallLean.Restriction
import PallLean.UniversalRestriction
import PallLean.RestrictedSPDP
import PallLean.BoolEval
import PallLean.Depth4Simulation
import PallLean.TopCoeffRank
import Mathlib.Tactic

namespace MobiusBridge

open MvPolynomial SPDP RestrictedSPDP Restriction BoolEval PneqNP_Defs
open Depth4Simulation UniversalRestriction ProperSubspaceGeneral TopCoeffRank

noncomputable def liveTopMonomial (n : ℕ) : Fin n →₀ ℕ :=
  ∑ i ∈ liveVars (universalRestriction n), Finsupp.single i 1

-- Axiom 1: Mobius inversion identity
axiom mobiusL_eq_top_coeff (n : ℕ) (hn : n ≥ 2) (f : BoolFun n) :
    mobiusL n (evalVec f) =
    MvPolynomial.coeff (liveTopMonomial n)
      (restrictPoly (universalRestriction n) (multilinearInterp f))

-- Axiom 2: Nonzero top coeff implies high restricted SPDP rank
axiom restrictedRank_ge_of_top_coeff_ne_zero (n : ℕ) (hn : n ≥ 2) (f : BoolFun n)
    (h_ne : MvPolynomial.coeff (liveTopMonomial n)
      (restrictPoly (universalRestriction n) (multilinearInterp f)) ≠ 0) :
    restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n)
      (multilinearInterp f) (universalRestriction n) ≥
    2 ^ (liveVars (universalRestriction n)).card

-- Helper: counting elements in {i : Fin n | i >= m}
private lemma card_filter_ge (n k : ℕ) (hk : k ≤ n) :
    (Finset.univ.filter (fun i : Fin n => n - k ≤ i.val)).card = k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at hk; subst hk; simp
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [Nat.sub_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro ⟨i, hi⟩ _; omega
  · have hlt : n - k < n := by omega
    have : (Finset.univ.filter (fun i : Fin n => n - k ≤ i.val)) =
      Finset.Icc (⟨n - k, hlt⟩ : Fin n) ⟨n - 1, by omega⟩ := by
      ext ⟨i, hi⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc,
        Fin.le_iff_val_le_val]
      omega
    rw [this, Fin.card_Icc]; simp; omega

-- PROVED: |liveVars| = log n
theorem liveVars_card_eq_log (n : ℕ) :
    (liveVars (universalRestriction n)).card = Nat.log 2 n := by
  simp only [liveVars, universalRestriction]
  -- Simplify: ρ i = none ↔ i.val ≥ n - log n
  have h_simp : (Finset.univ.filter fun i : Fin n =>
    (if i.val < n - Nat.log 2 n then some false else none) = none) =
    Finset.univ.filter (fun i : Fin n => n - Nat.log 2 n ≤ i.val) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; split_ifs at h with h' <;> simp_all
    · intro h; simp [show ¬ i.val < n - Nat.log 2 n from by omega]
  rw [h_simp]
  exact card_filter_ge n (Nat.log 2 n) (Nat.log_le_self 2 n)

-- PROVED: InFSPDP forces top coefficient = 0
theorem top_coeff_zero_of_InFSPDP (n : ℕ) (hn : n ≥ 4) (f : BoolFun n)
    (hf : InFSPDP f) :
    MvPolynomial.coeff (liveTopMonomial n)
      (restrictPoly (universalRestriction n) (multilinearInterp f)) = 0 := by
  by_contra h_ne
  have h_ge := restrictedRank_ge_of_top_coeff_ne_zero n (by omega) f h_ne
  rw [liveVars_card_eq_log] at h_ge
  unfold InFSPDP at hf
  have h_lt := ProperSubspaceGeneral.sqrt_lt_pow_log n hn
  omega

-- PROVED: Mobius functional vanishes on InFSPDP
theorem mobiusL_vanishes_on_InFSPDP (n : ℕ) (hn : n ≥ 4)
    (f : BoolFun n) (hf : InFSPDP f) :
    mobiusL n (evalVec f) = 0 := by
  rw [mobiusL_eq_top_coeff n (by omega) f]
  exact top_coeff_zero_of_InFSPDP n hn f hf

end MobiusBridge
