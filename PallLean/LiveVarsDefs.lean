/-
  LiveVarsDefs.lean — Definitions and lemmas about liveVars that both
  RankLowerBound and MobiusBridge need (breaks import cycle).
-/
import PallLean.PneqNP_Defs
import PallLean.TopCoeffExtract
import PallLean.Restriction
import PallLean.UniversalRestriction
import PallLean.RestrictedSPDP
import PallLean.BoolEval
import PallLean.Depth4Simulation
import Mathlib.Tactic

namespace LiveVarsDefs

open MvPolynomial SPDP RestrictedSPDP Restriction BoolEval PneqNP_Defs
open Depth4Simulation UniversalRestriction

noncomputable def liveTopMonomial (n : ℕ) : Fin n →₀ ℕ :=
  ∑ i ∈ liveVars (universalRestriction n), Finsupp.single i 1

theorem iterDerivList_allLive_eq_topCoeff (n : ℕ) (f : BoolFun n) :
    SPDP.iterDerivList (liveVars (universalRestriction n)).toList
      (restrictPoly (universalRestriction n) (multilinearInterp f)) =
    MvPolynomial.C (MvPolynomial.coeff (liveTopMonomial n)
      (restrictPoly (universalRestriction n) (multilinearInterp f))) :=
  TopCoeffExtract.iterDerivList_allLive_eq_topCoeff_proved n f

-- Helper for counting
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

theorem liveVars_card_eq_log (n : ℕ) :
    (liveVars (universalRestriction n)).card = Nat.log 2 n := by
  simp only [liveVars, universalRestriction]
  have h_simp : (Finset.univ.filter fun i : Fin n =>
    (if i.val < n - Nat.log 2 n then some false else none) = none) =
    Finset.univ.filter (fun i : Fin n => n - Nat.log 2 n ≤ i.val) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; split_ifs at h with h' <;> simp_all
    · intro h; simp [show ¬ i.val < n - Nat.log 2 n from by omega]
  rw [h_simp]
  exact card_filter_ge n (Nat.log 2 n) (Nat.log_le_self 2 n)

end LiveVarsDefs
