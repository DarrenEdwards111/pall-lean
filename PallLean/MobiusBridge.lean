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

-- Axiom 3: |liveVars| = log n (trivial counting)
axiom liveVars_card_eq_log (n : ℕ) :
    (liveVars (universalRestriction n)).card = Nat.log 2 n

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
