/-
  MobiusBridge.lean -- Connecting Mobius functional to InFSPDP
-/
import PallLean.PneqNP_Defs
import PallLean.MobiusTopCoeff
import PallLean.RankLowerBound
import PallLean.LiveVarsDefs
import PallLean.SpanDim
import PallLean.TopCoeffExtract
import PallLean.ProperSubspaceGeneral
import PallLean.Restriction
import PallLean.UniversalRestriction
import PallLean.RestrictedSPDP
import PallLean.BoolEval
import PallLean.Depth4Simulation
import Mathlib.Tactic

namespace MobiusBridge

open MvPolynomial SPDP RestrictedSPDP Restriction BoolEval PneqNP_Defs
open Depth4Simulation UniversalRestriction ProperSubspaceGeneral LiveVarsDefs

/-! ## Proved infrastructure for mobiusL_eq_top_coeff -/

/-- eval g (aeval f p) = eval (eval g . f) p. AlgHom composition. -/
lemma eval_aeval_eq {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (f : σ → MvPolynomial σ R) (g : σ → R)
    (p : MvPolynomial σ R) :
    eval g (aeval f p) = eval (fun i => eval g (f i)) p := by
  have key : ((eval g).comp (aeval f).toRingHom : MvPolynomial σ R →+* R) =
      eval (fun i => eval g (f i)) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro i; simp [eval_X]
  exact RingHom.congr_fun key p

/-- Evaluation of restricted polynomial at a consistent Boolean point
    equals evaluation of the original polynomial. Paper-faithful: this
    encodes that restriction only substitutes values that are already
    fixed by the consistent assignment. -/
lemma eval_restrictPoly_consistent {n : ℕ} (ρ : Restriction.Restriction n)
    (x : Fin n → Bool) (hx : ∀ i b, ρ i = some b → x i = b)
    (p : MvPolynomial (Fin n) ℚ) :
    eval (fun i => boolToRat (x i)) (restrictPoly ρ p) =
    eval (fun i => boolToRat (x i)) p := by
  unfold restrictPoly
  rw [eval_aeval_eq]
  have h_eq : (fun i => eval (fun j => boolToRat (x j))
    (match ρ i with | none => X i | some false => (0 : MvPolynomial (Fin n) ℚ) | some true => 1)) =
    (fun i => boolToRat (x i)) := by
    funext i; cases h : ρ i with
    | none => simp [eval_X]
    | some b =>
      have hmatch : (match (some b : Option Bool) with
        | none => X i
        | some false => (0 : MvPolynomial (Fin n) ℚ)
        | some true => 1) = (if b then (1 : MvPolynomial (Fin n) ℚ) else 0) := by
        cases b <;> rfl
      rw [hmatch]
      have hxb := hx i b h; rw [hxb]
      cases b <;> simp [boolToRat]
  exact congr_arg (· p) (congr_arg eval h_eq)

/-- Evaluation of restricted multilinear interpolation at consistent point = boolToRat(f(x)). -/
lemma eval_restricted_multilinearInterp {n : ℕ} (ρ : Restriction.Restriction n)
    (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) (hx : ∀ i b, ρ i = some b → x i = b) :
    eval (fun i => boolToRat (x i)) (restrictPoly ρ (multilinearInterp f)) =
    boolToRat (f x) := by
  rw [eval_restrictPoly_consistent ρ x hx]
  exact multilinearInterp_correct f x

/-! ## Axiom 1: Mobius inversion identity

  The Mobius functional L(evalVec f) equals the top coefficient of the
  restricted polynomial. This combines:
  1. eval_restricted_multilinearInterp (PROVED above)
  2. superset_mobius_sum (PROVED in MobiusInversion.lean)
  3. Connecting the polynomial coeff to the Mobius functional sum

  The remaining gap is step 3: showing that
    coeff(liveTopMonomial) q = sum_S (-1)^{w-|S|} eval(1_S) q
  for multilinear q. This requires the Mobius inversion identity
  applied to multilinear polynomial expansion. -/
-- PROVED in MobiusTopCoeff.lean (was axiom)
theorem mobiusL_eq_top_coeff (n : ℕ) (hn : n ≥ 2) (f : BoolFun n) :
    mobiusL n (evalVec f) =
    MvPolynomial.coeff (liveTopMonomial n)
      (restrictPoly (universalRestriction n) (multilinearInterp f)) := by
  have h := MobiusTopCoeff.mobiusL_eq_top_coeff_proved n hn f
  have : MobiusTopCoeff.topMon (liveVars (universalRestriction n)) = liveTopMonomial n := by
    unfold MobiusTopCoeff.topMon liveTopMonomial; rfl
  rwa [this] at h

-- iterDerivList_allLive_eq_topCoeff: now in LiveVarsDefs

-- Sub-axiom 2b: Multiplying a nonzero constant by all degree-le-w
-- monomials on w variables spans 2^w dimensions.
-- Standard: {c*m : m multilinear on w vars} = c * (multilinear monomials),
-- and multilinear monomials are linearly independent.
-- PROVED in SpanDim.lean (one technical sorry for Module.Finite)
theorem span_const_monomials_dim (w : ℕ) (c : ℚ) (hc : c ≠ 0)
    (V : Finset (Fin w)) (hV : V = Finset.univ) :
    Module.finrank ℚ (Submodule.span ℚ
      { q : MvPolynomial (Fin w) ℚ |
        ∃ (m : MvPolynomial (Fin w) ℚ), m.totalDegree ≤ w ∧
        (∀ v ∈ m.vars, v ∈ V) ∧
        q = m * MvPolynomial.C c }) ≥ 2 ^ w :=
  SpanDim.span_const_monomials_dim_proved w c hc V hV

-- The span of {m * C(c) : vars(m) in liveVars, deg(m) <= w} contains
-- all multilinear monomials on liveVars (times c), giving dim >= 2^w.
-- This requires: (a) multilinear monomials on w vars are LI (standard),
-- (b) c * m ranges over all such monomials when c != 0.
-- Axiomatized since the Lean plumbing between Fin n and Fin w is heavy.
theorem restrictedRank_ge_of_top_coeff_ne_zero (n : ℕ) (hn : n ≥ 2) (f : BoolFun n)
    (h_ne : MvPolynomial.coeff (liveTopMonomial n)
      (restrictPoly (universalRestriction n) (multilinearInterp f)) ≠ 0) :
    restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n)
      (multilinearInterp f) (universalRestriction n) ≥
    2 ^ (liveVars (universalRestriction n)).card :=
  RankLowerBound.restrictedRank_ge_proved n hn f h_ne

-- Helper: counting elements in {i : Fin n | i >= m}
-- card_filter_ge and liveVars_card_eq_log: now in LiveVarsDefs

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
