/-
  PneqNP_Defs.lean — Shared definitions for the P ≠ NP formalization

  Extracted from PneqNP_Paper.lean to break circular imports.
  Both PneqNP_Paper.lean and ProperSubspace.lean import this file.
-/
import PallLean.BoolEval
import PallLean.SPDPDefs
import PallLean.RestrictedSPDP
import PallLean.Restriction
import PallLean.UniversalRestriction
import PallLean.TuringMachine
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace PneqNP_Defs

open BoolEval SPDP RestrictedSPDP Restriction

abbrev BoolFun (n : ℕ) := (Fin n → Bool) → Bool

noncomputable def evalVec {n : ℕ} (f : BoolFun n) : (Fin n → Bool) → ℚ :=
  fun x => boolToRat (f x)

def BoolFunFamily := (n : ℕ) → BoolFun n

def UniformPtime (F : BoolFunFamily) : Prop :=
  ∃ (M : TuringMachine.DTM), ∀ n, M.decides (F n)

def InFSPDP {n : ℕ} (f : BoolFun n) : Prop :=
  ∃ (p : MvPolynomial (Fin n) ℚ),
    (∀ x, MvPolynomial.eval (fun i => boolToRat (x i)) p = boolToRat (f x)) ∧
    restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n) p
      (UniversalRestriction.universalRestriction n) ≤ Nat.sqrt n

def UniformNP (F : BoolFunFamily) : Prop :=
  ∃ (m : ℕ) (V : BoolFunFamily),
    UniformPtime V ∧
    ∀ n, ∀ x : Fin n → Bool,
      F n x = true ↔
        ∃ w : Fin m → Bool,
          V (n + m) (Fin.append x w) = true

def P_eq_NP : Prop := ∀ F : BoolFunFamily, UniformNP F → UniformPtime F

noncomputable def fspdpEvalSubspace (n : ℕ) : Submodule ℚ ((Fin n → Bool) → ℚ) :=
  Submodule.span ℚ { v | ∃ f : BoolFun n, InFSPDP f ∧ v = evalVec f }

end PneqNP_Defs
