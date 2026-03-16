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
import PallLean.Depth4Simulation
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

/-- InFSPDP: f is in the FSPDP class iff its multilinear interpolation
    has low restricted SPDP rank.

    Paper-faithful: the paper uses the unique multilinear polynomial
    representing f (§2.3, §7). Using the multilinear interpolation
    (rather than ∃ p) ensures the restricted polynomial is uniquely
    determined by f, which is essential for the proper subspace argument. -/
def InFSPDP {n : ℕ} (f : BoolFun n) : Prop :=
  restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n)
    (Depth4Simulation.multilinearInterp f)
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
