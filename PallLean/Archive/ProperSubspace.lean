/-
  ProperSubspace.lean — F_SPDP* ⊊ ALL (Paper §8.6)
-/
import PallLean.PneqNP_Defs
import PallLean.UniversalRestriction
import PallLean.SPDPRankLower
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace ProperSubspace

open PneqNP_Defs BoolEval SPDP RestrictedSPDP Restriction UniversalRestriction
open MvPolynomial

-- At n=2, universalRestriction fixes variable 0 to false
theorem ur2_fix0 : universalRestriction 2 (⟨0, by omega⟩ : Fin 2) = some false := by
  native_decide

-- At n=2, universalRestriction leaves variable 1 live
theorem ur2_live1 : universalRestriction 2 (⟨1, by omega⟩ : Fin 2) = none := by
  native_decide

-- Variable 1 is in the live vars
theorem ur2_one_live : (⟨1, by omega⟩ : Fin 2) ∈ liveVars (universalRestriction 2) := by
  simp [liveVars, Finset.mem_filter]
  exact ur2_live1

-- Variable 0 is NOT in the live vars
theorem ur2_zero_not_live : (⟨0, by omega⟩ : Fin 2) ∉ liveVars (universalRestriction 2) := by
  simp only [liveVars, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [ur2_fix0]; exact fun h => nomatch h

/-- At n=2, InFSPDP implies f(0,0) = f(0,1).

    The SPDP rank of a non-constant restricted polynomial exceeds √2 = 1,
    so InFSPDP forces the restricted poly to be constant, meaning
    f agrees on the two consistent inputs (where x₀ = false). -/
theorem infspdp_n2_consistent (f : BoolFun 2) (hf : InFSPDP f) :
    f (![false, false]) = f (![false, true]) := by
  by_contra hne
  obtain ⟨p, hp_eval, hp_spdp⟩ := hf
  exact SPDPRankLower.not_infspdp_of_inconsistent_n2 f hne p hp_eval hp_spdp

/-- The hyperplane {v | v(![false,false]) = v(![false,true])} is a submodule. -/
def hyperplane2 : Submodule ℚ ((Fin 2 → Bool) → ℚ) where
  carrier := { v | v (![false, false]) = v (![false, true]) }
  zero_mem' := rfl
  add_mem' := by
    intro a b ha hb
    show (a + b) (![false, false]) = (a + b) (![false, true])
    show a _ + b _ = a _ + b _
    rw [ha, hb]
  smul_mem' := by
    intro c x hx
    show (c • x) (![false, false]) = (c • x) (![false, true])
    show c • x _ = c • x _
    rw [hx]

theorem fspdpEvalSubspace_n2_in_hyperplane :
    fspdpEvalSubspace 2 ≤ hyperplane2 := by
  apply Submodule.span_le.mpr
  intro v ⟨f, hf, hv⟩
  show v (![false, false]) = v (![false, true])
  rw [hv]; unfold evalVec
  show boolToRat (f _) = boolToRat (f _)
  congr 1
  exact infspdp_n2_consistent f hf

/-- XOR function on 2 variables. -/
def xor2 : BoolFun 2 := fun x => x 0 ^^ x 1

/-- XOR violates the hyperplane constraint. -/
theorem xor2_violates :
    evalVec xor2 (![false, false]) ≠ evalVec xor2 (![false, true]) := by
  unfold evalVec xor2 boolToRat
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  norm_num

/-- XOR's evalVec is not in the fspdpEvalSubspace at n=2. -/
theorem xor2_not_in_subspace :
    evalVec xor2 ∉ fspdpEvalSubspace 2 := by
  intro h
  have := fspdpEvalSubspace_n2_in_hyperplane h
  exact xor2_violates this

/-- **F_SPDP* at n=2 is a proper subspace.** -/
theorem fspdp_proper_n2 : fspdpEvalSubspace 2 ≠ ⊤ := by
  intro h
  have : evalVec xor2 ∈ fspdpEvalSubspace 2 := by rw [h]; exact Submodule.mem_top
  exact xor2_not_in_subspace this

end ProperSubspace
