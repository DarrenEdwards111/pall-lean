import PallLean.Paper93.DeepMath.PathB.CompiledGadgetSingletonMinor
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- Singleton minor of compiledGadget α n at any i is α + (n-1). -/
theorem compiledGadget_singleton_minor_universal (α : ℝ) (n : ℕ) (i : Fin n) :
    ((compiledGadget α n).submatrix
      (fun j : ({i} : Finset (Fin n)) => (j.val : Fin n))
      (fun j : ({i} : Finset (Fin n)) => (j.val : Fin n))).det = α + ((n : ℝ) - 1) :=
  compiledGadget_singleton_minor α n i

/-- For n ≥ 1 and α > 0, the singleton minor is at least α. -/
theorem compiledGadget_singleton_minor_ge_alpha (α : ℝ) (n : ℕ) (hα : 0 ≤ α) (hn : 1 ≤ n) (i : Fin n) :
    α ≤ ((compiledGadget α n).submatrix
      (fun j : ({i} : Finset (Fin n)) => (j.val : Fin n))
      (fun j : ({i} : Finset (Fin n)) => (j.val : Fin n))).det := by
  rw [compiledGadget_singleton_minor]
  have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

/-- For n ≥ 2 and α > 0, the singleton minor is strictly greater than α. -/
theorem compiledGadget_singleton_minor_gt_alpha (α : ℝ) (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    α < ((compiledGadget α n).submatrix
      (fun j : ({i} : Finset (Fin n)) => (j.val : Fin n))
      (fun j : ({i} : Finset (Fin n)) => (j.val : Fin n))).det := by
  rw [compiledGadget_singleton_minor]
  have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

end PallLean.Paper93.DeepMath.PathB.Positroid
