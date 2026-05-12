import PallLean.Paper93.DeepMath.PathB.Positroid.PluckerAbstract
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Structural facts about empty submatrices of the compiled gadget

This kernel-only file specializes `principalMinor_empty` and
`principalMinor_univ` from `PluckerAbstract` to the canonical Cook–Levin
compiled gadget `compiledGadget α n` for small fixed values of `n`.

The principal minor of `compiledGadget α n` at the empty subset is `1`
(empty product), and the principal minor at `Finset.univ` equals the
determinant of `compiledGadget α n`.

The file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem principalMinor_empty_compiledGadget (α : ℝ) (n : ℕ) :
    principalMinor (compiledGadget α n) ∅ = 1 :=
  principalMinor_empty (compiledGadget α n)

theorem principalMinor_univ_compiledGadget_n1 (α : ℝ) :
    principalMinor (compiledGadget α 1) Finset.univ = (compiledGadget α 1).det :=
  principalMinor_univ (compiledGadget α 1)

theorem principalMinor_univ_compiledGadget_n2 (α : ℝ) :
    principalMinor (compiledGadget α 2) Finset.univ = (compiledGadget α 2).det :=
  principalMinor_univ (compiledGadget α 2)

theorem principalMinor_univ_compiledGadget_n3 (α : ℝ) :
    principalMinor (compiledGadget α 3) Finset.univ = (compiledGadget α 3).det :=
  principalMinor_univ (compiledGadget α 3)

theorem principalMinor_univ_compiledGadget_n4 (α : ℝ) :
    principalMinor (compiledGadget α 4) Finset.univ = (compiledGadget α 4).det :=
  principalMinor_univ (compiledGadget α 4)

end PallLean.Paper93.DeepMath.PathB.Positroid
