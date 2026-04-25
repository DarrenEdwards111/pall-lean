import PallLean.Paper93.DeepMath.PathB.Positroid.PluckerAbstract
import PallLean.Paper93.DeepMath.PathB.PrincipalMinorAtUniv
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetMinorEmpty
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem principalMinor_compiledGadget_empty (α : ℝ) (n : ℕ) :
    principalMinor (compiledGadget α n) ∅ = 1 :=
  principalMinor_empty (compiledGadget α n)

theorem principalMinor_compiledGadget_univ (α : ℝ) (n : ℕ) :
    principalMinor (compiledGadget α n) Finset.univ = (compiledGadget α n).det :=
  principalMinor_univ (compiledGadget α n)

theorem principalMinor_compiledGadget_n2_univ (α : ℝ) :
    principalMinor (compiledGadget α 2) Finset.univ = α * (α + 2) := by
  rw [principalMinor_univ]
  exact compiledGadget_2x2_det α

theorem principalMinor_compiledGadget_n3_univ (α : ℝ) :
    principalMinor (compiledGadget α 3) Finset.univ = α * (α + 3)^2 := by
  rw [principalMinor_univ]
  exact compiledGadget_3x3_det α

theorem principalMinor_compiledGadget_n4_univ (α : ℝ) :
    principalMinor (compiledGadget α 4) Finset.univ = α * (α + 4)^3 := by
  rw [principalMinor_univ]
  exact compiledGadget_4x4_det α

end PallLean.Paper93.DeepMath.PathB.Positroid
