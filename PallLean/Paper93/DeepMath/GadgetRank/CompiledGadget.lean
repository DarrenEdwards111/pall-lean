import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.GadgetRank

structure CompiledGadget (k : ℕ) where
  spdpRank : ℕ
  psdForm : Matrix (Fin k) (Fin k) ℝ

def trivialGadget (k : ℕ) : CompiledGadget k := ⟨0, 0⟩
