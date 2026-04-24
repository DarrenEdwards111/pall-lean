import Mathlib.Data.Finset.Basic

namespace PallLean.Paper93.DeepMath.LPS

structure PGL2Quotient (q : ℕ) where
  elements : Finset ℕ

def pgl2Size (q : ℕ) : ℕ := q * (q*q - 1)

theorem pgl2Size_formula (q : ℕ) : pgl2Size q = q * (q*q - 1) := rfl

end PallLean.Paper93.DeepMath.LPS
