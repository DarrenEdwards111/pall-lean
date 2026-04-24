import Mathlib.Data.Nat.Basic

namespace PallLean.Paper93.DeepMath.Amplituhedron

structure PlabicGraph (N : ℕ) where
  regions : ℕ
  regions_le : regions ≤ N

def trivialPlabic (N : ℕ) : PlabicGraph N := ⟨0, Nat.zero_le _⟩
