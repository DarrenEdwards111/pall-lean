import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

namespace PallLean.Paper93.DeepMath.Amplituhedron

structure Positroid (N k : ℕ) where
  indices : Finset (Fin N)
  card_eq : indices.card = k

def trivialPositroid (N : ℕ) : Positroid N 0 := ⟨∅, rfl⟩
