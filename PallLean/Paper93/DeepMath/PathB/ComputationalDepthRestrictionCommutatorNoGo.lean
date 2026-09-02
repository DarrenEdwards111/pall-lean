import Mathlib

/-!
# The restriction-commutator no-go

This file tests the literal "quaternion moment" for SAT: use noncommuting
operators as an interaction invariant.  Semantic restrictions of distinct
Boolean variables commute.  Consequently, any noncommutativity seen in a
solver trace comes from the chosen representation/state-update implementation,
not from the restricted Boolean function itself.

This is a small negative theorem, not a complexity separation.
-/

namespace PallLean.Paper93.DeepMath.PathB.RestrictionCommutatorNoGo

def restrictAt {n : ℕ} (f : (Fin n → Bool) → Bool)
    (i : Fin n) (b : Bool) : (Fin n → Bool) → Bool :=
  fun x ↦ f (Function.update x i b)

theorem update_distinct_comm {n : ℕ} (x : Fin n → Bool)
    (i j : Fin n) (b c : Bool) (hij : i ≠ j) :
    Function.update (Function.update x j c) i b =
      Function.update (Function.update x i b) j c := by
  exact (Function.update_comm hij b c x).symm

/-- Restrictions on distinct coordinates have zero semantic commutator. -/
theorem restrictAt_comm {n : ℕ} (f : (Fin n → Bool) → Bool)
    (i j : Fin n) (b c : Bool) (hij : i ≠ j) :
    restrictAt (restrictAt f i b) j c =
      restrictAt (restrictAt f j c) i b := by
  funext x
  simp only [restrictAt]
  rw [update_distinct_comm x i j b c hij]

end PallLean.Paper93.DeepMath.PathB.RestrictionCommutatorNoGo

#print axioms PallLean.Paper93.DeepMath.PathB.RestrictionCommutatorNoGo.update_distinct_comm
#print axioms PallLean.Paper93.DeepMath.PathB.RestrictionCommutatorNoGo.restrictAt_comm
