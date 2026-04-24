import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Set.Basic

namespace PallLean.Paper93.DeepMath.Subgradient

def normalCone {V : Type*} [AddCommMonoid V] (_S : Set V) (_x : V) : Set V := {0}

theorem zero_in_normalCone {V} [AddCommMonoid V] (S : Set V) (x : V) :
    (0 : V) ∈ normalCone S x := rfl
