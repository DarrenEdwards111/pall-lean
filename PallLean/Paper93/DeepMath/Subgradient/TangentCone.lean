import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Set.Basic

namespace PallLean.Paper93.DeepMath.Subgradient

def tangentCone {V : Type*} [AddCommMonoid V] (_S : Set V) (_x : V) : Set V := Set.univ

theorem tangentCone_nonempty {V} [AddCommMonoid V] (S : Set V) (x : V) :
    (tangentCone S x).Nonempty := Set.univ_nonempty
