import Mathlib

/-!
# Diagonal aliasing forbids representation-invariant Cartesian charging

The sought succinct product object must rule out a basic obstruction.  If an
unrestricted implementation may identify both nominal factors so that the
diagonal product is equivalent to the original object, then any charge that is
invariant under equivalent representations has the same value before and
after reflection.  A nontrivial multiplicative product law would require that
value to be at least its own square, which is impossible above one.

This theorem is independent of Hankel rank and applies to any proposed
representation-invariant charge.  Consequently, a successful succinct object
must carry a proved separation/non-aliasing property not supplied by ordinary
Boolean correctness.
-/

namespace PallLean.Paper93.DeepMath.PathB.CartesianAliasNoGo

/-- Abstract payload requested of a circuit-charging Cartesian object. -/
structure ProductCharge (Object : Type)
    (Equivalent : Object → Object → Prop)
    (product : Object → Object → Object)
    (charge : Object → Nat) : Prop where
  invariant : ∀ {x y}, Equivalent x y → charge x = charge y
  supermultiplicative : ∀ x y, charge x * charge y ≤ charge (product x y)

/-- A nontrivial object cannot have its diagonal product aliased back to
itself under a representation-invariant multiplicative charge. -/
theorem diagonal_alias_impossible
    {Object : Type} {Equivalent : Object → Object → Prop}
    {product : Object → Object → Object} {charge : Object → Nat}
    (payload : ProductCharge Object Equivalent product charge)
    (x : Object) (nontrivial : 2 ≤ charge x) :
    ¬ Equivalent (product x x) x := by
  intro hAlias
  have hinvariant : charge (product x x) = charge x := payload.invariant hAlias
  have hgrowth : charge x * charge x ≤ charge (product x x) :=
    payload.supermultiplicative x x
  rw [hinvariant] at hgrowth
  nlinarith

/-- Equivalently, any claimed charge package forces semantic diagonal
separation for every object of charge at least two. -/
theorem productCharge_forces_diagonal_separation
    {Object : Type} {Equivalent : Object → Object → Prop}
    {product : Object → Object → Object} {charge : Object → Nat}
    (payload : ProductCharge Object Equivalent product charge) :
    ∀ x, 2 ≤ charge x → ¬ Equivalent (product x x) x :=
  fun x hx => diagonal_alias_impossible payload x hx

/-- Direct no-go packaging: the existence of one nontrivial aliased object
refutes the existence of a representation-invariant multiplicative charge. -/
theorem no_productCharge_of_nontrivial_alias
    {Object : Type} {Equivalent : Object → Object → Prop}
    {product : Object → Object → Object} {charge : Object → Nat}
    (x : Object) (nontrivial : 2 ≤ charge x)
    (hAlias : Equivalent (product x x) x) :
    ¬ ProductCharge Object Equivalent product charge := by
  intro payload
  exact diagonal_alias_impossible payload x nontrivial hAlias

/-- A concrete one-object countermodel: the product necessarily aliases, so
no charge with value two can be both invariant and multiplicative. -/
theorem unit_alias_countermodel :
    ¬ ProductCharge Unit (fun _ _ => True) (fun _ _ => ()) (fun _ => 2) := by
  exact no_productCharge_of_nontrivial_alias () (by simp) trivial

end PallLean.Paper93.DeepMath.PathB.CartesianAliasNoGo

#print axioms PallLean.Paper93.DeepMath.PathB.CartesianAliasNoGo.diagonal_alias_impossible
#print axioms PallLean.Paper93.DeepMath.PathB.CartesianAliasNoGo.productCharge_forces_diagonal_separation
#print axioms PallLean.Paper93.DeepMath.PathB.CartesianAliasNoGo.no_productCharge_of_nontrivial_alias
#print axioms PallLean.Paper93.DeepMath.PathB.CartesianAliasNoGo.unit_alias_countermodel
