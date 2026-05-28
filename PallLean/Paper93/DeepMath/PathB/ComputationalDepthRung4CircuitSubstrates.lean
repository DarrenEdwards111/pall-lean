import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung3Complete

/-!
# Rung 4: bounded-depth circuit substrates

Rung 4 is the first circuit-complexity rung of the ladder: AC⁰ and AC⁰[p].
There are famous unconditional lower bounds here — Håstad's switching-lemma
lower bounds for parity against AC⁰, and Razborov--Smolensky lower bounds for
AC⁰[p] — but this file does **not** claim those deep theorems are formalized.

What is formalized here is the substrate they plug into:

* Boolean functions as predicates on `Bool` vectors;
* abstract AC⁰ circuit families with depth and size budgets;
* abstract AC⁰[p] circuit families with a modulus parameter;
* size/depth lower-bound interfaces;
* concrete no-small-circuit theorems obtained directly from those lower-bound
  interfaces;
* parity as an explicit Boolean function by recursion, plus small sanity facts.

This is the rung-4 analogue of the rung-2/rung-3 accounting files: it makes the
restricted circuit-lower-bound target precise without smuggling the switching
lemma, polynomial method, or approximation machinery in as an axiom.
-/

namespace PallLean.Paper93.DeepMath.PathB

/-! ## Boolean functions and parity -/

/-- A Boolean function on `n` input bits. -/
abbrev BoolFunction (n : Nat) := (Fin n -> Bool) -> Bool

/-- Parity of a finite Boolean vector, written recursively so that basic facts
are computational. -/
def boolParity : {n : Nat} -> (Fin n -> Bool) -> Bool
  | 0, _ => false
  | n + 1, x =>
      x 0 != boolParity (fun i : Fin n => x i.succ)

/-- The parity function as a rung-4 target. -/
def parityFunction (n : Nat) : BoolFunction n :=
  boolParity

@[simp] theorem boolParity_zero (x : Fin 0 -> Bool) :
    boolParity x = false :=
  rfl

@[simp] theorem boolParity_one_false :
    boolParity (fun _ : Fin 1 => false) = false := by
  rfl

@[simp] theorem boolParity_one_true :
    boolParity (fun _ : Fin 1 => true) = true := by
  rfl

/-! ## AC⁰ substrate -/

/-- An abstract AC⁰ circuit on `n` inputs, carrying only the resource data
relevant at rung 4: computed function, depth, and size.

The `isAC0` field is an explicit certificate slot for the intended gate-basis
restriction.  This file proves consequences from resource lower bounds; it does
not define the full syntax of unbounded fan-in AND/OR/NOT circuits. -/
structure AC0Circuit (n : Nat) where
  computes : BoolFunction n
  depth : Nat
  size : Nat
  isAC0 : Prop
  isAC0_cert : isAC0

/-- AC⁰ circuit families for a target family of Boolean functions. -/
structure AC0Family (F : (n : Nat) -> BoolFunction n) where
  circuit : forall n : Nat, AC0Circuit n
  computes_target : forall n : Nat, (circuit n).computes = F n

/-- The family has AC⁰ circuits bounded by depth `d` and size `s n`. -/
def AC0FamilyBounded
    (F : (n : Nat) -> BoolFunction n) (d : Nat) (s : Nat -> Nat) : Prop :=
  exists C : AC0Family F,
    forall n : Nat, (C.circuit n).depth <= d /\ (C.circuit n).size <= s n

/-- A pointwise AC⁰ size lower bound at input length `n`. -/
def AC0SizeLowerBoundAt
    (F : (n : Nat) -> BoolFunction n) (n d lower : Nat) : Prop :=
  forall C : AC0Circuit n,
    C.computes = F n -> C.depth <= d -> lower <= C.size

/-- A pointwise AC⁰ depth lower bound at input length `n`. -/
def AC0DepthLowerBoundAt
    (F : (n : Nat) -> BoolFunction n) (n sizeBudget lowerDepth : Nat) : Prop :=
  forall C : AC0Circuit n,
    C.computes = F n -> C.size <= sizeBudget -> lowerDepth <= C.depth

/-- A pointwise AC⁰ size lower bound rules out circuits under the lower bound. -/
theorem no_small_AC0Circuit_of_size_lower_bound
    {F : (n : Nat) -> BoolFunction n} {n d lower s : Nat}
    (H : AC0SizeLowerBoundAt F n d lower)
    (hgap : s < lower) :
    Not (exists C : AC0Circuit n,
      C.computes = F n /\ C.depth <= d /\ C.size <= s) := by
  rintro ⟨C, hcomp, hdepth, hsize⟩
  have hlower : lower <= C.size := H C hcomp hdepth
  exact Nat.not_lt_of_ge (Nat.le_trans hlower hsize) hgap

/-- A pointwise AC⁰ depth lower bound rules out circuits below that depth. -/
theorem no_shallow_AC0Circuit_of_depth_lower_bound
    {F : (n : Nat) -> BoolFunction n} {n sizeBudget lowerDepth d : Nat}
    (H : AC0DepthLowerBoundAt F n sizeBudget lowerDepth)
    (hgap : d < lowerDepth) :
    Not (exists C : AC0Circuit n,
      C.computes = F n /\ C.size <= sizeBudget /\ C.depth <= d) := by
  rintro ⟨C, hcomp, hsize, hdepth⟩
  have hlower : lowerDepth <= C.depth := H C hcomp hsize
  exact Nat.not_lt_of_ge (Nat.le_trans hlower hdepth) hgap

/-- A family-level lower bound rules out globally bounded AC⁰ families once the
claimed size bound is below the lower bound at some input length. -/
theorem no_AC0FamilyBounded_of_size_lower_bound_at
    {F : (n : Nat) -> BoolFunction n} {n d lower : Nat} {s : Nat -> Nat}
    (H : AC0SizeLowerBoundAt F n d lower)
    (hgap : s n < lower) :
    Not (AC0FamilyBounded F d s) := by
  rintro ⟨Fam, hFam⟩
  rcases hFam n with ⟨hdepth, hsize⟩
  have hcomp : (Fam.circuit n).computes = F n := Fam.computes_target n
  have hlower : lower <= (Fam.circuit n).size := H (Fam.circuit n) hcomp hdepth
  exact Nat.not_lt_of_ge (Nat.le_trans hlower hsize) hgap

/-! ## Parity lower-bound interfaces for AC⁰ -/

/-- AC⁰ lower bounds for parity, kept as an interface.  Håstad's theorem is the
external mathematical source for concrete instantiations, not an assumption in
this file. -/
abbrev AC0ParitySizeLowerBoundAt (n d lower : Nat) : Prop :=
  AC0SizeLowerBoundAt parityFunction n d lower

/-- If parity has an AC⁰ size lower bound at `n`, then there is no smaller AC⁰
circuit for parity at that depth. -/
theorem no_small_AC0_parity_circuit_of_lower_bound
    {n d lower s : Nat}
    (H : AC0ParitySizeLowerBoundAt n d lower)
    (hgap : s < lower) :
    Not (exists C : AC0Circuit n,
      C.computes = parityFunction n /\ C.depth <= d /\ C.size <= s) :=
  no_small_AC0Circuit_of_size_lower_bound H hgap

/-! ## AC⁰[p] substrate -/

/-- An abstract AC⁰[p] circuit on `n` inputs, with a modulus parameter for
MOD-p gates. -/
structure AC0pCircuit (n : Nat) where
  p : Nat
  computes : BoolFunction n
  depth : Nat
  size : Nat
  isAC0p : Prop
  isAC0p_cert : isAC0p

/-- AC⁰[p] circuit families for a target family. -/
structure AC0pFamily (p : Nat) (F : (n : Nat) -> BoolFunction n) where
  circuit : forall n : Nat, AC0pCircuit n
  modulus_eq : forall n : Nat, (circuit n).p = p
  computes_target : forall n : Nat, (circuit n).computes = F n

/-- The family has AC⁰[p] circuits bounded by depth `d` and size `s n`. -/
def AC0pFamilyBounded
    (p : Nat) (F : (n : Nat) -> BoolFunction n) (d : Nat) (s : Nat -> Nat) : Prop :=
  exists C : AC0pFamily p F,
    forall n : Nat, (C.circuit n).depth <= d /\ (C.circuit n).size <= s n

/-- A pointwise AC⁰[p] size lower bound at input length `n`. -/
def AC0pSizeLowerBoundAt
    (p : Nat) (F : (n : Nat) -> BoolFunction n) (n d lower : Nat) : Prop :=
  forall C : AC0pCircuit n,
    C.p = p -> C.computes = F n -> C.depth <= d -> lower <= C.size

/-- A pointwise AC⁰[p] size lower bound rules out smaller circuits. -/
theorem no_small_AC0pCircuit_of_size_lower_bound
    {p : Nat} {F : (n : Nat) -> BoolFunction n} {n d lower s : Nat}
    (H : AC0pSizeLowerBoundAt p F n d lower)
    (hgap : s < lower) :
    Not (exists C : AC0pCircuit n,
      C.p = p /\ C.computes = F n /\ C.depth <= d /\ C.size <= s) := by
  rintro ⟨C, hp, hcomp, hdepth, hsize⟩
  have hlower : lower <= C.size := H C hp hcomp hdepth
  exact Nat.not_lt_of_ge (Nat.le_trans hlower hsize) hgap

/-- A family-level AC⁰[p] lower bound rules out globally bounded families. -/
theorem no_AC0pFamilyBounded_of_size_lower_bound_at
    {p : Nat} {F : (n : Nat) -> BoolFunction n} {n d lower : Nat} {s : Nat -> Nat}
    (H : AC0pSizeLowerBoundAt p F n d lower)
    (hgap : s n < lower) :
    Not (AC0pFamilyBounded p F d s) := by
  rintro ⟨Fam, hFam⟩
  rcases hFam n with ⟨hdepth, hsize⟩
  have hp : (Fam.circuit n).p = p := Fam.modulus_eq n
  have hcomp : (Fam.circuit n).computes = F n := Fam.computes_target n
  have hlower : lower <= (Fam.circuit n).size :=
    H (Fam.circuit n) hp hcomp hdepth
  exact Nat.not_lt_of_ge (Nat.le_trans hlower hsize) hgap

/-- AC⁰[p] lower bounds for parity, again as a theorem-interface rather than a
fake formalization of Razborov--Smolensky. -/
abbrev AC0pParitySizeLowerBoundAt (p n d lower : Nat) : Prop :=
  AC0pSizeLowerBoundAt p parityFunction n d lower

/-- If parity has an AC⁰[p] size lower bound at `n`, then no smaller AC⁰[p]
circuit computes it at that depth. -/
theorem no_small_AC0p_parity_circuit_of_lower_bound
    {p n d lower s : Nat}
    (H : AC0pParitySizeLowerBoundAt p n d lower)
    (hgap : s < lower) :
    Not (exists C : AC0pCircuit n,
      C.p = p /\ C.computes = parityFunction n /\ C.depth <= d /\ C.size <= s) :=
  no_small_AC0pCircuit_of_size_lower_bound H hgap

/-! ## Rung-4 completion bundle -/

/-- The formal circuit substrates covered by rung 4 in this repository. -/
structure Rung4CompletedSubstrates : Prop where
  ac0_pointwise_size :
    forall {F : (n : Nat) -> BoolFunction n} {n d lower s : Nat},
      AC0SizeLowerBoundAt F n d lower ->
      s < lower ->
      Not (exists C : AC0Circuit n,
        C.computes = F n /\ C.depth <= d /\ C.size <= s)
  ac0_family_size :
    forall {F : (n : Nat) -> BoolFunction n} {n d lower : Nat} {s : Nat -> Nat},
      AC0SizeLowerBoundAt F n d lower ->
      s n < lower ->
      Not (AC0FamilyBounded F d s)
  ac0p_pointwise_size :
    forall {p : Nat} {F : (n : Nat) -> BoolFunction n} {n d lower s : Nat},
      AC0pSizeLowerBoundAt p F n d lower ->
      s < lower ->
      Not (exists C : AC0pCircuit n,
        C.p = p /\ C.computes = F n /\ C.depth <= d /\ C.size <= s)
  ac0p_family_size :
    forall {p : Nat} {F : (n : Nat) -> BoolFunction n} {n d lower : Nat} {s : Nat -> Nat},
      AC0pSizeLowerBoundAt p F n d lower ->
      s n < lower ->
      Not (AC0pFamilyBounded p F d s)
  ac0_parity :
    forall {n d lower s : Nat},
      AC0ParitySizeLowerBoundAt n d lower ->
      s < lower ->
      Not (exists C : AC0Circuit n,
        C.computes = parityFunction n /\ C.depth <= d /\ C.size <= s)
  ac0p_parity :
    forall {p n d lower s : Nat},
      AC0pParitySizeLowerBoundAt p n d lower ->
      s < lower ->
      Not (exists C : AC0pCircuit n,
        C.p = p /\ C.computes = parityFunction n /\ C.depth <= d /\ C.size <= s)

/-- Rung 4 is complete at the substrate/interface level: AC⁰ and AC⁰[p] lower
bounds, including parity lower-bound interfaces, have formal no-small-circuit
consequences. -/
theorem rung4_completed_substrates : Rung4CompletedSubstrates where
  ac0_pointwise_size := by
    intro F n d lower s H hgap
    exact no_small_AC0Circuit_of_size_lower_bound H hgap
  ac0_family_size := by
    intro F n d lower s H hgap
    exact no_AC0FamilyBounded_of_size_lower_bound_at H hgap
  ac0p_pointwise_size := by
    intro p F n d lower s H hgap
    exact no_small_AC0pCircuit_of_size_lower_bound H hgap
  ac0p_family_size := by
    intro p F n d lower s H hgap
    exact no_AC0pFamilyBounded_of_size_lower_bound_at H hgap
  ac0_parity := by
    intro n d lower s H hgap
    exact no_small_AC0_parity_circuit_of_lower_bound H hgap
  ac0p_parity := by
    intro p n d lower s H hgap
    exact no_small_AC0p_parity_circuit_of_lower_bound H hgap

/-! ## Kernel-only axiom trace -/

#print axioms boolParity_zero
#print axioms boolParity_one_false
#print axioms boolParity_one_true
#print axioms no_small_AC0Circuit_of_size_lower_bound
#print axioms no_shallow_AC0Circuit_of_depth_lower_bound
#print axioms no_AC0FamilyBounded_of_size_lower_bound_at
#print axioms no_small_AC0_parity_circuit_of_lower_bound
#print axioms no_small_AC0pCircuit_of_size_lower_bound
#print axioms no_AC0pFamilyBounded_of_size_lower_bound_at
#print axioms no_small_AC0p_parity_circuit_of_lower_bound
#print axioms rung4_completed_substrates

end PallLean.Paper93.DeepMath.PathB
