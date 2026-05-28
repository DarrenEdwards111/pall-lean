import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSignRankInvariant

/-!
# TC⁰/NC¹ observer route: non-natural invariant constraint

**STATUS: BARRIER ATLAS / DESIGN CONSTRAINT, NOT A TC⁰ OR NC¹ LOWER BOUND.**

This file formalizes the answer to the question: *what does the observer-invariant
program say a proof of TC⁰/NC¹ lower bounds would have to look like?*

The answer is a constraint, not a known invariant:

* an invariant must be **sound** for the model: every small TC⁰/NC¹ computation has
  low observer complexity;
* it must be **complete on an explicit target**: the target function has high
  observer complexity;
* and, because of the Razborov--Rudich natural-proofs barrier (with PRFs inside
  TC⁰, e.g. Naor--Reingold), it must be **non-natural**: not both large and
  truth-table-constructive.

This file deliberately does **not** define largeness, constructivity, KW cost, or
formula depth as `True`.  Those notions live in explicit interface records below.
That keeps this file from pretending to prove the deep literature inputs; it only
proves the implications once those inputs are supplied.

The file also records two honest frontiers:

* **KW communication for NC¹/formulas**: with a supplied Karchmer--Wigderson
  interface, formula-depth lower bounds and KW communication lower bounds are
  equivalent.  This is a conservation/equivalence route, not an escape hatch.
* **Sign-rank for depth-2 threshold / UPP**: this is the real threshold-adjacent
  partial route.  The existing sign-rank conservation theorem is imported, but
  the file explicitly does not claim a lift to full TC⁰.
-/

namespace PallLean.Paper93.DeepMath.PathB

/-! ## Abstract Boolean functions and circuit-class predicates -/

/-- A finite Boolean function at input length `n`. -/
abbrev BoolFun (n : Nat) := (Fin n -> Bool) -> Bool

/-- A budgeted semantic class, e.g. TC⁰ circuits of a fixed depth/size budget,
NC¹ formulas of a fixed depth/size budget, or width-5 branching programs of a
fixed length budget. -/
def BudgetedClass (n : Nat) := Nat -> BoolFun n -> Prop

/-- `LowerBound C f B` means no budget `< B` object in class `C` computes `f`. -/
def LowerBound {n : Nat} (C : BudgetedClass n) (f : BoolFun n) (B : Nat) : Prop :=
  ∀ s, s < B -> ¬ C s f

/-! ## Observer invariants as proof objects -/

/-- An observer invariant assigns a natural-number capacity/complexity to a
function.  Lower values mean the function is compressible by the observer;
higher values mean the target destroys that observer geometry. -/
structure TCObserverInvariant (n : Nat) where
  Q : BoolFun n -> Nat

/-- A budget bound for an invariant: every computation of budget `s` has
observer capacity at most `bound s`. -/
def ModelPreserves {n : Nat} (I : TCObserverInvariant n)
    (C : BudgetedClass n) (bound : Nat -> Nat) : Prop :=
  ∀ s f, C s f -> I.Q f <= bound s

/-- A target has a genuine observer gap if its invariant value is at least `B`. -/
def TargetGap {n : Nat} (I : TCObserverInvariant n) (f : BoolFun n) (B : Nat) : Prop :=
  B <= I.Q f

/-- The standard conservation theorem: preservation by small models plus a target
gap gives a lower bound. -/
theorem observer_lower_bound {n : Nat} {I : TCObserverInvariant n}
    {C : BudgetedClass n} {f : BoolFun n} {B : Nat} {bound : Nat -> Nat}
    (hpres : ModelPreserves I C bound) (hgap : TargetGap I f B)
    (hsmall : ∀ s, s < B -> bound s < B) : LowerBound C f B := by
  intro s hs hC
  have hlow : I.Q f <= bound s := hpres s f hC
  have hb : bound s < B := hsmall s hs
  exact Nat.not_lt.mpr (Nat.le_trans hgap hlow) hb

/-! ## Natural-proofs obstruction as an explicit interface -/

/-- A property of Boolean functions at length `n`. -/
abbrev FunctionProperty (n : Nat) := BoolFun n -> Prop

/-- Interface for the two Razborov--Rudich naturalness predicates at a fixed input
length.  This file does not define these predicates; a real natural-proofs
formalization must instantiate them with density and truth-table constructivity. -/
structure NaturalProofInterface (n : Nat) where
  Large : FunctionProperty n -> Prop
  Constructive : FunctionProperty n -> Prop

/-- `UsefulAgainstBelow C B P` means `P` separates from class `C` below budget
`B`: it accepts some hard target but rejects every function computed by `C` with
budget `< B`.  This finite-budget form is the one directly used by lower-bound
statements; asymptotic/poly-size variants are obtained by quantifying over a
family of such budgets. -/
def UsefulAgainstBelow {n : Nat} (C : BudgetedClass n) (B : Nat)
    (P : FunctionProperty n) : Prop :=
  (∃ f, P f) ∧ ∀ s, s < B -> ∀ f, C s f -> ¬ P f

/-- `NaturalProofBarrier N C B` packages the Razborov--Rudich obstruction at a
budget threshold: no property that is both large and constructive (according to
interface `N`) can be useful against `C` below `B`.  For TC⁰ this is the PRF
barrier instantiated by PRFs computable in TC⁰ (Naor--Reingold), in the
corresponding asymptotic family. -/
def NaturalProofBarrier {n : Nat} (N : NaturalProofInterface n)
    (C : BudgetedClass n) (B : Nat) : Prop :=
  ∀ P : FunctionProperty n,
    N.Large P -> N.Constructive P -> ¬ UsefulAgainstBelow C B P

/-- The property induced by an observer threshold: functions whose observer
complexity is at least `B`. -/
def ObserverProperty {n : Nat} (I : TCObserverInvariant n) (B : Nat) : FunctionProperty n :=
  fun f => B <= I.Q f

/-- A successful observer lower-bound proof induces a separating property below
budget `B`. -/
theorem observer_property_useful {n : Nat} {I : TCObserverInvariant n}
    {C : BudgetedClass n} {f : BoolFun n} {B : Nat} {bound : Nat -> Nat}
    (hpres : ModelPreserves I C bound)
    (hgap : TargetGap I f B)
    (hsmall : ∀ s, s < B -> bound s < B) :
    UsefulAgainstBelow C B (ObserverProperty I B) := by
  constructor
  · exact ⟨f, hgap⟩
  · intro s hs g hC hg
    have hlow : I.Q g <= bound s := hpres s g hC
    have hb : bound s < B := hsmall s hs
    exact Nat.not_lt.mpr (Nat.le_trans hg hlow) hb

/-- **Observer route constraint.**  Under a supplied natural-proofs barrier, a
successful observer invariant for TC⁰/NC¹ cannot be both large and constructive.
This is the formal version of: the winning invariant must be non-natural. -/
theorem observer_invariant_must_be_nonNatural {n : Nat}
    {N : NaturalProofInterface n}
    {I : TCObserverInvariant n} {C : BudgetedClass n} {f : BoolFun n}
    {B : Nat} {bound : Nat -> Nat}
    (hbarrier : NaturalProofBarrier N C B)
    (hpres : ModelPreserves I C bound)
    (hgap : TargetGap I f B)
    (hsmall : ∀ s, s < B -> bound s < B) :
    ¬ (N.Large (ObserverProperty I B) ∧ N.Constructive (ObserverProperty I B)) := by
  rintro ⟨hlarge, hconstructive⟩
  exact hbarrier (ObserverProperty I B) hlarge hconstructive
    (observer_property_useful hpres hgap hsmall)

/-! ## KW communication: exact NC¹/formula conservation route -/

/-- Interface for the Karchmer--Wigderson theorem at input length `n`.  The cost
and formula-depth predicates are fields, not stubbed definitions. -/
structure KWFormulaInterface (n : Nat) where
  KWCost : BoolFun n -> Nat -> Prop
  FormulaDepth : BoolFun n -> Nat -> Prop
  equivalence : ∀ f : BoolFun n, ∀ d, FormulaDepth f d ↔ KWCost f d

/-- If KW is equivalent to formula depth, then a KW lower bound is exactly a
formula-depth lower bound.  This is why KW is a precise observer language for
NC¹, but not a shortcut around the NC¹ lower-bound problem. -/
theorem formula_lower_bound_iff_KW_lower_bound {n : Nat}
    (K : KWFormulaInterface n) (f : BoolFun n) (B : Nat) :
    (∀ d, d < B -> ¬ K.FormulaDepth f d) ↔
      (∀ d, d < B -> ¬ K.KWCost f d) := by
  constructor
  · intro h d hd hcost
    exact h d hd ((K.equivalence f d).mpr hcost)
  · intro h d hd hform
    exact h d hd ((K.equivalence f d).mp hform)

/-! ## TC⁰/NC¹ route specification -/

/-- The complete specification of what the observer program says a TC⁰/NC¹ proof
must provide: a model-preservation theorem, an explicit target gap, and a proof
that the resulting property escapes the supplied natural-proofs barrier by being
non-natural. -/
structure NonNaturalObserverRoute {n : Nat}
    (N : NaturalProofInterface n) (C : BudgetedClass n) (f : BoolFun n) (B : Nat) where
  I : TCObserverInvariant n
  bound : Nat -> Nat
  preserves : ModelPreserves I C bound
  target_gap : TargetGap I f B
  small_budget_gap : ∀ s, s < B -> bound s < B
  non_natural : ¬ (N.Large (ObserverProperty I B) ∧ N.Constructive (ObserverProperty I B))

/-- Under a natural-proofs barrier, preservation + target gap automatically forces
the non-natural obligation for any successful route. -/
def nonNaturalObserverRoute_of_barrier {n : Nat}
    {N : NaturalProofInterface n} {C : BudgetedClass n} {f : BoolFun n} {B : Nat}
    (hbarrier : NaturalProofBarrier N C B)
    (I : TCObserverInvariant n) (bound : Nat -> Nat)
    (hpres : ModelPreserves I C bound)
    (hgap : TargetGap I f B)
    (hsmall : ∀ s, s < B -> bound s < B) :
    NonNaturalObserverRoute N C f B :=
  { I := I
    bound := bound
    preserves := hpres
    target_gap := hgap
    small_budget_gap := hsmall
    non_natural := observer_invariant_must_be_nonNatural hbarrier hpres hgap hsmall }

/-- Any completed non-natural observer route yields the advertised lower bound. -/
theorem lower_bound_of_nonNaturalObserverRoute {n : Nat}
    {N : NaturalProofInterface n} {C : BudgetedClass n} {f : BoolFun n} {B : Nat}
    (R : NonNaturalObserverRoute N C f B) : LowerBound C f B :=
  observer_lower_bound R.preserves R.target_gap R.small_budget_gap

/-! ## Sign-rank is the honest partial threshold route -/

/-- Sign-rank already supplies the conservation no-go for depth-2 threshold/UPP:
a lower bound in the sign-rank shape plus a bridge from a budgeted model to a
low-dimensional sign factorization rules out any budget whose dimension bound
falls below the sign-rank lower bound.  This theorem is just a renamed export of
the sign-rank rung, making explicit that it is a depth-2 threshold route, not a
full TC⁰ route. -/
theorem signRank_depth2_threshold_route {m n : Nat} {M : Fin m -> Fin n -> Bool}
    {B : Nat} (Compute : Nat -> Prop) (bound : Nat -> Nat)
    (hF : ForsterLowerBound M B)
    (hbridge : ∀ s, Compute s -> HasSignRankLE M (bound s))
    {s : Nat} (hs : Compute s) (hsmall : bound s < B) : False :=
  no_small_depth2 Compute bound hF hbridge hs hsmall

/-! ## Kernel trace -/

#print axioms observer_lower_bound
#print axioms observer_invariant_must_be_nonNatural
#print axioms formula_lower_bound_iff_KW_lower_bound
#print axioms nonNaturalObserverRoute_of_barrier
#print axioms lower_bound_of_nonNaturalObserverRoute
#print axioms signRank_depth2_threshold_route

end PallLean.Paper93.DeepMath.PathB
