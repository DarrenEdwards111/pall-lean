import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUCRDObserverNaturalityAudit

/-!
# UCRD legal-loop transport audit

The observer-naturality audit leaves a weaker, temporal possibility: require
compatibility only along legal context transitions, transport operational
meaning along a path, and charge disagreement when a loop returns to its
starting context.

The musical intuition is a repeated motif: meaning is carried through ordered
stages, and the invariant asks whether returning to the opening context restores
the opening state.  This file formalizes that idea as a four-transition loop
with explicit work.

The calibration is again exact.  Nontrivial loop holonomy can occur with four
constant-cost transitions.  Repeating any fixed finite loop has polynomial
total work, and in the concrete Boolean example two repetitions cancel the
holonomy completely.  Hence neither nonzero holonomy nor repeated legal
transport by itself forces superpolynomial reconstruction.

A viable SAT invariant must therefore prove scale growth: the number or
irreversible incompatibility of independent loops must grow faster than any
polynomial while resisting cancellation and shared transport.  That is an
additional SAT-specific lower-bound theorem, not a consequence of having a
legal loop.
-/

namespace PallLean.Paper93.DeepMath.PathB.UCRDLegalLoopTransportAudit

open SATDepthMachine

universe u v

/-- Four certified legal transitions returning to the starting context, with
state transport and explicit work on every transition. -/
structure LegalTransportLoop (Context : Type u) (State : Type v) where
  legal : Context → Context → Prop
  c0 : Context
  c1 : Context
  c2 : Context
  c3 : Context
  legal01 : legal c0 c1
  legal12 : legal c1 c2
  legal23 : legal c2 c3
  legal30 : legal c3 c0
  transport01 : State → State
  transport12 : State → State
  transport23 : State → State
  transport30 : State → State
  cost01 : Nat
  cost12 : Nat
  cost23 : Nat
  cost30 : Nat

/-- Operational meaning after one complete legal return. -/
def LegalTransportLoop.holonomy
    {Context : Type u} {State : Type v}
    (L : LegalTransportLoop Context State) : State → State :=
  fun s ↦ L.transport30 (L.transport23 (L.transport12 (L.transport01 s)))

/-- Total work charged to one traversal. -/
def LegalTransportLoop.loopWork
    {Context : Type u} {State : Type v}
    (L : LegalTransportLoop Context State) : Nat :=
  L.cost01 + L.cost12 + L.cost23 + L.cost30

/-- A flat loop restores every operational state. -/
def LegalTransportLoop.Flat
    {Context : Type u} {State : Type v}
    (L : LegalTransportLoop Context State) : Prop :=
  ∀ s, L.holonomy s = s

/-- Iterate the transported motif through observer-time. -/
def LegalTransportLoop.iterateHolonomy
    {Context : Type u} {State : Type v}
    (L : LegalTransportLoop Context State) : Nat → State → State
  | 0, s => s
  | n + 1, s => L.iterateHolonomy n (L.holonomy s)

/-- Work of `r` complete traversals. -/
def LegalTransportLoop.repeatedWork
    {Context : Type u} {State : Type v}
    (L : LegalTransportLoop Context State) (r : Nat) : Nat :=
  r * L.loopWork

/-- Repeating any fixed finite loop has a polynomial work budget. -/
theorem repeatedWork_isPolynomialBudget
    {Context : Type u} {State : Type v}
    (L : LegalTransportLoop Context State) :
    IsPolynomialBudget L.repeatedWork := by
  refine ⟨1, L.loopWork, ?_⟩
  intro n
  simpa [LegalTransportLoop.repeatedWork, pow_one, Nat.mul_comm] using
    Nat.mul_le_mul_left L.loopWork (Nat.le_succ n)

/-! ## A four-beat Boolean motif with cheap holonomy -/

inductive ExperienceContext
  | opening | rising | turning | returning
  deriving DecidableEq

def experienceLegal : ExperienceContext → ExperienceContext → Prop
  | .opening, .rising => True
  | .rising, .turning => True
  | .turning, .returning => True
  | .returning, .opening => True
  | _, _ => False

/-- Three transitions preserve the motif; the return changes its polarity. -/
def experienceLoop : LegalTransportLoop ExperienceContext Bool where
  legal := experienceLegal
  c0 := .opening
  c1 := .rising
  c2 := .turning
  c3 := .returning
  legal01 := by trivial
  legal12 := by trivial
  legal23 := by trivial
  legal30 := by trivial
  transport01 := id
  transport12 := id
  transport23 := id
  transport30 := Bool.not
  cost01 := 1
  cost12 := 1
  cost23 := 1
  cost30 := 1

theorem experience_holonomy_eq_not (s : Bool) :
    experienceLoop.holonomy s = !s := by
  rfl

theorem experience_loopWork_eq_four :
    experienceLoop.loopWork = 4 := by
  rfl

theorem experience_not_flat : ¬ experienceLoop.Flat := by
  intro hflat
  have h := hflat false
  change true = false at h
  contradiction

/-- Repeating the curved loop twice restores the initial Boolean meaning. -/
theorem experience_twoLoops_restore (s : Bool) :
    experienceLoop.iterateHolonomy 2 s = s := by
  cases s <;> rfl

/-- The non-flat loop nevertheless has polynomial cumulative transport work. -/
theorem experience_repeatedWork_polynomial :
    IsPolynomialBudget experienceLoop.repeatedWork :=
  repeatedWork_isPolynomialBudget experienceLoop

/-- Nonzero legal-loop holonomy is compatible with constant per-loop work,
injective transports, cancellation, and polynomial repeated dynamics. -/
theorem cheap_cancelling_holonomy_exists :
    ∃ L : LegalTransportLoop ExperienceContext Bool,
      L.loopWork = 4 ∧
      ¬ L.Flat ∧
      (∀ s, L.iterateHolonomy 2 s = s) ∧
      IsPolynomialBudget L.repeatedWork := by
  exact ⟨experienceLoop, experience_loopWork_eq_four,
    experience_not_flat, experience_twoLoops_restore,
    experience_repeatedWork_polynomial⟩

end PallLean.Paper93.DeepMath.PathB.UCRDLegalLoopTransportAudit

#print axioms PallLean.Paper93.DeepMath.PathB.UCRDLegalLoopTransportAudit.repeatedWork_isPolynomialBudget
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDLegalLoopTransportAudit.experience_not_flat
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDLegalLoopTransportAudit.experience_twoLoops_restore
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDLegalLoopTransportAudit.cheap_cancelling_holonomy_exists
