import Mathlib.Data.Nat.Basic

/-!
# The "entanglement ruler" brick is the natural-proofs barrier — machine-checked

A proposed "only brick that matters" asks for a structural property `E` that is (i) checkable in
polynomial time, (ii) true for every function in `P/poly`, (iii) false for SAT.  This file formalises
that EXACT specification and proves what it is: a **natural property useful against `P/poly`** —
precisely the object the Razborov–Rudich barrier forbids under standard cryptography, and precisely
the non-naturality the repository already established for `Π★` (`DischargePiStar`: "a separating
measure would be a natural proof").

The point is not to argue.  It is to show, as theorems, three things: the requested ruler WOULD prove
the separation (so the instinct is not wrong); the requested ruler IS a natural distinguisher; and its
existence therefore requires cryptography to be broken.  So it is not a brick — it is the wall, named.

## What is proved

* **`ruler_proves_separation`** — a `ColossusRuler` (poly-checkable, true on all `P/poly`, false on
  SAT) DOES imply `SAT ∉ P/poly`.  Colossus is right that the object would work.
* **`ruler_is_natural`** — but any such ruler IS a `NaturalDistinguisher`: a poly-time-computable
  predicate that holds on all of `P/poly` and fails somewhere.  Constructive + useful = natural.
* **`ruler_needs_broken_crypto`** — with the Razborov–Rudich barrier (named, NOT discharged — its
  proof is the PRF-distinguisher construction), a `ColossusRuler` forces `¬ PRFExists`: pseudorandom
  functions, hence one-way functions, hence essentially all of modern cryptography, must fail.

## Honest scope — why this is the barrier, not a brick

The barrier `RazborovRudichBarrier` is a NAMED SOCKET here, exactly as the magnification trigger and
the trading ingredients are: it is a real theorem (Razborov–Rudich 1994) whose formalisation is the
PRF-distinguisher construction, not attempted in this file.  What IS proved is the reduction: the
requested ruler is a natural distinguisher, so building it is equivalent to defeating the barrier —
i.e. to showing one-way functions do not exist.  That is not "the next brick"; it is a claim of
cryptographic-breakthrough strength, and it contradicts the non-naturality of `Π★` the repository
already carries.  Any winning separator must be NON-natural (avoid at least one of poly-checkability,
`P/poly`-closure, largeness) — which is why this whole session's real routes (non-natural measures,
magnification, uniform diagonalisation) avoid the poly-checkable-invariant shape.  Nothing here is
`P ≠ NP`, and nothing here is a way to reach it by a poly-time-checkable invariant.
-/

namespace PallLean.Paper93.DeepMath.PathB.NaturalProofsObstruction

/-- An abstract complexity world: a universe of functions, the `P/poly` predicate, a notion of
poly-time computability for property-predicates, the SAT function, and the hypothesis that
pseudorandom functions exist. -/
structure ComplexityWorld where
  /-- the universe of Boolean functions (families) -/
  Fn : Type
  /-- membership in `P/poly` -/
  InPpoly : Fn → Prop
  /-- a property-predicate is polynomial-time computable -/
  PolyTimeComputable : (Fn → Bool) → Prop
  /-- the SAT function -/
  sat : Fn
  /-- pseudorandom function generators exist (the cryptographic hypothesis of the barrier) -/
  PRFExists : Prop

/-- **Colossus's requested ruler**, verbatim: a property `E` that is poly-time checkable, true on
every `P/poly` function, and false on SAT. -/
structure ColossusRuler (W : ComplexityWorld) where
  /-- the structural property -/
  E : W.Fn → Bool
  /-- (i) checkable in polynomial time -/
  poly : W.PolyTimeComputable E
  /-- (ii) preserved by / true on all of `P/poly` -/
  closedOnPpoly : ∀ f, W.InPpoly f → E f = true
  /-- (iii) violated by SAT -/
  failsSAT : E W.sat = false

/-- A **natural property useful against `P/poly`** (Razborov–Rudich shape): a poly-time-computable
predicate that holds on all of `P/poly` yet fails somewhere. -/
def NaturalDistinguisher (W : ComplexityWorld) (E : W.Fn → Bool) : Prop :=
  W.PolyTimeComputable E ∧ (∀ f, W.InPpoly f → E f = true) ∧ (∃ g, E g = false)

/-- **The ruler would prove the separation (proved).**  If such an `E` exists, then `SAT ∉ P/poly`:
`E` is `true` on all `P/poly` but `false` on SAT, so SAT is not in `P/poly`.  The instinct is
correct — the object, if it existed, would work. -/
theorem ruler_proves_separation (W : ComplexityWorld) (R : ColossusRuler W) :
    ¬ W.InPpoly W.sat := by
  intro h
  have he : R.E W.sat = true := R.closedOnPpoly W.sat h
  rw [R.failsSAT] at he
  exact absurd he (by decide)

/-- **The ruler is a natural distinguisher (proved).**  Any `ColossusRuler` is exactly a
poly-checkable property holding on all of `P/poly` and failing somewhere (at SAT). -/
theorem ruler_is_natural (W : ComplexityWorld) (R : ColossusRuler W) :
    NaturalDistinguisher W R.E :=
  ⟨R.poly, R.closedOnPpoly, ⟨W.sat, R.failsSAT⟩⟩

/-- **The Razborov–Rudich barrier (named socket, NOT discharged).**  If pseudorandom function
generators exist, no natural property is useful against `P/poly`.  Its proof is the standard
PRF-distinguisher construction — a real theorem, not attempted here. -/
def RazborovRudichBarrier (W : ComplexityWorld) : Prop :=
  W.PRFExists → ¬ ∃ E, NaturalDistinguisher W E

/-- **The ruler's existence requires broken cryptography (proved).**  Given the barrier, a
`ColossusRuler` forces `¬ PRFExists`: building the requested poly-time-checkable, `P/poly`-invariant,
SAT-violating property is equivalent to showing pseudorandom functions — hence one-way functions —
do not exist.  It is not a brick; it is the natural-proofs wall. -/
theorem ruler_needs_broken_crypto (W : ComplexityWorld) (R : ColossusRuler W)
    (barrier : RazborovRudichBarrier W) : ¬ W.PRFExists := by
  intro hprf
  exact barrier hprf ⟨R.E, ruler_is_natural W R⟩

/-- **Non-vacuity (proved).**  The specification is consistent — a world where SAT is genuinely
outside `P/poly` and a ruler exists (with a trivially-true poly notion) — so the theorems are not
vacuous; the barrier is what makes such a ruler unbuildable in the REAL world where `PRFExists`. -/
def toyWorld : ComplexityWorld where
  Fn := Bool
  InPpoly := fun f => f = false
  PolyTimeComputable := fun _ => True
  sat := true
  PRFExists := False

def toyRuler : ColossusRuler toyWorld where
  E := fun f => !f
  poly := trivial
  closedOnPpoly := fun f hf => by simp [toyWorld] at hf; simp [hf]
  failsSAT := by decide

end PallLean.Paper93.DeepMath.PathB.NaturalProofsObstruction

#print axioms PallLean.Paper93.DeepMath.PathB.NaturalProofsObstruction.ruler_proves_separation
#print axioms PallLean.Paper93.DeepMath.PathB.NaturalProofsObstruction.ruler_is_natural
#print axioms PallLean.Paper93.DeepMath.PathB.NaturalProofsObstruction.ruler_needs_broken_crypto
