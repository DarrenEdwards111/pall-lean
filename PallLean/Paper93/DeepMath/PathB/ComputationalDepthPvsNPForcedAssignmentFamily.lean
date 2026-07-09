import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPTranscriptObserver

/-!
# Forced-assignment SAT family — concrete dynamic H4 instantiation

This file instantiates the dynamic transcript/fooling-set schema with a concrete SAT-shaped family: for every `m`-bit
assignment `a`, build a CNF whose unit clauses force exactly those bits.

The theorem proved here is intentionally precise:

```text
forced-assignment family indexed by 2^m labels
+ transcript observer whose state decodes the forced label correctly
⇒ boundary has at least 2^m states
```

This is **not** `P ≠ NP`.  The family is easy SAT.  Its purpose is to prove that the dynamic H4 machinery now works on a
real CNF residual family and to isolate the next hard requirement: a *hard* SAT/search family with the same kind of
forced transcript-label soundness for P-time solvers.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPForcedAssignmentFamily

open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.PvsNPTranscriptObserver
open SATDepthMachine

/-- Literal forcing variable `i` to value `b`. -/
def forcedLit (i : ℕ) (b : Bool) : Lit where
  var := i
  pol := if b then Polarity.pos else Polarity.neg

/-- Unit clause forcing variable `i` to value `b`. -/
def forcedClause (i : ℕ) (b : Bool) : Clause :=
  [forcedLit i b]

/-- CNF with one unit clause for each bit of `a`. -/
def forcedAssignmentCNF {m : ℕ} (a : Assignment m) : CNF where
  vars := m
  clauses := List.ofFn (fun i : Fin m => forcedClause i.val (a i))

/-- The residual instance associated to the forced assignment.  Prefix is empty: the formula itself carries the forced
label. -/
def forcedResidualInstance {m : ℕ} (a : Assignment m) : ResidualInstance where
  φ := forcedAssignmentCNF a
  pref := []

/-- The forced-assignment fooling family: semantic/search label is the assignment that the CNF forces. -/
def forcedAssignmentFamily (m : ℕ) : FoolingResidualFamily m :=
  identityFoolingFamily m (forcedResidualInstance (m := m))

/-- A decoder from transcript/boundary states into assignment labels. -/
abbrev AssignmentDecoder (m : ℕ) (α : Type) := α → Option (Assignment m)

/-- The observer decodes the forced label correctly on the forced-assignment family. -/
def DecodesForcedLabels {m : ℕ} {α : Type}
    (obs : TranscriptObserver α) (dec : AssignmentDecoder m α) : Prop :=
  ∀ a : Assignment m, dec (obs (forcedResidualInstance a)) = some a

/-- Correct decoding of forced labels implies fooling-family soundness. -/
theorem soundOnForcedFamily_of_decodes {m : ℕ} {α : Type}
    (obs : TranscriptObserver α) (dec : AssignmentDecoder m α)
    (hdec : DecodesForcedLabels obs dec) :
    SoundOnFoolingFamily obs (forcedAssignmentFamily m) := by
  intro a b hobs
  have ha : dec (obs (forcedResidualInstance a)) = some a := hdec a
  have hb : dec (obs (forcedResidualInstance b)) = some b := hdec b
  have hobs' : obs (forcedResidualInstance a) = obs (forcedResidualInstance b) := by
    simpa [forcedAssignmentFamily, identityFoolingFamily] using hobs
  have hs : some a = some b := by
    calc
      some a = dec (obs (forcedResidualInstance a)) := ha.symm
      _ = dec (obs (forcedResidualInstance b)) := by rw [hobs']
      _ = some b := hb
  exact Option.some.inj hs

/-- Concrete forced-family lower bound: any finite transcript boundary that decodes the forced labels correctly has at
least `2^m` states. -/
theorem forced_family_boundary_card_ge_exp {m : ℕ} {α : Type} [Fintype α]
    (obs : TranscriptObserver α) (dec : AssignmentDecoder m α)
    (hdec : DecodesForcedLabels obs dec) :
    2 ^ m ≤ Fintype.card α := by
  exact transcript_boundary_card_ge_exp_of_fooling
    obs (forcedAssignmentFamily m) (soundOnForcedFamily_of_decodes obs dec hdec)

/-- Polynomial transcript boundary cannot decode all forced labels once the exponential gap opens. -/
theorem forced_family_contradicts_poly_boundary {m k : ℕ} {α : Type} [Fintype α]
    (obs : TranscriptObserver α) (dec : AssignmentDecoder m α)
    (hdec : DecodesForcedLabels obs dec)
    (hpoly : Fintype.card α ≤ m ^ k) (hgap : m ^ k < 2 ^ m) : False := by
  exact transcript_fooling_contradicts_poly_boundary
    obs (forcedAssignmentFamily m) (soundOnForcedFamily_of_decodes obs dec hdec) hpoly hgap

/-- Contrapositive: a polynomial-size boundary below the exponential gap must fail to decode at least one forced label. -/
theorem poly_boundary_fails_forced_label_decoding {m k : ℕ} {α : Type} [Fintype α]
    (obs : TranscriptObserver α) (dec : AssignmentDecoder m α)
    (hpoly : Fintype.card α ≤ m ^ k) (hgap : m ^ k < 2 ^ m) :
    ¬ DecodesForcedLabels obs dec := by
  intro hdec
  exact forced_family_contradicts_poly_boundary obs dec hdec hpoly hgap

/-- A direct label observer for the family index, used to show the schema's tightness without parsing CNF syntax. -/
def forcedIndexObserver {m : ℕ} : Assignment m → Assignment m := id

/-- The direct forced-index observer is injective. -/
theorem forcedIndexObserver_injective (m : ℕ) :
    Function.Injective (forcedIndexObserver (m := m)) := by
  intro a b h
  exact h

/-!
Current status:

```text
Concrete SAT-shaped family built:
  forcedAssignmentCNF a = unit clauses pinning every bit of a.

Lower bound proved:
  any transcript observer whose finite state decodes every forced label needs ≥ 2^m states.
```

This is intentionally an easy family, so it does not prove `P ≠ NP`.  It proves that the dynamic H4/fooling machinery
correctly fires on a real CNF residual family.  The live next target is replacing `forcedAssignmentCNF` by a hard
SAT/search family where correctness of a P-time solver forces an analogous decoded label/transcript condition.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPForcedAssignmentFamily

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPForcedAssignmentFamily.soundOnForcedFamily_of_decodes
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPForcedAssignmentFamily.forced_family_boundary_card_ge_exp
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPForcedAssignmentFamily.forced_family_contradicts_poly_boundary
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPForcedAssignmentFamily.poly_boundary_fails_forced_label_decoding
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPForcedAssignmentFamily.forcedIndexObserver_injective
