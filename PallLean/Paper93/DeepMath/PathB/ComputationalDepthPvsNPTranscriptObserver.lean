import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDynamicSPDP

/-!
# P-vs-NP dynamic transcript observer — fooling-set lower-bound schema

This file is the next H4 step after `ComputationalDepthDynamicSPDP.lean`.

The previous files proved:

* static residual SAT truth is only a Boolean boundary and cannot be H4;
* dynamic transcripts can distinguish `2^m` branches;
* polynomial boundary + exponential distinction gives a contradiction.

This file formalizes the standard lower-bound pattern needed next:

```text
hard/fooling residual family indexed by 2^m branches
+ observer correctness/soundness on the family
+ labels distinguish the branches
------------------------------------------------
observer has at least 2^m boundary states
```

This is **not** `P ≠ NP`: the missing future theorem is to instantiate `FoolingResidualFamily` with a genuine SAT/search
family and prove the correctness premise for transcript observers induced by P-time SAT solvers.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPTranscriptObserver

open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.DynamicSPDP
open SATDepthMachine

/-- A residual SAT/search instance: a formula together with a current prefix. -/
structure ResidualInstance where
  φ : CNF
  pref : RawAssignment

/-- A dynamic transcript/state observer over residual instances. -/
abbrev TranscriptObserver (α : Type) := ResidualInstance → α

/-- A fooling residual family indexed by all `m`-bit branch labels.  The `label` field is the semantic/search feature
that a correct observer must preserve.  In the strongest toy case, the label is the branch itself. -/
structure FoolingResidualFamily (m : ℕ) where
  instanceOf : Assignment m → ResidualInstance
  label : Assignment m → Assignment m
  label_injective : Function.Injective label

/-- The strongest/canonical fooling labels: the label of a branch is the branch itself. -/
def identityFoolingFamily (m : ℕ) (inst : Assignment m → ResidualInstance) : FoolingResidualFamily m where
  instanceOf := inst
  label := id
  label_injective := by
    intro a b h
    exact h

/-- Observer soundness on a fooling family: equal transcript states cannot identify branches with different semantic
labels.  This is the dynamic/fooling-set analogue of residual truth-soundness, but with richer labels than Bool. -/
def SoundOnFoolingFamily {m : ℕ} {α : Type}
    (obs : TranscriptObserver α) (fam : FoolingResidualFamily m) : Prop :=
  ∀ a b : Assignment m,
    obs (fam.instanceOf a) = obs (fam.instanceOf b) → fam.label a = fam.label b

/-- The observer induced on the `2^m` indexed fooling branches. -/
def branchTranscriptObserver {m : ℕ} {α : Type}
    (obs : TranscriptObserver α) (fam : FoolingResidualFamily m) : BoundaryObserver m α :=
  fun a => obs (fam.instanceOf a)

/-- Soundness on a fooling family forces injectivity of the branch transcript observer. -/
theorem branchTranscript_injective_of_sound {m : ℕ} {α : Type}
    (obs : TranscriptObserver α) (fam : FoolingResidualFamily m)
    (hsound : SoundOnFoolingFamily obs fam) :
    Function.Injective (branchTranscriptObserver obs fam) := by
  intro a b h
  have hlabel : fam.label a = fam.label b := hsound a b h
  exact fam.label_injective hlabel

/-- Fooling-set lower bound: any sound transcript observer for an `m`-bit fooling family has at least `2^m` boundary
states. -/
theorem transcript_boundary_card_ge_exp_of_fooling {m : ℕ} {α : Type} [Fintype α]
    (obs : TranscriptObserver α) (fam : FoolingResidualFamily m)
    (hsound : SoundOnFoolingFamily obs fam) :
    2 ^ m ≤ Fintype.card α := by
  exact boundary_card_ge_exp
    (branchTranscriptObserver obs fam)
    (branchTranscript_injective_of_sound obs fam hsound)

/-- Polynomial transcript boundary contradicts a sound `2^m` fooling family once the exponential gap opens. -/
theorem transcript_fooling_contradicts_poly_boundary {m k : ℕ} {α : Type} [Fintype α]
    (obs : TranscriptObserver α) (fam : FoolingResidualFamily m)
    (hsound : SoundOnFoolingFamily obs fam)
    (hpoly : Fintype.card α ≤ m ^ k) (hgap : m ^ k < 2 ^ m) : False := by
  exact dynamic_full_distinction_contradicts_poly_boundary
    (branchTranscriptObserver obs fam)
    (branchTranscript_injective_of_sound obs fam hsound)
    hpoly hgap

/-- Contrapositive form: a polynomial-size observer below the exponential gap must fail soundness on every such fooling
family. -/
theorem poly_transcript_boundary_fails_fooling_soundness {m k : ℕ} {α : Type} [Fintype α]
    (obs : TranscriptObserver α) (fam : FoolingResidualFamily m)
    (hpoly : Fintype.card α ≤ m ^ k) (hgap : m ^ k < 2 ^ m) :
    ¬ SoundOnFoolingFamily obs fam := by
  intro hsound
  exact transcript_fooling_contradicts_poly_boundary obs fam hsound hpoly hgap

/-- Identity-labelled fooling families are the direct transcript version of the full-branch dynamic observer. -/
theorem identity_fooling_sound_iff_branch_injective {m : ℕ} {α : Type}
    (obs : TranscriptObserver α) (inst : Assignment m → ResidualInstance) :
    SoundOnFoolingFamily obs (identityFoolingFamily m inst) ↔
      Function.Injective (fun a : Assignment m => obs (inst a)) := by
  constructor
  · intro hsound a b h
    exact hsound a b h
  · intro hinj a b h
    exact hinj h

/-!
Current H4 status:

```text
Dynamic/fooling schema PROVED:
  fooling residual family with 2^m distinguishable labels
  + observer soundness on that family
  ⇒ observer boundary has ≥ 2^m states.

Polynomial contradiction PROVED:
  + |boundary| ≤ m^k and m^k < 2^m
  ⇒ False.
```

Remaining genuine P-vs-NP work:

1. construct a SAT/search residual family `fam : FoolingResidualFamily m`;
2. prove that transcript observers induced by hypothetical P-time SAT solvers are sound on that family;
3. prove those induced transcript observers have polynomial boundary.

That is the dynamic H4 bridge, now reduced to concrete instantiation obligations.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPTranscriptObserver

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPTranscriptObserver.branchTranscript_injective_of_sound
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPTranscriptObserver.transcript_boundary_card_ge_exp_of_fooling
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPTranscriptObserver.transcript_fooling_contradicts_poly_boundary
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPTranscriptObserver.poly_transcript_boundary_fails_fooling_soundness
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPTranscriptObserver.identity_fooling_sound_iff_branch_injective
