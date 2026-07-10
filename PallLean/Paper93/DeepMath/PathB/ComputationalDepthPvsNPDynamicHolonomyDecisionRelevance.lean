import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPNFrameDynamicMERAHolonomy

/-!
# Dynamic holonomy: the decision-relevance bridge

The dynamic MERA theorem proves that exact recovery of `n` independent holonomy bits cannot pass through
a polynomial-state bounded-bond boundary.  The remaining semantic question is why correctness of a SAT
*decision* machine should recover those bits at all.

This file gives the precise non-circular answer available at the semantic level: each holonomy bit must
be represented by a concrete SAT query whose satisfiability equals that bit.  A correct SAT decider then
recovers the whole signature coordinate by coordinate; this correctness-to-label implication is proved,
not assumed.

The file also proves the matching no-go.  Adding exponentially many labels to an NP-hard problem while
letting the decision predicate ignore them preserves hardness, but no decision correctness theorem can
force those irrelevant labels to survive.  Thus "NP-complete family with many labels" is insufficient;
the labels must be *decision-relevant* through a uniform query construction.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyDecisionRelevance

open SATDepthMachine

/-- An `n`-bit task/holonomy signature. -/
abbrev HolonomySignature (n : Nat) := Fin n → Bool

/-- A residual family whose holonomy bits are individually exposed by concrete SAT queries.

For instance `x` and coordinate `i`, `query x i` is satisfiable exactly when bit `i` of `label x` is
true.  `label_surjective` states that all `2^n` signatures occur in the family.

For a non-circular application, `query` must be an explicit syntactic construction independent of any
alleged solver; this structure records its semantic specification. -/
structure SATQueryHolonomyFamily (n : Nat) where
  Instance : Type
  label : Instance → HolonomySignature n
  query : Instance → Fin n → CNF
  query_sat_iff : ∀ x i, Satisfiable (query x i) ↔ label x i = true
  label_surjective : Function.Surjective label

namespace SATQueryHolonomyFamily

/-- The bit-vector returned by applying a decision machine to all coordinate queries. -/
def answers {n : Nat} {U : MachineModel} (F : SATQueryHolonomyFamily n)
    (D : DecisionMachine U) (x : F.Instance) : HolonomySignature n :=
  fun i => U.decisionRun D.code (F.query x i)

/-- **Correctness-to-holonomy transport, derived.**  A SAT-correct decision machine returns exactly
the family's holonomy label on all coordinate queries. -/
theorem answers_eq_label {n : Nat} {U : MachineModel} (F : SATQueryHolonomyFamily n)
    (D : DecisionMachine U) (hD : DecidesSAT U D) (x : F.Instance) :
    F.answers D x = F.label x := by
  funext i
  have hiff : F.answers D x i = true ↔ F.label x i = true :=
    (hD (F.query x i)).trans (F.query_sat_iff x i)
  cases ha : F.answers D x i <;> cases hb : F.label x i <;> simp_all

/-- Since all labels occur, the answer patterns of any SAT-correct decider are surjective onto all
`2^n` holonomy signatures. -/
theorem answers_surjective {n : Nat} {U : MachineModel} (F : SATQueryHolonomyFamily n)
    (D : DecisionMachine U) (hD : DecidesSAT U D) :
    Function.Surjective (F.answers D) := by
  intro target
  obtain ⟨x, hx⟩ := F.label_surjective target
  exact ⟨x, (F.answers_eq_label D hD x).trans hx⟩

/-- Any finite boundary from which the SAT-query answer vector can be decoded must have at least
`2^n` states. -/
theorem boundary_card_ge_two_pow_of_decodes_answers
    {n : Nat} {U : MachineModel} (F : SATQueryHolonomyFamily n)
    (D : DecisionMachine U) (hD : DecidesSAT U D)
    {Boundary : Type} [Fintype Boundary]
    (observe : F.Instance → Boundary) (decode : Boundary → HolonomySignature n)
    (hdecode : ∀ x, decode (observe x) = F.answers D x) :
    2 ^ n ≤ Fintype.card Boundary := by
  have hsurj : Function.Surjective decode := by
    intro target
    obtain ⟨x, hx⟩ := F.answers_surjective D hD target
    exact ⟨observe x, (hdecode x).trans hx⟩
  have hcard := Fintype.card_le_of_surjective decode hsurj
  simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hcard

/-- A polynomial-state boundary cannot decode all decision-relevant holonomy answers once the
exponential gap opens. -/
theorem no_polyBoundary_decodes_answers
    {n k : Nat} {U : MachineModel} (F : SATQueryHolonomyFamily n)
    (D : DecisionMachine U) (hD : DecidesSAT U D)
    {Boundary : Type} [Fintype Boundary]
    (observe : F.Instance → Boundary) (decode : Boundary → HolonomySignature n)
    (hpoly : Fintype.card Boundary ≤ n ^ k) (hgap : n ^ k < 2 ^ n) :
    ¬ (∀ x, decode (observe x) = F.answers D x) := by
  intro hdecode
  have hlower := F.boundary_card_ge_two_pow_of_decodes_answers D hD observe decode hdecode
  omega

end SATQueryHolonomyFamily

/-! ## No-go: hardness with irrelevant labels -/

/-- A simple many-one reduction predicate between abstract decision problems. -/
def ManyOneReduces {X Y : Type} (P : X → Prop) (Q : Y → Prop) : Prop :=
  ∃ reduce : X → Y, ∀ x, P x ↔ Q (reduce x)

/-- Attach an arbitrary `n`-bit label to an instance while letting the decision predicate ignore it. -/
def LabelIgnoredLift {X : Type} (base : X → Prop) {n : Nat} :
    (X × HolonomySignature n) → Prop :=
  fun input => base input.1

/-- Any reduction to the base problem lifts to the label-ignored problem by attaching the all-zero
label.  In particular, abstract NP-hardness is preserved by this padding. -/
theorem reduction_lifts_to_labelIgnored
    {A X : Type} (problem : A → Prop) (base : X → Prop) {n : Nat}
    (hreduce : ManyOneReduces problem base) :
    ManyOneReduces problem (LabelIgnoredLift base (n := n)) := by
  obtain ⟨reduce, hreduce⟩ := hreduce
  refine ⟨fun x => (reduce x, fun _ => false), ?_⟩
  intro x
  exact hreduce x

/-- A correct decider for the base problem lifts by ignoring the added holonomy label. -/
theorem decider_ignores_labels
    {X : Type} (base : X → Prop) {n : Nat}
    (decideBase : X → Bool)
    (hcorrect : ∀ x, decideBase x = true ↔ base x) :
    ∀ input : X × HolonomySignature n,
      decideBase input.1 = true ↔ LabelIgnoredLift base input := by
  intro input
  exact hcorrect input.1

/-- All labels on the same base instance have exactly the same decision value.  Therefore decision
correctness alone contains no information from which to recover the attached label. -/
theorem labelIgnored_decision_constant
    {X : Type} (decideBase : X → Bool) {n : Nat}
    (x : X) (left right : HolonomySignature n) :
    decideBase (x, left).1 = decideBase (x, right).1 := rfl

/-- For at least one label bit, no decoder of the single label-ignored decision value can recover every
possible attached signature. -/
theorem no_decisionBit_decoder_for_ignored_labels
    {X : Type} (decideBase : X → Bool) (x : X) {n : Nat} (hn : 1 ≤ n) :
    ¬ ∃ decode : Bool → HolonomySignature n,
      ∀ label, decode (decideBase x) = label := by
  rintro ⟨decode, hdecode⟩
  let zero : HolonomySignature n := fun _ => false
  let oneAtZero : HolonomySignature n := fun i => decide (i = ⟨0, hn⟩)
  have hzero := hdecode zero
  have hone := hdecode oneAtZero
  have heq : zero = oneAtZero := hzero.symm.trans hone
  have hcoord := congrFun heq ⟨0, hn⟩
  simp [zero, oneAtZero] at hcoord

/-!
## Honest endpoint

`answers_eq_label` is the desired correctness-to-holonomy implication, but only after every bit has
been made semantically decision-relevant by an explicit SAT query.  The ignored-label construction
proves why NP-hardness plus exponentially many labels is not enough: hardness survives even when the
decision problem discards all label information.

The next genuine construction target is therefore precise: build a uniform genuine NP-complete
residual family whose independent holonomy coordinates admit the `query_sat_iff` reductions without
encoding the answers by hand.  Then connect the resulting adaptive SAT-query transcript to the
bounded-MERA dynamic boundary.  Those are the remaining nontrivial bridges.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyDecisionRelevance

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyDecisionRelevance.SATQueryHolonomyFamily.answers_eq_label
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyDecisionRelevance.SATQueryHolonomyFamily.answers_surjective
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyDecisionRelevance.SATQueryHolonomyFamily.boundary_card_ge_two_pow_of_decodes_answers
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyDecisionRelevance.SATQueryHolonomyFamily.no_polyBoundary_decodes_answers
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyDecisionRelevance.reduction_lifts_to_labelIgnored
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyDecisionRelevance.decider_ignores_labels
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyDecisionRelevance.no_decisionBit_decoder_for_ignored_labels
