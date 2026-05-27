import PallLean.Paper93.DeepMath.PathC.PiPlusProjectedPWindowPivotGuardrail

/-!
# Rotational-encoder kill test (Path C)

This file formalizes the quick test for any proposed rotational encoder `RotEnc`.

If `RotEnc` is only basis transport (i.e. it gives back-and-forth transport of the
same projected pivot contradiction package), then it does not create a new route:
it is equivalent to the existing Path C no-decider endpoint.

So a rotation helps only if it enforces genuinely new semantic constraints that
*break* this equivalence (for example by restricting admissible deciders/encodings
in a non-transport way).
-/

namespace PallLean.Paper93.DeepMath.PathC

open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- Data for a candidate rotational encoder at fixed `(M,n)`.

`toRot` and `toBase` are the kill-test levers:
if both exist as plain package transport maps, rotation is only representational. -/
structure RotEncPivotTransport
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gaugeBase gaugeRot : ProjectedPivotGaugeMap M n hn2 htb hns) where
  toRot :
    ProjectedPWindowPivotData M n hn2 htb hns gaugeBase ->
      ProjectedPWindowPivotData M n hn2 htb hns gaugeRot
  toBase :
    ProjectedPWindowPivotData M n hn2 htb hns gaugeRot ->
      ProjectedPWindowPivotData M n hn2 htb hns gaugeBase

/-- Local large-`n` endpoint for the base gauge. -/
def RotEncBaseNoDecider
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gaugeBase : ProjectedPivotGaugeMap M n hn2 htb hns) : Prop :=
  ∀ D : ProjectedPWindowPivotData M n hn2 htb hns gaugeBase,
    ¬ DecidesSAT M

/-- Local large-`n` endpoint for the rotated gauge. -/
def RotEncRotNoDecider
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gaugeRot : ProjectedPivotGaugeMap M n hn2 htb hns) : Prop :=
  ∀ D : ProjectedPWindowPivotData M n hn2 htb hns gaugeRot,
    ¬ DecidesSAT M

/-- Base endpoint is already implied by each base contradiction package. -/
theorem rotEncBaseNoDecider_of_basePivotData
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gaugeBase : ProjectedPivotGaugeMap M n hn2 htb hns) :
    RotEncBaseNoDecider M n hn hn2 htb hns gaugeBase := by
  intro D
  exact no_decidesSAT_of_projectedPWindowPivotData_guardrail
    M n hn hn2 htb hns gaugeBase D

/-- Rotated endpoint is already implied by each rotated contradiction package. -/
theorem rotEncRotNoDecider_of_rotPivotData
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gaugeRot : ProjectedPivotGaugeMap M n hn2 htb hns) :
    RotEncRotNoDecider M n hn hn2 htb hns gaugeRot := by
  intro D
  exact no_decidesSAT_of_projectedPWindowPivotData_guardrail
    M n hn hn2 htb hns gaugeRot D

/-- Kill-test theorem:
if rotation is just package transport in both directions, the rotated endpoint is
logically equivalent to the base endpoint. No new separation content is gained. -/
theorem rotEnc_killTest_equiv_if_bidirectional_transport
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gaugeBase gaugeRot : ProjectedPivotGaugeMap M n hn2 htb hns)
    (T : RotEncPivotTransport M n hn2 htb hns gaugeBase gaugeRot) :
    RotEncBaseNoDecider M n hn hn2 htb hns gaugeBase ↔
      RotEncRotNoDecider M n hn hn2 htb hns gaugeRot := by
  constructor
  · intro hBase Drot
    exact hBase (T.toBase Drot)
  · intro hRot Dbase
    exact hRot (T.toRot Dbase)

/-- Operational verdict:
for a viable new rotation route, you must *fail* this transport equivalence by
adding semantic constraints not expressible as bidirectional package transport. -/
def RotEncNeedsNewSemantics
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (_gaugeBase gaugeRot : ProjectedPivotGaugeMap M n hn2 htb hns) : Prop :=
  True

/-! ## Axiom audit anchors -/

#print axioms rotEncBaseNoDecider_of_basePivotData
#print axioms rotEncRotNoDecider_of_rotPivotData
#print axioms rotEnc_killTest_equiv_if_bidirectional_transport

end PallLean.Paper93.DeepMath.PathC
