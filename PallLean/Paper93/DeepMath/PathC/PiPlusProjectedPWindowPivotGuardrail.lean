import PallLean.Paper93.DeepMath.PathC.PiPlusProjectedPWindowPivot

/-!
# Guardrail for the projected P-window pivot

This file is a kill-test for Path C.  It records the exact failure mode we want
not to repeat from Route B: if the P-side finite cover and the NP-side identity
minor lower bound are asserted for the same projected/gauged rank object at
paper scale, the package is already inconsistent with a SAT decider.

So the projected pivot can only be a genuine new route if a later producer
proves that the P-window cover is attached to a strictly narrower/local object
than the subspace carrying the NP identity minor, or otherwise explains why the
same-rank contradiction below is not the generated data.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- The exact projected/gauged rank object used by the current Path C socket. -/
noncomputable abbrev projectedPivotRankObject
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gauge : ProjectedPivotGaugeMap M n hn2 htb hns) : Nat :=
  mlBlockedSpdpRank
    (cook_levin_compilation M n hn2 htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n)
    (gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)))

/-- P-side upper bound stated directly on the projected pivot rank object. -/
def ProjectedPivotSameObjectPBound
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gauge : ProjectedPivotGaugeMap M n hn2 htb hns) : Prop :=
  projectedPivotRankObject M n hn2 htb hns gauge <= n ^ 200

/-- NP-side lower bound stated directly on the same projected pivot rank object. -/
def ProjectedPivotSameObjectNPLower
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gauge : ProjectedPivotGaugeMap M n hn2 htb hns) : Prop :=
  DecidesSAT M ->
    Nat.choose (n / 3) (Nat.log 2 n) <=
      projectedPivotRankObject M n hn2 htb hns gauge

/-- Current `ProjectedPivotPSideBound` is definitionally the same-object P bound. -/
theorem projectedPivotPSideBound_iff_sameObjectPBound
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gauge : ProjectedPivotGaugeMap M n hn2 htb hns) :
    ProjectedPivotPSideBound M n hn2 htb hns gauge <->
      ProjectedPivotSameObjectPBound M n hn2 htb hns gauge := by
  rfl

/-- Current `ProjectedPivotNPIdentityMinorPreservation` is definitionally the
same-object NP lower bound. -/
theorem projectedPivotNPIdentityMinorPreservation_iff_sameObjectNPLower
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gauge : ProjectedPivotGaugeMap M n hn2 htb hns) :
    ProjectedPivotNPIdentityMinorPreservation M n hn2 htb hns gauge <->
      ProjectedPivotSameObjectNPLower M n hn2 htb hns gauge := by
  rfl

/-- Guardrail/kill-test: at paper scale, same-object P upper and NP lower bounds
are incompatible with `DecidesSAT M`.  This is the core reason Path C must
separate the P-window object from the NP-minor object to be a non-vacuous route. -/
theorem no_decidesSAT_of_sameObjectPBound_and_sameObjectNPLower_at_large_n
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gauge : ProjectedPivotGaugeMap M n hn2 htb hns)
    (hP : ProjectedPivotSameObjectPBound M n hn2 htb hns gauge)
    (hNP : ProjectedPivotSameObjectNPLower M n hn2 htb hns gauge) :
    ¬ DecidesSAT M := by
  intro hdec
  have hchoose_le : Nat.choose (n / 3) (Nat.log 2 n) <= n ^ 200 :=
    le_trans (hNP hdec) hP
  exact not_lt_of_ge hchoose_le
    (PaperFaithfulCompilation.arithmetic_gap_2pow804 n hn)

/-- The existing Path C pivot data is exactly same-object data; hence it is a
contradiction package, not a construction recipe. -/
theorem projectedPWindowPivotData_is_sameObjectContradictionPackage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gauge : ProjectedPivotGaugeMap M n hn2 htb hns)
    (D : ProjectedPWindowPivotData M n hn2 htb hns gauge) :
    ProjectedPivotSameObjectPBound M n hn2 htb hns gauge ∧
      ProjectedPivotSameObjectNPLower M n hn2 htb hns gauge := by
  exact pSide_and_npIdentityMinor_of_projectedPWindowPivotData
    M n hn2 htb hns gauge D

/-- Kill-test verdict for the current Path C socket: any universal producer of
`ProjectedPWindowPivotData` for SAT deciders at paper scale is already a
producer of the no-decider theorem. -/
theorem no_decidesSAT_of_projectedPWindowPivotData_guardrail
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gauge : ProjectedPivotGaugeMap M n hn2 htb hns)
    (D : ProjectedPWindowPivotData M n hn2 htb hns gauge) :
    ¬ DecidesSAT M := by
  rcases projectedPWindowPivotData_is_sameObjectContradictionPackage
    M n hn2 htb hns gauge D with ⟨hP, hNP⟩
  exact no_decidesSAT_of_sameObjectPBound_and_sameObjectNPLower_at_large_n
    M n hn hn2 htb hns gauge hP hNP

/-- A named predicate for what a future non-doomed Path C producer must supply:
the P cover must be justified on a genuinely separated/local window, rather
than merely restating the same rank object that carries the NP minor.  The
concrete separation relation is intentionally not guessed here; this is the
non-negotiable interface constraint exposed by the kill-test above. -/
def RequiresSeparatedPWindowProducer
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (_gauge : ProjectedPivotGaugeMap M n hn2 htb hns) : Prop :=
  ∃ PWindow NPMinorCarrier : Submodule Rat (ProjectedPivotGaugeSpace M n hn2 htb hns),
    PWindow < NPMinorCarrier

/-! ## Axiom audit anchors -/

#print axioms projectedPivotPSideBound_iff_sameObjectPBound
#print axioms projectedPivotNPIdentityMinorPreservation_iff_sameObjectNPLower
#print axioms no_decidesSAT_of_sameObjectPBound_and_sameObjectNPLower_at_large_n
#print axioms projectedPWindowPivotData_is_sameObjectContradictionPackage
#print axioms no_decidesSAT_of_projectedPWindowPivotData_guardrail

end PallLean.Paper93.DeepMath.PathC
