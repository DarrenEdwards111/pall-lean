import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeMapPiPhi
import PallLean.GodMoveReal

/-!
# Projected identity-minor frontier

This file gives a paper-faithful spelling of the SAT-decider NP-side
identity-minor obligation: first name the explicitly projected hard object,
then measure its rank.  The existing
`SATDeciderGaugeNPIdentityMinorPreservation` field is recovered only as a
bridge theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine

/-- The hard Cook-Levin object after the chosen projection/gauge has been
applied.  This is the object whose rank appears in the paper-faithful
identity-minor lower-bound formulation. -/
noncomputable def projectedIdentityMinorHardObject
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns) :
    SATDeciderGaugeSpace M n hn2 htb hns :=
  gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns))

/-- Rank of the explicitly projected identity-minor hard object at the
Cook-Levin identity-minor parameters. -/
noncomputable def projectedIdentityMinorRank
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns) : Nat :=
  mlBlockedSpdpRank
    (cook_levin_compilation M n hn2 htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n)
    (projectedIdentityMinorHardObject M n hn2 htb hns gauge)

/-- Projected lower-bound hypothesis, stated on the named projected hard object
rather than by reopening the raw SAT-decider preservation field. -/
def ProjectedIdentityMinorLowerBound
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns) : Prop :=
  Nat.choose (n / 3) (Nat.log 2 n) ≤
    projectedIdentityMinorRank M n hn2 htb hns gauge

/-- Projected NP identity-minor preservation field: for SAT deciders, the rank
of the explicitly projected hard object keeps the identity-minor lower bound. -/
def ProjectedNPIdentityMinorPreservation
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns) : Prop :=
  DecidesSAT M →
    ProjectedIdentityMinorLowerBound M n hn2 htb hns gauge

/-- A projected lower-bound hypothesis directly discharges the projected
NP identity-minor preservation field. -/
theorem projectedNPIdentityMinorPreservation_of_projected_lower_bound
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hprojected :
      ProjectedIdentityMinorLowerBound M n hn2 htb hns gauge) :
    ProjectedNPIdentityMinorPreservation M n hn2 htb hns gauge := by
  intro _hdec
  exact hprojected

/-- With a SAT-decider hypothesis, projected preservation is equivalent to the
named projected lower-bound hypothesis. -/
theorem projectedNPIdentityMinorPreservation_iff_projected_lower_bound
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hdec : DecidesSAT M) :
    ProjectedNPIdentityMinorPreservation M n hn2 htb hns gauge ↔
      ProjectedIdentityMinorLowerBound M n hn2 htb hns gauge := by
  constructor
  · intro hpres
    exact hpres hdec
  · intro hprojected
    exact projectedNPIdentityMinorPreservation_of_projected_lower_bound
      M n hn2 htb hns gauge hprojected

/-- The projected formulation implies the existing raw SAT-decider
NP-preservation field. -/
theorem satDeciderGaugeNPIdentityMinorPreservation_of_projected
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hprojected :
      ProjectedNPIdentityMinorPreservation M n hn2 htb hns gauge) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns gauge := by
  intro hdec
  simpa [ProjectedNPIdentityMinorPreservation,
    ProjectedIdentityMinorLowerBound, projectedIdentityMinorRank,
    projectedIdentityMinorHardObject] using hprojected hdec

/-- Conversely, the existing raw SAT-decider field can be read as the projected
hard-object formulation. -/
theorem projectedNPIdentityMinorPreservation_of_satDeciderGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hraw :
      SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns gauge) :
    ProjectedNPIdentityMinorPreservation M n hn2 htb hns gauge := by
  intro hdec
  simpa [ProjectedNPIdentityMinorPreservation,
    ProjectedIdentityMinorLowerBound, projectedIdentityMinorRank,
    projectedIdentityMinorHardObject] using hraw hdec

/-- The two formulations are definitionally the same inequality once the named
projected hard object is unfolded. -/
theorem projectedNPIdentityMinorPreservation_iff_satDeciderGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns) :
    ProjectedNPIdentityMinorPreservation M n hn2 htb hns gauge ↔
      SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns gauge :=
  ⟨satDeciderGaugeNPIdentityMinorPreservation_of_projected
      M n hn2 htb hns gauge,
    projectedNPIdentityMinorPreservation_of_satDeciderGauge
      M n hn2 htb hns gauge⟩

/-- Under the identity gauge, the projected hard object is the original
Cook-Levin compiled polynomial. -/
theorem projectedIdentityMinorHardObject_id
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    projectedIdentityMinorHardObject M n hn2 htb hns
        (LinearMap.id : SATDeciderGaugeMap M n hn2 htb hns) =
      compiledPoly (cook_levin_compilation M n hn2 htb hns) := by
  rfl

/-- Identity/trivial specialization: the identity gauge satisfies the projected
NP identity-minor preservation field at the paper scale. -/
theorem projectedNPIdentityMinorPreservation_id
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ProjectedNPIdentityMinorPreservation M n hn2 htb hns
      (LinearMap.id : SATDeciderGaugeMap M n hn2 htb hns) := by
  intro _hdec
  have hnp := GodMoveReal.compiled_np_lower_bound_any_dtm M n hn htb hns
  simpa [ProjectedIdentityMinorLowerBound, projectedIdentityMinorRank,
    projectedIdentityMinorHardObject, SATDeciderGaugeMap,
    SATDeciderGaugeSpace] using hnp

/-- The flat `piPhi` candidate is identity on the flat Cook-Levin space, so its
projected hard object is also the original compiled polynomial. -/
theorem projectedIdentityMinorHardObject_flatPiPhi
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    projectedIdentityMinorHardObject M n hn2 htb hns
        (satDeciderGaugeMapPiPhi M n hn2 htb hns) =
      compiledPoly (cook_levin_compilation M n hn2 htb hns) := by
  rw [satDeciderGaugeMapPiPhi_eq_id]
  rfl

/-- Trivial flat-`piPhi` specialization of the projected NP identity-minor
field.  This is useful as a sanity check; the final P-side collapse still
requires a nontrivial projection. -/
theorem projectedNPIdentityMinorPreservation_flatPiPhi
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ProjectedNPIdentityMinorPreservation M n hn2 htb hns
      (satDeciderGaugeMapPiPhi M n hn2 htb hns) := by
  rw [satDeciderGaugeMapPiPhi_eq_id]
  exact projectedNPIdentityMinorPreservation_id M n hn hn2 htb hns

/-!
## Axiom audit anchors
-/
#print axioms projectedNPIdentityMinorPreservation_of_projected_lower_bound
#print axioms projectedNPIdentityMinorPreservation_iff_projected_lower_bound
#print axioms satDeciderGaugeNPIdentityMinorPreservation_of_projected
#print axioms projectedNPIdentityMinorPreservation_of_satDeciderGauge
#print axioms projectedNPIdentityMinorPreservation_iff_satDeciderGauge
#print axioms projectedNPIdentityMinorPreservation_id
#print axioms projectedNPIdentityMinorPreservation_flatPiPhi

end PallLean.Paper93.DeepMath.PathB
