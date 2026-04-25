import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeNonzeroFrontier
import PallLean.GodMoveReal

/-!
# Real compiled-polynomial SAT-decider gauge frontier

This file records facts about the exact `GlobalGodMoveGauge` target object:

* the identity map preserves the NP identity-minor lower bound on the real
  Cook-Levin compiled polynomial;
* the identity map therefore cannot satisfy the projected P-side bound at the
  paper scale;
* more generally, the P-side bound and NP identity-minor preservation fields
  are incompatible for any gauge at `n ≥ 2^804` once `DecidesSAT M` is present.

The last point is intentionally an obstruction theorem, not a fake closure:
constructing a gauge with both fields is precisely the contradiction-strength
content of the remaining amplituhedron/God-Move frontier.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine

/-- The identity endomorphism on the exact SAT-decider gauge space. -/
noncomputable abbrev identitySATDeciderGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeMap M n hn2 htb hns :=
  LinearMap.id

/-- The identity map is rank-monotone on the exact SAT-decider gauge space. -/
theorem identitySATDeciderGauge_rankMonotonicity
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns
      (identitySATDeciderGauge M n hn2 htb hns) := by
  intro κ ℓ p
  rfl

/-- The identity map preserves the real compiled-polynomial NP identity-minor
lower bound.

This theorem is on the exact Cook-Levin compiled polynomial used by
`GlobalGodMoveGauge.IsAmplituhedronGauge`, not on the constant-one family or a
finite matrix toy model. It uses the existing axiom-free NP-side lower bound
`GodMoveReal.compiled_np_lower_bound_any_dtm`.
-/
theorem identitySATDeciderGauge_npIdentityMinorPreservation
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
      (identitySATDeciderGauge M n hn2 htb hns) := by
  intro _hdec
  have hnp := GodMoveReal.compiled_np_lower_bound_any_dtm M n hn htb hns
  dsimp [SATDeciderGaugeNPIdentityMinorPreservation,
    identitySATDeciderGauge, SATDeciderGaugeMap, SATDeciderGaugeSpace]
  convert hnp using 2

/-- The identity map cannot be the final SAT-decider gauge at the paper scale:
it preserves the NP identity minor, so the P-side bound would contradict the
arithmetic gap `n^200 < choose (n/3) (log₂ n)`.
-/
theorem identitySATDeciderGauge_not_pSideBound_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ¬ SATDeciderGaugePSideBound M n hn2 htb hns
      (identitySATDeciderGauge M n hn2 htb hns) := by
  intro hP
  dsimp [SATDeciderGaugePSideBound, identitySATDeciderGauge,
    SATDeciderGaugeMap, SATDeciderGaugeSpace] at hP
  have hNP : Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) := by
    have hnp := GodMoveReal.compiled_np_lower_bound_any_dtm M n hn htb hns
    convert hnp using 2
  have hchoose_le : Nat.choose (n / 3) (Nat.log 2 n) ≤ n ^ 200 :=
    le_trans hNP hP
  exact not_lt_of_ge hchoose_le
    (PaperFaithfulCompilation.arithmetic_gap_2pow804 n hn)

/-- The two load-bearing rank fields of the SAT-decider gauge package are
incompatible at the paper scale.

This isolates the exact contradiction: once `DecidesSAT M` is available, a
gauge satisfying both the projected P-side bound and projected NP-side
identity-minor preservation yields `choose (n/3) (log₂ n) ≤ n^200`, contrary to
the landed arithmetic gap.
-/
theorem satDeciderGauge_pSide_and_npIdentityMinor_incompatible_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hdec : DecidesSAT M)
    (hP : SATDeciderGaugePSideBound M n hn2 htb hns gauge)
    (hNP : SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns gauge) :
    False := by
  have hchoose_le : Nat.choose (n / 3) (Nat.log 2 n) ≤ n ^ 200 :=
    le_trans (hNP hdec) hP
  exact not_lt_of_ge hchoose_le
    (PaperFaithfulCompilation.arithmetic_gap_2pow804 n hn)

/-- No gauge can satisfy all explicit SAT-decider gauge subgoals at the paper
scale under a `DecidesSAT M` hypothesis. This is the field-level version of the
final contradiction.
-/
theorem not_satDeciderGaugeSubgoals_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hdec : DecidesSAT M) :
    ¬ SATDeciderGaugeSubgoals M n hn2 htb hns gauge := by
  intro hsubgoals
  exact satDeciderGauge_pSide_and_npIdentityMinor_incompatible_at_large_n
    M n hn hn2 htb hns gauge hdec hsubgoals.2.1 hsubgoals.2.2

/-- If the remaining SAT-decider gauge frontier is discharged, then no bounded
SAT-deciding DTM can exist at the paper scale. This is the direct logical role
of the remaining amplituhedron projection construction.
-/
theorem satDeciderSpecificGaugeSubgoalDischarge_implies_no_sat_decider
    (hfrontier : SATDeciderSpecificGaugeSubgoalDischarge)
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ¬ DecidesSAT M := by
  intro hdec
  obtain ⟨gauge, hsubgoals⟩ :=
    hfrontier M n hn hn2 htb hns hdec
  exact not_satDeciderGaugeSubgoals_at_large_n
    M n hn hn2 htb hns gauge hdec hsubgoals

/-- The exact no-bounded-SAT-decider proposition matched to the current
SAT-decider gauge frontier. -/
def NoBoundedSATDeciderAtPaperScale : Prop :=
  ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (_hn2 : n ≥ 2)
    (_htb : M.timeBound ≤ 4) (_hns : M.numStates ≤ n),
    ¬ DecidesSAT M

/-- If no bounded SAT-decider exists at the paper scale, the gauge frontier is
vacuously discharged: the `DecidesSAT M` input is contradictory. -/
theorem satDeciderSpecificGaugeSubgoalDischarge_of_no_bounded_sat_decider
    (hno : NoBoundedSATDeciderAtPaperScale) :
    SATDeciderSpecificGaugeSubgoalDischarge := by
  intro M n hn hn2 htb hns hdec
  exact False.elim ((hno M n hn hn2 htb hns) hdec)

/-- The current SAT-decider gauge frontier is logically equivalent to proving
there is no bounded SAT-decider at the paper scale.

This is the key status theorem: because the P-side upper bound and NP
identity-minor preservation fields are already incompatible at `n ≥ 2^804`,
the bundled gauge statement is not merely asking for a better linear map. It is
an equivalent way to state the final no-SAT-decider contradiction.
-/
theorem satDeciderSpecificGaugeSubgoalDischarge_iff_no_bounded_sat_decider :
    SATDeciderSpecificGaugeSubgoalDischarge ↔
      NoBoundedSATDeciderAtPaperScale := by
  constructor
  · intro hfrontier M n hn hn2 htb hns
    exact satDeciderSpecificGaugeSubgoalDischarge_implies_no_sat_decider
      hfrontier M n hn hn2 htb hns
  · exact satDeciderSpecificGaugeSubgoalDischarge_of_no_bounded_sat_decider

/-!
## Axiom audit anchors
-/
#print axioms identitySATDeciderGauge_rankMonotonicity
#print axioms identitySATDeciderGauge_npIdentityMinorPreservation
#print axioms identitySATDeciderGauge_not_pSideBound_at_large_n
#print axioms satDeciderGauge_pSide_and_npIdentityMinor_incompatible_at_large_n
#print axioms not_satDeciderGaugeSubgoals_at_large_n
#print axioms satDeciderSpecificGaugeSubgoalDischarge_implies_no_sat_decider
#print axioms satDeciderSpecificGaugeSubgoalDischarge_of_no_bounded_sat_decider
#print axioms satDeciderSpecificGaugeSubgoalDischarge_iff_no_bounded_sat_decider

end PallLean.Paper93.DeepMath.PathB
