import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeRealFrontier
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeNPBridge

/-!
# Necessary rank drop for SAT-decider gauges

This file records only necessary consequences of a
`SATDeciderGaugeSubgoals` witness.  It does not construct a gauge, nor does it
strengthen the remaining frontier into an existence theorem.

The useful obstruction is simple: a successful witness must give the projected
P-side upper bound on the gauged compiled polynomial, while NP preservation
gives the matching lower bound under a SAT-decider hypothesis.  Separately,
if the gauged polynomial has the same SPDP rank as the raw/identity image, the
raw Cook-Levin lower bound from `SATDeciderGaugeNPBridge` and the paper-scale
arithmetic gap contradict the P-side upper bound.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine

/-- The P-side field of `SATDeciderGaugeSubgoals` is exactly the upper rank
bound on the gauged Cook-Levin compiled polynomial. -/
theorem satDeciderGaugeSubgoals_gauged_compiled_rank_le
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hsubgoals : SATDeciderGaugeSubgoals M n hn2 htb hns gauge) :
    mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≤
      n ^ 200 :=
  hsubgoals.2.1

/-- Under the SAT-decider hypothesis, the NP-preservation field is exactly the
lower rank bound on the gauged Cook-Levin compiled polynomial. -/
theorem satDeciderGaugeSubgoals_gauged_compiled_rank_ge_choose
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hdec : DecidesSAT M)
    (hsubgoals : SATDeciderGaugeSubgoals M n hn2 htb hns gauge) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns))) :=
  hsubgoals.2.2 hdec

/-- At the paper scale, any successful SAT-decider gauge package must place
the gauged compiled polynomial between the P-side upper bound and the
NP-side identity-minor lower bound. -/
theorem satDeciderGaugeSubgoals_gauged_compiled_rank_sandwich_at_large_n
    (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hdec : DecidesSAT M)
    (hsubgoals : SATDeciderGaugeSubgoals M n hn2 htb hns gauge) :
    mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≤
      n ^ 200 ∧
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns))) :=
  ⟨satDeciderGaugeSubgoals_gauged_compiled_rank_le
      M n hn2 htb hns gauge hsubgoals,
    satDeciderGaugeSubgoals_gauged_compiled_rank_ge_choose
      M n hn2 htb hns gauge hdec hsubgoals⟩

/-- The rank sandwich is incompatible at the paper scale under a SAT-decider
hypothesis.  This is the existing `RealFrontier` obstruction restated in the
rank-necessity vocabulary, not a gauge-existence claim. -/
theorem satDeciderGaugeSubgoals_rank_sandwich_impossible_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hdec : DecidesSAT M)
    (hsubgoals : SATDeciderGaugeSubgoals M n hn2 htb hns gauge) :
    False :=
  satDeciderGauge_pSide_and_npIdentityMinor_incompatible_at_large_n
    M n hn hn2 htb hns gauge hdec hsubgoals.2.1 hsubgoals.2.2

/-- If the arithmetic gap applies and the raw compiled polynomial has the
standard NP lower bound, then a successful witness cannot leave the gauged
compiled polynomial with the same SPDP rank as the raw compiled polynomial. -/
theorem satDeciderGaugeSubgoals_forces_rank_ne_raw_of_raw_lower_bound_of_gap
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hgap : n ^ 200 < Nat.choose (n / 3) (Nat.log 2 n))
    (hraw :
      Nat.choose (n / 3) (Nat.log 2 n) ≤
        mlBlockedSpdpRank
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)))
    (hsubgoals : SATDeciderGaugeSubgoals M n hn2 htb hns gauge) :
    mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≠
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) := by
  intro hsame
  have hgauge_lower :
      Nat.choose (n / 3) (Nat.log 2 n) ≤
        mlBlockedSpdpRank
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns))) := by
    simpa [hsame] using hraw
  have hchoose_le : Nat.choose (n / 3) (Nat.log 2 n) ≤ n ^ 200 :=
    le_trans hgauge_lower
      (satDeciderGaugeSubgoals_gauged_compiled_rank_le
        M n hn2 htb hns gauge hsubgoals)
  exact (not_lt_of_ge hchoose_le) hgap

/-- At the paper scale, `SATDeciderGaugeNPBridge` supplies the raw lower bound
and the landed arithmetic gap supplies the contradiction.  Therefore a
successful witness must strictly change the relevant SPDP rank away from the
raw compiled polynomial. -/
theorem satDeciderGaugeSubgoals_forces_rank_ne_raw_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hsubgoals : SATDeciderGaugeSubgoals M n hn2 htb hns gauge) :
    mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≠
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) :=
  satDeciderGaugeSubgoals_forces_rank_ne_raw_of_raw_lower_bound_of_gap
    M n hn2 htb hns gauge
    (PaperFaithfulCompilation.arithmetic_gap_2pow804 n hn)
    (lemma124_compiledPoly_identity_minor_lower_bound M n hn hn2 htb hns)
    hsubgoals

/-- Equivalently, the gauged compiled polynomial cannot have the same SPDP rank
as the identity map's image of the compiled polynomial. -/
theorem satDeciderGaugeSubgoals_forces_rank_ne_identity_image_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hsubgoals : SATDeciderGaugeSubgoals M n hn2 htb hns gauge) :
    mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≠
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        ((identitySATDeciderGauge M n hn2 htb hns)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))) := by
  simpa [identitySATDeciderGauge] using
    satDeciderGaugeSubgoals_forces_rank_ne_raw_at_large_n
      M n hn hn2 htb hns gauge hsubgoals

/-- Under the same raw lower-bound and arithmetic-gap hypotheses, a successful
witness cannot send the compiled polynomial to the raw compiled polynomial. -/
theorem satDeciderGaugeSubgoals_image_eq_raw_compiledPoly_impossible_of_gap
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hgap : n ^ 200 < Nat.choose (n / 3) (Nat.log 2 n))
    (hraw :
      Nat.choose (n / 3) (Nat.log 2 n) ≤
        mlBlockedSpdpRank
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)))
    (hsubgoals : SATDeciderGaugeSubgoals M n hn2 htb hns gauge) :
    gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        compiledPoly (cook_levin_compilation M n hn2 htb hns) →
      False := by
  intro himage
  exact
    (satDeciderGaugeSubgoals_forces_rank_ne_raw_of_raw_lower_bound_of_gap
      M n hn2 htb hns gauge hgap hraw hsubgoals) (by simp [himage])

/-- At paper scale, if the image of the Cook-Levin compiled polynomial is the
raw compiled polynomial, the `SATDeciderGaugeSubgoals` package is impossible. -/
theorem satDeciderGaugeSubgoals_image_eq_raw_compiledPoly_impossible_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hsubgoals : SATDeciderGaugeSubgoals M n hn2 htb hns gauge) :
    gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        compiledPoly (cook_levin_compilation M n hn2 htb hns) →
      False := by
  intro himage
  exact
    (satDeciderGaugeSubgoals_forces_rank_ne_raw_at_large_n
      M n hn hn2 htb hns gauge hsubgoals) (by simp [himage])

/-- Direct obstruction form: a gauge whose image on the Cook-Levin compiled
polynomial is the raw compiled polynomial cannot satisfy the explicit
SAT-decider gauge subgoals at paper scale. -/
theorem satDeciderGauge_image_eq_raw_compiledPoly_not_subgoals_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (himage :
      gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        compiledPoly (cook_levin_compilation M n hn2 htb hns)) :
    ¬ SATDeciderGaugeSubgoals M n hn2 htb hns gauge := by
  intro hsubgoals
  exact satDeciderGaugeSubgoals_image_eq_raw_compiledPoly_impossible_at_large_n
    M n hn hn2 htb hns gauge hsubgoals himage

/-!
## Axiom audit anchors
-/
#print axioms satDeciderGaugeSubgoals_gauged_compiled_rank_sandwich_at_large_n
#print axioms satDeciderGaugeSubgoals_rank_sandwich_impossible_at_large_n
#print axioms satDeciderGaugeSubgoals_forces_rank_ne_raw_at_large_n
#print axioms satDeciderGaugeSubgoals_forces_rank_ne_identity_image_at_large_n
#print axioms satDeciderGaugeSubgoals_image_eq_raw_compiledPoly_impossible_at_large_n
#print axioms satDeciderGauge_image_eq_raw_compiledPoly_not_subgoals_at_large_n

end PallLean.Paper93.DeepMath.PathB
