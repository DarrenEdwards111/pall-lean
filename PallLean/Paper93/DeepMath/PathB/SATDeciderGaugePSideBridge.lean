import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeMapPiPhi

/-!
# SAT-decider P-side bridge

This file isolates the honest P-side bridge that is available today:
rank monotonicity turns an unprojected P-side rank bound into the projected
P-side field.

It does not prove the unprojected flat Cook-Levin P-side bound.  That remains
the profile/template-collapse or genuine UV-split projection construction
frontier.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine

/-- Rank monotonicity plus an unprojected flat Cook-Levin P-side bound gives
the projected P-side field.

This is deliberately conditional: the premise is exactly the unprojected
flat bound that the known legacy route proves only through the bad
`spdp_profile_generators` axiom, while the honest template-collapse variants
still keep it as real content.
-/
theorem satDeciderGaugePSideBound_of_rankMonotone_of_unprojected_bound
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hrank : SATDeciderGaugeRankMonotonicity M n hn2 htb hns gauge)
    (hunprojected :
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≤ n ^ 200) :
    SATDeciderGaugePSideBound M n hn2 htb hns gauge :=
  le_trans
    (hrank (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns)))
    hunprojected

/-- For the flat `piPhi` candidate, the projected P-side field is equivalent
to the unprojected flat P-side bound, because this candidate is the identity.
-/
theorem satDeciderGaugeMapPiPhi_pSideBound_iff_unprojected_bound
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (satDeciderGaugeMapPiPhi M n hn2 htb hns) ↔
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≤ n ^ 200 := by
  rw [satDeciderGaugeMapPiPhi_eq_id]
  rfl

/-!
## Axiom audit anchors
-/
#print axioms satDeciderGaugePSideBound_of_rankMonotone_of_unprojected_bound
#print axioms satDeciderGaugeMapPiPhi_pSideBound_iff_unprojected_bound

end PallLean.Paper93.DeepMath.PathB
