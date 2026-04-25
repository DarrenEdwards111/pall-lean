import PallLean.GlobalGodMoveGauge
import PallLean.PaperFaithfulCompilation

/-!
# Zero linear map is not the bundled Global God-Move gauge for SAT deciders

This file proves the direct bundled-structure obstruction: at the paper scale,
the zero linear map cannot satisfy `GlobalGodMoveGauge.IsAmplituhedronGauge`
for a SAT-deciding DTM.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine

/-- At `n ≥ 2^804`, the zero linear map is not a bundled
`GlobalGodMoveGauge.IsAmplituhedronGauge` for a SAT decider.

The obstruction is the bundled NP-side preservation field: under the zero map,
the gauged compiled polynomial has SPDP rank zero, while
`PaperFaithfulCompilation.arithmetic_gap_2pow804` gives
`0 < Nat.choose (n / 3) (Nat.log 2 n)`. -/
theorem zeroLinearMap_not_isAmplituhedronGauge_for_sat_decider_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    ¬ GlobalGodMoveGauge.IsAmplituhedronGauge M n hn hn2 htb hns
      (0 : MvPolynomial
              (Fin (cook_levin_compilation M n hn2 htb hns).numVars) Rat →ₗ[Rat]
            MvPolynomial
              (Fin (cook_levin_compilation M n hn2 htb hns).numVars) Rat) := by
  intro hgauge
  have hnp :=
    hgauge.preserves_identity_minor_for_sat_deciders hdec
  have hle_zero :
      Nat.choose (n / 3) (Nat.log 2 n) ≤ 0 := by
    simpa [MultilinearSPDP.mlBlockedSpdpRank_zero] using hnp
  have hbinom_pos : 0 < Nat.choose (n / 3) (Nat.log 2 n) :=
    lt_of_le_of_lt (Nat.zero_le _)
      (PaperFaithfulCompilation.arithmetic_gap_2pow804 n hn)
  exact (not_lt_of_ge hle_zero) hbinom_pos

end PallLean.Paper93.DeepMath.PathB
