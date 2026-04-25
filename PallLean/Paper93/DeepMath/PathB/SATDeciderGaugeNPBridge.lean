import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeDischargeSubgoals
import PallLean.Step4Compiler

/-!
# SAT-decider NP identity-minor bridge

This file isolates the exact bridge between the existing Cook-Levin NP
lower-bound object and the field
`SATDeciderGaugeNPIdentityMinorPreservation`.

The direct arbitrary-gauge closure is intentionally not asserted here:
`lemma_124_unconditional` / `Q_times_Phi_135` / `cookLevinQ` provide the
ungauged Cook-Levin lower bound.  The field asks for that same lower bound
after applying a particular gauge to `compiledPoly`, so the remaining
mathematical content is precisely the projected-rank lower bound below.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine

/-- The NP-preservation field is exactly discharged by a lower bound on the
gauged Cook-Levin compiled polynomial.  This is the clean subgoal left after
the `lemma_124_unconditional` / `Q_times_Phi_135` / `cookLevinQ` lower-bound
object has been transported through the chosen gauge. -/
theorem satDeciderGaugeNPIdentityMinorPreservation_of_projected_compiled_lower_bound
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hprojected :
      Nat.choose (n / 3) (Nat.log 2 n) ≤
        mlBlockedSpdpRank
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns gauge := by
  intro _hdec
  exact hprojected

/-- With a SAT-decider hypothesis in hand, the NP-preservation field is
equivalent to the projected lower-bound subgoal. -/
theorem satDeciderGaugeNPIdentityMinorPreservation_iff_projected_compiled_lower_bound
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hdec : DecidesSAT M) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns gauge ↔
      Nat.choose (n / 3) (Nat.log 2 n) ≤
        mlBlockedSpdpRank
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns))) := by
  constructor
  · intro hpres
    exact hpres hdec
  · intro hprojected
    exact satDeciderGaugeNPIdentityMinorPreservation_of_projected_compiled_lower_bound
      M n hn2 htb hns gauge hprojected

/-- The §189 concrete `Q_times_Phi_135` witness is definitionally the same
Cook-Levin compiled polynomial used by the SAT-decider gauge field. -/
theorem lemma124_Q_times_Phi_135_eq_compiledPoly
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Step4Compiler.Q_times_Phi_135 Step4Compiler.lemma_124_Phi_chosen
        (Step4Compiler.lemma_124_z_chosen M n hn2 htb hns)
        (Step4Compiler.lemma_124_V_chosen n) =
      (compiledPoly (cook_levin_compilation M n hn2 htb hns) :
        MvPolynomial (Fin n) Rat) := by
  calc
    Step4Compiler.Q_times_Phi_135 Step4Compiler.lemma_124_Phi_chosen
        (Step4Compiler.lemma_124_z_chosen M n hn2 htb hns)
        (Step4Compiler.lemma_124_V_chosen n)
        =
      (show MvPolynomial (Fin n) Rat from
        PaperFaithfulCompilation.cookLevinQ M n hn2 htb hns) :=
        Step4Compiler.lemma_124_Q_times_Phi_eq_cookLevinQ M n hn2 htb hns
    _ = (compiledPoly (cook_levin_compilation M n hn2 htb hns) :
        MvPolynomial (Fin n) Rat) := by
        unfold PaperFaithfulCompilation.cookLevinQ
        rfl

/-- The ungauged Cook-Levin compiled polynomial has the NP identity-minor lower
bound at the same polynomial and partition appearing in the gauge field. -/
theorem lemma124_compiledPoly_identity_minor_lower_bound
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) := by
  simpa using GodMoveReal.compiled_np_lower_bound_any_dtm M n hn htb hns

/-- As a sanity specialization, the identity linear gauge satisfies the
NP-preservation field.  This does not close the full SAT-decider gauge package:
the P-side collapse field needs a nontrivial gauge. -/
theorem satDeciderGaugeNPIdentityMinorPreservation_id
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
      (LinearMap.id : SATDeciderGaugeMap M n hn2 htb hns) := by
  refine satDeciderGaugeNPIdentityMinorPreservation_of_projected_compiled_lower_bound
    M n hn2 htb hns (LinearMap.id : SATDeciderGaugeMap M n hn2 htb hns) ?_
  simpa [SATDeciderGaugeMap, SATDeciderGaugeSpace] using
    lemma124_compiledPoly_identity_minor_lower_bound M n hn hn2 htb hns

end PallLean.Paper93.DeepMath.PathB
