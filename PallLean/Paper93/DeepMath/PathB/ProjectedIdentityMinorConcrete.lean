import PallLean.Paper93.DeepMath.PathB.ProjectedIdentityMinorPaperFaithful

/-!
# Concrete projected identity-minor instance

This file instantiates the paper-faithful projected identity-minor package at
the concrete Step247 Cook-Levin partitioned output.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulCompilation

namespace ProjectedIdentityMinorConcrete

/-- Source-side identity-minor lower bound for the concrete Step247
Cook-Levin partitioned output. -/
theorem sourceIdentityMinorLowerBound_cookLevin_partitionedOutput
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn2 : n ≥ 2) :
    SourceIdentityMinorLowerBound n
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ
      (extendedCookLevinPartition M n hn2)
      (Nat.log 2 n) (Nat.log 2 n)
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).Q_verifier := by
  unfold SourceIdentityMinorLowerBound
  rw [Step4Compiler.Step247.partitioned_output_cookLevin_Q_verifier_eq]
  rw [Step4Compiler.lemma_124_Q_times_Phi_eq_cookLevinQ M n hn2 htb hns]
  convert cookLevinQ_rank_ge M n hn htb hns using 2

/-- Projected identity-minor lower bound on the concrete Step247 full output. -/
theorem partitionedOutput_cookLevin_projectedIdentityMinorLowerBound
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn2 : n ≥ 2) :
    PartitionedOutputProjectedIdentityMinorLowerBound n
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns)
      (extendedCookLevinPartition M n hn2)
      (Nat.log 2 n) (Nat.log 2 n) := by
  exact partitionedOutput_projectedIdentityMinorLowerBound_of_source
    n (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns)
    (extendedCookLevinPartition M n hn2)
    (Nat.log 2 n) (Nat.log 2 n)
    (sourceIdentityMinorLowerBound_cookLevin_partitionedOutput
      M n hn htb hns hn2)

/-- Projected compiler-side identity-minor lower bound on the concrete Step247
Cook-Levin output. -/
theorem partitionedOutput_cookLevin_projectedCompilerIdentityMinorLowerBound
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn2 : n ≥ 2) :
    PaperFaithfulProjectedCompilerIdentityMinorLowerBound n
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ
      (extendedCookLevinPartition M n hn2)
      (Nat.log 2 n) (Nat.log 2 n)
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).Q_verifier
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).full_output
      (piPhi (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ) := by
  exact partitionedOutput_projectedCompilerIdentityMinorLowerBound_of_source
    n (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns)
    (extendedCookLevinPartition M n hn2)
    (Nat.log 2 n) (Nat.log 2 n)
    (sourceIdentityMinorLowerBound_cookLevin_partitionedOutput
      M n hn htb hns hn2)

/-- Direct P-side bound needed by the concrete projected Cook-Levin package. -/
def CookLevinProjectedPSideBound
    (M : TuringMachine.DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
    PaperFaithfulCompilerPSideBound n
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ
      (extendedCookLevinPartition M n hn2)
      (Nat.log 2 n) (Nat.log 2 n)
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).full_output

/-- The concrete Step247 Cook-Levin output satisfies the projected
contradiction package from a direct P-side full-output bound. -/
theorem paperFaithfulProjectedContradictionPackage_cookLevin_of_pSide
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn2 : n ≥ 2)
    (hP : CookLevinProjectedPSideBound M n hn2 htb hns) :
    PaperFaithfulProjectedContradictionPackage n
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ
      (extendedCookLevinPartition M n hn2)
      (Nat.log 2 n) (Nat.log 2 n)
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).Q_verifier
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).full_output := by
  refine ⟨?_, ?_, ?_⟩
  · exact sourceIdentityMinorLowerBound_cookLevin_partitionedOutput
      M n hn htb hns hn2
  · exact Step4Compiler.Step241.partitioned_output_piPhi_extracts
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns)
  · exact hP

/-- Concrete contradiction from the projected paper-faithful package at the
Step247 Cook-Levin output, assuming the direct P-side rank bound. -/
theorem false_of_cookLevinProjectedPSideBound
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn2 : n ≥ 2)
    (hP : CookLevinProjectedPSideBound M n hn2 htb hns) :
    False := by
  exact false_of_paperFaithfulProjectedContradictionPackage n hn
    (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ
    (Step4Compiler.cookLevin_sigma_numV_pos M n hn)
    (extendedCookLevinPartition M n hn2)
    (Nat.log 2 n) (Nat.log 2 n)
    (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).Q_verifier
    (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).full_output
    (paperFaithfulProjectedContradictionPackage_cookLevin_of_pSide
      M n hn htb hns hn2 hP)

/-- The existing kernel-only template-collapse bridge supplies the direct
P-side full-output bound for the projected Cook-Levin package. -/
theorem cookLevinProjectedPSideBound_of_templateCollapse
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn2 : n ≥ 2)
    (hcollapse : WithinProfileBound.CookLevinProfileTemplateCollapseLemma
      M n hn2 htb hns) :
    CookLevinProjectedPSideBound M n hn2 htb hns := by
  unfold CookLevinProjectedPSideBound PaperFaithfulCompilerPSideBound
  exact Step4Compiler.Step252.cookLevin_full_output_rank_le_of_pullback_rank_le
    M n hn2 htb hns
    (Step4Compiler.Step252.cookLevinQ_rank_le_from_templateCollapse
      M n hn htb hns hcollapse)

/-- The concrete Step247 Cook-Levin output satisfies the projected
contradiction package under the honest template-collapse hypothesis. -/
theorem paperFaithfulProjectedContradictionPackage_cookLevin_of_templateCollapse
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn2 : n ≥ 2)
    (hcollapse : WithinProfileBound.CookLevinProfileTemplateCollapseLemma
      M n hn2 htb hns) :
    PaperFaithfulProjectedContradictionPackage n
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ
      (extendedCookLevinPartition M n hn2)
      (Nat.log 2 n) (Nat.log 2 n)
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).Q_verifier
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).full_output :=
  paperFaithfulProjectedContradictionPackage_cookLevin_of_pSide
    M n hn htb hns hn2
    (cookLevinProjectedPSideBound_of_templateCollapse
      M n hn htb hns hn2 hcollapse)

/-- Fully instantiated projected Cook-Levin contradiction under the honest
template-collapse hypothesis. -/
theorem false_of_cookLevin_templateCollapse_projected
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn2 : n ≥ 2)
    (hcollapse : WithinProfileBound.CookLevinProfileTemplateCollapseLemma
      M n hn2 htb hns) :
    False :=
  false_of_cookLevinProjectedPSideBound M n hn htb hns hn2
    (cookLevinProjectedPSideBound_of_templateCollapse
      M n hn htb hns hn2 hcollapse)

/-! ## Axiom audit anchors -/

#print axioms sourceIdentityMinorLowerBound_cookLevin_partitionedOutput
#print axioms partitionedOutput_cookLevin_projectedIdentityMinorLowerBound
#print axioms partitionedOutput_cookLevin_projectedCompilerIdentityMinorLowerBound
#print axioms paperFaithfulProjectedContradictionPackage_cookLevin_of_pSide
#print axioms false_of_cookLevinProjectedPSideBound
#print axioms cookLevinProjectedPSideBound_of_templateCollapse
#print axioms paperFaithfulProjectedContradictionPackage_cookLevin_of_templateCollapse
#print axioms false_of_cookLevin_templateCollapse_projected

end ProjectedIdentityMinorConcrete

end PallLean.Paper93.DeepMath.PathB
