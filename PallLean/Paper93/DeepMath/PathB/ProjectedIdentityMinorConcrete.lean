import PallLean.Paper93.DeepMath.PathB.ProjectedIdentityMinorPaperFaithful
import PallLean.Paper93.DeepMath.PathB.ConcreteWRowEmbeddingBridge
import PallLean.Paper93.DeepMath.PathB.ConcreteWRowEmbeddingsClosure

/-!
# Concrete projected identity-minor instance

This file instantiates the paper-faithful projected identity-minor package at
the concrete Step247 Cook-Levin partitioned output.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulCompilation

namespace ProjectedIdentityMinorConcrete

/-- The concrete Kronecker system obtained by applying
`IdentityMinorReal.buildKroneckerSystem` to the actual Tseitin disjoint-packing
clause system.  This names the item-(1) object explicitly: its rows are the
identity-minor gadget products, and the right-inverse route below places those
same private-tag coordinates inside the concrete `coupledVerifier` SPDP row
space. -/
noncomputable def concreteTseitinKroneckerSystem
    (Φ : Tseitin.TseitinFormula) (pack : Tseitin.DisjointPacking Φ) (κ : ℕ) :
    IdentityMinorReal.KroneckerDeltaSystem ℚ (Tseitin.tseitinNumVars Φ)
      (Nat.choose pack.selected.length κ) :=
  IdentityMinorReal.buildKroneckerSystem
    (IdentityMinorReal.tseitinClauseSystem ℚ Φ pack) κ

/-- The `buildKroneckerSystem` rows for the concrete Tseitin clause system are
linearly independent.  This is the literal `IdentityMinorReal` Kronecker-delta
minor specialized to the packed clauses of `Φ`. -/
theorem concreteTseitinKroneckerSystem_rows_linearIndependent
    (Φ : Tseitin.TseitinFormula) (pack : Tseitin.DisjointPacking Φ) (κ : ℕ) :
    LinearIndependent ℚ
      (fun i : Fin (Nat.choose pack.selected.length κ) =>
        (concreteTseitinKroneckerSystem Φ pack κ).rows i) := by
  exact IdentityMinorReal.linearIndependent_of_kronecker
    (concreteTseitinKroneckerSystem Φ pack κ)

/-- Property 3 item (1), paper-scale concrete form.

For the actual paper-scale Tseitin formula `tseitinAt n`, the greedy packed
clause family gives the promised disjoint-support system; the abstract
`IdentityMinorReal.buildKroneckerSystem` has its Kronecker δ certificate; and
that same packed family gives the Kronecker δ rows obtained by differentiating
the actual `coupledVerifier ℚ (tseitinAt n)` in the selected selector
coordinates. -/
theorem paperScale_tseitinAt_coupledVerifier_property3_item1
    (n : ℕ) (hn1024 : n ≥ 2 ^ 10) (heven : 2 ∣ n) :
    ∃ pack : Tseitin.DisjointPacking (NPWitness.tseitinAt n),
      let sys := IdentityMinorReal.tseitinClauseSystem ℚ (NPWitness.tseitinAt n) pack
      (∀ i j : Fin sys.numClauses, i ≠ j →
        Disjoint (sys.clauseVars i) (sys.clauseVars j)) ∧
      (∀ i j : Fin (Nat.choose sys.numClauses (Nat.log 2 n)),
        MvPolynomial.coeff
          ((IdentityMinorReal.buildKroneckerSystem sys (Nat.log 2 n)).cols i)
          ((IdentityMinorReal.buildKroneckerSystem sys (Nat.log 2 n)).rows j) =
        if i = j then
          (IdentityMinorReal.buildKroneckerSystem sys (Nat.log 2 n)).signs i
        else 0) ∧
      (∀ i j : Fin (Nat.choose pack.selected.length (Nat.log 2 n)),
        MvPolynomial.coeff
          (IdentityMinor.tagMono ℚ (NPWitness.tseitinAt n) pack (Nat.log 2 n) i)
          (IdentityMinor.rowPoly ℚ (NPWitness.tseitinAt n) pack (Nat.log 2 n) j) =
        if i = j then
          IdentityMinor.subsetSign ℚ (NPWitness.tseitinAt n) pack (Nat.log 2 n) i
        else 0) := by
  have hv := NPWitness.tseitinAt_vertices n (by omega) heven
  have hverts : (NPWitness.tseitinAt n).graph.numVertices ≥ 100 := by
    rw [hv]
    omega
  let pack := Tseitin.disjoint_packing_exists (NPWitness.tseitinAt n) hverts
  refine ⟨pack, ?_⟩
  let sys := IdentityMinorReal.tseitinClauseSystem ℚ (NPWitness.tseitinAt n) pack
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    exact sys.disjoint i j hij
  · intro i j
    exact (IdentityMinorReal.buildKroneckerSystem sys (Nat.log 2 n)).kronecker i j
  · intro i j
    exact IdentityMinor.kronecker_delta (F := ℚ) (NPWitness.tseitinAt n) pack (Nat.log 2 n) i j

/-- Item-(1) bridge, concrete Tseitin form: the explicit
`IdentityMinorReal.buildKroneckerSystem` attached to a disjoint packing of `Φ`
is the source identity-minor certificate consumed by the projected/private-tag
right-inverse machinery, giving the SPDP rank lower bound for the actual
`coupledVerifier ℚ Φ` at the canonical Tseitin partition. -/
theorem concreteTseitinKroneckerSystem_feeds_coupledVerifier_rank
    (Φ : Tseitin.TseitinFormula) (pack : Tseitin.DisjointPacking Φ) (κ ℓ : ℕ) :
    mlBlockedSpdpRank (IdentityMinor.tseitinPartition Φ) κ ℓ
      (Tseitin.coupledVerifier ℚ Φ) ≥ Nat.choose pack.selected.length κ := by
  exact coupledVerifier_projected_identity_minor_rank_lower_from_rightInverse
    (F := ℚ) Φ pack κ ℓ

/-- Paper-scale Tseitin specialization of the bridge: at `Φ = tseitinAt n` and
`κ = ℓ = log₂ n`, the concrete coupled verifier carries a minor of size at
least `choose (n/30) (log₂ n)`.  This is the paper-scale instance to plug into
Route B before the remaining Property-2 Booleanity/product obligations. -/
theorem paperScale_tseitinAt_coupledVerifier_identityMinor_bridge
    (n : ℕ) (hn1024 : n ≥ 2 ^ 10) (heven : 2 ∣ n) :
    Nat.choose (n / 30) (Nat.log 2 n) ≤
      mlBlockedSpdpRank (IdentityMinor.tseitinPartition (NPWitness.tseitinAt n))
        (Nat.log 2 n) (Nat.log 2 n)
        (Tseitin.coupledVerifier ℚ (NPWitness.tseitinAt n)) := by
  exact tseitinAt_coupledVerifier_projected_rank_lower_choose_div30_from_rightInverse
    ℚ n hn1024 heven

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

/-- Concrete Step247 Cook-Levin preservation for the actual `T_Φ` extraction
pipeline.  The source identity-minor lower bound on the verifier sheet is
carried by the basis/relabel/restrict/project composite applied to the full
compiler output. -/
theorem partitionedOutput_cookLevin_T_Phi_projectedCompilerIdentityMinorLowerBound
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn2 : n ≥ 2)
    (Φ : Finset
      (Step4Compiler.Step247.partitioned_output_cookLevin
        M n hn2 htb hns).σ.Idx) :
    PaperFaithfulProjectedCompilerIdentityMinorLowerBound n
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ
      (extendedCookLevinPartition M n hn2)
      (Nat.log 2 n) (Nat.log 2 n)
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).Q_verifier
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).full_output
      (Step4Compiler.T_Phi
        (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ
        Φ) := by
  exact PallLean.Paper93.DeepMath.PathB.partitionedOutput_T_Phi_projectedCompilerIdentityMinorLowerBound_of_source
    n (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns)
    Φ (extendedCookLevinPartition M n hn2)
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

/-- ConcreteW row embeddings supply the template-collapse hypothesis needed
for the concrete projected Cook-Levin P-side bound. -/
theorem cookLevinProjectedPSideBound_of_concreteW_rowEmbeddings
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn2 : n ≥ 2) (hn4 : n ≥ 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4) :
    CookLevinProjectedPSideBound M n hn2 htb hns :=
  cookLevinProjectedPSideBound_of_templateCollapse
    M n hn htb hns hn2
    (cookLevinProfileTemplateCollapseLemma_of_concreteW_rowEmbeddings
      M n hn2 htb hns hn4 hRowEmbeddings)

/-- The concreteW H3/H4/I5 closure-frontier feeds the projected Cook-Levin
P-side bound through the row-embedding bridge.  The frontier itself remains
load-bearing: canonical H4 is separately refuted by
`not_CookLevinConcreteWRowEmbeddingClosureFrontier`. -/
theorem cookLevinProjectedPSideBound_of_concreteW_closureFrontier
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn2 : n ≥ 2) (hn4 : n ≥ 4)
    (hFrontier :
      CookLevinConcreteWRowEmbeddingClosureFrontier M n hn2 htb hns hn4) :
    CookLevinProjectedPSideBound M n hn2 htb hns :=
  cookLevinProjectedPSideBound_of_concreteW_rowEmbeddings
    M n hn htb hns hn2 hn4
    (CookLevinPerTypeRowEmbeddings_concreteW_of_closureFrontier
      M n hn2 htb hns hn4 hFrontier)

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

/-- Fully instantiated projected Cook-Levin contradiction from the concreteW
row-embedding package.  This keeps the Route B endpoint on the staged
projection/extraction path and exposes the remaining algebra as the concreteW
row-embedding closure package. -/
theorem false_of_cookLevin_concreteW_rowEmbeddings_projected
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn2 : n ≥ 2) (hn4 : n ≥ 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4) :
    False :=
  false_of_cookLevinProjectedPSideBound M n hn htb hns hn2
    (cookLevinProjectedPSideBound_of_concreteW_rowEmbeddings
      M n hn htb hns hn2 hn4 hRowEmbeddings)

/-- Projected Cook-Levin contradiction from the concreteW closure frontier.
This is intentionally a frontier-consuming theorem, not an unconditional
claim: the canonical frontier is impossible unless the Route B local interface
is corrected away from the old H4 field. -/
theorem false_of_cookLevin_concreteW_closureFrontier_projected
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn2 : n ≥ 2) (hn4 : n ≥ 4)
    (hFrontier :
      CookLevinConcreteWRowEmbeddingClosureFrontier M n hn2 htb hns hn4) :
    False :=
  false_of_cookLevinProjectedPSideBound M n hn htb hns hn2
    (cookLevinProjectedPSideBound_of_concreteW_closureFrontier
      M n hn htb hns hn2 hn4 hFrontier)

/-! ## Axiom audit anchors -/

#print axioms concreteTseitinKroneckerSystem_rows_linearIndependent
#print axioms paperScale_tseitinAt_coupledVerifier_property3_item1
#print axioms concreteTseitinKroneckerSystem_feeds_coupledVerifier_rank
#print axioms paperScale_tseitinAt_coupledVerifier_identityMinor_bridge
#print axioms sourceIdentityMinorLowerBound_cookLevin_partitionedOutput
#print axioms partitionedOutput_cookLevin_projectedIdentityMinorLowerBound
#print axioms partitionedOutput_cookLevin_projectedCompilerIdentityMinorLowerBound
#print axioms partitionedOutput_cookLevin_T_Phi_projectedCompilerIdentityMinorLowerBound
#print axioms paperFaithfulProjectedContradictionPackage_cookLevin_of_pSide
#print axioms false_of_cookLevinProjectedPSideBound
#print axioms cookLevinProjectedPSideBound_of_templateCollapse
#print axioms cookLevinProjectedPSideBound_of_concreteW_rowEmbeddings
#print axioms cookLevinProjectedPSideBound_of_concreteW_closureFrontier
#print axioms paperFaithfulProjectedContradictionPackage_cookLevin_of_templateCollapse
#print axioms false_of_cookLevin_templateCollapse_projected
#print axioms false_of_cookLevin_concreteW_rowEmbeddings_projected
#print axioms false_of_cookLevin_concreteW_closureFrontier_projected

end ProjectedIdentityMinorConcrete

end PallLean.Paper93.DeepMath.PathB
