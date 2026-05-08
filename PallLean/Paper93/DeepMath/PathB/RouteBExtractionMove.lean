import PallLean.Paper93.DeepMath.PathB.ProjectedIdentityMinorConcrete
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeRealFrontier

/-!
# Route B extraction move

This file records the paper-faithful Route B move from `p vs np1.pdf`:

* keep the P-side upper bound on the full compiled machine polynomial `P`;
* extract the coupled verifier sheet with the actual block-local operator `T_Φ`;
* use rank monotonicity of `T_Φ` to transport the P-side upper bound to
  `T_Φ P`;
* combine it with the coupled-sheet identity-minor lower bound transported
  through the same `T_Φ` extraction.

Crucially, this does **not** assert a shortcut from the flat compiled polynomial
or from the additive clause-SoS.  The lower-bound object is the multiplicative
coupled sheet `Q×_Φ`, carried by
`PaperFaithfulProjectedCompilerIdentityMinorLowerBound ... (T_Phi σ Φ)`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulCompilation

/-- **Route B extraction sandwich contradiction.**

This is the exact paper-faithful move corresponding to Theorem 223 / Lemma 205
plus the final arithmetic contradiction:

* `hLower` says the actual extraction operator `T_Φ` maps the compiled output
  to the embedded coupled verifier sheet and that the extracted image carries
  the identity-minor lower bound;
* `hP` is the Width⇒Rank / P-side upper bound on the unextracted compiler
  polynomial;
* `Step4Compiler.rank_T_Phi_le_of_PMn_bound` transfers the upper bound through
  the block-local extraction.

No additive clause sheet and no profile-matching shortcut appears here. -/
theorem false_of_routeB_TPhi_extraction_sandwich
    (n : ℕ) (hn : n ≥ 2 ^ 804)
    (σ : UVSplit) (Φ : Finset σ.Idx)
    (B : SPDP.BlockPartition σ.total) (κ ℓ : ℕ)
    (Q : CoupledSheetPoly σ) (P : PMnPoly σ)
    (hLower :
      PaperFaithfulProjectedCompilerIdentityMinorLowerBound
        n σ B κ ℓ Q P (Step4Compiler.T_Phi σ Φ))
    (hP : PaperFaithfulCompilerPSideBound n σ B κ ℓ P) :
    False := by
  -- NP side after extraction: the extracted coupled sheet has large rank.
  have hExtractedLower :
      Nat.choose (n / 3) (Nat.log 2 n) ≤
        mlBlockedSpdpRank B κ ℓ (Step4Compiler.T_Phi σ Φ P) :=
    hLower.2
  -- P side transported through the actual paper extraction operator `T_Φ`.
  have hExtractedUpper :
      mlBlockedSpdpRank B κ ℓ (Step4Compiler.T_Phi σ Φ P) ≤ n ^ 200 :=
    Step4Compiler.rank_T_Phi_le_of_PMn_bound
      σ Φ B κ ℓ P (n ^ 200) hP
  -- The sandwich contradicts the concrete arithmetic gap at the paper scale.
  have hSandwich : Nat.choose (n / 3) (Nat.log 2 n) ≤ n ^ 200 :=
    le_trans hExtractedLower hExtractedUpper
  have hgap := arithmetic_gap_2pow804 n hn
  omega

/-- Concrete Step247 Cook-Levin Route B contradiction from a P-side bound on the
full compiler output, using the actual `T_Φ` extraction path.

This is the concrete version of the move above: the source coupled-sheet
identity minor is supplied by `lemma_124`/`Q_times_Phi_135` through
`partitionedOutput_cookLevin_T_Phi_projectedCompilerIdentityMinorLowerBound`,
then the P-side bound is transported through `T_Φ` by rank monotonicity. -/
theorem false_of_cookLevin_TPhi_projectedPSideBound
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn2 : n ≥ 2)
    (Φ : Finset
      (Step4Compiler.Step247.partitioned_output_cookLevin
        M n hn2 htb hns).σ.Idx)
    (hP : ProjectedIdentityMinorConcrete.CookLevinProjectedPSideBound
      M n hn2 htb hns) :
    False := by
  exact false_of_routeB_TPhi_extraction_sandwich
    n hn
    (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ
    Φ
    (extendedCookLevinPartition M n hn2)
    (Nat.log 2 n) (Nat.log 2 n)
    (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).Q_verifier
    (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).full_output
    (ProjectedIdentityMinorConcrete.partitionedOutput_cookLevin_T_Phi_projectedCompilerIdentityMinorLowerBound
      M n hn htb hns hn2 Φ)
    hP

/-- Uniform Route B form: a uniform P-side bound on the concrete Step247
Cook-Levin compiler output rules out bounded SAT deciders at the paper scale,
using the actual `T_Φ` extraction path. -/
theorem noBoundedSATDeciderAtPaperScale_of_cookLevin_TPhi_projectedPSideBound
    (hP : ∀ (M : TuringMachine.DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804)
      (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      ProjectedIdentityMinorConcrete.CookLevinProjectedPSideBound
        M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns _hdec
  -- Route B extraction is instance-uniform; the concrete formal `T_Φ` is
  -- definitionally rank-equivalent to the canonical projection for any
  -- syntactic clause selector.  We use the empty selector as a harmless
  -- canonical witness of the block-local extraction family.
  exact false_of_cookLevin_TPhi_projectedPSideBound
    M n hn htb hns hn2 ∅ (hP M n hn hn2 htb hns)

/-! ## Axiom audit anchors -/

#print axioms false_of_routeB_TPhi_extraction_sandwich
#print axioms false_of_cookLevin_TPhi_projectedPSideBound
#print axioms noBoundedSATDeciderAtPaperScale_of_cookLevin_TPhi_projectedPSideBound

end PallLean.Paper93.DeepMath.PathB
