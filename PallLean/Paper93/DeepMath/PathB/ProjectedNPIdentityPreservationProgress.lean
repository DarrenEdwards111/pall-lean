import PallLean.Paper93.DeepMath.PathB.ProjectedIdentityMinorPaperFaithful
import PallLean.Paper93.DeepMath.PathB.ProjectedIdentityMinorConcrete
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeNPBridge
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeFinalTarget

/-!
# Projected NP identity-minor preservation progress

This file isolates the reusable NP-side preservation criterion for a projected
gauge image.  The criterion is intentionally local: if a projection fixes an
embedded source obstruction and the chosen compiler polynomial extracts to that
fixed image, then the source lower bound is enough to discharge the flat
`SATDeciderGaugeNPIdentityMinorPreservation` field for the gauge image.

No P-side collapse or final gauge existence is asserted here.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine

/-- A fixed embedded obstruction plus an extraction identity gives the
paper-faithful projected compiler identity-minor lower bound.

This is the reusable projection criterion: the extraction identity is stated as
`Pi P = Pi (embed Q)`, while the fixed-image hypothesis identifies that image
with `embed Q`. -/
theorem paperFaithfulProjectedCompilerIdentityMinorLowerBound_of_fixed_embed_extraction_source
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ) (P : PMnPoly σ)
    (Pi : PaperFaithfulProjection σ)
    (hfix : Pi (CoupledSheetPoly.embed σ Q) = CoupledSheetPoly.embed σ Q)
    (hextract : Pi P = Pi (CoupledSheetPoly.embed σ Q))
    (hsource : SourceIdentityMinorLowerBound n σ B κ ℓ Q) :
    PaperFaithfulProjectedCompilerIdentityMinorLowerBound
      n σ B κ ℓ Q P Pi := by
  exact projectedCompilerIdentityMinorLowerBound_of_extraction_and_source
    n σ B κ ℓ Q P Pi (hextract.trans hfix) hsource

/-- Flat Cook-Levin specialization of the fixed-image criterion: it produces
exactly the raw projected lower bound consumed by the SAT-decider NP bridge. -/
theorem flatProjectedCompiledLowerBound_of_fixed_embed_extraction_source
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hfix :
      gauge (CoupledSheetPoly.embed
        (flatCookLevinUVSplit M n hn2 htb hns) Q) =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        gauge (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns))) := by
  have hpaper :
      PaperFaithfulProjectedCompilerIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q
        (compiledPoly (cook_levin_compilation M n hn2 htb hns))
        gauge :=
    paperFaithfulProjectedCompilerIdentityMinorLowerBound_of_fixed_embed_extraction_source
      n (flatCookLevinUVSplit M n hn2 htb hns)
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) Q
      (compiledPoly (cook_levin_compilation M n hn2 htb hns))
      gauge hfix hextract hsource
  exact hpaper.2

/-- Flat Cook-Levin projected lower bound directly from explicit Kronecker
rows.  This is the concrete SAT-decider-facing version of Property 3: it no
longer asks for a prepackaged `SourceIdentityMinorLowerBound`; the source
lower bound is built from row membership, row count, and the dual delta law. -/
theorem flatProjectedCompiledLowerBound_of_fixed_embed_extraction_dual_kronecker_rows
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : ι → CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (dual : ι → CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns) →ₗ[ℚ] ℚ)
    (hfix :
      gauge (CoupledSheetPoly.embed
        (flatCookLevinUVSplit M n hn2 htb hns) Q) =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        gauge (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hcard : Nat.choose (n / 3) (Nat.log 2 n) ≤ Fintype.card ι)
    (hmem : ∀ i, b i ∈ mlBlockedSpdpSubspace
      (pullbackPartition
        (cook_levin_compilation M n hn2 htb hns).partition
        (flatCookLevinUVSplit M n hn2 htb hns).inlU)
      (Nat.log 2 n) (Nat.log 2 n) Q)
    (hdual : ∀ i j, dual i (b j) = if i = j then (1 : ℚ) else 0) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns))) := by
  have hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q :=
    sourceIdentityMinorLowerBound_of_dual_kronecker_rows
      n (flatCookLevinUVSplit M n hn2 htb hns)
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) Q b dual hcard hmem hdual
  exact flatProjectedCompiledLowerBound_of_fixed_embed_extraction_source
    M n hn2 htb hns Q gauge hfix hextract hsource

/-- Flat Cook-Levin projected lower bound directly from an `IdentityMinorReal`
coefficient-space Kronecker system over the coupled-sheet variables. -/
theorem flatProjectedCompiledLowerBound_of_fixed_embed_extraction_kroneckerDeltaSystem_rows
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    {N : ℕ}
    (sys : IdentityMinorReal.KroneckerDeltaSystem ℚ
      (flatCookLevinUVSplit M n hn2 htb hns).numU N)
    (hfix :
      gauge (CoupledSheetPoly.embed
        (flatCookLevinUVSplit M n hn2 htb hns) Q) =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        gauge (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hcard : Nat.choose (n / 3) (Nat.log 2 n) ≤ N)
    (hmem : ∀ i, sys.rows i ∈ mlBlockedSpdpSubspace
      (pullbackPartition
        (cook_levin_compilation M n hn2 htb hns).partition
        (flatCookLevinUVSplit M n hn2 htb hns).inlU)
      (Nat.log 2 n) (Nat.log 2 n) Q) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns))) := by
  have hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q :=
    sourceIdentityMinorLowerBound_of_kroneckerDeltaSystem_rows
      n (flatCookLevinUVSplit M n hn2 htb hns)
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) Q sys hcard hmem
  exact flatProjectedCompiledLowerBound_of_fixed_embed_extraction_source
    M n hn2 htb hns Q gauge hfix hextract hsource

/-- SAT-decider NP identity-minor preservation follows for any gauge whose
compiled-polynomial image extracts to a fixed embedded source obstruction
carrying the source lower bound. -/
theorem satDeciderGaugeNPIdentityMinorPreservation_of_fixed_embed_extraction_source
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hfix :
      gauge (CoupledSheetPoly.embed
        (flatCookLevinUVSplit M n hn2 htb hns) Q) =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        gauge (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns gauge := by
  exact satDeciderGaugeNPIdentityMinorPreservation_of_projected_compiled_lower_bound
    M n hn2 htb hns gauge
    (flatProjectedCompiledLowerBound_of_fixed_embed_extraction_source
      M n hn2 htb hns Q gauge hfix hextract hsource)

/-- SAT-decider NP preservation directly from explicit Kronecker rows. -/
theorem satDeciderGaugeNPIdentityMinorPreservation_of_fixed_embed_extraction_dual_kronecker_rows
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : ι → CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (dual : ι → CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns) →ₗ[ℚ] ℚ)
    (hfix :
      gauge (CoupledSheetPoly.embed
        (flatCookLevinUVSplit M n hn2 htb hns) Q) =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        gauge (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hcard : Nat.choose (n / 3) (Nat.log 2 n) ≤ Fintype.card ι)
    (hmem : ∀ i, b i ∈ mlBlockedSpdpSubspace
      (pullbackPartition
        (cook_levin_compilation M n hn2 htb hns).partition
        (flatCookLevinUVSplit M n hn2 htb hns).inlU)
      (Nat.log 2 n) (Nat.log 2 n) Q)
    (hdual : ∀ i j, dual i (b j) = if i = j then (1 : ℚ) else 0) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns gauge := by
  exact satDeciderGaugeNPIdentityMinorPreservation_of_projected_compiled_lower_bound
    M n hn2 htb hns gauge
    (flatProjectedCompiledLowerBound_of_fixed_embed_extraction_dual_kronecker_rows
      M n hn2 htb hns Q gauge b dual hfix hextract hcard hmem hdual)

/-- SAT-decider NP preservation directly from a coefficient-space Kronecker
system over the coupled-sheet variables. -/
theorem satDeciderGaugeNPIdentityMinorPreservation_of_fixed_embed_extraction_kroneckerDeltaSystem_rows
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    {N : ℕ}
    (sys : IdentityMinorReal.KroneckerDeltaSystem ℚ
      (flatCookLevinUVSplit M n hn2 htb hns).numU N)
    (hfix :
      gauge (CoupledSheetPoly.embed
        (flatCookLevinUVSplit M n hn2 htb hns) Q) =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        gauge (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hcard : Nat.choose (n / 3) (Nat.log 2 n) ≤ N)
    (hmem : ∀ i, sys.rows i ∈ mlBlockedSpdpSubspace
      (pullbackPartition
        (cook_levin_compilation M n hn2 htb hns).partition
        (flatCookLevinUVSplit M n hn2 htb hns).inlU)
      (Nat.log 2 n) (Nat.log 2 n) Q) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns gauge := by
  exact satDeciderGaugeNPIdentityMinorPreservation_of_projected_compiled_lower_bound
    M n hn2 htb hns gauge
    (flatProjectedCompiledLowerBound_of_fixed_embed_extraction_kroneckerDeltaSystem_rows
      M n hn2 htb hns Q gauge sys hfix hextract hcard hmem)

/-- The same NP-side criterion plugs into the final rich-projection target once
rank monotonicity and the template-collapse P-side frontier are supplied. -/
theorem cookLevinRichProjectionTarget_of_templateCollapse_of_fixed_embed_extraction_source
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hrank : SATDeciderGaugeRankMonotonicity M n hn2 htb hns gauge)
    (hfix :
      gauge (CoupledSheetPoly.embed
        (flatCookLevinUVSplit M n hn2 htb hns) Q) =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        gauge (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q)
    (hcollapse : WithinProfileBound.CookLevinProfileTemplateCollapseLemma
      M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns := by
  refine cookLevinRichProjectionTarget_of_templateCollapse_of_npPreservation
    M n hn hn2 htb hns gauge hrank ?_ hcollapse
  exact satDeciderGaugeNPIdentityMinorPreservation_of_fixed_embed_extraction_source
    M n hn2 htb hns Q gauge hfix hextract hsource

/-- Final rich-projection target directly from explicit Kronecker rows, plus
the P-side template-collapse input. -/
theorem cookLevinRichProjectionTarget_of_templateCollapse_of_fixed_embed_extraction_dual_kronecker_rows
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : ι → CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (dual : ι → CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns) →ₗ[ℚ] ℚ)
    (hrank : SATDeciderGaugeRankMonotonicity M n hn2 htb hns gauge)
    (hfix :
      gauge (CoupledSheetPoly.embed
        (flatCookLevinUVSplit M n hn2 htb hns) Q) =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        gauge (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hcard : Nat.choose (n / 3) (Nat.log 2 n) ≤ Fintype.card ι)
    (hmem : ∀ i, b i ∈ mlBlockedSpdpSubspace
      (pullbackPartition
        (cook_levin_compilation M n hn2 htb hns).partition
        (flatCookLevinUVSplit M n hn2 htb hns).inlU)
      (Nat.log 2 n) (Nat.log 2 n) Q)
    (hdual : ∀ i j, dual i (b j) = if i = j then (1 : ℚ) else 0)
    (hcollapse : WithinProfileBound.CookLevinProfileTemplateCollapseLemma
      M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns := by
  refine cookLevinRichProjectionTarget_of_templateCollapse_of_npPreservation
    M n hn hn2 htb hns gauge hrank ?_ hcollapse
  exact satDeciderGaugeNPIdentityMinorPreservation_of_fixed_embed_extraction_dual_kronecker_rows
    M n hn2 htb hns Q gauge b dual hfix hextract hcard hmem hdual

/-- Concrete Step247 Cook-Levin instance of the paper-faithful fixed-image
criterion, using the already-proved concrete source lower bound. -/
theorem concreteCookLevin_projectedCompilerIdentityMinorLowerBound_of_fixed_embed_extraction
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn2 : n ≥ 2)
    (Pi : PaperFaithfulProjection
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ)
    (hfix :
      Pi (CoupledSheetPoly.embed
        (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ
        (Step4Compiler.Step247.partitioned_output_cookLevin
          M n hn2 htb hns).Q_verifier) =
        CoupledSheetPoly.embed
          (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ
          (Step4Compiler.Step247.partitioned_output_cookLevin
            M n hn2 htb hns).Q_verifier)
    (hextract :
      Pi (Step4Compiler.Step247.partitioned_output_cookLevin
          M n hn2 htb hns).full_output =
        Pi (CoupledSheetPoly.embed
          (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ
          (Step4Compiler.Step247.partitioned_output_cookLevin
            M n hn2 htb hns).Q_verifier)) :
    PaperFaithfulProjectedCompilerIdentityMinorLowerBound n
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ
      (extendedCookLevinPartition M n hn2)
      (Nat.log 2 n) (Nat.log 2 n)
      (Step4Compiler.Step247.partitioned_output_cookLevin
        M n hn2 htb hns).Q_verifier
      (Step4Compiler.Step247.partitioned_output_cookLevin
        M n hn2 htb hns).full_output
      Pi := by
  exact paperFaithfulProjectedCompilerIdentityMinorLowerBound_of_fixed_embed_extraction_source
    n (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ
    (extendedCookLevinPartition M n hn2)
    (Nat.log 2 n) (Nat.log 2 n)
    (Step4Compiler.Step247.partitioned_output_cookLevin
      M n hn2 htb hns).Q_verifier
    (Step4Compiler.Step247.partitioned_output_cookLevin
      M n hn2 htb hns).full_output
    Pi hfix hextract
    (ProjectedIdentityMinorConcrete.sourceIdentityMinorLowerBound_cookLevin_partitionedOutput
      M n hn htb hns hn2)

/-- Concrete Step247 Cook-Levin instance with the source lower bound opened up
into explicit identity-minor rows and Kronecker duals.

This is the most local concrete form of the NP-side preservation criterion:
for the actual partitioned Cook-Levin output, it is enough to provide the row
family in the pulled-back verifier SPDP space, its dual certificate, and the
usual binomial row-count lower bound. -/
theorem concreteCookLevin_projectedCompilerIdentityMinorLowerBound_of_fixed_embed_extraction_dual_kronecker_rows
    (M : DTM) (n : ℕ)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn2 : n ≥ 2)
    (Pi : PaperFaithfulProjection
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ)
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : ι → CoupledSheetPoly
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ)
    (dual : ι → CoupledSheetPoly
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ →ₗ[ℚ] ℚ)
    (hfix :
      Pi (CoupledSheetPoly.embed
        (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ
        (Step4Compiler.Step247.partitioned_output_cookLevin
          M n hn2 htb hns).Q_verifier) =
        CoupledSheetPoly.embed
          (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ
          (Step4Compiler.Step247.partitioned_output_cookLevin
            M n hn2 htb hns).Q_verifier)
    (hextract :
      Pi (Step4Compiler.Step247.partitioned_output_cookLevin
          M n hn2 htb hns).full_output =
        Pi (CoupledSheetPoly.embed
          (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ
          (Step4Compiler.Step247.partitioned_output_cookLevin
            M n hn2 htb hns).Q_verifier))
    (hcard : Nat.choose (n / 3) (Nat.log 2 n) ≤ Fintype.card ι)
    (hmem : ∀ i, b i ∈ mlBlockedSpdpSubspace
      (pullbackPartition (extendedCookLevinPartition M n hn2)
        (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ.inlU)
      (Nat.log 2 n) (Nat.log 2 n)
      (Step4Compiler.Step247.partitioned_output_cookLevin
        M n hn2 htb hns).Q_verifier)
    (hdual : ∀ i j, dual i (b j) = if i = j then (1 : ℚ) else 0) :
    PaperFaithfulProjectedCompilerIdentityMinorLowerBound n
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ
      (extendedCookLevinPartition M n hn2)
      (Nat.log 2 n) (Nat.log 2 n)
      (Step4Compiler.Step247.partitioned_output_cookLevin
        M n hn2 htb hns).Q_verifier
      (Step4Compiler.Step247.partitioned_output_cookLevin
        M n hn2 htb hns).full_output
      Pi := by
  exact paperFaithfulProjectedCompilerIdentityMinorLowerBound_of_fixed_embed_extraction_source
    n (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ
    (extendedCookLevinPartition M n hn2)
    (Nat.log 2 n) (Nat.log 2 n)
    (Step4Compiler.Step247.partitioned_output_cookLevin
      M n hn2 htb hns).Q_verifier
    (Step4Compiler.Step247.partitioned_output_cookLevin
      M n hn2 htb hns).full_output
    Pi hfix hextract
    (sourceIdentityMinorLowerBound_of_dual_kronecker_rows
      n (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ
      (extendedCookLevinPartition M n hn2)
      (Nat.log 2 n) (Nat.log 2 n)
      (Step4Compiler.Step247.partitioned_output_cookLevin
        M n hn2 htb hns).Q_verifier
      b dual hcard hmem hdual)

/-- The concrete `piPhi` projection is recovered as an instance of the
fixed-image criterion, using `piPhi_embed_eq` for fixedness and the Step241
extraction theorem for the full Cook-Levin output. -/
theorem concreteCookLevin_piPhi_projectedCompilerIdentityMinorLowerBound_via_fixed_embed
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn2 : n ≥ 2) :
    PaperFaithfulProjectedCompilerIdentityMinorLowerBound n
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ
      (extendedCookLevinPartition M n hn2)
      (Nat.log 2 n) (Nat.log 2 n)
      (Step4Compiler.Step247.partitioned_output_cookLevin
        M n hn2 htb hns).Q_verifier
      (Step4Compiler.Step247.partitioned_output_cookLevin
        M n hn2 htb hns).full_output
      (piPhi
        (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ) := by
  let W := Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns
  refine concreteCookLevin_projectedCompilerIdentityMinorLowerBound_of_fixed_embed_extraction
    M n hn htb hns hn2
    (piPhi
      (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).σ) ?_ ?_
  · exact piPhi_embed_eq W.σ W.Q_verifier
  · rw [piPhi_embed_eq W.σ W.Q_verifier]
    simpa [W, Step4Compiler.Step241.PartitionedCompilerOutput.embedded_Q] using
      Step4Compiler.Step241.partitioned_output_piPhi_extracts W

/-! ## Axiom audit anchors -/

#print axioms paperFaithfulProjectedCompilerIdentityMinorLowerBound_of_fixed_embed_extraction_source
#print axioms flatProjectedCompiledLowerBound_of_fixed_embed_extraction_source
#print axioms flatProjectedCompiledLowerBound_of_fixed_embed_extraction_dual_kronecker_rows
#print axioms flatProjectedCompiledLowerBound_of_fixed_embed_extraction_kroneckerDeltaSystem_rows
#print axioms satDeciderGaugeNPIdentityMinorPreservation_of_fixed_embed_extraction_source
#print axioms satDeciderGaugeNPIdentityMinorPreservation_of_fixed_embed_extraction_dual_kronecker_rows
#print axioms satDeciderGaugeNPIdentityMinorPreservation_of_fixed_embed_extraction_kroneckerDeltaSystem_rows
#print axioms cookLevinRichProjectionTarget_of_templateCollapse_of_fixed_embed_extraction_source
#print axioms cookLevinRichProjectionTarget_of_templateCollapse_of_fixed_embed_extraction_dual_kronecker_rows
#print axioms concreteCookLevin_projectedCompilerIdentityMinorLowerBound_of_fixed_embed_extraction
#print axioms concreteCookLevin_projectedCompilerIdentityMinorLowerBound_of_fixed_embed_extraction_dual_kronecker_rows
#print axioms concreteCookLevin_piPhi_projectedCompilerIdentityMinorLowerBound_via_fixed_embed

end PallLean.Paper93.DeepMath.PathB
