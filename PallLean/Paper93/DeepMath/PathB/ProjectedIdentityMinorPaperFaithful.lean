import PallLean.Step4Compiler

/-!
# Paper-faithful projected identity-minor frontier

The flat SAT-decider gauge field used by `GlobalGodMoveGauge` asks for both
the P-side upper bound and the NP identity-minor lower bound on the same
polynomial `gauge (compiledPoly ...)`.  That is the right contradiction once
all paper hypotheses are assembled, but it is not the paper's intermediate
object language.

This file records the paper-faithful formulation used by Path A / Lemma 205:

* the NP identity minor is first a lower bound on the coupled sheet
  `Q : CoupledSheetPoly σ` over the `u` variables;
* the projected/compiler-side hard object is `Π P = embed σ Q`;
* the lower bound is transported through the `embed` rank-preservation theorem.

So the identity-minor preservation surface is stated on the projected extracted
object `Π P`, not directly on the flat Cook-Levin `compiledPoly`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulCompilation

/-- A paper-faithful projection over the `u/v` split ambient polynomial space. -/
abbrev PaperFaithfulProjection (σ : UVSplit) : Type :=
  PMnPoly σ →ₗ[ℚ] PMnPoly σ

/-- Source-side identity-minor lower bound on the coupled sheet `Q`.

This is the paper §18 / §40.3 object: the rank is measured before embedding,
against the pulled-back block partition on the `u` variables. -/
def SourceIdentityMinorLowerBound
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ) : Prop :=
  Nat.choose (n / 3) (Nat.log 2 n) ≤
    mlBlockedSpdpRank (pullbackPartition B σ.inlU) κ ℓ Q

/-- Projected identity-minor lower bound on the embedded hard object.

Unlike `SATDeciderGaugeNPIdentityMinorPreservation`, this formulation does not
mention the flat `compiledPoly`.  It asks whether the projection preserves the
embedded coupled-sheet obstruction. -/
def PaperFaithfulProjectedIdentityMinorLowerBound
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ)
    (Pi : PaperFaithfulProjection σ) : Prop :=
  Nat.choose (n / 3) (Nat.log 2 n) ≤
    mlBlockedSpdpRank B κ ℓ (Pi (CoupledSheetPoly.embed σ Q))

/-- Projected compiler-side identity-minor lower bound.

This is the paper Lemma 205 shape: a compiler polynomial `P` extracts to the
embedded hard object under the projection, and that projected image carries the
identity-minor lower bound. -/
def PaperFaithfulProjectedCompilerIdentityMinorLowerBound
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ) (P : PMnPoly σ)
    (Pi : PaperFaithfulProjection σ) : Prop :=
  Pi P = CoupledSheetPoly.embed σ Q ∧
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank B κ ℓ (Pi P)

/-- The projected identity-minor lower bound follows from the source lower
bound when the projection fixes the embedded hard object. -/
theorem projectedIdentityMinorLowerBound_of_source_of_fixed_embed
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ)
    (Pi : PaperFaithfulProjection σ)
    (hfix : Pi (CoupledSheetPoly.embed σ Q) = CoupledSheetPoly.embed σ Q)
    (hsource : SourceIdentityMinorLowerBound n σ B κ ℓ Q) :
    PaperFaithfulProjectedIdentityMinorLowerBound n σ B κ ℓ Q Pi := by
  unfold PaperFaithfulProjectedIdentityMinorLowerBound
  rw [hfix]
  exact le_trans hsource (embed_rank_preservation σ B κ ℓ Q)

/-- The compiler-side projected lower bound follows from the extraction
identity `Π P = embed σ Q` and the source identity-minor lower bound. -/
theorem projectedCompilerIdentityMinorLowerBound_of_extraction_and_source
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ) (P : PMnPoly σ)
    (Pi : PaperFaithfulProjection σ)
    (hExtract : Pi P = CoupledSheetPoly.embed σ Q)
    (hsource : SourceIdentityMinorLowerBound n σ B κ ℓ Q) :
    PaperFaithfulProjectedCompilerIdentityMinorLowerBound n σ B κ ℓ Q P Pi := by
  refine ⟨hExtract, ?_⟩
  rw [hExtract]
  exact le_trans hsource (embed_rank_preservation σ B κ ℓ Q)

/-- The concrete `piPhi` projection preserves the embedded identity-minor
obstruction whenever the source coupled sheet has the lower bound. -/
theorem piPhi_projectedIdentityMinorLowerBound_of_source
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ)
    (hsource : SourceIdentityMinorLowerBound n σ B κ ℓ Q) :
    PaperFaithfulProjectedIdentityMinorLowerBound n σ B κ ℓ Q (piPhi σ) :=
  projectedIdentityMinorLowerBound_of_source_of_fixed_embed
    n σ B κ ℓ Q (piPhi σ) (piPhi_embed_eq σ Q) hsource

/-- The paper Lemma 205 extraction identity plus the source lower bound gives
the projected compiler-side identity-minor lower bound for `piPhi`. -/
theorem piPhi_projectedCompilerIdentityMinorLowerBound_of_extraction
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ) (P : PMnPoly σ)
    (hExtract : piPhi σ P = CoupledSheetPoly.embed σ Q)
    (hsource : SourceIdentityMinorLowerBound n σ B κ ℓ Q) :
    PaperFaithfulProjectedCompilerIdentityMinorLowerBound n σ B κ ℓ Q P (piPhi σ) :=
  projectedCompilerIdentityMinorLowerBound_of_extraction_and_source
    n σ B κ ℓ Q P (piPhi σ) hExtract hsource

/-- The explicit paper extraction operator `T_Φ` preserves the embedded
identity-minor obstruction when the source coupled sheet has the lower bound.

This uses the actual factorized extraction map from `Step4Compiler`:
`T_Φ = basis ∘ affine relabel ∘ restriction ∘ projection`, which reduces to
`piPhi` in the canonical Cook-Levin basis. -/
theorem T_Phi_projectedIdentityMinorLowerBound_of_source
    (n : ℕ) (σ : UVSplit) (Φ : Finset σ.Idx)
    (B : SPDP.BlockPartition σ.total) (κ ℓ : ℕ)
    (Q : CoupledSheetPoly σ)
    (hsource : SourceIdentityMinorLowerBound n σ B κ ℓ Q) :
    PaperFaithfulProjectedIdentityMinorLowerBound
      n σ B κ ℓ Q (Step4Compiler.T_Phi σ Φ) := by
  apply projectedIdentityMinorLowerBound_of_source_of_fixed_embed
  · rw [Step4Compiler.T_Phi_eq_piPhi σ Φ]
    exact piPhi_embed_eq σ Q
  · exact hsource

/-- The paper Lemma 205 extraction equation for `T_Φ`, plus the source
identity-minor lower bound on the coupled sheet, gives the projected compiler
identity-minor lower bound on the extracted image. -/
theorem T_Phi_projectedCompilerIdentityMinorLowerBound_of_extraction
    (n : ℕ) (σ : UVSplit) (Φ : Finset σ.Idx)
    (B : SPDP.BlockPartition σ.total) (κ ℓ : ℕ)
    (Q : CoupledSheetPoly σ) (P : PMnPoly σ)
    (hExtract : piPhi σ P = CoupledSheetPoly.embed σ Q)
    (hsource : SourceIdentityMinorLowerBound n σ B κ ℓ Q) :
    PaperFaithfulProjectedCompilerIdentityMinorLowerBound
      n σ B κ ℓ Q P (Step4Compiler.T_Phi σ Φ) :=
  projectedCompilerIdentityMinorLowerBound_of_extraction_and_source
    n σ B κ ℓ Q P (Step4Compiler.T_Phi σ Φ)
    (Step4Compiler.T_Phi_image_of_PMn_real_embed σ Φ P Q hExtract)
    hsource

/-- Projected identity-minor lower bound for a paper §40 partitioned output.

This is the direct `Step241.PartitionedCompilerOutput` formulation: once the
embedded verifier sheet has the identity-minor lower bound, the projected full
compiler output has the same lower bound because `piPhi` extracts exactly
`embedded_Q`. -/
def PartitionedOutputProjectedIdentityMinorLowerBound
    (n : ℕ) (W : Step4Compiler.Step241.PartitionedCompilerOutput)
    (B : SPDP.BlockPartition W.σ.total) (κ ℓ : ℕ) : Prop :=
  Nat.choose (n / 3) (Nat.log 2 n) ≤
    mlBlockedSpdpRank B κ ℓ (piPhi W.σ W.full_output)

/-- If the embedded verifier sheet has the identity-minor lower bound, then
the projected full partitioned output has it too. -/
theorem partitionedOutput_projectedIdentityMinorLowerBound_of_embedded
    (n : ℕ) (W : Step4Compiler.Step241.PartitionedCompilerOutput)
    (B : SPDP.BlockPartition W.σ.total) (κ ℓ : ℕ)
    (hembedded :
      Nat.choose (n / 3) (Nat.log 2 n) ≤
        mlBlockedSpdpRank B κ ℓ W.embedded_Q) :
    PartitionedOutputProjectedIdentityMinorLowerBound n W B κ ℓ := by
  unfold PartitionedOutputProjectedIdentityMinorLowerBound
  rw [Step4Compiler.Step241.partitioned_output_piPhi_extracts W]
  exact hembedded

/-- Source-side identity-minor lower bound on `W.Q_verifier` lifts to the
projected full partitioned output. -/
theorem partitionedOutput_projectedIdentityMinorLowerBound_of_source
    (n : ℕ) (W : Step4Compiler.Step241.PartitionedCompilerOutput)
    (B : SPDP.BlockPartition W.σ.total) (κ ℓ : ℕ)
    (hsource : SourceIdentityMinorLowerBound n W.σ B κ ℓ W.Q_verifier) :
    PartitionedOutputProjectedIdentityMinorLowerBound n W B κ ℓ := by
  apply partitionedOutput_projectedIdentityMinorLowerBound_of_embedded
  change Nat.choose (n / 3) (Nat.log 2 n) ≤
    mlBlockedSpdpRank B κ ℓ (CoupledSheetPoly.embed W.σ W.Q_verifier)
  exact le_trans hsource (embed_rank_preservation W.σ B κ ℓ W.Q_verifier)

/-- The partitioned output directly satisfies the paper-faithful projected
compiler-side identity-minor field. -/
theorem partitionedOutput_projectedCompilerIdentityMinorLowerBound_of_source
    (n : ℕ) (W : Step4Compiler.Step241.PartitionedCompilerOutput)
    (B : SPDP.BlockPartition W.σ.total) (κ ℓ : ℕ)
    (hsource : SourceIdentityMinorLowerBound n W.σ B κ ℓ W.Q_verifier) :
    PaperFaithfulProjectedCompilerIdentityMinorLowerBound
      n W.σ B κ ℓ W.Q_verifier W.full_output (piPhi W.σ) := by
  apply projectedCompilerIdentityMinorLowerBound_of_extraction_and_source
  · simpa [Step4Compiler.Step241.PartitionedCompilerOutput.embedded_Q] using
      Step4Compiler.Step241.partitioned_output_piPhi_extracts W
  · exact hsource

/-- Partitioned-output form for the actual `T_Φ` extraction pipeline.  The
same source lower bound survives the basis/relabel/restrict/project composite
because the full compiler output extracts to the embedded verifier sheet. -/
theorem partitionedOutput_T_Phi_projectedCompilerIdentityMinorLowerBound_of_source
    (n : ℕ) (W : Step4Compiler.Step241.PartitionedCompilerOutput)
    (Φ : Finset W.σ.Idx)
    (B : SPDP.BlockPartition W.σ.total) (κ ℓ : ℕ)
    (hsource : SourceIdentityMinorLowerBound n W.σ B κ ℓ W.Q_verifier) :
    PaperFaithfulProjectedCompilerIdentityMinorLowerBound
      n W.σ B κ ℓ W.Q_verifier W.full_output
        (Step4Compiler.T_Phi W.σ Φ) := by
  apply T_Phi_projectedCompilerIdentityMinorLowerBound_of_extraction
  · simpa [Step4Compiler.Step241.PartitionedCompilerOutput.embedded_Q] using
      Step4Compiler.Step241.partitioned_output_piPhi_extracts W
  · exact hsource

/-- Paper-faithful P-side upper bound: the small-rank statement belongs to
the compiler polynomial `P`, while the lower bound belongs to its projected
extracted image. -/
def PaperFaithfulCompilerPSideBound
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (P : PMnPoly σ) : Prop :=
  mlBlockedSpdpRank B κ ℓ P ≤ n ^ 200

/-- The paper-faithful projected contradiction package.

This is the precise non-flat formulation: source `Q` has the identity-minor
lower bound, `P` extracts to `embed Q` through `piPhi`, and `P` has the P-side
rank bound. -/
def PaperFaithfulProjectedContradictionPackage
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ) (P : PMnPoly σ) : Prop :=
  SourceIdentityMinorLowerBound n σ B κ ℓ Q ∧
    piPhi σ P = CoupledSheetPoly.embed σ Q ∧
      PaperFaithfulCompilerPSideBound n σ B κ ℓ P

/-- Consuming the paper-faithful projected formulation gives the same final
rank contradiction, but without asking the raw flat `compiledPoly` to carry
both sides of the argument. -/
theorem false_of_paperFaithfulProjectedContradictionPackage
    (n : ℕ) (hn : n ≥ 2 ^ 804)
    (σ : UVSplit) (hV : 0 < σ.numV)
    (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ) (P : PMnPoly σ)
    (hpack : PaperFaithfulProjectedContradictionPackage n σ B κ ℓ Q P) :
    False :=
  pathA_general_separation n hn hV B Q P κ ℓ
    hpack.2.1 hpack.1 hpack.2.2

/-! ## Axiom audit anchors -/

#print axioms projectedIdentityMinorLowerBound_of_source_of_fixed_embed
#print axioms projectedCompilerIdentityMinorLowerBound_of_extraction_and_source
#print axioms piPhi_projectedIdentityMinorLowerBound_of_source
#print axioms piPhi_projectedCompilerIdentityMinorLowerBound_of_extraction
#print axioms T_Phi_projectedIdentityMinorLowerBound_of_source
#print axioms T_Phi_projectedCompilerIdentityMinorLowerBound_of_extraction
#print axioms partitionedOutput_projectedIdentityMinorLowerBound_of_embedded
#print axioms partitionedOutput_projectedIdentityMinorLowerBound_of_source
#print axioms partitionedOutput_projectedCompilerIdentityMinorLowerBound_of_source
#print axioms partitionedOutput_T_Phi_projectedCompilerIdentityMinorLowerBound_of_source
#print axioms false_of_paperFaithfulProjectedContradictionPackage

end PallLean.Paper93.DeepMath.PathB
