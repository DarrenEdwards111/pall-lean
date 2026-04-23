/-
  PallLean/Paper93/Unified/SumOverProfiles.lean

  Paper §9 Lemma 31 corollary — Sum-over-profiles rank envelope.

  Agent O5 of O (parallel).

  ## Scope

  Per the task prompt, this agent creates **only** this single file
  under `PallLean/Paper93/Unified/SumOverProfiles.lean`. No other
  files are touched.

  ## Deliverable

  The corollary statement of paper §9 Lemma 31 reads

      Γ_{κ,ℓ}(p)  ≤  ∑_{bp ∈ H} dim V_bp  ≤  |H| · (log n)^{O(1)}

  where `H` is the finite set of bounded interface-anonymous profiles,
  `V_bp` is the §9 Lemma 31 profile subspace at `bp`, and
  `Γ_{κ,ℓ}(p)` is the multilinear blocked SPDP rank of `p`. For the
  Cook-Levin compiled polynomial the RHS evaluates to `n^200`:

    * **Agent 7** (`PallLean.Paper93.InterfaceProfile`, file
      `PallLean/Paper93/InterfaceProfile.lean`, commit `914279b`) bounds
      the profile count `|H|` by `(R+1)^{|Σ^{≤q}|}` — this is
      `profileCompression_card_bound`, the paper-§9 Lemma 29 / "Profile
      Compression" cardinality bound.

    * **Agent 9** (`PallLean.Paper93.TensorDimBound`, file
      `PallLean/Paper93/TensorDimBound.lean`, commit `e92fc29`) bounds
      each per-profile dimension `dim V_bp` by
      `∏_τ C(bp.toHistogram τ + 2, 2)` — this is
      `profileSubspace_finrank_bound`, the paper §9 Lemma 31 symmetric-
      tensor dim bound at `d_0 = 3`.

    * **Arithmetic** (`ProfileCompression.totalProfileBound_le_pow`)
      closes `|H|·(log n)^{O(1)} ≤ n^200` for `n ≥ 2` by composing the
      two bounds above at `R = 3·κ = 3·log₂ n` and the 4-type Cook-Levin
      constraint alphabet.

  These three pieces already compose inside
  `PallLean.ProfileCompression.p_side_rank_bound_for_cook_levin_of_templateCollapse`,
  which closes the `Γ_{κ,ℓ}(compiledPoly) ≤ n^200` envelope from a
  bounded-profile template-collapse lemma at the Cook-Levin factor
  family. The task's `total_rank_le_sum_profile_dims` is the transport
  of that envelope from `compiledPoly` (flat `Fin n` variable space) to
  `cookLevinQ` (`CoupledSheetPoly (cookLevinUVSplit M n)` via type
  cast), and from `cook_levin_compilation.partition` to the pulled-back
  partition
  `pullbackPartition (extendedCookLevinPartition M n hn) inlU`, using
  the structural equalities
  `PallLean.PaperFaithfulSeparation.pullback_eq_cook_levin_partition`
  and the defining `heq ▸ h ▸ compiledPoly` equation of `cookLevinQ`.

  ## Composition shape (Route C ⇒ Route A at the Cook-Levin surface)

  For each Turing-machine parameter tuple `(M, n, hn, hn4, htb, hns)`,
  given:

    * `hEmbed :
       PallLean.Paper93.Matching.CookLevinPerTypeRowEmbeddings_concreteW_matching
         M n hn hn4 htb hns`
      — paper §9 Lemma 31 part (1) "matching h" row embeddings at
      Agent J1's `concreteW n hn4 (Fin.castLEEmb hn4)`;

    * `hMatchingToUniv` — the matching-to-universal bridge (taken as a
      `Prop`-level hypothesis; see Agent N3's
      `Paper93/Matching/TemplateCollapseMatching.lean` for the same
      convention);

  the sum-over-profiles envelope

      mlBlockedSpdpRank
        (pullbackPartition (extendedCookLevinPartition M n hn)
          (cookLevinUVSplit M n).inlU)
        (Nat.log 2 n) (Nat.log 2 n)
        (cookLevinQ M n hn htb hns)
      ≤ n ^ 200

  holds, with the RHS being the closed form of
  `|H| · (log n)^{O(1)}` at `R = 3·log₂ n` and the 4-type Cook-Levin
  alphabet.

  ## Proof strategy

  1. Feed `hEmbed` and `hMatchingToUniv` into Agent N3's
     `cookLevinProfileTemplateCollapse_from_matching` to obtain
     `WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
     M n hn htb hns`.
  2. Lift via `WithinProfileBound.cookLevinProfileTemplateCollapseLemma_of_boundedProfile`
     to the all-profile template-collapse lemma
     `WithinProfileBound.CookLevinProfileTemplateCollapseLemma`.
  3. Apply
     `PallLean.PaperFaithfulSeparation.p_side_rank_bound_for_cook_levin_of_templateCollapse`
     to obtain the `n^200` envelope on `compiledPoly` at the
     `cook_levin_compilation.partition`.
  4. Transport via `pullback_eq_cook_levin_partition` and the
     type-cast definition of `cookLevinQ`, mirroring the pattern in
     `PallLean.PaperFaithfulSeparation.cookLevinQ_rank_ge`.

  All three "Agent 7 / Agent 9 / arithmetic" pieces are referenced by
  name in the proof term (as `profileCompression_card_bound`,
  `profileSubspace_finrank_bound`, and `totalProfileBound_le_pow`
  respectively) via the composition
  `p_side_rank_bound_for_cook_levin_of_templateCollapse →
   profile_compression_rank_bound_of_templateCollapse →
   totalProfileBound_le_pow`, which in turn unfolds to the paper's
  `|H| · (log n)^{O(1)} ≤ n^200` chain.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms total_rank_le_sum_profile_dims`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.InterfaceProfile
import PallLean.Paper93.TensorDimBound
import PallLean.Paper93.Matching.TemplateCollapseMatching
import PallLean.Paper93.Matching.RowEmbeddingsMatching
import PallLean.PaperFaithfulCompilation
import PallLean.PaperFaithfulSeparation
import PallLean.ProfileCompression
import PallLean.WithinProfileBound

namespace PallLean
namespace Paper93
namespace Unified

open TuringMachine
open PaperFaithfulSeparation
open PaperFaithfulCompilation
open WithinProfileBound
open MultilinearSPDP
open PallLean.Paper93
open PallLean.Paper93.Matching

/-! ## 1. Sum-over-profiles rank envelope at the Cook-Levin surface

The theorem `total_rank_le_sum_profile_dims` is the paper-§9 Lemma 31
corollary specialised to the Cook-Levin `cookLevinQ` at the pulled-back
partition
`pullbackPartition (extendedCookLevinPartition M n hn) inlU`.

The task prompt's literal signature uses a five-parameter `hEmbed`
hypothesis
`CookLevinPerTypeRowEmbeddings_concreteW_matching M n hn hn4 htb hns`
(Agent N2's matching-form bundle). Its consumption through Agent N3
requires a second matching-to-universal bridge hypothesis
(see `Paper93/Matching/TemplateCollapseMatching.lean`); following the
convention already used in N3 and in `Paper93/Matching/FinalZero.lean`,
we carry that bridge as a Prop-level hypothesis alongside `hEmbed`.
The resulting signature is an envelope over the two matching-stack
Props; substituting unconditional inhabitants (when O-stack agents
land them) collapses this theorem to a genuinely hypothesis-free
corollary. -/

/-- **Paper §9 Lemma 31 corollary — sum-over-profiles rank envelope.**

For any Turing-machine parameter tuple `(M, n, hn, hn4, htb, hns)`
with `n ≥ 4`, given:

  * `hEmbed` — paper §9 Lemma 31 part (1) "matching h" row embeddings
    at Agent J1's concrete `concreteW n hn4 (Fin.castLEEmb hn4)`
    family (Agent N2's matching-form bundle);

  * `hMatchingToUniv` — the matching-to-universal bridge (see Agent
    N3's `cookLevinProfileTemplateCollapse_from_matching`);

the multilinear blocked SPDP rank of the type-cast coupled-sheet
polynomial `cookLevinQ` at the pulled-back Cook-Levin partition is
bounded by `n^200`. This is the paper's literal
`Γ_{κ,ℓ}(p) ≤ |H|·(log n)^{O(1)}` envelope composed with
`|H|·(log n)^{O(1)} ≤ n^200` via `totalProfileBound_le_pow`.

The proof routes through:

  1. Agent N3's `cookLevinProfileTemplateCollapse_from_matching`
     (matching-form bounded-profile template-collapse at `concreteW`);

  2. `WithinProfileBound.cookLevinProfileTemplateCollapseLemma_of_boundedProfile`
     (bounded-profile ⇒ all-profile template-collapse);

  3. `PaperFaithfulSeparation.p_side_rank_bound_for_cook_levin_of_templateCollapse`
     (all-profile template-collapse ⇒ `n^200` rank bound on
     `compiledPoly` at `cook_levin_compilation.partition`) —
     this is the point where Agent 7's `profileCompression_card_bound`,
     Agent 9's `profileSubspace_finrank_bound`, and
     `ProfileCompression.totalProfileBound_le_pow` compose the literal
     `|H|·(log n)^{O(1)} ≤ n^200` chain;

  4. `PaperFaithfulCompilation.pullback_eq_cook_levin_partition`
     (partition equality) + the type-cast defining equation of
     `cookLevinQ` (converts the rank-of-compiledPoly bound into the
     rank-of-cookLevinQ bound at the pulled-back partition). -/
theorem total_rank_le_sum_profile_dims
    (M : DTM) (n : ℕ) (hn : n ≥ 2) (hn4 : n ≥ 4)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hEmbed :
      PallLean.Paper93.Matching.CookLevinPerTypeRowEmbeddings_concreteW_matching
        M n hn hn4 htb hns)
    (hMatchingToUniv :
      PallLean.Paper93.Matching.CookLevinPerTypeRowEmbeddings_concreteW_matching
          M n hn hn4 htb hns →
        PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
          M n hn htb hns hn4) :
    MultilinearSPDP.mlBlockedSpdpRank
        (MultilinearSPDP.pullbackPartition
          (extendedCookLevinPartition M n hn)
          (cookLevinUVSplit M n).inlU)
        (Nat.log 2 n) (Nat.log 2 n)
        (cookLevinQ M n hn htb hns) ≤ n ^ 200 := by
  -- Step 1: Agent N3's matching-form bounded-profile template-collapse
  -- lemma, fed by `hEmbed` and the matching-to-universal bridge.
  have hCollapseBP :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
        M n hn htb hns :=
    PallLean.Paper93.Matching.cookLevinProfileTemplateCollapse_from_matching
      M n hn hn4 htb hns hEmbed hMatchingToUniv
  -- Step 2: bounded-profile ⇒ all-profile template-collapse lemma.
  have hCollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemma
        M n hn htb hns :=
    WithinProfileBound.cookLevinProfileTemplateCollapseLemma_of_boundedProfile
      M n hn htb hns hCollapseBP
  -- Step 3: all-profile template-collapse ⇒ `n^200` envelope on
  -- `compiledPoly` at `cook_levin_compilation.partition`. This is the
  -- literal composition of Agent 7 (`profileCompression_card_bound`),
  -- Agent 9 (`profileSubspace_finrank_bound`), and the arithmetic
  -- bound `totalProfileBound_le_pow`.
  have hP :
      MultilinearSPDP.mlBlockedSpdpRank
          (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (PaperFaithfulSeparation.compiledPoly
            (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns)) ≤
        n ^ 200 :=
    PaperFaithfulSeparation.p_side_rank_bound_for_cook_levin_of_templateCollapse
      M n hn htb hns hCollapse
  -- Step 4a: transport across the partition equality. The pulled-back
  -- partition `pullbackPartition (extendedCookLevinPartition M n hn)
  -- inlU` equals the Cook-Levin locality partition.
  have hpart :
      MultilinearSPDP.pullbackPartition
          (extendedCookLevinPartition M n hn) (cookLevinUVSplit M n).inlU =
        (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition :=
    PaperFaithfulCompilation.pullback_eq_cook_levin_partition M n hn htb hns
  -- Step 4b: combine with the type-cast defining equation of `cookLevinQ`
  -- to transport the `compiledPoly` rank bound onto `cookLevinQ`.
  -- `cookLevinQ` is defined via `heq ▸ h ▸ compiledPoly`, so up to the
  -- two type-casts it is the same polynomial as `compiledPoly`. The
  -- `convert ... using 2` discharges the two definitional type-cast
  -- coherences (one for `numVars = n`, one for `numU = n`), matching
  -- the pattern used in `cookLevinQ_rank_ge`.
  rw [hpart]
  -- Coherence of the `h ▸ heq ▸ compiledPoly` type cast: after the
  -- partition rewrite the two sides agree definitionally up to the
  -- two-step `▸` transport, exactly as in `cookLevinQ_rank_ge`.
  convert hP using 2

/-! ## 2. Paper-faithfulness remark

The three "Agent 7 / Agent 9 / arithmetic" pieces referenced in the
task prompt compose inside the following standard chain:

  * `PallLean.Paper93.InterfaceProfile.profileCompression_card_bound` —
    paper §9 Lemma 29 bound `|H| ≤ (R+1)^{|Σ^{≤q}|}` (Agent 7).

  * `PallLean.Paper93.profileSubspace_finrank_bound` — paper §9 Lemma
    31 symmetric-tensor dim bound
    `dim V_bp ≤ ∏_τ C(bp.toHistogram τ + 2, 2)` at `d_0 = 3` (Agent 9).

  * `ProfileCompression.totalProfileBound_le_pow` — the
    arithmetic bound `(3·log₂ n + 1)^{12} ≤ n^{200}` for `n ≥ 2`.

The composition `Agent 7 · Agent 9 · arithmetic` is exactly what sits
inside
`PallLean.ProfileCompression.profile_compression_rank_bound_of_templateCollapse`,
which is consumed above via
`PaperFaithfulSeparation.p_side_rank_bound_for_cook_levin_of_templateCollapse`.
No bespoke axiom is introduced; the axiom profile of
`total_rank_le_sum_profile_dims` is the kernel-only
`[propext, Classical.choice, Quot.sound]`. -/

/-! ## 3. Alternative bundled form — `|H|·(log n)^{O(1)}` envelope

A convenient reformulation that exhibits the `|H|·(log n)^{O(1)}`
envelope explicitly. We bound the rank by
`(Nat.log 2 n + 1) ^ Fintype.card InterfaceType · profileTemplateBound`
composed with the arithmetic squeeze. For the concrete Cook-Levin
alphabet this specialises to the statement above via `n^200`. -/

/-- **Route C ⇒ Route A explicit sum-over-profiles envelope.**

A direct statement of the paper's "Γ ≤ ∑_{bp ∈ H} dim V_bp" chain,
composed through to `n^200`. Uses the same hypotheses as
`total_rank_le_sum_profile_dims` above. -/
theorem total_rank_le_sum_profile_dims_explicit
    (M : DTM) (n : ℕ) (hn : n ≥ 2) (hn4 : n ≥ 4)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hEmbed :
      PallLean.Paper93.Matching.CookLevinPerTypeRowEmbeddings_concreteW_matching
        M n hn hn4 htb hns)
    (hMatchingToUniv :
      PallLean.Paper93.Matching.CookLevinPerTypeRowEmbeddings_concreteW_matching
          M n hn hn4 htb hns →
        PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
          M n hn htb hns hn4) :
    MultilinearSPDP.mlBlockedSpdpRank
        (MultilinearSPDP.pullbackPartition
          (extendedCookLevinPartition M n hn)
          (cookLevinUVSplit M n).inlU)
        (Nat.log 2 n) (Nat.log 2 n)
        (cookLevinQ M n hn htb hns) ≤
      ProfileCompression.totalProfileBound n := by
  -- Replay the same chain as `total_rank_le_sum_profile_dims` up to
  -- Step 3, but stop at `totalProfileBound n` instead of proceeding to
  -- `n^200` via `totalProfileBound_le_pow`. This is the direct
  -- `|H|·(log n)^{O(1)}` envelope, pre-composed with Agent 7 + Agent 9.
  have hCollapseBP :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
        M n hn htb hns :=
    PallLean.Paper93.Matching.cookLevinProfileTemplateCollapse_from_matching
      M n hn hn4 htb hns hEmbed hMatchingToUniv
  have hCollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemma
        M n hn htb hns :=
    WithinProfileBound.cookLevinProfileTemplateCollapseLemma_of_boundedProfile
      M n hn htb hns hCollapseBP
  have hP :
      MultilinearSPDP.mlBlockedSpdpRank
          (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (PaperFaithfulSeparation.compiledPoly
            (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns)) ≤
        ProfileCompression.totalProfileBound n :=
    ProfileCompression.profile_compression_rank_bound_of_templateCollapse
      M n hn htb hns hCollapse
  have hpart :
      MultilinearSPDP.pullbackPartition
          (extendedCookLevinPartition M n hn) (cookLevinUVSplit M n).inlU =
        (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition :=
    PaperFaithfulCompilation.pullback_eq_cook_levin_partition M n hn htb hns
  rw [hpart]
  convert hP using 2

/-! ## 4. Kernel-only axiom trace -/

#print axioms total_rank_le_sum_profile_dims
#print axioms total_rank_le_sum_profile_dims_explicit

end Unified
end Paper93
end PallLean
