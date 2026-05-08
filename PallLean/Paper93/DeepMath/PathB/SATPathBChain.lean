import PallLean.Paper93.DeepMath.PathB.SATDeciderHypothesis
import PallLean.Paper93.DeepMath.PathB.SATDeciderRankStatement
import PallLean.Paper93.DeepMath.PathB.SATTiedGauge
import PallLean.Paper93.DeepMath.PathB.PathBToExistingChain
import PallLean.Paper93.DeepMath.PathB.RouteBExtractionMove
import PallLean.Paper93.DeepMath.PathB.RouteBWidthRankPSide
import PallLean.Paper93.DeepMath.PathB.RouteBCompilerLocalityPSide
import PallLean.Paper93.DeepMath.PathB.RouteBPlainCookLevinQPSide
import PallLean.Paper93.DeepMath.PathB.RouteBFactorLocalCookLevin
import PallLean.Paper93.DeepMath.PathB.RouteBFactorRowCover
import PallLean.Paper93.DeepMath.PathB.RouteBLeibnizTermCover

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame
open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- Path B for SAT deciders: combining
    (1) the rank chain on the compiled gadget (kernel-only),
    (2) the SAT-tied gauge identification (currently weak/trivial form), and
    (3) the existing PaperFaithfulSeparation chain via `accesses_paper_unconditional`
    gives ¬PeqNP_Paper at the cost of one upstream gauge axiom. -/
theorem SAT_path_B_chain :
    -- Rank chain (kernel-only)
    (∀ α : ℝ, ∀ κ n : ℕ, 0 < α → 2 ≤ n → κ ≤ (pocketFamily α κ n).rank) ∧
    -- Gauge existence for any family (kernel-only via identity matrix)
    (∀ n : ℕ, ∀ 𝒥 : Finset (Finset (Fin n)),
       ∃ A : Matrix (Fin n) (Fin n) ℝ, IsAmplituhedronGauge A 𝒥) ∧
    -- ¬PeqNP_Paper (kernel + 1 upstream axiom)
    (∀ (_ : SATDecider), False) := by
  refine ⟨?_, ?_, ?_⟩
  · intros α κ n hα hn
    exact rank_for_SAT_decider_compilation α κ n hα hn
  · intros n 𝒥
    exact ⟨1, identity_isAmplituhedronGauge_any 𝒥⟩
  · exact SATDecider_implies_False

/-- Route B's paper-faithful extraction move, exposed at the SAT chain level:
a uniform P-side bound on the full Step247 Cook-Levin compiler output rules
out bounded SAT deciders by the actual `T_Φ` extraction sandwich. -/
theorem SAT_path_B_TPhi_extraction_move
    (hP : ∀ (M : TuringMachine.DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804)
      (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      ProjectedIdentityMinorConcrete.CookLevinProjectedPSideBound
        M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_cookLevin_TPhi_projectedPSideBound hP

/-- Same SAT-chain exposure, but with the P-side hypothesis stated in the
paper's §40.2 Width⇒Rank form: a Theorem216 Khatri--Rao spanning witness on
the **full Step247 compiler output** plus absolute-constant digitisation.
This is the non-shortcut Route B surface. -/
theorem SAT_path_B_widthRank_TPhi_extraction_move
    (hWR : Step247UniformWidthRankData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_widthRankData_TPhi hWR

/-- Lower-level SAT-chain exposure: the P-side hypothesis is stated directly as
paper §40.2 compiler-locality / CEW / Khatri--Rao data for the full Step247
compiler output. This is the surface to discharge by the real deterministic
compiler analysis. -/
theorem SAT_path_B_compilerLocality_TPhi_extraction_move
    (hCL : Step247UniformCompilerLocalityData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_compilerLocalityData_TPhi hCL

/-- Plain-product SAT-chain exposure: it is enough to prove the P-side rank
bound directly for `cookLevinQ` at the pullback partition. This is the correct
place for the factor-local Khatri--Rao proof, before the `rename σ.inlU`
transport to Step247 `full_output`. -/
theorem SAT_path_B_plainCookLevinQ_TPhi_extraction_move
    (hQ : Step247UniformPlainCookLevinQPSideBound) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_plainCookLevinQPSideBound_TPhi hQ

/-- Factor-local SAT-chain exposure: the only remaining P-side work is the
finite Khatri--Rao row-span construction for the actual Cook--Levin product
`∏ᵢ (1 - Cᵢ)`. The factor-local structural facts are now proved separately;
this theorem shows that the KR data is enough for the full Route B `T_Φ`
closure. -/
theorem SAT_path_B_factorLocalKR_TPhi_extraction_move
    (hKR : Step247UniformFactorLocalKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_factorLocalKRData_TPhi hKR

/-- Row-cover SAT-chain exposure: the remaining paper §40.2 obligation is now
stated generator-by-generator for rows
`mlProj (m * ∂_S (∏ᵢ (1 - Cᵢ)))`. A uniform row cover by one finite family
`G` of size `≤ n^200` is enough to close Route B. -/
theorem SAT_path_B_factorRowCover_TPhi_extraction_move
    (hRows : Step247UniformFactorRowCoverData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_factorRowCoverData_TPhi hRows

/-- Leibniz-term SAT-chain exposure: after iterated Leibniz expansion, it is
enough to cover every distributed derivative product term after multiplication
by `m` and `mlProj`. This is the current paper-faithful KR construction seam. -/
theorem SAT_path_B_leibnizTermCover_TPhi_extraction_move
    (hTerms : Step247UniformLeibnizTermCoverData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_leibnizTermCoverData_TPhi hTerms

end PallLean.Paper93.DeepMath.PathB
