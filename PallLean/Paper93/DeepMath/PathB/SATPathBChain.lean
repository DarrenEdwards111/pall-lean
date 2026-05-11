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
import PallLean.Paper93.DeepMath.PathB.RouteBLeibnizAllocationCover
import PallLean.Paper93.DeepMath.PathB.RouteBConcreteConstraintAllocationCover
import PallLean.Paper93.DeepMath.PathB.RouteBConcreteLocalDerivativeFacts
import PallLean.Paper93.DeepMath.PathB.RouteBSupportCompatibleAllocationCover
import PallLean.Paper93.DeepMath.PathB.RouteBLengthPrunedAllocationCover
import PallLean.Paper93.DeepMath.PathB.RouteBRowFaithfulLengthPrunedKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedConstraintKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedSplitKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedMonomialShiftKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedMonomialInterfaceUniqueKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedMonomialInterfaceSpanKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedMonomialInterfaceFiniteSpanKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedMonomialCodedFiniteSpanKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedAtomTraceCodedBridgeKR
import PallLean.Paper93.DeepMath.PathB.RouteBPlacedQuotientDescentKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedIncidenceCountKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedConstantKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedLocalAlphabetKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedExtractorKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedWindowKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedConcreteWindowKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedWindowSourceKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedTypedSourceKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedActualTypeKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedCanonicalSourceKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedCanonicalInterfaceKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedRowInterfaceKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedRowInterfaceUniqueKR

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame
open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB
open PaperFaithfulSeparation
open TuringMachine

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

/-- Allocation-cover SAT-chain exposure: the remaining object is now the paper's
actual derivative-allocation family `alloc : factor → List vars`; cover all
allocated Khatri--Rao products and Route B closes. -/
theorem SAT_path_B_leibnizAllocationCover_TPhi_extraction_move
    (hAlloc : Step247UniformLeibnizAllocationCoverData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_allocationCoverData_TPhi hAlloc

/-- Concrete constraint-allocation SAT-chain exposure: the factor index is now
literally the finite type of positions in the Cook--Levin constraint list, with
factor `(1 - Cᵢ)`. Cover those allocated products and Route B closes. -/
theorem SAT_path_B_concreteConstraintAllocationCover_TPhi_extraction_move
    (hConcrete : Step247UniformConcreteConstraintAllocationCoverData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_concreteConstraintAllocationCoverData_TPhi
    hConcrete

/-- Local-derivative SAT-chain exposure: each allocated concrete factor
derivative is now known to use ≤10 variables and have degree ≤6; a KR cover
allowed to use those true local facts is enough to close Route B. -/
theorem SAT_path_B_localDerivativeAllocationCover_TPhi_extraction_move
    (hLocal : Step247UniformConcreteLocalDerivativeAllocationCoverData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_localDerivativeAllocationCoverData_TPhi
    hLocal

/-- Support-compatible SAT-chain exposure: allocations differentiating any local
constraint outside its own support are proved zero rows, so the KR cover only
has to cover support-compatible allocated products. -/
theorem SAT_path_B_supportCompatibleAllocationCover_TPhi_extraction_move
    (hSupp : Step247UniformSupportCompatibleAllocationCoverData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_supportCompatibleAllocationCoverData_TPhi
    hSupp

/-- Length-pruned SAT-chain exposure: because every concrete Cook--Levin factor
has degree ≤6, allocations of length >6 to a single factor are zero rows.  The
KR cover only has to cover support-compatible allocations with local length ≤6. -/
theorem SAT_path_B_lengthPrunedAllocationCover_TPhi_extraction_move
    (hLen : Step247UniformLengthPrunedAllocationCoverData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_lengthPrunedAllocationCoverData_TPhi hLen

/-- Row-faithful length-pruned KR exposure: the final KR family only has to
cover nonzero concrete allocations arising from actual strict-κ SPDP rows, with
`S.length = log₂ n`, multiplier degree/vars constraints, and block
admissibility retained. -/
theorem SAT_path_B_rowFaithfulLengthPrunedKR_TPhi_extraction_move
    (hKR : Step247UniformRowFaithfulLengthPrunedKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_rowFaithfulLengthPrunedKRData_TPhi hKR

/-- Touched-constraint KR exposure: support-compatible allocations are forced to
be empty outside the concrete constraints whose support intersects the row `S`.
The final KR count may therefore range over touched constraints only. -/
theorem SAT_path_B_touchedConstraintKR_TPhi_extraction_move
    (hTouched : Step247UniformTouchedConstraintKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedConstraintKRData_TPhi hTouched

/-- Split-touched KR exposure: the final KR obligation is written as the exact
product over touched constraints times the exact product over untouched
constraints.  This keeps the Cook--Levin background product visible and avoids
silently discarding the untouched factors. -/
theorem SAT_path_B_touchedSplitKR_TPhi_extraction_move
    (hSplit : Step247UniformTouchedSplitKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedSplitKRData_TPhi hSplit

/-- Monomial-shift KR exposure: the finite local classifier only has to cover
monomial shift rows; arbitrary polynomial shifts are recovered by linearity. -/
theorem SAT_path_B_touchedMonomialShiftKR_TPhi_extraction_move
    (hData : Step247UniformTouchedMonomialShiftKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedMonomialShiftKRData_TPhi hData

/-- Monomial-interface uniqueness exposure: the finite local word is proved
complete only for monomial-shift rows; arbitrary polynomial shifts enter later
by the monomial-shift linearity bridge. -/
theorem SAT_path_B_touchedMonomialInterfaceUniqueKR_TPhi_extraction_move
    (hData : Step247UniformTouchedMonomialInterfaceUniqueData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedMonomialInterfaceUniqueData_TPhi hData

/-- Monomial-interface span exposure: local words index generators whose spans
contain the exact monomial rows; machine-dependent gadget coefficients are
handled by span scalars, not encoded into the finite alphabet. -/
theorem SAT_path_B_touchedMonomialInterfaceSpanKR_TPhi_extraction_move
    (hData : Step247UniformTouchedMonomialInterfaceSpanData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedMonomialInterfaceSpanData_TPhi hData

/-- Monomial-interface finite-span exposure: each finite local word indexes a
bounded local basis, matching the KR/profile proof shape rather than forcing a
single generator per word. -/
theorem SAT_path_B_touchedMonomialInterfaceFiniteSpanKR_TPhi_extraction_move
    (hData : Step247UniformTouchedMonomialInterfaceFiniteSpanData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedMonomialInterfaceFiniteSpanData_TPhi hData

/-- Coded finite-span exposure: the actual paper local chart may use any
absolute constant alphabet `C₃`, with a bounded local basis per coded word. -/
theorem SAT_path_B_touchedMonomialCodedFiniteSpanKR_TPhi_extraction_move
    (hData : Step247UniformTouchedMonomialCodedFiniteSpanData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedMonomialCodedFiniteSpanData_TPhi hData

/-- Atom-trace coded-basis exposure: the exact touched row is routed through
the concrete untouched-background atom-trace classifier and then into the
per-code local basis span. -/
theorem SAT_path_B_touchedAtomTraceCodedBasisKR_TPhi_extraction_move
    (hData : Step247UniformTouchedMonomialAtomTraceCodedBasisData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedMonomialCodedFiniteSpanData_TPhi
    (step247UniformTouchedMonomialCodedFiniteSpanData_of_atomTraceCodedBasis hData)

/-- Exact-budget atom-trace coded-basis exposure: same as the atom-trace
coded-basis seam, but with the background type budget fixed to the literal
finite local monoid profile sum. -/
theorem SAT_path_B_touchedAtomTraceExactCodedBasisKR_TPhi_extraction_move
    (hData : Step247UniformTouchedMonomialAtomTraceExactCodedBasisData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedMonomialCodedFiniteSpanData_TPhi
    (step247UniformTouchedMonomialCodedFiniteSpanData_of_atomTraceExactCodedBasis hData)

/-- Paper-faithful canonical-window/local-monoid Route-B exposure.

This is the literal §9.3--§9.4 closure surface from `p vs np1.pdf`: canonical
windows are classified by interface-anonymous local-monoid profiles; Lemma 29
bounds the number of profiles; Lemma 31 bounds each selected profile subspace;
and selected canonical rows land in their own `V_h`.  No global chart,
all-profile common span, or broad residual-balance identity is used. -/
theorem SAT_path_B_paperFaithfulCanonicalWindowLocalMonoidProfileAnalysis_TPhi_extraction_move
    (hAnalysis :
      ∀ (M : TuringMachine.DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804)
        (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictCanonicalWindowLocalMonoidProfileAnalysis
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileAnalysis
    hAnalysis

/-- Same paper-faithful Route-B exposure with Lemma 29 and Lemma 31 kept as
separate data fields before the combined profile budget is derived. -/
theorem SAT_path_B_paperFaithfulCanonicalWindowLocalMonoidProfileData_TPhi_extraction_move
    (hData :
      ∀ (M : TuringMachine.DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804)
        (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictCanonicalWindowLocalMonoidProfileData
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileData
    hData



/-- Concrete `AlphabetWord 1` Route-B closeout.

This is the first instantiated option-2 endpoint: profile-count arithmetic for
`Σ^{≤1}` is proved, so the only hypothesis is the selected Lemma-31 profile row
data for the literal normal-form word alphabet. -/
theorem SAT_path_B_paperFaithfulAlphabetWordOneLocalMonoidProfile_TPhi_extraction_move
    (hData : Step247UniformRouteBPaperFaithfulTPhiAlphabetWordOneLocalMonoidProfileData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiAlphabetWordOneLocalMonoidProfileData
    hData

/-- The placed quotient/descent construction closes SAT through the concrete
`AlphabetWord 1` option-2 route, not through a four-bin profile-count budget. -/
theorem SAT_path_B_paperFaithfulAlphabetWordOneLocalMonoidProfile_of_placedQuotientDescent_TPhi_extraction_move
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData) :
    NoBoundedSATDeciderAtPaperScale :=
  SAT_path_B_paperFaithfulAlphabetWordOneLocalMonoidProfile_TPhi_extraction_move
    (step247UniformRouteBPaperFaithfulTPhiAlphabetWordOneLocalMonoidProfileData_of_placedQuotientDescent
      hData)

/-- Full finite-normal-form alphabet Route-B closeout.

This is the option-2 path: keep the paper's finite `Σ^{≤q}` normal-form
alphabet explicit and prove the assembled profile budget directly under the
ambient `n^200` envelope, rather than proving a collapse to four
`ConstraintType` bins. -/
theorem SAT_path_B_paperFaithfulLooseInterfaceAnonymousLocalMonoidProfile_TPhi_extraction_move
    (hData : Step247UniformRouteBPaperFaithfulTPhiLooseInterfaceAnonymousLocalMonoidProfileData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiLooseInterfaceAnonymousLocalMonoidProfileData
    hData

/-- Literal bounded local-monoid/profile Route-B closeout.

This is the corrected paper §9.3--§9.4 refactor: the local normal-form alphabet
is supplied as finite monoid quotient data, Lemma 29 bounds the number of
interface-anonymous profiles, and Lemma 31 supplies selected within-profile
row-span membership.  This theorem deliberately sits above the narrower
`ConstraintType` specialization, so the final route need not identify
normal-form words with raw constraint types. -/
theorem SAT_path_B_paperFaithfulBoundedInterfaceAnonymousLocalMonoidProfile_TPhi_extraction_move
    (hData : Step247UniformRouteBPaperFaithfulTPhiBoundedInterfaceAnonymousLocalMonoidProfileData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiBoundedInterfaceAnonymousLocalMonoidProfileData
    hData

/-- Tightest current paper-faithful local-monoid/profile seam: prove selected
`ConstraintType` profile subspace containment for each canonical strict `TΦ`
row.  This is the direct Lean analogue of Lemma 31's selected `V_h` row
membership plus its within-profile dimension bound. -/
theorem SAT_path_B_paperFaithfulConstraintTypeProfileSubspace_TPhi_extraction_move
    (hData :
      ∀ (M : TuringMachine.DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804)
        (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictConstraintTypeProfileSubspaceData
    hData

/-- Literal selected-row-span version of the paper-faithful Lemma-31 seam.

This is the `V_h = span{canonical strict rows selecting h}` formulation.  The
row-membership field is constructive by `Submodule.subset_span`; the remaining
content is exactly the finite-dimensional within-profile bound for each
selected row span.  This avoids both the false global chart and the stronger
post-span/residual-balance shortcuts. -/
theorem SAT_path_B_paperFaithfulCanonicalProfileRowSpan_TPhi_extraction_move
    (hData :
      ∀ (M : TuringMachine.DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804)
        (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictCanonicalProfileRowSpanData
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictCanonicalProfileRowSpanData
    hData

/-- Source-coordinate literal selected-row-span seam.

This is the strict first-of-block source version of the same `V_h` target, prior
to ambient rename transport.  It is often the most convenient place to prove the
real Lemma-31 compression because the local words/types live in source
coordinates. -/
theorem SAT_path_B_paperFaithfulSourceCanonicalProfileRowSpan_TPhi_extraction_move
    (hData :
      ∀ (M : TuringMachine.DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804)
        (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceCanonicalProfileRowSpanData
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictSourceCanonicalProfileRowSpanData
    hData

/-- Source local-type compression seam for the real Lemma-31 proof.

This is the term/local-monoid normal-form target below the selected row-span
surface: for each selected interface profile, classify the canonical source row
into a bounded local-type alphabet and prove membership in that same selected
local-type space. -/
theorem SAT_path_B_paperFaithfulSourceLocalTypeCompression_TPhi_extraction_move
    (hData :
      ∀ (M : TuringMachine.DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804)
        (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceLocalTypeCompressionData
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictSourceLocalTypeCompressionData
    hData

/-- Branch-atom profile-template local-type seam.

This is the paper-faithful atomic Lemma-31 surface below source local-type
compression: local types are the concrete bounded `NFOfWord` witness words,
local bases are singleton whole-branch atoms, and the budget is the selected
`profileTemplateBound ρ.val`.  No common/global span or derivative-histogram
collapse is introduced. -/
theorem SAT_path_B_paperFaithfulSourceBranchAtomProfileTemplateLocalTypeMaps_TPhi_extraction_move
    (hData :
      ∀ (M : TuringMachine.DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804)
        (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceWitnessedLeibnizNFOfWordBranchAtomProfileTemplateLocalTypeMaps
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictSourceBranchAtomProfileTemplateLocalTypeMaps
    hData

/-- Exact-budget local-monoid normal-form seam.

This keeps the witnessed Leibniz local word explicit and asks for finite normal
forms with the literal selected-profile budget `profileTemplateBound ρ.val`.
It is the no-shortcut local monoid route into the source local-type theorem. -/
theorem SAT_path_B_paperFaithfulSourceProfileTemplateLocalMonoidNormalForms_TPhi_extraction_move
    (hData :
      ∀ (M : TuringMachine.DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804)
        (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceWitnessedLeibnizProfileTemplateLocalMonoidNormalForms
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizProfileTemplateLocalMonoidNormalForms
    hData

/-- Fixed-`q` singleton event-atom budget seam.

This is the bookkeeping half of the local-algebra target: finite bounds and
basis embedding only, with no row-membership closure claim. -/
theorem SAT_path_B_paperFaithfulSourceEventAtomQDimBudgetData_fromFinalMaps
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalMaps) :
    Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimBudgetData :=
  step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimBudgetData_of_finalMaps
    hData

/-- Fixed-`q` singleton event-atom seam from split budget plus an explicit
final-map builder.

This keeps the seam split honest: budget bookkeeping is supplied separately,
and the remaining constructor obligation is isolated as a builder from each
budget payload to a full fixed-`q` final payload. -/
theorem SAT_path_B_paperFaithfulSourceEventAtomQDimFinalMaps_fromBudgetAndBuilder_TPhi_extraction_move
    (hBudget : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimBudgetData)
    (hBuild : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalBuilder) :
    NoBoundedSATDeciderAtPaperScale :=
  PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps
    (fun M n hn hn2 htb hns hdec =>
      let D := Classical.choice (hBudget M n hn hn2 htb hns)
      Classical.choice (hBuild M n hn hn2 htb hns D))

/-- Fixed-`q` singleton event-atom closeout routed through the explicit
uniform target-membership frontier. -/
theorem SAT_path_B_paperFaithfulSourceEventAtomQDimFinalMaps_viaTargetMembership_TPhi_extraction_move
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalMaps) :
    NoBoundedSATDeciderAtPaperScale :=
  SAT_path_B_paperFaithfulSourceEventAtomQDimFinalMaps_fromBudgetAndTargetMembership_TPhi_extraction_move
    (step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimBudgetData_of_finalMaps hData)
    (step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimTargetMembership_of_finalMaps hData)

/-- Fixed-`q` singleton event-atom closeout directly from split budget plus
uniform target-row membership. -/
theorem SAT_path_B_paperFaithfulSourceEventAtomQDimFinalMaps_fromBudgetAndTargetMembership_TPhi_extraction_move
    (hBudget : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimBudgetData)
    (hTarget : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimTargetMembership) :
    NoBoundedSATDeciderAtPaperScale :=
  SAT_path_B_paperFaithfulSourceEventAtomQDimFinalMaps_fromBudgetAndBuilder_TPhi_extraction_move
    hBudget
    (step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalBuilder_of_budgetData_and_targetMembership
      hTarget)

/-- Fixed-`q` singleton event-atom closeout directly from split budget plus
uniform row-membership witness. -/
theorem SAT_path_B_paperFaithfulSourceEventAtomQDimFinalMaps_fromBudgetAndRowWitness_TPhi_extraction_move
    (hBudget : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimBudgetData)
    (hRow : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimRowWitness) :
    NoBoundedSATDeciderAtPaperScale :=
  SAT_path_B_paperFaithfulSourceEventAtomQDimFinalMaps_fromBudgetAndBuilder_TPhi_extraction_move
    hBudget
    (step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalBuilder_of_budgetData_and_rowWitness
      hRow)

/-- Fixed-`q` singleton event-atom `NFOfWord` seam.

This is the currently most atomic exposed Cook--Levin local-algebra target: the
basis letters are the concrete singleton derivative atoms, the local dimension
is the actual bounded-word length `q`, and the remaining row proof is exact
membership of the witnessed product-rule row in that folded atom basis. -/
theorem SAT_path_B_paperFaithfulSourceEventAtomQDimFinalMaps_TPhi_extraction_move
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalMaps) :
    NoBoundedSATDeciderAtPaperScale :=
  PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps
    (fun M n hn hn2 htb hns hdec =>
      Classical.choice (hData M n hn hn2 htb hns))

/-- Exact-profile template-collapse sufficient seam for the strict source row.

This exposes the checked route
`selected template collapse + selected row post-span membership → source
local-type compression → selected V_h → strict TΦ contradiction`.  It is kept as
a sound sufficient surface; it does not replace the more general local-monoid
classification target above. -/
theorem SAT_path_B_paperFaithfulSourceCanonicalRowExactProfileTemplateCollapse_TPhi_extraction_move
    (hData :
      ∀ (M : TuringMachine.DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804)
        (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceCanonicalRowExactProfileTemplateCollapseData
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictSourceCanonicalRowExactProfileTemplateCollapseData
    hData

/-- Row-interface-slot expansion seam for the strict source row.

This is the most literal currently exposed Lemma-31 source target: for the
selected canonical-window profile, expand the row as a finite linear
combination of products of exactly `ρ.val σ` slots, with each slot living in
its concrete compiled-basis interface space `Wσ`.  It avoids the old false
single global chart and does not collapse the selected row into a broad
residual-balance shortcut. -/
theorem SAT_path_B_paperFaithfulSourceSelectedRowInterfaceSlotExpansion_TPhi_extraction_move
    (hData :
      ∀ (M : TuringMachine.DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804)
        (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedRowInterfaceSlotExpansionData
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictSourceSelectedRowInterfaceSlotExpansionData
    hData

/-- Renamed canonical-interface expansion seam.

This keeps the selected-profile finite expansion after the source/ambient
rename transport has been made explicit.  It is a sufficient route into the
same selected `V_h` profile-subspace bound, not a replacement by a common span. -/
theorem SAT_path_B_paperFaithfulSourceSelectedRowRenamedCanonicalInterfaceExpansion_TPhi_extraction_move
    (hData :
      ∀ (M : TuringMachine.DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804)
        (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedRowRenamedCanonicalInterfaceExpansionData
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictSourceSelectedRowRenamedCanonicalInterfaceExpansionData
    hData

/-- Local compiled-profile row seam.

This exposes the Route-B target where Lemma 31 is interpreted as a local
compiled-coordinate profile-subspace statement: each `Wσ` is supplied with
finite rank at most three, and the selected canonical source row lands in the
selected profile product space `profileSubspace ρ.val W`. -/
theorem SAT_path_B_paperFaithfulSourceSelectedLocalCompiledProfileSubspaceRow_TPhi_extraction_move
    (hData :
      ∀ (M : TuringMachine.DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804)
        (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedLocalCompiledProfileSubspaceRowData
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictSourceSelectedLocalCompiledProfileSubspaceRowData
    hData

/-- Paper-faithful placed quotient/descent exposure: this is the replacement
surface for the broken unplaced atom-trace chart route.  It keeps the exact
placed Cook--Levin local-interface expansion and then descends to the selected
interface-anonymous profile subspace. -/
noncomputable def SAT_path_B_paperFaithfulPlacedQuotientDescent_TPhi_profileSubspace
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData) :
    ∀ (M : TuringMachine.DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804)
      (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData
        M n hn2 htb hns :=
  step247UniformRouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData_of_placedQuotientDescent
    hData

/-- Same placed quotient/descent exposure, pushed all the way to the strict
paper `TΦ` P-side rank bound.  The remaining mathematical obligation is now
exactly the placed quotient/descent data, not the old atom-trace chart. -/
noncomputable def SAT_path_B_paperFaithfulPlacedQuotientDescent_TPhi_pSideBound
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData) :
    ∀ (M : TuringMachine.DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804)
      (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      SATDeciderGaugePSideBound M n hn2 htb hns
        (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiAmbientGauge
          M n hn2 htb hns) :=
  step247UniformRouteBPaperFaithfulTPhiPSideBound_of_placedQuotientDescent hData

/-- Paper-faithful placed quotient/descent exposure, closed all the way to the
final no-bounded-SAT-decider theorem for strict `TΦ`. -/
theorem SAT_path_B_paperFaithfulPlacedQuotientDescent_TPhi_extraction_move
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescent
    hData

/-- Explicit equivariant quotient-map Route-B closeout.  This is the sharpened
paper-faithful seam: provide quotient maps, finite selected `W_σ`, landing, and
row-slot equivariance; the existing slot/product/profile assembly closes the
strict `TΦ` path. -/
theorem SAT_path_B_paperFaithfulEquivariantQuotientMapNormalForm_TPhi_extraction_move
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedInterfaceEquivariantQuotientMapNormalFormData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiPlacedInterfaceEquivariantQuotientMapNormalFormData
    hData

/-- Projected quotient-normal-form Route-B closeout: this is the sound route
that replaces literal ambient selected-place equality by quotient/projection
normalisation plus residual-balance preservation. -/
theorem SAT_path_B_projectedQuotientNormalForm_TPhi_extraction_move
    (hData : Step247UniformRouteBPaperFaithfulTPhiProjectedQuotientNormalFormData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiProjectedQuotientNormalFormData
    hData

/-- Concrete selected singleton-quotient Route-B closeout: concrete per-type
row embeddings plus normalized coefficients and fixed derivative representative
instantiate the selected projected quotient-normal-form gate. -/
theorem SAT_path_B_singletonQuotient_concreteW_normalizedCoeff_fixedDerivative_TPhi_extraction_move
    (hcert :
      ∀ (M : TuringMachine.DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        ∃ hn4 : n ≥ 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
            M n hn2 htb hns ∧
          PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
            M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhi_singletonQuotient_concreteW_normalizedCoeff_fixedDerivative
    hcert

/-- Corrected quotient-normalisation factoring: the local placed expansion is
kept separate from the ambient quotient/rank soundness bridge.  This is the
honest replacement for the false fixed raw-chart shortcut. -/
theorem SAT_path_B_paperFaithfulPlacedExpansion_withAmbientQuotientSoundness_TPhi_extraction_move
    (hExpansion : Step247UniformRouteBPaperFaithfulTPhiPlacedExpansionData)
    (hSound : Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiPlacedExpansionData_and_ambientQuotientSoundness
    hExpansion hSound

/-- Incidence-count split KR exposure: the final KR obligation now also carries
the real union-bound count over row-variable incidence fibres. -/
theorem SAT_path_B_touchedIncidenceSplitKR_TPhi_extraction_move
    (hData : Step247UniformTouchedIncidenceSplitKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedIncidenceSplitKRData_TPhi hData

/-- Constant-`C₃` KR exposure: the remaining generator-family obligation is now
in the paper's actual `C₃^κ` form, converted to `n^200` only by the Step 223
`C₃^log n = n^O(1)` arithmetic. -/
theorem SAT_path_B_touchedConstantSplitKR_TPhi_extraction_move
    (hData : Step247UniformTouchedConstantSplitKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedConstantSplitKRData_TPhi hData

/-- Local-alphabet KR exposure: the remaining obligation is now a classifier
from each exact split row to a length-`log n` word over the fixed local alphabet
`Fin C₃`, with generators the image of the word interpretation map. -/
theorem SAT_path_B_touchedLocalAlphabetKR_TPhi_extraction_move
    (hData : Step247UniformTouchedLocalAlphabetKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedLocalAlphabetKRData_TPhi hData

/-- Extractor KR exposure: the classifier is now a per-position local-state
extractor `Fin(log n) → Fin C₃`; the classified word is assembled from those
local states and interpreted back to the exact split row. -/
theorem SAT_path_B_touchedExtractorKR_TPhi_extraction_move
    (hData : Step247UniformTouchedExtractorKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedExtractorKRData_TPhi hData

/-- Window KR exposure: the per-position extractor state is now an actual paper
interface-local symbol `(ConstraintType, Fin 4)`, encoded into the fixed
16-symbol local alphabet. -/
theorem SAT_path_B_touchedWindowKR_TPhi_extraction_move
    (hData : Step247UniformTouchedWindowKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedWindowKRData_TPhi hData

/-- Concrete-window KR exposure: each per-position window state is now backed by
an actual row variable and optional touched Cook--Levin constraint, with support
proofs for every non-dormant window. -/
theorem SAT_path_B_touchedConcreteWindowKR_TPhi_extraction_move
    (hData : Step247UniformTouchedConcreteWindowKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedConcreteWindowKRData_TPhi hData

/-- Source-fibre KR exposure: every non-dormant selected source must lie in the
actual support fibre of the row variable at that KR position; touchedness is
then proved from support-fibre membership. -/
theorem SAT_path_B_touchedWindowSourceKR_TPhi_extraction_move
    (hData : Step247UniformTouchedWindowSourceKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedWindowSourceKRData_TPhi hData

/-- Typed-source KR exposure: the emitted interface symbol is now forced from a
Cook--Levin constraint-type map and bounded local state; non-dormant windows use
the type of their selected source. -/
theorem SAT_path_B_touchedTypedSourceKR_TPhi_extraction_move
    (hData : Step247UniformTouchedTypedSourceKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedTypedSourceKRData_TPhi hData

/-- Actual-type KR exposure: the emitted interface symbol now uses the concrete
`cookLevinConstraintType` of every selected non-dormant source. -/
theorem SAT_path_B_touchedActualTypeKR_TPhi_extraction_move
    (hData : Step247UniformTouchedActualTypeKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedActualTypeKRData_TPhi hData

/-- Canonical-source KR exposure: source selection is no longer arbitrary; every
window uses the least constraint in the actual row-variable support fibre, or is
dormant when that fibre is empty. -/
theorem SAT_path_B_touchedCanonicalSourceKR_TPhi_extraction_move
    (hData : Step247UniformTouchedCanonicalSourceKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedCanonicalSourceKRData_TPhi hData

/-- Canonical-interface KR exposure: source, constraint type, and local state are
all derived from the concrete Cook--Levin support/type data; only the exact
canonical-word interpretation theorem remains. -/
theorem SAT_path_B_touchedCanonicalInterfaceKR_TPhi_extraction_move
    (hData : Step247UniformTouchedCanonicalInterfaceKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedCanonicalInterfaceKRData_TPhi hData

/-- Row-interface KR exposure: the local state is derived from the actual SPDP
row/window data (`m` and `alloc`) together with the canonical support-fibre
source, matching the paper's row-local normal-form dependency. -/
theorem SAT_path_B_touchedRowInterfaceKR_TPhi_extraction_move
    (hData : Step247UniformTouchedRowInterfaceKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedRowInterfaceKRData_TPhi hData

/-- Row-interface uniqueness exposure: the exact interpreter is constructed
from the paper §9.3 local-normal-form uniqueness/fibre theorem. -/
theorem SAT_path_B_touchedRowInterfaceUniqueKR_TPhi_extraction_move
    (hData : Step247UniformTouchedRowInterfaceUniqueData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedRowInterfaceUniqueData_TPhi hData

/-- Shifted branch-atom compiled-basis profile exposure: proving every
witnessed shifted `NFOfWord` branch atom lies in the selected compiled-basis
profile subspace closes the placed quotient/descent Route-B chain. -/
theorem SAT_path_B_paperFaithfulShiftedBranchAtomCompiledBasisProfile_TPhi_extraction_move
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedBranchAtomCompiledBasisProfileData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescent
    (step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData_of_renamedCanonicalInterfaceExpansionData
      (step247UniformRouteBPaperFaithfulTPhiRenamedCanonicalInterfaceExpansionData_of_canonicalInterfaceExpansionData
        (step247UniformRouteBPaperFaithfulTPhiCanonicalInterfaceExpansionData_of_interfaceSlotExpansionData
          (step247UniformRouteBPaperFaithfulTPhiInterfaceSlotExpansionData_of_compiledBasisProfileSubspaceRowData
            (step247UniformRouteBPaperFaithfulTPhiCompiledBasisProfileSubspaceRowData_of_shiftedBranchAtomCompiledBasisProfileData
              hData)))))

/-- Shifted Leibniz-product compiled-basis profile exposure: the product-level
local membership rewrites to the witnessed branch-atom surface, then follows
the same placed quotient/descent chain. -/
theorem SAT_path_B_paperFaithfulShiftedLeibnizProductCompiledBasisProfile_TPhi_extraction_move
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisProfileData) :
    NoBoundedSATDeciderAtPaperScale :=
  SAT_path_B_paperFaithfulShiftedBranchAtomCompiledBasisProfile_TPhi_extraction_move
    (step247UniformRouteBPaperFaithfulTPhiShiftedBranchAtomCompiledBasisProfileData_of_shiftedLeibnizProductData
      hData)

/-- Shifted Leibniz local-algebra exposure: it is enough to prove the unshifted
bounded Leibniz product is in the selected profile subspace and that the
selected shift/`mlProj` operation preserves that subspace. -/
theorem SAT_path_B_paperFaithfulShiftedLeibnizProductLocalAlgebra_TPhi_extraction_move
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisLocalAlgebraData) :
    NoBoundedSATDeciderAtPaperScale :=
  SAT_path_B_paperFaithfulShiftedLeibnizProductCompiledBasisProfile_TPhi_extraction_move
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisProfileData_of_localAlgebraData
      hData)

/-- Interface-contribution exposure: it is enough to split every unshifted
bounded Leibniz product into one symmetric-power contribution per interface
type, plus the selected shift/`mlProj` closure. -/
theorem SAT_path_B_paperFaithfulShiftedLeibnizProductInterfaceContribution_TPhi_extraction_move
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceContributionData) :
    NoBoundedSATDeciderAtPaperScale :=
  SAT_path_B_paperFaithfulShiftedLeibnizProductLocalAlgebra_TPhi_extraction_move
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisLocalAlgebraData_of_interfaceContributionData
      hData)

/-- Interface-slot factorization exposure: the remaining local proof can be
stated in the most literal Lemma-31 form, with exactly `ρ.val σ` compiled-basis
slots for each selected interface type. -/
theorem SAT_path_B_paperFaithfulShiftedLeibnizProductInterfaceSlotFactorization_TPhi_extraction_move
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotFactorizationData) :
    NoBoundedSATDeciderAtPaperScale :=
  SAT_path_B_paperFaithfulShiftedLeibnizProductInterfaceContribution_TPhi_extraction_move
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceContributionData_of_interfaceSlotFactorizationData
      hData)

/-- Row-specific slot-product shift exposure: exact slot products plus the
selected shifted membership for each bounded Leibniz term supply the shifted
Leibniz-product profile seam without asserting profile-uniform operator
closure. -/
theorem SAT_path_B_paperFaithfulShiftedLeibnizProductInterfaceSlotProductRowShift_TPhi_extraction_move
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftData) :
    NoBoundedSATDeciderAtPaperScale :=
  SAT_path_B_paperFaithfulShiftedLeibnizProductCompiledBasisProfile_TPhi_extraction_move
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisProfileData_of_interfaceSlotProductRowShiftData
      hData)

/-- Coherent exact slot-product plus shifted branch-atom exposure: this closes
 the row-specific shifted slot-product seam without profile-uniform operator
 closure. -/
theorem SAT_path_B_paperFaithfulShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtom_TPhi_extraction_move
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData) :
    NoBoundedSATDeciderAtPaperScale :=
  SAT_path_B_paperFaithfulShiftedLeibnizProductInterfaceSlotProductRowShift_TPhi_extraction_move
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftData_of_slotProductBranchAtomData
      hData)

/-- Coherent factor-indexed slot-product plus shifted branch-atom exposure:
the concrete factor-index classification instantiates the exact anonymous slot
product, and the independent branch-atom payload supplies the shifted selected
row membership. -/
theorem SAT_path_B_paperFaithfulShiftedLeibnizProductInterfaceSlotProductRowShiftFromIndexedBranchAtom_TPhi_extraction_move
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromIndexedBranchAtomData) :
    NoBoundedSATDeciderAtPaperScale :=
  SAT_path_B_paperFaithfulShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtom_TPhi_extraction_move
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData_of_indexedBranchAtomData
      hData)

/-- Disjoint-covering factor-fiber exposure below the indexed branch-atom seam.

Here the concrete slot fibers are required to partition the Cook--Levin factor
indices; the indexed product identity is derived by finite-product algebra
rather than assumed. -/
theorem SAT_path_B_paperFaithfulShiftedLeibnizProductInterfaceSlotProductRowShiftFromIndexedFiberPartitionBranchAtom_TPhi_extraction_move
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromIndexedFiberPartitionBranchAtomData) :
    NoBoundedSATDeciderAtPaperScale :=
  SAT_path_B_paperFaithfulShiftedLeibnizProductInterfaceSlotProductRowShiftFromIndexedBranchAtom_TPhi_extraction_move
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromIndexedBranchAtomData_of_indexedFiberPartitionBranchAtomData
      hData)

/-- Slot-factorization exposure through the coherent branch-atom row-shift
route.  This is definitionally coherent: the branch-atom data is derived from
the same slot-factorization package, so there is no separate partition/profile
selector to reconcile. -/
theorem SAT_path_B_paperFaithfulShiftedLeibnizProductInterfaceSlotFactorization_viaRowShiftBranchAtom_TPhi_extraction_move
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotFactorizationData) :
    NoBoundedSATDeciderAtPaperScale :=
  SAT_path_B_paperFaithfulShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtom_TPhi_extraction_move
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData_of_interfaceSlotFactorizationData
      hData)

/-- Uniform-shift-closure slot-product exposure: the slot product construction
plus a profile-uniform shift/`mlProj` closure theorem supplies the previous
slot-factorization seam. -/
theorem SAT_path_B_paperFaithfulShiftedLeibnizProductInterfaceSlotProductUniformShiftClosure_TPhi_extraction_move
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductUniformShiftClosureData) :
    NoBoundedSATDeciderAtPaperScale :=
  SAT_path_B_paperFaithfulShiftedLeibnizProductInterfaceSlotFactorization_TPhi_extraction_move
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotFactorizationData_of_slotProductUniformShiftClosureData
      hData)

end PallLean.Paper93.DeepMath.PathB
