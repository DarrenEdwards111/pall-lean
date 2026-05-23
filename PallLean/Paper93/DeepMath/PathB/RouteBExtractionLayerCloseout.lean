import PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiExtraction
import PallLean.Paper93.DeepMath.PathB.PeqNPBridge

/-!
# Route B extraction-layer closeout

This is the paper-faithful Route-B target, not the flattened `q_n` reading.

The P-side upper bound is placed on the instrumented Cook--Levin source
polynomial.  The NP-side lower bound is placed on the strict coupled-sheet
`TΦ` target.  The extraction layer supplies the bridge:

`P_{M',n} --(basis ◦ affine ◦ restriction ◦ projection)--> Q×_Φ`

with SPDP rank non-increase.  Thus any bounded SAT decider yields the low-rank
bound on the extracted coupled sheet, contradicting the identity-minor lower
bound there.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- The strict `TΦ` extraction layer rules out bounded SAT deciders at paper
scale.

This is the corrected Route-B closeout: it does **not** collapse the hard
coupled sheet directly as the raw compiler object.  It first passes through the
paper's extraction map and rank-monotone source transport, using
`false_of_routeBPaperFaithfulTPhi_from_p_side` internally. -/
theorem noBoundedSATDeciderAtPaperScale_via_strict_TPhi_extraction :
    NoBoundedSATDeciderAtPaperScale :=
  PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_p_side

/-- Paper-level consequence of the strict `TΦ` extraction closeout:
`PeqNP_Paper` is contradictory via the bounded-SAT-decider bridge. -/
theorem not_PeqNP_Paper_via_strict_TPhi_extraction :
    ∀ (_ : PeqNP_Paper), False :=
  noBoundedSATDeciderAtPaperScale_implies_not_PeqNP
    noBoundedSATDeciderAtPaperScale_via_strict_TPhi_extraction

/-- Empty-type packaging of the strict extraction-layer Route-B result. -/
theorem isEmpty_PeqNP_Paper_via_strict_TPhi_extraction :
    IsEmpty PeqNP_Paper :=
  ⟨not_PeqNP_Paper_via_strict_TPhi_extraction⟩

/-- **No-seam Route-B closeout (conditional frontier form).**

This route removes the legacy `spdp_profile_generators` dependency by using the
paper-faithful template-collapse frontier directly. -/
theorem noBoundedSATDeciderAtPaperScale_via_strict_TPhi_extraction_no_seams
    (hcollapse :
      ∀ (M : TuringMachine.DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        WithinProfileBound.CookLevinProfileTemplateCollapseLemma
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_templateCollapse
    hcollapse

/-- No-seam paper-level closeout: `PeqNP_Paper` contradiction from the strict
`TΦ` extraction plus the template-collapse frontier. -/
theorem not_PeqNP_Paper_via_strict_TPhi_extraction_no_seams
    (hcollapse :
      ∀ (M : TuringMachine.DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        WithinProfileBound.CookLevinProfileTemplateCollapseLemma
          M n hn2 htb hns) :
    ∀ (_ : PeqNP_Paper), False :=
  noBoundedSATDeciderAtPaperScale_implies_not_PeqNP
    (noBoundedSATDeciderAtPaperScale_via_strict_TPhi_extraction_no_seams hcollapse)

/-- No-seam empty-type packaging for `PeqNP_Paper`. -/
theorem isEmpty_PeqNP_Paper_via_strict_TPhi_extraction_no_seams
    (hcollapse :
      ∀ (M : TuringMachine.DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        WithinProfileBound.CookLevinProfileTemplateCollapseLemma
          M n hn2 htb hns) :
    IsEmpty PeqNP_Paper :=
  ⟨not_PeqNP_Paper_via_strict_TPhi_extraction_no_seams hcollapse⟩

/-! ## Axiom audit anchors -/

#print axioms noBoundedSATDeciderAtPaperScale_via_strict_TPhi_extraction
#print axioms not_PeqNP_Paper_via_strict_TPhi_extraction
#print axioms isEmpty_PeqNP_Paper_via_strict_TPhi_extraction
#print axioms noBoundedSATDeciderAtPaperScale_via_strict_TPhi_extraction_no_seams
#print axioms not_PeqNP_Paper_via_strict_TPhi_extraction_no_seams
#print axioms isEmpty_PeqNP_Paper_via_strict_TPhi_extraction_no_seams

end PallLean.Paper93.DeepMath.PathB
