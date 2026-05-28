import Mathlib.Data.List.Basic

/-!
# First 25 bridge-candidate kill tests

This file turns the first 25 `needs_lean_proof` bridge candidates from the
JSON kill-filter pass into a small Lean audit surface.

The key point is deliberately conservative:

* none of the 25 is marked as passed;
* the first 10 are `WLOC` / hidden same-object-collapse candidates, so their
  Lean obligation is a genuine source/target rank separation theorem;
* the next 15 are `ZRAE` candidates, so their Lean obligation is a genuine
  zero-rank/degenerate-presentation exclusion theorem.

A later file can instantiate `CandidateLeanObligations` with real mathematical
content.  Until then, these 25 are formal frontier obligations, not survivors.
-/

namespace PallLean.Paper93.DeepMath.PathC.BridgeCandidateFirst25

/-- The first 25 candidates that survived the syntactic kill-filter only as
`needs_lean_proof`.  Constructor names record the original generated id. -/
inductive First25Candidate where
  | SNF_PI_IU_WLOC_077
  | SNF_PI_IU_WLOC_082
  | SNF_PI_IU_WLOC_087
  | SNF_PI_IU_WLOC_092
  | SNF_PI_IU_WLOC_097
  | SNF_PI_DTC_WLOC_202
  | SNF_PI_DTC_WLOC_207
  | SNF_PI_DTC_WLOC_212
  | SNF_PI_DTC_WLOC_217
  | SNF_PI_DTC_WLOC_222
  | SNF_PI_ZRAE_SLW_254
  | SNF_PI_ZRAE_SLW_259
  | SNF_PI_ZRAE_SLW_264
  | SNF_PI_ZRAE_SLW_269
  | SNF_PI_ZRAE_SLW_274
  | SNF_PI_ZRAE_RFE_279
  | SNF_PI_ZRAE_RFE_284
  | SNF_PI_ZRAE_RFE_289
  | SNF_PI_ZRAE_RFE_294
  | SNF_PI_ZRAE_RFE_299
  | SNF_PI_ZRAE_IMP_304
  | SNF_PI_ZRAE_IMP_309
  | SNF_PI_ZRAE_IMP_314
  | SNF_PI_ZRAE_IMP_319
  | SNF_PI_ZRAE_IMP_324
  deriving DecidableEq

/-- Explicit list of the first 25 candidates. -/
def first25List : List First25Candidate :=
  [ .SNF_PI_IU_WLOC_077
  , .SNF_PI_IU_WLOC_082
  , .SNF_PI_IU_WLOC_087
  , .SNF_PI_IU_WLOC_092
  , .SNF_PI_IU_WLOC_097
  , .SNF_PI_DTC_WLOC_202
  , .SNF_PI_DTC_WLOC_207
  , .SNF_PI_DTC_WLOC_212
  , .SNF_PI_DTC_WLOC_217
  , .SNF_PI_DTC_WLOC_222
  , .SNF_PI_ZRAE_SLW_254
  , .SNF_PI_ZRAE_SLW_259
  , .SNF_PI_ZRAE_SLW_264
  , .SNF_PI_ZRAE_SLW_269
  , .SNF_PI_ZRAE_SLW_274
  , .SNF_PI_ZRAE_RFE_279
  , .SNF_PI_ZRAE_RFE_284
  , .SNF_PI_ZRAE_RFE_289
  , .SNF_PI_ZRAE_RFE_294
  , .SNF_PI_ZRAE_RFE_299
  , .SNF_PI_ZRAE_IMP_304
  , .SNF_PI_ZRAE_IMP_309
  , .SNF_PI_ZRAE_IMP_314
  , .SNF_PI_ZRAE_IMP_319
  , .SNF_PI_ZRAE_IMP_324
  ]

/-- Sanity check: this file is exactly for the first 25 candidates. -/
theorem first25_list_length : first25List.length = 25 := by
  rfl

/-- Risk bucket assigned by the JSON kill-filter. -/
inductive CandidateRisk where
  | hiddenSameObjectCollapse
  | zeroRankEscape
  deriving DecidableEq

/-- First-pass status.  `needsLeanProof` is not a proof of survival. -/
inductive FirstPassStatus where
  | killed
  | needsLeanProof
  | survived
  deriving DecidableEq

/-- Human-readable original candidate name. -/
def candidateName : First25Candidate -> String
  | .SNF_PI_IU_WLOC_077 => "SNF-PI-IU-WLOC-77"
  | .SNF_PI_IU_WLOC_082 => "SNF-PI-IU-WLOC-82"
  | .SNF_PI_IU_WLOC_087 => "SNF-PI-IU-WLOC-87"
  | .SNF_PI_IU_WLOC_092 => "SNF-PI-IU-WLOC-92"
  | .SNF_PI_IU_WLOC_097 => "SNF-PI-IU-WLOC-97"
  | .SNF_PI_DTC_WLOC_202 => "SNF-PI-DTC-WLOC-202"
  | .SNF_PI_DTC_WLOC_207 => "SNF-PI-DTC-WLOC-207"
  | .SNF_PI_DTC_WLOC_212 => "SNF-PI-DTC-WLOC-212"
  | .SNF_PI_DTC_WLOC_217 => "SNF-PI-DTC-WLOC-217"
  | .SNF_PI_DTC_WLOC_222 => "SNF-PI-DTC-WLOC-222"
  | .SNF_PI_ZRAE_SLW_254 => "SNF-PI-ZRAE-SLW-254"
  | .SNF_PI_ZRAE_SLW_259 => "SNF-PI-ZRAE-SLW-259"
  | .SNF_PI_ZRAE_SLW_264 => "SNF-PI-ZRAE-SLW-264"
  | .SNF_PI_ZRAE_SLW_269 => "SNF-PI-ZRAE-SLW-269"
  | .SNF_PI_ZRAE_SLW_274 => "SNF-PI-ZRAE-SLW-274"
  | .SNF_PI_ZRAE_RFE_279 => "SNF-PI-ZRAE-RFE-279"
  | .SNF_PI_ZRAE_RFE_284 => "SNF-PI-ZRAE-RFE-284"
  | .SNF_PI_ZRAE_RFE_289 => "SNF-PI-ZRAE-RFE-289"
  | .SNF_PI_ZRAE_RFE_294 => "SNF-PI-ZRAE-RFE-294"
  | .SNF_PI_ZRAE_RFE_299 => "SNF-PI-ZRAE-RFE-299"
  | .SNF_PI_ZRAE_IMP_304 => "SNF-PI-ZRAE-IMP-304"
  | .SNF_PI_ZRAE_IMP_309 => "SNF-PI-ZRAE-IMP-309"
  | .SNF_PI_ZRAE_IMP_314 => "SNF-PI-ZRAE-IMP-314"
  | .SNF_PI_ZRAE_IMP_319 => "SNF-PI-ZRAE-IMP-319"
  | .SNF_PI_ZRAE_IMP_324 => "SNF-PI-ZRAE-IMP-324"

/-- The first 10 need a separated-object theorem; the next 15 need ZRAE. -/
def candidateRisk : First25Candidate -> CandidateRisk
  | .SNF_PI_IU_WLOC_077 => .hiddenSameObjectCollapse
  | .SNF_PI_IU_WLOC_082 => .hiddenSameObjectCollapse
  | .SNF_PI_IU_WLOC_087 => .hiddenSameObjectCollapse
  | .SNF_PI_IU_WLOC_092 => .hiddenSameObjectCollapse
  | .SNF_PI_IU_WLOC_097 => .hiddenSameObjectCollapse
  | .SNF_PI_DTC_WLOC_202 => .hiddenSameObjectCollapse
  | .SNF_PI_DTC_WLOC_207 => .hiddenSameObjectCollapse
  | .SNF_PI_DTC_WLOC_212 => .hiddenSameObjectCollapse
  | .SNF_PI_DTC_WLOC_217 => .hiddenSameObjectCollapse
  | .SNF_PI_DTC_WLOC_222 => .hiddenSameObjectCollapse
  | .SNF_PI_ZRAE_SLW_254 => .zeroRankEscape
  | .SNF_PI_ZRAE_SLW_259 => .zeroRankEscape
  | .SNF_PI_ZRAE_SLW_264 => .zeroRankEscape
  | .SNF_PI_ZRAE_SLW_269 => .zeroRankEscape
  | .SNF_PI_ZRAE_SLW_274 => .zeroRankEscape
  | .SNF_PI_ZRAE_RFE_279 => .zeroRankEscape
  | .SNF_PI_ZRAE_RFE_284 => .zeroRankEscape
  | .SNF_PI_ZRAE_RFE_289 => .zeroRankEscape
  | .SNF_PI_ZRAE_RFE_294 => .zeroRankEscape
  | .SNF_PI_ZRAE_RFE_299 => .zeroRankEscape
  | .SNF_PI_ZRAE_IMP_304 => .zeroRankEscape
  | .SNF_PI_ZRAE_IMP_309 => .zeroRankEscape
  | .SNF_PI_ZRAE_IMP_314 => .zeroRankEscape
  | .SNF_PI_ZRAE_IMP_319 => .zeroRankEscape
  | .SNF_PI_ZRAE_IMP_324 => .zeroRankEscape

/-- Every one of the first 25 is still only `needsLeanProof`; none passed. -/
def firstPassStatus (_c : First25Candidate) : FirstPassStatus :=
  .needsLeanProof

/-- What a real Lean discharge would have to provide for candidate `c`. -/
structure CandidateLeanObligations (c : First25Candidate) : Type where
  /-- For WLOC candidates: prove the bridge does not rank-sandwich the same
  object at paper scale.  For ZRAE candidates this field may be vacuous. -/
  sourceTargetRankSeparated : Prop
  /-- For ZRAE candidates: prove zero-rank/degenerate presentations cannot
  satisfy the candidate premises.  For WLOC candidates this field may be vacuous. -/
  zeroRankPresentationExcluded : Prop

/-- The actual frontier obligation selected by the candidate's risk bucket. -/
def requiredLeanObligation (c : First25Candidate)
    (O : CandidateLeanObligations c) : Prop :=
  match candidateRisk c with
  | .hiddenSameObjectCollapse => O.sourceTargetRankSeparated
  | .zeroRankEscape => O.zeroRankPresentationExcluded

/-- First-pass audit theorem: all 25 are obligations, not passes. -/
theorem all_first25_need_lean_proof :
    ∀ c : First25Candidate, firstPassStatus c = .needsLeanProof := by
  intro c
  rfl

/-- First-pass audit theorem: zero of the 25 passed in the formal sense. -/
theorem no_first25_survived_first_pass :
    ∀ c : First25Candidate, firstPassStatus c ≠ .survived := by
  intro c h
  cases h

/-- WLOC kill-test: if the source/target rank separation obligation is absent,
the candidate cannot be promoted by this file. -/
theorem hiddenSameObject_requires_separation
    (c : First25Candidate) (O : CandidateLeanObligations c)
    (hrisk : candidateRisk c = .hiddenSameObjectCollapse)
    (hmissing : ¬ O.sourceTargetRankSeparated) :
    ¬ requiredLeanObligation c O := by
  unfold requiredLeanObligation
  rw [hrisk]
  exact hmissing

/-- ZRAE kill-test: if zero-rank presentations are not excluded, the candidate
cannot be promoted by this file. -/
theorem zeroRankEscape_requires_exclusion
    (c : First25Candidate) (O : CandidateLeanObligations c)
    (hrisk : candidateRisk c = .zeroRankEscape)
    (hmissing : ¬ O.zeroRankPresentationExcluded) :
    ¬ requiredLeanObligation c O := by
  unfold requiredLeanObligation
  rw [hrisk]
  exact hmissing

/-- Any future promotion of one of the 25 must pass its selected obligation. -/
theorem promotion_requires_selected_obligation
    (c : First25Candidate) (O : CandidateLeanObligations c)
    (hpromoted : requiredLeanObligation c O) :
    match candidateRisk c with
    | .hiddenSameObjectCollapse => O.sourceTargetRankSeparated
    | .zeroRankEscape => O.zeroRankPresentationExcluded := by
  simpa [requiredLeanObligation] using hpromoted

/-! ## Actual pass test

The empty-obligation package represents the state of the generated candidates
before any new mathematical Lean proof is supplied.  If any candidate passed
with this package, it would mean the first-pass filter accidentally promoted it
without proving the real guard. -/

/-- No separated-object theorem and no zero-rank exclusion theorem supplied. -/
def emptyObligations (c : First25Candidate) : CandidateLeanObligations c where
  sourceTargetRankSeparated := False
  zeroRankPresentationExcluded := False

/-- Test result: none of the 25 pass without the selected Lean obligation. -/
theorem no_first25_auto_pass :
    ∀ c : First25Candidate, ¬ requiredLeanObligation c (emptyObligations c) := by
  intro c
  cases c <;> simp [requiredLeanObligation, emptyObligations, candidateRisk]

/-! ## Axiom audit anchors -/

#print axioms first25_list_length
#print axioms all_first25_need_lean_proof
#print axioms no_first25_survived_first_pass
#print axioms hiddenSameObject_requires_separation
#print axioms zeroRankEscape_requires_exclusion
#print axioms promotion_requires_selected_obligation
#print axioms no_first25_auto_pass

end PallLean.Paper93.DeepMath.PathC.BridgeCandidateFirst25
