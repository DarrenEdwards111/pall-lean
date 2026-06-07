import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RazborovWIP
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DseqNoGo
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DseqPureSatisfy
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DseqNoSkip
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DseqCleanSkip
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FullPathRecover
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RecoverStreamBase
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3StreamRecursion
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3MaintainInvariant
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SubRestriction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingReconstructed

/-!
# Manifest: the depth-3 switching reconstruction arc (branch `razborov-recoverRho-wip`)

A machine-checked index of the whole reconstruction effort.  Every `#check` is a proved theorem with
clean axioms (no `sorry`, no `native_decide`).  The arc removes the depth-3 switching collapse's last
gap (`deepestSatSeq` recovery) down to a single, precisely-named recursive obligation.

## Section 1 — the satisfy-position decoder `Dseq`: regimes + a no-go

The first decoder reads only the satisfy positions.  Its correctness is proved in three regimes, and a
no-go proves it cannot be general (it cannot emit an empty interior block, which the confound forces).

* `recoverRhoObligation_iff_reconstructionCorrect`, `satSeqReconstruct_general` — the reduction to
  recovering the satisfy sequence.
* `Dseq` + `Dseq_pos_lt` / `Dseq_clause_mem` / `Dseq_idxOf_pairwise` — the concrete decoder + sanity.
* `Dseq_correct_pure_satisfy`, `Dseq_correct_no_skip`, `Dseq_correct_clean_skip` — three proved regimes.
* `Dseq_first_clause_mem` — the **no-go**: `Dseq` cannot skip a clause, so it is not general.

## Section 2 — the full-path replacement

The fix records the full canonical path (satisfy *and* falsify steps), restoring the boundary
information the satisfy-position label dropped.

* `deepestFullSeq` + `deepestFullSeq_satSeq` — the full path, subsuming `deepestSatSeq`.
* `deepestSatSeq_length_le_full` — length bound (the new `(2w)^s` exponent).
* `fullReplaySat` + `fullReplaySat_clause_mem` — the full-path forward decoder + sanity.

## Section 3 — replay correctness, given the active-clause stream

* `fullReplaySatPar`, `activeStreamPar`, `fullReplaySatPar_correct` — the full path *plus* the
  active-clause stream reconstruct `deepestSatSeq` exactly (confound included).

## Section 4 — `FullPathRecoverable`: the reduction to the two recoveries

* `FullPathRecoverable`, `fullpath_deepestSatSeq_recover` — the full reconstruction follows from
  recovering the active-clause stream and the path from the leaf.

## Section 5 — `recoverStream`: base case proved + the recursion engine

* `bad_live_everywhere`, `activeTerm_eq_head_of_bad` — a bad ρ is live everywhere, so the first active
  clause is `cs.head?`, recovered with no leaf reference.
* `activeStreamPar_head`, `activeStreamPar_head_of_bad` — that base, pinned on the target stream.
* `activeTerm_eq_of_falsified_agree` — the **recursion engine**: falsification-agreement ⟹ same active
  term (the running decoder state stays synchronised with the descent state, because a bad ρ falsifies
  nothing, so ρ-fixed variables never affect falsification — dissolving the circularity).

## Section 6 — the recursive `recoverStream`, COMPLETED

The recursion engine, its invariant infrastructure, the concrete decoder, and its correctness:

* `activeTerm_eq_of_falsified_agree` — engine (falsification-agreement ⟹ same active term).
* `maintain_falsified_agree` — the agreement invariant survives a step.
* `anyTermSat_false_of_sub`, `subRestriction_fixVar` — the `⊑` half of the invariant.
* `recoverStream` + `recoverStream_correct` — the concrete leaf-only decoder *recovers the active-clause
  stream of a bad ρ with no reference to ρ*.  The circularity is dissolved (a bad ρ falsifies nothing).

## Endpoint — reconstruction CLOSED

* `deepestSatSeq_reconstructed` — **the keystone**: `deepestSatSeq cs F ρ` is reconstructed from the
  leaf `deepestEnd cs F ρ` and the full path `deepestFullSeq cs F ρ` by the legal-data decoders
  (`recoverStream` then `fullReplaySatPar`).
* `fullPathRecoverable_of_encoder` — the reconstruction obligation discharged for any full-path encoder.

So the switching **reconstruction** (the hard, formerly-circular half) is **complete**: ρ — via
`deepestSatSeq` and `freeOn_deepestEnd` — is recovered from the leaf and the full path.  All that
remains for the full lemma is the `(2w)^s` **count** packaging (encode `deepestFullSeq` into `PathLabel`
+ the cardinality bound), which the codebase's counting machinery consumes.  `Depth3CollapseModel.collapse`
and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

-- Section 1 — Dseq: regimes + no-go
#check @Depth3.recoverRhoObligation_iff_reconstructionCorrect
#check @Depth3.satSeqReconstruct_general
#check @Depth3.Dseq
#check @Depth3.Dseq_pos_lt
#check @Depth3.Dseq_clause_mem
#check @Depth3.Dseq_idxOf_pairwise
#check @Depth3.Dseq_correct_pure_satisfy
#check @Depth3.Dseq_correct_no_skip
#check @Depth3.Dseq_correct_clean_skip
#check @Depth3.Dseq_first_clause_mem

-- Section 2 — full-path replacement
#check @Depth3.deepestFullSeq
#check @Depth3.deepestFullSeq_satSeq
#check @Depth3.deepestSatSeq_length_le_full
#check @Depth3.fullReplaySat
#check @Depth3.fullReplaySat_clause_mem

-- Section 3 — replay correctness given the stream
#check @Depth3.fullReplaySatPar
#check @Depth3.activeStreamPar
#check @Depth3.fullReplaySatPar_correct

-- Section 4 — FullPathRecoverable
#check @Depth3.FullPathRecoverable
#check @Depth3.fullpath_deepestSatSeq_recover

-- Section 5 — recoverStream base + recursion engine
#check @Depth3.bad_live_everywhere
#check @Depth3.activeTerm_eq_head_of_bad
#check @Depth3.activeStreamPar_head
#check @Depth3.activeStreamPar_head_of_bad
#check @Depth3.activeTerm_eq_of_falsified_agree

-- Section 6: the recursive recoverStream, completed.
#check @Depth3.activeTerm_eq_of_falsified_agree
#check @Depth3.maintain_falsified_agree
#check @Depth3.anyTermSat_false_of_sub
#check @Depth3.subRestriction_fixVar
#check @Depth3.recoverStream
#check @Depth3.recoverStream_correct

-- Endpoint: reconstruction CLOSED — deepestSatSeq (hence ρ) recovered from leaf + full path.
#check @Depth3.fullpath_deepestSatSeq_recover
#check @Depth3.deepestSatSeq_reconstructed
#check @Depth3.fullPathRecoverable_of_encoder

end PallLean.Paper93.DeepMath.PathB
