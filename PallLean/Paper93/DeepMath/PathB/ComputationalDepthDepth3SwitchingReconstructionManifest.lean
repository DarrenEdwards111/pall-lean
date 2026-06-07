import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RazborovWIP
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DseqNoGo
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DseqPureSatisfy
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DseqNoSkip
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DseqCleanSkip
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FullPathRecover
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RecoverStreamBase
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3StreamRecursion

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

## Endpoint

The switching reconstruction **reduces to**: the recursive `recoverStream` (assemble the running-state
decoder on top of `activeTerm_eq_of_falsified_agree`, whose base case is `activeStreamPar_head_of_bad`)
**plus** the `(2w)^s` count.  `fullpath_deepestSatSeq_recover` is the proved reduction consuming that
obligation; everything else above is proved.  `Depth3CollapseModel.collapse` and P≠NP untouched.
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

-- Endpoint: the reconstruction reduces to recursive recoverStream + count.
#check @Depth3.fullpath_deepestSatSeq_recover

end PallLean.Paper93.DeepMath.PathB
