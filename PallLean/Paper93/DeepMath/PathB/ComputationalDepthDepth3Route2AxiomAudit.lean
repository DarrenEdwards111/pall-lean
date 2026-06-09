import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityRefuteFindepN160
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityBlockDepth3Inst
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityBlockDepthDInst
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TerminalShallowFindep
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsurvBlockRound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RecursiveTowerSeqBlock
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityGeneralDBlock
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityGeneralDBlockDischarge

/-!
# Route 2 — aggregated axiom audit over the m-free AC⁰ capstones

A single hardening artifact: one place that `#print axioms` over every load-bearing capstone of the
m-free AC⁰ program, so a single build confirms the entire chain rests only on
`[propext, Classical.choice, Quot.sound]` — no `sorry`, no `sorryAx`, no `native_decide`/`ofReduceBool`,
no custom/seam/gauge axioms.

Coverage:
* **Option (a)** — the unconditional single-DNF parity refutation.
* **Option (b) B1** — the m-free survivor/round, the block engine, the general-`d` block assembly, the
  width-aware + clean + gate-count towers, the two-parameter (depth ⟂ star) survivor and capstone, and
  the two unconditional instances (concrete depth-3 and general-`d`).

If any of these regresses (picks up `sorryAx` or a non-standard axiom), this file's build output changes
— making the audit a build-time tripwire.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

-- Option (a): unconditional single-DNF parity refutation
#print axioms parity_not_dnf_width1_n160

-- Option (b) B1: the m-free survivor / round machinery
#print axioms exists_shallow_survivor_extends_findep
#print axioms one_round_or_findep
#print axioms terminal_shallow_of_survivor_findep
#print axioms hsurv_block_round
#print axioms hsurv_block_REL2_round_dt

-- the block engine + general-d assembly
#print axioms recursive_tower_not_parity_surv_seq_block
#print axioms parity_not_altO_block
#print axioms parity_not_altO_block_hround_discharged

-- width-aware + clean + gate-count towers
#print axioms parity_not_altO_block_width_aware
#print axioms parity_not_altO_block_width_aware_clean

-- the decoupled (depth ⟂ star) capstone
#print axioms parity_not_altO_block_seq_dt

-- the two UNCONDITIONAL instances (the end results)
#print axioms parity_not_depth3_block
#print axioms parity_not_depthd_block

end PallLean.Paper93.DeepMath.PathB.Depth3
