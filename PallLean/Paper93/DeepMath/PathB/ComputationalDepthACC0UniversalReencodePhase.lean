import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalDecodePhase
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PhysicalStep

/-!
# The universal re-encode phase — write the post-step state back, completing the four phases

Fourth and last of entry 182's per-phase realizations (rewrite 183, lookup 184, decode 185).  The **re-encode phase**
writes the post-step simulation state `(M, d)` back onto the universal machine's tape as `encodeSim M d`.  It is the
inverse of the decode phase, so the encoding contracts already cover it: the output tape round-trips
(`decodeSim_encodeSim`) and is the *unique* tape for `(M, d)` (`encodeSim_inj`, entry 185).  This file states the
re-encode phase and assembles all four phases into the full universal-step tape correctness.

## What is proved (clean axioms, no `sorry`)

* **`reencode_phase`** — the post-step tape is canonical: `decodeSim (encodeSim M d) = some (M, d)` (it round-trips) and
  `∀ M' d', encodeSim M d = encodeSim M' d' → M = M' ∧ d = d'` (it is the unique encoding of `(M, d)`).
* **`universal_step_complete`** — all four phases assembled: for a firing rule `t` at `c`, the universal step takes the
  tape `encodeSim M c` (decodes to `(M, c)`) through a genuine one-step `M`-transition (`reachIn (toNTM M) 1 c
  (applyTrans c t)`) to the re-encoded tape `encodeSim M (applyTrans c t)` (decodes to `(M, applyTrans c t)`, the unique
  such tape) — the complete decode → step → re-encode cycle, faithful and round-tripping.

## Honest scope

This completes the four per-phase correctness realizations: the re-encode is the inverse of decode, covered by the same
round-trip + injectivity contracts, and `universal_step_complete` assembles all four into the full tape-level universal
step.  What remains — as for the other phases — is realising the re-encode (and the parse/scan) as the universal `U`'s
*own* transitions writing the `encodeTape` bit-layout with explicit per-symbol step counts; combined with entry 182's
overhead composition, that yields the fully physical `hstep` machine with its `B` bound.  This is classical
Turing-machine construction, not an open problem; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalReencodePhase

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM
  (TMachine TMTrans CConfig readSym applyTrans concreteStep toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalDecode (encodeSim decodeSim decodeSim_encodeSim)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalDecodePhase (encodeSim_inj)
open PallLean.Paper93.DeepMath.PathB.ACC0PhysicalStep (firing_rule_step)

/-- **The re-encode phase (proved): the post-step tape is the canonical encoding of `(M, d)`.**  `encodeSim M d`
round-trips (`decodeSim (encodeSim M d) = some (M, d)`) and is the *unique* tape encoding `(M, d)` (`encodeSim_inj`) — so
writing it back faithfully records the post-step simulation state. -/
theorem reencode_phase (M : TMachine) (d : CConfig) :
    decodeSim (encodeSim M d) = some (M, d)
      ∧ (∀ M' d', encodeSim M d = encodeSim M' d' → M = M' ∧ d = d') :=
  ⟨decodeSim_encodeSim M d, fun _ _ he => encodeSim_inj he⟩

/-- **The full four-phase universal step (proved): decode → step → re-encode at the tape level.**  For a firing rule `t`
at `c` (`t ∈ M`, `t.1 = (c.1, readSym c)`): the tape `encodeSim M c` decodes to `(M, c)`; a genuine one-step
`M`-transition reaches `applyTrans c t` (`reachIn (toNTM M) 1 …`); and the re-encoded tape `encodeSim M (applyTrans c t)`
decodes to `(M, applyTrans c t)` and is the unique such tape.  Assembles all four per-phase contracts (decode 185 +
lookup 184 / rewrite 183 firing + re-encode) into the complete universal-step tape correctness. -/
theorem universal_step_complete (M : TMachine) (c : CConfig) (t : TMTrans)
    (htM : t ∈ M) (ht1 : t.1 = (c.1, readSym c)) :
    decodeSim (encodeSim M c) = some (M, c)
      ∧ reachIn (toNTM M) 1 c (applyTrans c t)
      ∧ decodeSim (encodeSim M (applyTrans c t)) = some (M, applyTrans c t)
      ∧ (∀ M' d', encodeSim M (applyTrans c t) = encodeSim M' d' → M = M' ∧ applyTrans c t = d') :=
  ⟨decodeSim_encodeSim M c, firing_rule_step M c t htM ht1,
   decodeSim_encodeSim M (applyTrans c t), fun _ _ he => encodeSim_inj he⟩

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalReencodePhase

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalReencodePhase.reencode_phase
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalReencodePhase.universal_step_complete
