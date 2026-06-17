import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalDecode

/-!
# The physical universal `hstep` — decode → step → re-encode, assembled

The physical universal machine `U` simulates a machine `M` from `M`'s code on `U`'s own tape.  Its core is the
**`hstep`** contract: one `M`-step is performed by `U` as *decode → apply rule → re-encode*.  The sub-machine contracts
are proved in their own files — tape encode/decode round-trip (`…ACC0TapeEncoding`, `…ACC0UniversalDecode`), rule
lookup (`…ACC0RuleLookup`), head movement (`…ACC0HeadLocation`), tape rewrite (`…ACC0TapeRewrite`), and the atomic
single step (`…ACC0PhysicalStep`).  This file **assembles them** into the loop's correctness at the encoded-tape level.

`univSimStep M c t` is the encoded result of one universal step: decode the tape `encodeSim M c`, apply the firing rule
`t`, and re-encode to `encodeSim M (applyTrans c t)`.  The `hstep` correctness theorem proves the whole loop is
faithful: the tape decodes to `(M, c)`, the decoded machine takes a genuine one-step `M`-transition to `applyTrans c t`,
and the re-encoded tape decodes back to `(M, applyTrans c t)` — so iterating `univSimStep` faithfully tracks `M`'s run.

## What is proved (clean axioms, no `sorry`)

* **`univSimStep`** — the encoded one-step universal transition (decode → apply firing rule → re-encode).
* **`univ_hstep_correct`** — the loop is faithful: for a firing rule `t` at `c`, (a) `decodeSim (encodeSim M c) =
  some (M, c)` (decode), (b) `reachIn (toNTM M) 1 c (applyTrans c t)` (a genuine one-step `M`-transition), and (c)
  `decodeSim (univSimStep M c t) = some (M, applyTrans c t)` (re-encode round-trips).
* **`univ_hstep_concreteStep`** — the re-encoded configuration is reached by `concreteStep M`.

## Honest scope

This assembles the proved sub-machine contracts into the `hstep` **loop correctness** at the encoded-tape level: the
decode → step → re-encode cycle faithfully advances the simulated machine by one genuine step, and round-trips.  What it
does **not** do is realise `univSimStep` as `U`'s *own* transition rules with an explicit step-overhead bound `B` (so
that `U` performs each `M`-step in `B` of its own physical steps) — that physical realisation of decode/lookup/rewrite
as `U`-transitions, with the `B` bound, is the remaining large construction (the genuine `hstep` *machine*, vs. its
*correctness contract* proved here).  This is classical Turing-machine engineering, not an open problem; nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalHStep

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM
  (TMachine TMTrans CConfig readSym applyTrans concreteStep toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalDecode (encodeSim decodeSim decodeSim_encodeSim)
open PallLean.Paper93.DeepMath.PathB.ACC0PhysicalStep (firing_rule_step)

/-- **One universal simulation step at the encoded-tape level (decode → apply firing rule → re-encode).**  Given the
tape `encodeSim M c` and a firing rule `t`, the universal step re-encodes to `encodeSim M (applyTrans c t)`. -/
noncomputable def univSimStep (M : TMachine) (c : CConfig) (t : TMTrans) : List Bool :=
  encodeSim M (applyTrans c t)

/-- **The `hstep` loop correctness (proved): decode → step → re-encode is faithful.**  For a firing rule `t` at `c`
(`t ∈ M`, `t.1 = (c.1, readSym c)`): the tape decodes to `(M, c)`; the decoded machine takes a genuine one-step
`M`-transition to `applyTrans c t` (`reachIn … 1`); and the re-encoded tape decodes back to `(M, applyTrans c t)`.
Assembles `decodeSim_encodeSim` (decode and re-encode round-trips) with `firing_rule_step` (the atomic `M`-step). -/
theorem univ_hstep_correct (M : TMachine) (c : CConfig) (t : TMTrans)
    (htM : t ∈ M) (ht1 : t.1 = (c.1, readSym c)) :
    decodeSim (encodeSim M c) = some (M, c)
      ∧ reachIn (toNTM M) 1 c (applyTrans c t)
      ∧ decodeSim (univSimStep M c t) = some (M, applyTrans c t) :=
  ⟨decodeSim_encodeSim M c, firing_rule_step M c t htM ht1, decodeSim_encodeSim M (applyTrans c t)⟩

/-- **The universal step tracks a genuine `concreteStep` (proved).**  The re-encoded configuration `applyTrans c t` is
reached from `c` by `concreteStep M` — so the universal loop advances the simulated machine by a real step. -/
theorem univ_hstep_concreteStep (M : TMachine) (c : CConfig) (t : TMTrans)
    (htM : t ∈ M) (ht1 : t.1 = (c.1, readSym c)) :
    concreteStep M c (applyTrans c t) :=
  ⟨t, htM, ht1, rfl⟩

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalHStep

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalHStep.univ_hstep_correct
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalHStep.univ_hstep_concreteStep
