import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalHStep

/-!
# The universal run — multi-step `hstep` faithfulness (proved)

`…ACC0UniversalHStep` proved the **single**-step universal loop is faithful (decode → apply firing rule → re-encode
advances the simulated machine by one genuine step and round-trips).  This file lifts that to the **multi-step run**:
the encoded universal machine, iterating its logical step, faithfully tracks the simulated machine's *entire*
`k`-step computation.

**The encoded universal step.**  `uEncStep s s'` holds when the tape `s` decodes to some `(M, c)`, a rule `t` fires at
`c`, and `s'` is the re-encoding `encodeSim M (applyTrans c t)` — exactly `U`'s logical step (decode → lookup firing
rule → apply → re-encode).  It forms the encoded universal NTM `uEncNTM`.

**Faithfulness.**  One `concreteStep M c d` lifts to one `uEncStep (encodeSim M c) (encodeSim M d)`
(`uEncStep_of_concreteStep`); by induction, an entire `M`-run `reachIn (toNTM M) k c c'` lifts to an encoded run
`reachIn uEncNTM k (encodeSim M c) (encodeSim M c')` (`uEncNTM_tracks`).  So `uEncNTM` simulates `M`'s full
`k`-step computation, at the encoded-tape level — the multi-step counterpart of the single-step `hstep` contract.

## What is proved (clean axioms, no `sorry`)

* **`uEncStep`, `uEncNTM`** — the encoded universal step (decode → firing rule → re-encode) and its NTM.
* **`uEncStep_of_concreteStep`** — one `M`-step lifts to one encoded universal step.
* **`uEncNTM_tracks`** — the encoded universal machine tracks `M`'s **full** `k`-step run: `reachIn (toNTM M) k c c' →
  reachIn uEncNTM k (encodeSim M c) (encodeSim M c')`.

## Honest scope

This proves the **multi-step** faithfulness of the encoded universal machine — it simulates the simulated machine's
entire run, not merely one step — assembling the single-step `hstep` contract (`…ACC0UniversalHStep`) over an arbitrary
`M`-computation.  What remains for the transition-table *compile* socket is the **physical realisation**: encoding the
logical `uEncStep` (decode/lookup/rewrite/re-encode) as the explicit transition rules of a concrete `TMachine` `U`, with
a per-step overhead bound `B` (so `U` performs each `uEncStep` in `B` of its own primitive steps).  That physical
construction over the sub-machine contracts (`…ACC0UniversalDecode`, `…ACC0RuleLookup`, `…ACC0TapeRewrite`, …) is the
remaining classical Turing-machine engineering, not an open problem.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalRun

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (NTM reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM
  (TMachine TMTrans CConfig readSym applyTrans concreteStep toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalDecode (encodeSim decodeSim decodeSim_encodeSim)

/-- **The encoded universal step.**  Decode the tape `s` to `(M, c)`, find a firing rule `t` at `c`, and re-encode to
`encodeSim M (applyTrans c t)` — `U`'s logical step (decode → lookup → apply → re-encode). -/
def uEncStep (s s' : List Bool) : Prop :=
  ∃ (M : TMachine) (c : CConfig) (t : TMTrans),
    decodeSim s = some (M, c) ∧ t ∈ M ∧ t.1 = (c.1, readSym c) ∧ s' = encodeSim M (applyTrans c t)

/-- The encoded universal NTM: configurations are tapes, the step is `uEncStep`. -/
def uEncNTM : NTM where
  Config := List Bool
  step := uEncStep
  init := fun x => x
  accept := fun s => ∃ M c, decodeSim s = some (M, c) ∧ c.1 = 1

/-- **One `M`-step lifts to one encoded universal step (proved).**  A `concreteStep M c d` becomes a `uEncStep
(encodeSim M c) (encodeSim M d)`: decode round-trips (`decodeSim_encodeSim`), the same rule fires, and the re-encoding
matches. -/
theorem uEncStep_of_concreteStep (M : TMachine) (c d : CConfig) (h : concreteStep M c d) :
    uEncStep (encodeSim M c) (encodeSim M d) := by
  obtain ⟨t, htM, ht1, hd⟩ := h
  exact ⟨M, c, t, decodeSim_encodeSim M c, htM, ht1, by rw [hd]⟩

/-- **The universal machine tracks `M`'s full run (proved).**  An entire `M`-computation `reachIn (toNTM M) k c c'`
lifts to an encoded run `reachIn uEncNTM k (encodeSim M c) (encodeSim M c')` — the multi-step counterpart of the
single-step `hstep` contract, by induction on `k` via `uEncStep_of_concreteStep`. -/
theorem uEncNTM_tracks (M : TMachine) (k : ℕ) (c c' : CConfig)
    (h : reachIn (toNTM M) k c c') :
    reachIn uEncNTM k (encodeSim M c) (encodeSim M c') := by
  induction k generalizing c with
  | zero =>
    simp only [reachIn] at h ⊢
    rw [h]
  | succ k ih =>
    obtain ⟨d, hs, hr⟩ := h
    exact ⟨encodeSim M d, uEncStep_of_concreteStep M c d hs, ih d hr⟩

/-!
**The universal run.**  The encoded universal machine `uEncNTM` faithfully tracks the simulated machine's **entire**
`k`-step computation (`uEncNTM_tracks`), lifting the single-step `hstep` contract (`…ACC0UniversalHStep`) to the full
run.  What remains for the transition-table compile socket is the physical realisation of the logical `uEncStep` as the
explicit rules of a concrete `TMachine` with a per-step overhead bound — classical Turing-machine engineering over the
proved sub-machine contracts, not an open problem.  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalRun

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalRun.uEncStep_of_concreteStep
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalRun.uEncNTM_tracks
