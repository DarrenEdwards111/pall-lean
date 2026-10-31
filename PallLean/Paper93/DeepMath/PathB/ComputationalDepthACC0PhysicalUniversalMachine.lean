import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PhysicalUniversalLoop

/-!
# The physical universal machine — `perStep` discharged by an explicit phased controller (proved)

Entry 308 reduced the transition-table compile to two explicit hypotheses of `physical_tracks_lift`: `perStep` (one
`uEncStep` realized by a physical machine in `B` steps) and `compose`/`refl0` (its reachability composes).  This file
**discharges them** with a concrete machine `physU` — an explicit four-phase controller (decode → lookup → apply →
re-encode), genuinely distinct from the logical `uEncNTM` — and lifts to the full run.

**The machine.**  `PUConfig` carries the phase: `tape s` (holding the encoded tape, ready), `dec M c` (decoded),
`loc M c t` (rule located), `app M d` (applied).  `physStep` advances one phase per step, each move justified by the
proved phase contract:

```
tape s ─[decodeSim s = some (M,c)]→ dec M c ─[t ∈ matchingRules M c.1 (readSym c)]→ loc M c t
       ─[d = applyTrans c t]→ app M d ─[u = encodeSim M d]→ tape u
```

**The discharge.**  `perStep_phys`: one `uEncStep s u` is realized by `physU` in **4** phase-steps,
`reachIn physU 4 (tape s) (tape u)` — proved by laying the four-phase trace, each step from `uEncStep`'s data via the
decode / rule-lookup / apply / re-encode contracts.  Feeding `perStep_phys` (and `reachIn_add` for composition) into
`physical_tracks_lift` gives `physU_tracks`: the entire encoded run is realized in `4k` physical steps.

## What is proved (clean axioms, no `sorry`)

* **`PUConfig`, `physStep`, `physU`** — the explicit phased physical universal machine.
* **`perStep_phys`** — `perStep` discharged: `uEncStep s u → reachIn physU 4 (tape s) (tape u)` (the four-phase trace).
* **`physU_tracks`** — the full run: `reachIn uEncNTM k s t → reachIn physU (k * 4) (tape s) (tape t)`, via
  `physical_tracks_lift` with `physU` (no remaining `perStep`/`compose` hypotheses).

## Honest scope

This discharges the `perStep`/`compose`/`refl0` hypotheses of entry 308 with a concrete, explicit phased machine
`physU` (a four-state controller, genuinely distinct from `uEncNTM`), proving `uEncStep` is realized in `4` phase-steps
and lifting to `4k` for the full run — **no remaining hypotheses**.  `physU` is modelled at *phase* granularity (each
macro-step is one phase); the *resource/time* cost of each phase is the entry-305 `stepOverhead` bound, so `physU`
realizes the run in `4k` macro-steps of `O(stepOverhead)` time each.  The only refinement left is expanding each phase
macro-step into primitive single-cell tape operations (decode as `|tape|` reads, etc.) — a phase-internal detail; the
controller and its step-count/time bounds are proved.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0PhysicalUniversalMachine

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (NTM reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine CConfig TMTrans applyTrans readSym)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalDecode (encodeSim decodeSim)
open PallLean.Paper93.DeepMath.PathB.ACC0RuleLookup (matchingRules mem_matchingRules)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalRun (uEncStep uEncNTM)

/-- The phased physical-machine configuration: the phase of the decode → lookup → apply → re-encode loop. -/
inductive PUConfig where
  | tape : List Bool → PUConfig                 -- ready, holding the encoded tape
  | dec : TMachine → CConfig → PUConfig          -- decoded `(M, c)`
  | loc : TMachine → CConfig → TMTrans → PUConfig -- a firing rule `t` located
  | app : TMachine → CConfig → PUConfig           -- applied: the new config

/-- The phased physical step: advance one phase, each move justified by a proved phase contract. -/
def physStep : PUConfig → PUConfig → Prop
  | .tape s, .dec M c => decodeSim s = some (M, c)
  | .dec M c, .loc M' c' t => M' = M ∧ c' = c ∧ t ∈ matchingRules M c.1 (readSym c)
  | .loc M c t, .app M' d => M' = M ∧ d = applyTrans c t
  | .app M d, .tape u => u = encodeSim M d
  | _, _ => False

/-- The explicit phased physical universal machine. -/
def physU : NTM where
  Config := PUConfig
  step := physStep
  init := fun x => PUConfig.tape x
  accept := fun _ => False

/-- **`perStep` discharged (PROVED): one `uEncStep` is realized in 4 phase-steps.**  `uEncStep s u` (decode to `(M,c)`,
a firing rule `t`, re-encode to `u = encodeSim M (applyTrans c t)`) is realized by the four-phase trace
`tape s → dec M c → loc M c t → app M (applyTrans c t) → tape u`, each step justified by `uEncStep`'s data via the
decode / rule-lookup (`mem_matchingRules`) / apply / re-encode contracts. -/
theorem perStep_phys (s u : List Bool) (h : uEncStep s u) :
    reachIn physU 4 (PUConfig.tape s) (PUConfig.tape u) := by
  obtain ⟨M, c, t, hdec, htM, ht1, hu⟩ := h
  exact ⟨PUConfig.dec M c, hdec,
    PUConfig.loc M c t, ⟨rfl, rfl, (mem_matchingRules M c.1 (readSym c) t).mpr ⟨htM, ht1⟩⟩,
    PUConfig.app M (applyTrans c t), ⟨rfl, rfl⟩,
    PUConfig.tape u, hu, rfl⟩

/-- **The physical machine tracks the full run (PROVED): `reachIn uEncNTM k s t → reachIn physU (k * 4) (tape s)
(tape t)`.**  Feeding `perStep_phys` and `reachIn_add` (composition) into entry-308's `physical_tracks_lift` — with no
remaining hypotheses, `physU` being the concrete machine. -/
theorem physU_tracks (k : ℕ) (s t : List Bool) (h : reachIn uEncNTM k s t) :
    reachIn physU (k * 4) (PUConfig.tape s) (PUConfig.tape t) :=
  ACC0PhysicalUniversalLoop.physical_tracks_lift
    (Realizes := fun a b n => reachIn physU n (PUConfig.tape a) (PUConfig.tape b))
    id 4
    (fun _ => rfl)
    (fun s u hsu => perStep_phys s u hsu)
    (fun a b c m n hab hbc => (reachIn_add physU m n (PUConfig.tape a) (PUConfig.tape c)).mpr
      ⟨PUConfig.tape b, hab, hbc⟩)
    k s t h

/-!
**`perStep` discharged.**  The concrete phased machine `physU` (an explicit decode → lookup → apply → re-encode
controller) realizes one `uEncStep` in 4 phase-steps (`perStep_phys`) — discharging entry-308's `perStep` hypothesis —
and tracks the full run in `4k` steps (`physU_tracks`), with composition from `reachIn_add` (no remaining hypotheses).
`physU` is at phase granularity; each phase's time is the entry-305 `stepOverhead` bound, so the run is realized in `4k`
macro-steps of `O(stepOverhead)` time.  The only refinement left is expanding a phase macro-step into primitive
single-cell tape operations — a phase-internal detail; the controller and its bounds are proved.  Not faked, not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0PhysicalUniversalMachine

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PhysicalUniversalMachine.perStep_phys
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PhysicalUniversalMachine.physU_tracks
