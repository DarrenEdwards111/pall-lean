import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3MatchTableWin
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3RegionClean

/-!
# Entry 466 — universal-TM-table build: the lookup phase on the stitched tape `phiLookup_fullTape` (proved)

The first step toward the global `U`: the rule-table matcher actually runs on the **concrete stitched tape** `fullTape3`.
This instantiates the windowed matcher (`matchTable3_run_windowed`, entry 464) on `fullTape3 a csBool rules simtape` at the
config home `c = 1`, discharging every layout hypothesis from the proven invariants:

* the home marker (`fullTape3_config`, entry 461),
* the windowed cleanliness `hcleanW` (`fullTape3_matcher_clean`, entry 463, with window bound `(cfgHead ++ recordsTape3
  rules).length` — the head marker lives beyond),
* the config key (state field, separator, cache) (`fullTape3_config`).

The remaining hypotheses — the record descriptors, each `RecOK`, all before the head marker, and some matching — are exactly
what the descriptor list (next step) and the `bitLookup` bridge (entry 455) supply.

## What is proved (clean axioms, no `sorry`)

* **`phiLookup_fullTape`** (PROVED) — on `fullTape3 a csBool rules simtape`, given descriptors `recs` each `RecOK`, before
  the head marker, with one matching `(a, boolToSym3 csBool)`: `∃ N q, reachIn N (base, 1, fullTape3 …) (recMatch, q,
  fullTape3 …)` — the matcher reaches the match-found state.

## Honest scope

This grounds the **lookup phase** on the concrete tape.  It does **not** yet construct the descriptor list, nor assemble the
global `U` / prove `EmitsEncodedStepEx3` (the large but obstruction-free remaining assembly, per entry 456).  Building the
rest fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3PhiLookup

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EncTrans (boolToSym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3RecordsLayout (recordsTape3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MatchTable (matchTable3 RecOK RecMatch)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FullLayout (fullTape3 cfgHead fullTape3_config)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3RegionClean (fullTape3_matcher_clean)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MatchTableWin (matchTable3_run_windowed)

/-- **The lookup phase runs on the stitched tape (PROVED).** -/
theorem phiLookup_fullTape (recMatch L a : ℕ) (csBool : Bool) (rules : List (ℕ × Bool)) (simtape : List Sym3)
    (recs : List (ℕ × ℕ × Sym3)) (base : ℕ)
    (hOK : ∀ rec ∈ recs, RecOK (fullTape3 a csBool rules simtape) 1 a L rec)
    (hHead : ∀ rec ∈ recs, 1 + a + 1 + rec.1 < (cfgHead a csBool ++ recordsTape3 rules).length)
    (hEx : ∃ rec ∈ recs, RecMatch a (boolToSym3 csBool) rec) :
    ∃ N q, reachIn (toNTM3 (matchTable3 recMatch L base recs)) N
      (base, 1, fullTape3 a csBool rules simtape) (recMatch, q, fullTape3 a csBool rules simtape) := by
  have hcfg := fullTape3_config a csBool rules simtape
  exact matchTable3_run_windowed recMatch L (fullTape3 a csBool rules simtape) 1 a
    (cfgHead a csBool ++ recordsTape3 rules).length (boolToSym3 csBool) (by omega)
    (by cases csBool <;> simp [boolToSym3]) (by simpa using hcfg.1)
    (fun j hj1 hj2 => fullTape3_matcher_clean a csBool rules simtape j (by omega) hj2)
    (fun i hi => hcfg.2.1 i hi) hcfg.2.2.1 hcfg.2.2.2 recs base hOK hHead hEx

/-!
**The lookup phase on the stitched tape, proved.**  The matcher reaches the match-found state on the concrete `fullTape3`,
every layout hypothesis discharged from the proven invariants (461, 463).  Next: construct the descriptor list (with
cumulative offsets, each `RecOK` via entry 461, the match via 455), then the apply phase and the global `U` toward
`EmitsEncodedStepEx3` — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3PhiLookup

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3PhiLookup.phiLookup_fullTape
