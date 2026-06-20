import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3ResetHome
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3MoveN

/-!
# Entry 427 — universal-TM-table build: the transfer-side navigation `navigateToSource3` (proved)

The apply's *transfer* side must bring values from the matched rule into the configuration, which means moving the head to
a **data-dependent** rule position.  This brick is the clean addressing solution: combine the config-home reset
(`resetToHome3`, entry 408) — which returns the head to the config key start `c` from *anywhere* in the config window,
distance-independently via the home marker — with a **fixed-offset** rightward move (`moveRightN3 d'`, entry 401), reaching
the rule source `c + d'`.

The fixed offset `d'` is a *parameter* of the machine (exactly as the matcher took the inter-field distance `d` as a
parameter), so the data-dependent "where is the head now" is absorbed by the reset, and the data-determined "where is the
rule" is a static offset the machine is built for.  No counter-driven walk is needed.

## What is proved (clean axioms, no `sorry`)

* **`navigateToSource3 s found cont mid d'`** — `resetToHome3 s found cont mid ++ moveRightN3 mid d'`.
* **`navigateToSource3_run`** (PROVED) — with the home marker at `home`, no marker in `(home, home+dq]`, and bounds: `∃ N,
  reachIn N (s, home+dq, tp) (mid+d', home+1+d', tp)` — from any config-window position `home+dq` the head ends at
  `home+1+d' = c+d'` (the rule source), the tape identical.

## Honest scope

This is the **transfer-side navigation** to a data-dependent rule position.  It does **not** yet perform the field copy
there (`copyFieldLeft3`, entry 415), nor assemble the full state transfer / `EmitsEncodedStep3`.  Building those fragment
by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Navigate

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ResetHome (resetToHome3 resetToHome3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveN (moveRightN3 moveRightN3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- **The transfer-side navigation.**  Reset to the config home, then move right a fixed `d'` to the rule source. -/
def navigateToSource3 (s found cont mid d' : ℕ) : TMachine3 :=
  resetToHome3 s found cont mid ++ moveRightN3 mid d'

/-- **The transfer-side navigation run (PROVED).**  From any config-window position `home+dq`, end at `home+1+d'` (the rule
source `c+d'`), tape identical. -/
theorem navigateToSource3_run (s found cont mid d' home dq : ℕ) (tp : List Sym3)
    (hmark : tp.getD home Sym3.O = Sym3.M) (hno : ∀ k, 0 < k → k ≤ dq → tp.getD (home + k) Sym3.O ≠ Sym3.M)
    (hbnd1 : home + dq < tp.length) (hbnd2 : home + 1 + d' ≤ tp.length) :
    ∃ N, reachIn (toNTM3 (navigateToSource3 s found cont mid d')) N (s, home + dq, tp) (mid + d', home + 1 + d', tp) := by
  obtain ⟨N1, h1⟩ := resetToHome3_run s found cont mid home dq tp hmark hno hbnd1
  have h2 := moveRightN3_run mid d' (home + 1) tp hbnd2
  exact ⟨N1 + d', reachIn_seq3 (resetToHome3 s found cont mid) (moveRightN3 mid d') N1 d' _ _ _ h1 h2⟩

/-!
**The transfer-side navigation, proved.**  `navigateToSource3` moves the head from anywhere in the config window to a
data-dependent rule position, distance-independently (via the home marker) plus a fixed offset — the addressing the
transfer side needs.  Next: copy the rule field there into the configuration (`copyFieldLeft3`, entry 415), and assemble
the state transfer toward `EmitsEncodedStep3` — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Navigate

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Navigate.navigateToSource3_run
