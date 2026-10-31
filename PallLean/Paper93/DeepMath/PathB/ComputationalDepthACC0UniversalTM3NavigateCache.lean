import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3ResetHome
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Scan

/-!
# Entry 431 — universal-TM-table build: navigation to the symbol cache `navigateToCache3` (proved)

Unifying the matcher and the apply phases requires reconciling the matcher's fixed-offset *symbol cache* (the cell right
after the state field, read at `c+a+1`) with the marker head representation (the apply moves a marker `M`).  After a head
move the cache must be refreshed, which first means *reaching* the cache cell from wherever the head is.

This brick is that navigation: from anywhere in the config window, return to the config home `c` (`resetToHome3`, entry
408, distance-independently via the home marker), then scan past the variable-length state field (`scanNatFrom3`, entry
395) to land on the cache cell `c+a+1` — the cell right after the state field's `O` separator.  The state field length `a`
is *data*, but `scanNatFrom3` walks it to its separator without needing it statically.

## What is proved (clean axioms, no `sorry`)

* **`navigateToCache3 s found cont mid sOut`** — `resetToHome3 s found cont mid ++ scanNatFrom3 mid sOut`.
* **`navigateToCache3_run`** (PROVED) — with the home marker at `home`, no marker in `(home, home+dq]`, the state field
  (`a` ones then `O` at `home+1`), and bounds: `∃ N, reachIn N (s, home+dq, tp) (sOut, home+1+a+1, tp)` — from any
  config-window position the head ends on the cache cell `home+1+a+1 = c+a+1`, the tape identical.

## Honest scope

This is the **navigation to the symbol cache** — the addressing that reconciles the matcher's fixed-offset cache with the
marker head.  It does **not** yet refresh the cache (read the marker symbol and write it here), nor assemble the full step
/ `EmitsEncodedStep3`.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3NavigateCache

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ResetHome (resetToHome3 resetToHome3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Scan (scanNatFrom3 scanNatFrom3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- **Navigation to the symbol cache.**  Reset to the config home, then scan past the state field to the cache cell. -/
def navigateToCache3 (s found cont mid sOut : ℕ) : TMachine3 :=
  resetToHome3 s found cont mid ++ scanNatFrom3 mid sOut

/-- **The navigation-to-cache run (PROVED).**  From any config-window position, end on the cache cell `c+a+1`, tape
identical. -/
theorem navigateToCache3_run (s found cont mid sOut home dq a : ℕ) (tp : List Sym3)
    (hmark : tp.getD home Sym3.O = Sym3.M) (hno : ∀ k, 0 < k → k ≤ dq → tp.getD (home + k) Sym3.O ≠ Sym3.M)
    (hbnd1 : home + dq < tp.length) (hco : ∀ i, i < a → tp.getD (home + 1 + i) Sym3.O = Sym3.I)
    (hcsep : tp.getD (home + 1 + a) Sym3.O = Sym3.O) (hbnd2 : home + 1 + a < tp.length) :
    ∃ N, reachIn (toNTM3 (navigateToCache3 s found cont mid sOut)) N (s, home + dq, tp)
      (sOut, home + 1 + a + 1, tp) := by
  obtain ⟨N1, h1⟩ := resetToHome3_run s found cont mid home dq tp hmark hno hbnd1
  have h2 := scanNatFrom3_run_eq mid sOut a (home + 1) tp hco hcsep hbnd2
  exact ⟨N1 + (a + 1), reachIn_seq3 (resetToHome3 s found cont mid) (scanNatFrom3 mid sOut) N1 (a + 1) _ _ _ h1 h2⟩

/-!
**The navigation to the symbol cache, proved.**  `navigateToCache3` positions the head on the cache cell from anywhere in
the config window — reaching the fixed-offset cache by scanning the data-length state field.  Next: refresh the cache (read
the marker symbol and write it here), then assemble the full simulated step toward `EmitsEncodedStep3` — fragment by
verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3NavigateCache

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3NavigateCache.navigateToCache3_run
