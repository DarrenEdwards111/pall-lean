import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3CacheNav
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Unmark

/-!
# Entry 434 — universal-TM-table build: navigate-and-write the cache `navigateAndWriteCache3` (proved)

This completes the *write* end of the cache refresh.  After the cache-refresh navigation (`cacheRefreshNav3`, entry 433)
carries the head from inside the tape to the cache cell, this brick writes a given symbol `w` there (`unmark3`, the
write-and-stay primitive), giving a verified "set the symbol cache to `w`" operation that starts from inside the tape.

Composed with the O/I branch of `readHeadSym3` (entry 420), which supplies `w` as the symbol read at the marker, this is
the full cache refresh.  Here we prove the symbol-parameterised core.

## What is proved (clean axioms, no `sorry`)

* **`navigateAndWriteCache3 s found1 cont1 s2 found2 cont2 mid sMidW sOut2 w`** — `cacheRefreshNav3 s found1 cont1 s2
  found2 cont2 mid sMidW ++ unmark3 sMidW sOut2 w`.
* **`navigateAndWriteCache3_run`** (PROVED) — under the `cacheRefreshNav3` hypotheses: `∃ N, reachIn N (s, hm+e, tp)
  (sOut2, home+1+a+1, writeAt3 tp (home+1+a+1) w)` — from inside the tape, the head ends on the cache cell and the cache
  cell now holds `w`.

## Honest scope

This is **navigate-and-write the cache** for a *given* symbol `w`.  It does **not** yet supply `w` from the marker symbol
(the O/I branch of `readHeadSym3`), nor assemble the full step / `EmitsEncodedStep3`.  Building those fragment by fragment
is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CacheWrite

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 writeAt3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CacheNav (cacheRefreshNav3 cacheRefreshNav3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Unmark (unmark3 unmark3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- **Navigate from inside the tape to the cache, then write `w` there.** -/
def navigateAndWriteCache3 (s found1 cont1 s2 found2 cont2 mid sMidW sOut2 : ℕ) (w : Sym3) : TMachine3 :=
  cacheRefreshNav3 s found1 cont1 s2 found2 cont2 mid sMidW ++ unmark3 sMidW sOut2 w

/-- **The navigate-and-write-cache run (PROVED).**  From inside the tape, end on the cache cell with the cache holding
`w`. -/
theorem navigateAndWriteCache3_run (s found1 cont1 s2 found2 cont2 mid sMidW sOut2 hm e home a : ℕ) (w : Sym3)
    (tp : List Sym3) (hhome_lt : home + 1 ≤ hm) (hmarkHead : tp.getD hm Sym3.O = Sym3.M)
    (hnoHead : ∀ k, 0 < k → k ≤ e → tp.getD (hm + k) Sym3.O ≠ Sym3.M)
    (hmarkHome : tp.getD home Sym3.O = Sym3.M)
    (hnoHome : ∀ k, 0 < k → k ≤ hm - 1 - home → tp.getD (home + k) Sym3.O ≠ Sym3.M)
    (hbndSkip : hm + e < tp.length) (hco : ∀ i, i < a → tp.getD (home + 1 + i) Sym3.O = Sym3.I)
    (hcsep : tp.getD (home + 1 + a) Sym3.O = Sym3.O) (hbnd2 : home + 1 + a < tp.length) :
    ∃ N, reachIn (toNTM3 (navigateAndWriteCache3 s found1 cont1 s2 found2 cont2 mid sMidW sOut2 w)) N (s, hm + e, tp)
      (sOut2, home + 1 + a + 1, writeAt3 tp (home + 1 + a + 1) w) := by
  obtain ⟨N1, h1⟩ := cacheRefreshNav3_run s found1 cont1 s2 found2 cont2 mid sMidW hm e home a tp hhome_lt
    hmarkHead hnoHead hmarkHome hnoHome hbndSkip hco hcsep hbnd2
  have h2 := unmark3_run sMidW sOut2 w (home + 1 + a + 1) tp
  exact ⟨N1 + 1, reachIn_seq3 (cacheRefreshNav3 s found1 cont1 s2 found2 cont2 mid sMidW) (unmark3 sMidW sOut2 w)
    N1 1 _ _ _ h1 h2⟩

/-!
**Navigate-and-write the cache, proved.**  `navigateAndWriteCache3` sets the symbol cache to a given `w` after navigating
from inside the tape — the write end of the cache refresh.  Next: supply `w` from the marker symbol (the O/I branch of
`readHeadSym3`), then assemble the full simulated step toward `EmitsEncodedStep3` — fragment by verified fragment, not
faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CacheWrite

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CacheWrite.navigateAndWriteCache3_run
