import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3SkipMark
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3NavigateCache

/-!
# Entry 433 — universal-TM-table build: the cache-refresh navigation `cacheRefreshNav3` (proved)

To refresh the symbol cache after a head move, the head — sitting inside the tape, to the right of the simulated head
marker — must navigate back to the cache cell.  That crosses the head marker, which (single-symbol `M`) would otherwise
trap a leftward seek (entry 432).  This brick composes the resolution: **skip the head marker** (`skipMarkLeft3`, entry
432) to land just left of it, then **navigate to the cache** (`navigateToCache3`, entry 431) — which now seeks past to the
home marker and scans the state field to the cache cell.

## What is proved (clean axioms, no `sorry`)

* **`cacheRefreshNav3 s found1 cont1 s2 found2 cont2 mid sOut`** — `skipMarkLeft3 s found1 cont1 s2 ++ navigateToCache3 s2
  found2 cont2 mid sOut`.
* **`cacheRefreshNav3_run`** (PROVED) — with the head marker at `hm` (and the head at `hm+e` right of it), the home marker
  at `home < hm`, the state field (`a` ones then `O` at `home+1`), no other markers, and bounds: `∃ N, reachIn N (s, hm+e,
  tp) (sOut, home+1+a+1, tp)` — from inside the tape the head ends on the cache cell `c+a+1`, the tape identical.

## Honest scope

This is the **cache-refresh navigation** (from inside the tape to the cache, past the head marker).  It does **not** yet
*write* the read symbol into the cache, nor assemble the full step / `EmitsEncodedStep3`.  Building those fragment by
fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CacheNav

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SkipMark (skipMarkLeft3 skipMarkLeft3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3NavigateCache (navigateToCache3 navigateToCache3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- **The cache-refresh navigation.**  Skip the head marker, then navigate to the cache cell. -/
def cacheRefreshNav3 (s found1 cont1 s2 found2 cont2 mid sOut : ℕ) : TMachine3 :=
  skipMarkLeft3 s found1 cont1 s2 ++ navigateToCache3 s2 found2 cont2 mid sOut

/-- **The cache-refresh navigation run (PROVED).**  From inside the tape (right of the head marker), end on the cache cell
`c+a+1`, tape identical. -/
theorem cacheRefreshNav3_run (s found1 cont1 s2 found2 cont2 mid sOut hm e home a : ℕ) (tp : List Sym3)
    (hhome_lt : home + 1 ≤ hm) (hmarkHead : tp.getD hm Sym3.O = Sym3.M)
    (hnoHead : ∀ k, 0 < k → k ≤ e → tp.getD (hm + k) Sym3.O ≠ Sym3.M)
    (hmarkHome : tp.getD home Sym3.O = Sym3.M)
    (hnoHome : ∀ k, 0 < k → k ≤ hm - 1 - home → tp.getD (home + k) Sym3.O ≠ Sym3.M)
    (hbndSkip : hm + e < tp.length) (hco : ∀ i, i < a → tp.getD (home + 1 + i) Sym3.O = Sym3.I)
    (hcsep : tp.getD (home + 1 + a) Sym3.O = Sym3.O) (hbnd2 : home + 1 + a < tp.length) :
    ∃ N, reachIn (toNTM3 (cacheRefreshNav3 s found1 cont1 s2 found2 cont2 mid sOut)) N (s, hm + e, tp)
      (sOut, home + 1 + a + 1, tp) := by
  obtain ⟨N1, h1⟩ := skipMarkLeft3_run s found1 cont1 s2 hm e tp hmarkHead hnoHead hbndSkip
  obtain ⟨N2, h2⟩ := navigateToCache3_run s2 found2 cont2 mid sOut home (hm - 1 - home) a tp hmarkHome hnoHome
    (by omega) hco hcsep hbnd2
  rw [show home + (hm - 1 - home) = hm - 1 from by omega] at h2
  exact ⟨N1 + N2, reachIn_seq3 (skipMarkLeft3 s found1 cont1 s2) (navigateToCache3 s2 found2 cont2 mid sOut)
    N1 N2 _ _ _ h1 h2⟩

/-!
**The cache-refresh navigation, proved.**  `cacheRefreshNav3` carries the head from inside the tape, past the head marker,
to the cache cell — the navigation half of the cache refresh.  Next: write the read symbol into the cache (completing the
refresh), then assemble the full simulated step toward `EmitsEncodedStep3` — fragment by verified fragment, not faked.  Not
a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CacheNav

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CacheNav.cacheRefreshNav3_run
