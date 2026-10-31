import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3CacheRefresh
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3ResetHome

/-!
# Entry 444 — universal-TM-table build: the home-to-home cache refresh `cacheRefreshHome3` (proved)

The cache refresh (`cacheRefresh3`, entry 435) starts at the config home but ends on the cache cell.  This brick makes it
**home-to-home**: append a reset (`resetToHome3`, entry 408) from the cache cell back to the config home.  The result tape
is a single `writeAt3` (the cache cell set to the current symbol), and the reset's no-marker window covers only the state
field, separator, and cache — all marker-free — so the head marker further right is untouched.

## What is proved (clean axioms, no `sorry`)

* **`cacheRefreshHome3 <cache-refresh states> rf rc rout`** — `cacheRefresh3 … ++ resetToHome3 sFin rf rc rout`.
* **`cacheRefreshHome3_run`** (PROVED) — starting at the config home `home+1`, with the head marker at `home+1+d`, the
  state field at `home+1`, and bounds: `∃ N, reachIn N (s, home+1, tp) (rout, home+1, writeAt3 tp (home+1+a+1) (tp.getD
  (home+1+d+1) O))` — the cache cell is set to the current symbol and the head returns to the config home.

## Honest scope

This is the **home-to-home cache refresh** — one apply phase with a canonical endpoint.  It does **not** assemble
`EmitsEncodedStep3`.  Building the rest fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CacheRefreshHome

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 writeAt3 writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CacheRefresh (cacheRefresh3 cacheRefresh3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ResetHome (resetToHome3 resetToHome3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- In-bounds write preserves length. -/
private theorem writeAt3_length_eq (tp : List Sym3) (q : ℕ) (w : Sym3) (hq : q < tp.length) :
    (writeAt3 tp q w).length = tp.length := by
  simp only [writeAt3, List.length_set, List.length_append, List.length_replicate]; omega

/-- **The home-to-home cache refresh.**  Refresh the cache, then reset to the config home. -/
def cacheRefreshHome3 (s sO sI oF1 oC1 oS2 oF2 oC2 oMid oMidW iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin rf rc rout : ℕ) :
    TMachine3 :=
  cacheRefresh3 s sO sI oF1 oC1 oS2 oF2 oC2 oMid oMidW iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin ++ resetToHome3 sFin rf rc rout

/-- **The home-to-home cache-refresh run (PROVED).**  Sets the cache to the current symbol and returns to the config home. -/
theorem cacheRefreshHome3_run
    (s sO sI oF1 oC1 oS2 oF2 oC2 oMid oMidW iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin rf rc rout d home a : ℕ)
    (tp : List Sym3)
    (hmark : tp.getD ((home + 1) + d) Sym3.O = Sym3.M)
    (hclear : ∀ k, k < d → tp.getD ((home + 1) + k) Sym3.O ≠ Sym3.M)
    (hbound : (home + 1) + d < tp.length) (hbound2 : (home + 1) + d + 1 < tp.length)
    (hcur : tp.getD ((home + 1) + d + 1) Sym3.O = Sym3.O ∨ tp.getD ((home + 1) + d + 1) Sym3.O = Sym3.I)
    (hmarkHome : tp.getD home Sym3.O = Sym3.M)
    (hnoHome : ∀ k, 0 < k → k ≤ (home + 1) + d - 1 - home → tp.getD (home + k) Sym3.O ≠ Sym3.M)
    (hco : ∀ i, i < a → tp.getD (home + 1 + i) Sym3.O = Sym3.I) (hcsep : tp.getD (home + 1 + a) Sym3.O = Sym3.O)
    (hbnd2 : home + 1 + a < tp.length) (hcache : home + 1 + a + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (cacheRefreshHome3 s sO sI oF1 oC1 oS2 oF2 oC2 oMid oMidW iF1 iC1 iS2 iF2 iC2 iMid iMidW
        sFin rf rc rout)) N (s, home + 1, tp)
      (rout, home + 1, writeAt3 tp (home + 1 + a + 1) (tp.getD ((home + 1) + d + 1) Sym3.O)) := by
  obtain ⟨N1, h1⟩ := cacheRefresh3_run s sO sI oF1 oC1 oS2 oF2 oC2 oMid oMidW iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin
    d (home + 1) home a tp hmark hclear hbound hbound2 hcur (by omega) hmarkHome hnoHome hco hcsep hbnd2
  set RT := writeAt3 tp (home + 1 + a + 1) (tp.getD ((home + 1) + d + 1) Sym3.O) with hRT
  have hlen : RT.length = tp.length := by rw [hRT]; exact writeAt3_length_eq tp _ _ hcache
  have hmark_r : RT.getD home Sym3.O = Sym3.M := by rw [hRT, writeAt3_getD, if_neg (by omega)]; exact hmarkHome
  have hno_r : ∀ k, 0 < k → k ≤ a + 2 → RT.getD (home + k) Sym3.O ≠ Sym3.M := by
    intro k hk0 hk
    rcases Nat.lt_or_ge (home + k) (home + 1 + a + 1) with hlt | hge
    · rw [hRT, writeAt3_getD, if_neg (by omega)]
      rcases Nat.lt_or_ge (home + k) (home + 1 + a) with hlt2 | hge2
      · have : home + k = home + 1 + (k - 1) := by omega
        rw [this, hco (k - 1) (by omega)]; decide
      · have : home + k = home + 1 + a := by omega
        rw [this, hcsep]; decide
    · have hkc : home + k = home + 1 + a + 1 := by omega
      rw [hkc, hRT, writeAt3_getD, if_pos rfl]
      rcases hcur with hb | hb <;> rw [hb] <;> decide
  obtain ⟨N2, h2⟩ := resetToHome3_run sFin rf rc rout home (a + 2) RT hmark_r hno_r (by rw [hlen]; omega)
  rw [show home + (a + 2) = home + 1 + a + 1 from by omega] at h2
  exact ⟨N1 + N2, reachIn_seq3 (cacheRefresh3 s sO sI oF1 oC1 oS2 oF2 oC2 oMid oMidW iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin)
    (resetToHome3 sFin rf rc rout) N1 N2 _ _ _ h1 h2⟩

/-!
**The home-to-home cache refresh, proved.**  `cacheRefreshHome3` refreshes the cache and returns to the config home — one
apply phase with a canonical endpoint, ready to chain.  Next: the home-to-home state update, the master apply sequence, and
the matcher↔lookup correspondence toward `EmitsEncodedStep3` — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CacheRefreshHome

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CacheRefreshHome.cacheRefreshHome3_run
