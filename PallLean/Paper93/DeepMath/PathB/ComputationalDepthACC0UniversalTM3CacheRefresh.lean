import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3ReadHead
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3CacheWrite

/-!
# Entry 435 — universal-TM-table build: the full cache refresh `cacheRefresh3` (proved)

This completes the symbol-cache refresh that unifies the matcher (which reads a fixed-offset cache) with the marker head
representation.  It reads the current symbol at the head marker (`readHeadSym3`, entry 420), which routes the control state
to `sO`/`sI` by the symbol, and then — on each lineage — navigates back to the cache and writes that symbol there
(`navigateAndWriteCache3`, entry 434).  The net effect is the rep-unification operation **cache := current symbol**.

It is a two-branch assembly: the machine appends *both* lineage sub-machines after `readHeadSym3`; the relevant one runs
and the other is never entered (lifted into the union by `reachIn_append_left3`/`reachIn_append_right3`).

## What is proved (clean axioms, no `sorry`)

* **`cacheRefresh3`** — `readHeadSym3 s sO sI ++ (navigateAndWriteCache3 sO … O ++ navigateAndWriteCache3 sI … I)`.
* **`cacheRefresh3_run`** (PROVED) — with the head marker at `h+d` (no marker in `[h, h+d)`), the current cell a bit, the
  home marker at `home < h+d`, the state field at `home+1`, and bounds: `∃ N, reachIn N (s, h, tp) (sFin, home+1+a+1,
  writeAt3 tp (home+1+a+1) (tp.getD (h+d+1) O))` — the cache cell `c+a+1` is set to the current symbol, both lineages
  converging to `sFin`.

## Honest scope

This is the **full cache refresh** (`cache := current symbol`).  It does **not** yet rework the matcher to call it, nor
sequence read → lookup → apply → refresh into one step / `EmitsEncodedStep3`.  Building those fragment by fragment is the
genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CacheRefresh

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 writeAt3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ReadHead (readHeadSym3 readHeadSym3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CacheWrite (navigateAndWriteCache3 navigateAndWriteCache3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3 reachIn_append_left3 reachIn_append_right3)

/-- **The full cache refresh.**  Read the symbol at the head marker, branch, navigate to the cache and write it. -/
def cacheRefresh3 (s sO sI oF1 oC1 oS2 oF2 oC2 oMid oMidW iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin : ℕ) : TMachine3 :=
  readHeadSym3 s sO sI ++
    (navigateAndWriteCache3 sO oF1 oC1 oS2 oF2 oC2 oMid oMidW sFin Sym3.O ++
     navigateAndWriteCache3 sI iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin Sym3.I)

/-- **The full cache-refresh run (PROVED).**  Sets the cache cell to the current symbol, both lineages converging to
`sFin`. -/
theorem cacheRefresh3_run (s sO sI oF1 oC1 oS2 oF2 oC2 oMid oMidW iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin d h home a : ℕ)
    (tp : List Sym3) (hmark : tp.getD (h + d) Sym3.O = Sym3.M)
    (hclear : ∀ k, k < d → tp.getD (h + k) Sym3.O ≠ Sym3.M) (hbound : h + d < tp.length) (hbound2 : h + d + 1 < tp.length)
    (hcur : tp.getD (h + d + 1) Sym3.O = Sym3.O ∨ tp.getD (h + d + 1) Sym3.O = Sym3.I)
    (hhome_lt : home + 1 ≤ h + d) (hmarkHome : tp.getD home Sym3.O = Sym3.M)
    (hnoHome : ∀ k, 0 < k → k ≤ h + d - 1 - home → tp.getD (home + k) Sym3.O ≠ Sym3.M)
    (hco : ∀ i, i < a → tp.getD (home + 1 + i) Sym3.O = Sym3.I) (hcsep : tp.getD (home + 1 + a) Sym3.O = Sym3.O)
    (hbnd2 : home + 1 + a < tp.length) :
    ∃ N, reachIn (toNTM3 (cacheRefresh3 s sO sI oF1 oC1 oS2 oF2 oC2 oMid oMidW iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin)) N
      (s, h, tp) (sFin, home + 1 + a + 1, writeAt3 tp (home + 1 + a + 1) (tp.getD (h + d + 1) Sym3.O)) := by
  obtain ⟨N1, hread⟩ := readHeadSym3_run s sO sI d h tp hmark hclear hbound hbound2 hcur
  have hnoHead : ∀ k, 0 < k → k ≤ 1 → tp.getD (h + d + k) Sym3.O ≠ Sym3.M := by
    intro k hk0 hk1
    have hk : k = 1 := by omega
    subst hk
    rcases hcur with hb | hb <;> rw [hb] <;> decide
  rcases hcur with hb | hb
  · rw [if_pos hb] at hread
    obtain ⟨N2, hwrite⟩ := navigateAndWriteCache3_run sO oF1 oC1 oS2 oF2 oC2 oMid oMidW sFin (h + d) 1 home a Sym3.O tp
      hhome_lt hmark hnoHead hmarkHome hnoHome hbound2 hco hcsep hbnd2
    rw [hb]
    exact ⟨N1 + N2, reachIn_seq3 (readHeadSym3 s sO sI)
      (navigateAndWriteCache3 sO oF1 oC1 oS2 oF2 oC2 oMid oMidW sFin Sym3.O ++
       navigateAndWriteCache3 sI iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin Sym3.I)
      N1 N2 _ _ _ hread
      (reachIn_append_left3 (navigateAndWriteCache3 sO oF1 oC1 oS2 oF2 oC2 oMid oMidW sFin Sym3.O)
        (navigateAndWriteCache3 sI iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin Sym3.I) N2 _ _ hwrite)⟩
  · rw [if_neg (by rw [hb]; decide)] at hread
    obtain ⟨N2, hwrite⟩ := navigateAndWriteCache3_run sI iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin (h + d) 1 home a Sym3.I tp
      hhome_lt hmark hnoHead hmarkHome hnoHome hbound2 hco hcsep hbnd2
    rw [hb]
    exact ⟨N1 + N2, reachIn_seq3 (readHeadSym3 s sO sI)
      (navigateAndWriteCache3 sO oF1 oC1 oS2 oF2 oC2 oMid oMidW sFin Sym3.O ++
       navigateAndWriteCache3 sI iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin Sym3.I)
      N1 N2 _ _ _ hread
      (reachIn_append_right3 (navigateAndWriteCache3 sO oF1 oC1 oS2 oF2 oC2 oMid oMidW sFin Sym3.O)
        (navigateAndWriteCache3 sI iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin Sym3.I) N2 _ _ hwrite)⟩

/-!
**The full cache refresh, proved.**  `cacheRefresh3` sets the symbol cache to the current symbol read at the head marker —
the rep-unification operation, both lineages converging.  Next: rework the matcher to use the cache (now coherently
maintained), and sequence read → lookup → apply → refresh into one simulated step toward `EmitsEncodedStep3` — fragment by
verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CacheRefresh

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CacheRefresh.cacheRefresh3_run
