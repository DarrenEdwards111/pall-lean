import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3ApplyWriteMove
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3CacheRefreshHome

/-!
# Entry 450 — universal-TM-table build: the tape-side master apply `applyTapeRight3` (proved)

The coherent tape-side master apply (rightward): write the rule's symbol, advance the head right, then refresh the symbol
cache — three home-to-home phases in one machine.  It chains the write-then-move core (`applyWriteMoveRight3`, entry 449)
with the home-to-home cache refresh (`cacheRefreshHome3`, entry 444), which reads the new current cell `p+2` (after the
move) and writes it into the cache.

The cache refresh's hypotheses are discharged on the post-move tape `T3 = writeAt3 (writeAt3 (writeAt3 tp (p+1) w) p w)
(p+1) M` via three `getD` facts (cell `p+1` is `M`, cell `p` is `w`, all others unchanged), under the layout relation
`home+1+a+1 < p` (the state field and cache lie strictly left of the head marker, so the write/move leaves them intact).

## What is proved (clean axioms, no `sorry`)

* **`applyTapeRight3 <write states> mid <move states> mid2 <cache states>`** — `applyWriteMoveRight3 … mid2 w ++
  cacheRefreshHome3 mid2 …`.
* **`applyTapeRight3_run`** (PROVED) — with the home/head markers, a clean window `(home, p)`, the state field at `home+1`
  (length `a`), the write symbol `w` and the next cell `p+2` bits, `home+1+a+1 < p`, and `p+2 < tp.length`: `∃ N, reachIn N
  (a0, home+1, tp) (rout, home+1, writeAt3 (writeAt3 (writeAt3 (writeAt3 tp (p+1) w) p w) (p+1) M) (home+1+a+1) (tp.getD
  (p+2) O))` — the symbol is written and carried, the head advances, and the cache is updated to the new current symbol;
  head returns to the config home.

## Honest scope

This is the **coherent tape-side master apply** (write + move + cache refresh, rightward).  It does **not** add the
state-update phase (which needs a tape-shift for the variable-length unary state field), nor connect to the matched rule /
`EmitsEncodedStep3`.  Building the rest fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ApplyTape

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 writeAt3 writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ApplyWriteMove (applyWriteMoveRight3 applyWriteMoveRight3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CacheRefreshHome (cacheRefreshHome3 cacheRefreshHome3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- In-bounds write preserves length. -/
private theorem writeAt3_length_eq (tp : List Sym3) (q : ℕ) (v : Sym3) (hq : q < tp.length) :
    (writeAt3 tp q v).length = tp.length := by
  simp only [writeAt3, List.length_set, List.length_append, List.length_replicate]; omega

/-- **The tape-side master apply.**  Write the symbol, advance the head right, refresh the cache. -/
def applyTapeRight3 (a aF aC bb c cF cC dd dF dC mid sFound sCont s1 f1 c1 s2 f2 c2 mid2
    sO sI oF1 oC1 oS2 oF2 oC2 oMid oMidW iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin rf rc rout : ℕ) (w : Sym3) : TMachine3 :=
  applyWriteMoveRight3 a aF aC bb c cF cC dd dF dC mid sFound sCont s1 f1 c1 s2 f2 c2 mid2 w ++
    cacheRefreshHome3 mid2 sO sI oF1 oC1 oS2 oF2 oC2 oMid oMidW iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin rf rc rout

/-- **The tape-side master-apply run (PROVED).**  Writes `w`, advances the head, and refreshes the cache to the new current
symbol; head returns to the config home. -/
theorem applyTapeRight3_run (a aF aC bb c cF cC dd dF dC mid sFound sCont s1 f1 c1 s2 f2 c2 mid2
    sO sI oF1 oC1 oS2 oF2 oC2 oMid oMidW iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin rf rc rout home p a' : ℕ)
    (w : Sym3) (tp : List Sym3)
    (hhp : home < p) (hcacheLt : home + 1 + a' + 1 < p)
    (hmarkHome : tp.getD home Sym3.O = Sym3.M) (hmarkHead : tp.getD p Sym3.O = Sym3.M)
    (hclean : ∀ j, home < j → j < p → tp.getD j Sym3.O ≠ Sym3.M) (hw : w = Sym3.O ∨ w = Sym3.I)
    (hco : ∀ i, i < a' → tp.getD (home + 1 + i) Sym3.O = Sym3.I) (hcsep : tp.getD (home + 1 + a') Sym3.O = Sym3.O)
    (hc2 : tp.getD (p + 2) Sym3.O = Sym3.O ∨ tp.getD (p + 2) Sym3.O = Sym3.I) (hbnd : p + 2 < tp.length) :
    ∃ N, reachIn (toNTM3 (applyTapeRight3 a aF aC bb c cF cC dd dF dC mid sFound sCont s1 f1 c1 s2 f2 c2 mid2
        sO sI oF1 oC1 oS2 oF2 oC2 oMid oMidW iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin rf rc rout w)) N (a, home + 1, tp)
      (rout, home + 1, writeAt3 (writeAt3 (writeAt3 (writeAt3 tp (p + 1) w) p w) (p + 1) Sym3.M) (home + 1 + a' + 1)
        (tp.getD (p + 2) Sym3.O)) := by
  obtain ⟨N1, h1⟩ := applyWriteMoveRight3_run a aF aC bb c cF cC dd dF dC mid sFound sCont s1 f1 c1 s2 f2 c2 mid2
    home p w tp hhp hmarkHome hmarkHead hclean hw (by omega)
  set T3 := writeAt3 (writeAt3 (writeAt3 tp (p + 1) w) p w) (p + 1) Sym3.M with hT3
  have hLa : (writeAt3 tp (p + 1) w).length = tp.length := writeAt3_length_eq tp (p + 1) w (by omega)
  have hLb : (writeAt3 (writeAt3 tp (p + 1) w) p w).length = tp.length := by
    rw [writeAt3_length_eq _ p w (by rw [hLa]; omega), hLa]
  have hT3len : T3.length = tp.length := by rw [hT3, writeAt3_length_eq _ (p + 1) Sym3.M (by rw [hLb]; omega), hLb]
  have hT3_p1 : T3.getD (p + 1) Sym3.O = Sym3.M := by rw [hT3, writeAt3_getD, if_pos rfl]
  have hT3_p : T3.getD p Sym3.O = w := by rw [hT3, writeAt3_getD, if_neg (by omega), writeAt3_getD, if_pos rfl]
  have hT3_o : ∀ j, j ≠ p → j ≠ p + 1 → T3.getD j Sym3.O = tp.getD j Sym3.O := by
    intro j hjp hjp1
    rw [hT3, writeAt3_getD, if_neg hjp1, writeAt3_getD, if_neg hjp, writeAt3_getD, if_neg hjp1]
  -- cache refresh on T3 with d = p - home, a = a'
  have hcr_mark : T3.getD ((home + 1) + (p - home)) Sym3.O = Sym3.M := by
    rw [show (home + 1) + (p - home) = p + 1 from by omega]; exact hT3_p1
  have hcr_clear : ∀ k, k < p - home → T3.getD ((home + 1) + k) Sym3.O ≠ Sym3.M := by
    intro k hk
    rcases Nat.lt_or_ge ((home + 1) + k) p with hlt | hge
    · rw [hT3_o ((home + 1) + k) (by omega) (by omega)]; exact hclean ((home + 1) + k) (by omega) hlt
    · rw [show (home + 1) + k = p from by omega, hT3_p]; rcases hw with hb | hb <;> rw [hb] <;> decide
  have hcr_noHome : ∀ k, 0 < k → k ≤ (home + 1) + (p - home) - 1 - home → T3.getD (home + k) Sym3.O ≠ Sym3.M := by
    intro k hk0 hk
    rcases Nat.lt_or_ge (home + k) p with hlt | hge
    · rw [hT3_o (home + k) (by omega) (by omega)]; exact hclean (home + k) (by omega) hlt
    · rw [show home + k = p from by omega, hT3_p]; rcases hw with hb | hb <;> rw [hb] <;> decide
  have hcr_cur : T3.getD ((home + 1) + (p - home) + 1) Sym3.O = Sym3.O ∨
      T3.getD ((home + 1) + (p - home) + 1) Sym3.O = Sym3.I := by
    rw [show (home + 1) + (p - home) + 1 = p + 2 from by omega, hT3_o (p + 2) (by omega) (by omega)]; exact hc2
  have hcr_markHome : T3.getD home Sym3.O = Sym3.M := by rw [hT3_o home (by omega) (by omega)]; exact hmarkHome
  have hcr_co : ∀ i, i < a' → T3.getD (home + 1 + i) Sym3.O = Sym3.I := by
    intro i hi; rw [hT3_o (home + 1 + i) (by omega) (by omega)]; exact hco i hi
  have hcr_csep : T3.getD (home + 1 + a') Sym3.O = Sym3.O := by
    rw [hT3_o (home + 1 + a') (by omega) (by omega)]; exact hcsep
  obtain ⟨N2, h2⟩ := cacheRefreshHome3_run mid2 sO sI oF1 oC1 oS2 oF2 oC2 oMid oMidW iF1 iC1 iS2 iF2 iC2 iMid iMidW
    sFin rf rc rout (p - home) home a' T3 hcr_mark hcr_clear (by rw [hT3len, show (home + 1) + (p - home) = p + 1 from by omega]; omega)
    (by rw [hT3len, show (home + 1) + (p - home) + 1 = p + 2 from by omega]; omega) hcr_cur hcr_markHome hcr_noHome
    hcr_co hcr_csep (by rw [hT3len]; omega) (by rw [hT3len]; omega)
  rw [show (home + 1) + (p - home) + 1 = p + 2 from by omega, hT3_o (p + 2) (by omega) (by omega)] at h2
  exact ⟨N1 + N2, reachIn_seq3 (applyWriteMoveRight3 a aF aC bb c cF cC dd dF dC mid sFound sCont s1 f1 c1 s2 f2 c2 mid2 w)
    (cacheRefreshHome3 mid2 sO sI oF1 oC1 oS2 oF2 oC2 oMid oMidW iF1 iC1 iS2 iF2 iC2 iMid iMidW sFin rf rc rout)
    N1 N2 _ _ _ h1 h2⟩

/-!
**The tape-side master apply, proved.**  `applyTapeRight3` writes the rule's symbol, advances the head, and refreshes the
cache — three home-to-home phases composed, the cache-refresh hypotheses discharged on the post-move tape.  Next: the
left/dispatch variant, the state-update tape-shift, and the matcher↔lookup correspondence toward `EmitsEncodedStep3` —
fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ApplyTape

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ApplyTape.applyTapeRight3_run
