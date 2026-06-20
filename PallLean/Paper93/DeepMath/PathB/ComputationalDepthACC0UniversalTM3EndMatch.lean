import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3CursTape
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3MarkAdvance
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3SeekR
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3WriteAlg

/-!
# Entry 481 — generic scan loop: the comparison match verdict `endMatch` (proved)

The positive verdict of the two-cursor comparison (per the fixed-`U` finding, entry 467): when both unary fields end at the
same step (`a = b`), the comparison confirms a **match** and restores the tape.  From the canonical tape with both cursors at
their last field cells (`cursTape tp cp g d`, both separators `O` ahead), the machine: advances the config cursor onto its
separator (`markAdvance3` end-case, entry 472, removing the cursor), seeks right to the record cursor (`seekMarkRight`, 388),
and advances it onto its separator (end-case, removing it) — landing in the match state with the tape back to base `tp`.

`endMatch s mid1 cont1 e1 m2 sc2 mid3 matchSt recEnd := markAdvance3 s mid1 cont1 e1 ++ seekMarkRight e1 m2 sc2 ++
markAdvance3 m2 mid3 recEnd matchSt`.

## What is proved (clean axioms, no `sorry`)

* **`endMatch …`** — the match-verdict machine.
* **`endMatch_run`** (PROVED) — base fields' last cells `I` (`cp+d`, `cp+g+d`), both separators `O` (`cp+d+1`, `cp+g+d+1`),
  inter-cursor gap marker-free, in bounds: `∃ N, reachIn N (s, cp+d, cursTape tp cp g d) (matchSt, cp+g+d+1, tp)` — match
  confirmed, the tape restored to base `tp`.

## Honest scope

This is the **match verdict** (both fields end together).  It does **not** yet build the mismatch branches, the symbol
compare, the match-or-advance branch into the scan loop, the generic apply, nor a fixed `U` / `EmitsEncodedStepEx3`.
Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EndMatch

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 writeAt3 toNTM3 writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MarkAdvance (markAdvance3 markAdvance3_run_end)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SeekR (seekMarkRight seekMarkRight_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteAlg (writeAt3_eq_set)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CursTape
  (cursTape cursTape_length cursTape_cursorL cursTape_cursorR cursTape_other)

private theorem wlen (t : List Sym3) (p : ℕ) (w : Sym3) (hp : p < t.length) :
    (writeAt3 t p w).length = t.length := by
  rw [writeAt3_eq_set t p w hp, List.length_set]

/-- **The match-verdict machine.** -/
def endMatch (s mid1 cont1 e1 m2 sc2 mid3 matchSt recEnd : ℕ) : TMachine3 :=
  markAdvance3 s mid1 cont1 e1 ++ seekMarkRight e1 m2 sc2 ++ markAdvance3 m2 mid3 recEnd matchSt

/-- **The comparison match verdict (PROVED).** -/
theorem endMatch_run (s mid1 cont1 e1 m2 sc2 mid3 matchSt recEnd : ℕ) (tp : List Sym3) (cp g d : ℕ) (hg : 2 ≤ g)
    (hCfield : tp.getD (cp + d) Sym3.O = Sym3.I) (hCsep : tp.getD (cp + d + 1) Sym3.O = Sym3.O)
    (hRfield : tp.getD (cp + g + d) Sym3.O = Sym3.I) (hRsep : tp.getD (cp + g + d + 1) Sym3.O = Sym3.O)
    (hgap : ∀ j, cp + d < j → j < cp + g + d → tp.getD j Sym3.O ≠ Sym3.M) (hbound : cp + g + d + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (endMatch s mid1 cont1 e1 m2 sc2 mid3 matchSt recEnd)) N
      (s, cp + d, cursTape tp cp g d) (matchSt, cp + g + d + 1, tp) := by
  have hclen : (cursTape tp cp g d).length = tp.length := cursTape_length tp cp g d (by omega) (by omega)
  -- T1 : config cursor removed, head on the config separator
  set T1 := writeAt3 (writeAt3 (cursTape tp cp g d) (cp + d) Sym3.I) (cp + d + 1) Sym3.O with hT1def
  have hT1other : ∀ x, x ≠ cp + d → x ≠ cp + d + 1 → T1.getD x Sym3.O = (cursTape tp cp g d).getD x Sym3.O := by
    intro x h1 h2; rw [hT1def, writeAt3_getD, if_neg h2, writeAt3_getD, if_neg h1]
  have hT1len : T1.length = tp.length := by
    rw [hT1def, wlen _ _ _ (by rw [wlen _ _ _ (by rw [hclen]; omega)]; rw [hclen]; omega),
      wlen _ _ _ (by rw [hclen]; omega), hclen]
  have hT1sep : T1.getD (cp + d + 1) Sym3.O = Sym3.O := by rw [hT1def, writeAt3_getD, if_pos rfl]
  -- step A: advance config cursor onto its separator (end-case)
  have hstepA := markAdvance3_run_end s mid1 cont1 e1 (cp + d) (cursTape tp cp g d)
    (cursTape_cursorL tp cp g d (by omega))
    (by rw [cursTape_other tp cp g d _ (by omega) (by omega)]; exact hCsep)
  -- step B: seek right to the record cursor (still M on T1)
  have hMrec : T1.getD (cp + g + d) Sym3.O = Sym3.M := by
    rw [hT1other _ (by omega) (by omega)]; exact cursTape_cursorR tp cp g d
  obtain ⟨Nseek, hstepB⟩ := seekMarkRight_run e1 m2 sc2 T1 (g - 1) (cp + d + 1)
    (by rw [show cp + d + 1 + (g - 1) = cp + g + d from by omega]; exact hMrec)
    (fun k hk => by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0; rw [show cp + d + 1 + 0 = cp + d + 1 from rfl, hT1sep]; decide
      · rw [hT1other _ (by omega) (by omega), cursTape_other tp cp g d _ (by omega) (by omega)]
        exact hgap (cp + d + 1 + k) (by omega) (by omega))
    (by rw [hT1len, show cp + d + 1 + (g - 1) = cp + g + d from by omega]; omega)
  rw [show cp + d + 1 + (g - 1) = cp + g + d from by omega] at hstepB
  -- step C: advance record cursor onto its separator (end-case)
  have hRsep1 : T1.getD (cp + g + d + 1) Sym3.O = Sym3.O := by
    rw [hT1other _ (by omega) (by omega), cursTape_other tp cp g d _ (by omega) (by omega)]; exact hRsep
  have hstepC := markAdvance3_run_end m2 mid3 recEnd matchSt (cp + g + d) T1 hMrec hRsep1
  -- the final tape is the base tp (both cursors removed)
  have key : writeAt3 (writeAt3 T1 (cp + g + d) Sym3.I) (cp + g + d + 1) Sym3.O = tp := by
    have hT1len' := hT1len
    apply List.ext_getElem
    · rw [wlen _ _ _ (by rw [wlen _ _ _ (by rw [hT1len]; omega)]; rw [hT1len]; omega),
        wlen _ _ _ (by rw [hT1len]; omega), hT1len]
    · intro n h1 h2
      rw [← List.getD_eq_getElem (d := Sym3.O) _ h1, ← List.getD_eq_getElem (d := Sym3.O) _ h2]
      simp only [hT1def, cursTape, writeAt3_getD]
      split_ifs <;> simp_all
  -- chain A ++ B ++ C
  have hAB := reachIn_seq3 (markAdvance3 s mid1 cont1 e1) (seekMarkRight e1 m2 sc2) 2 Nseek _ _ _ hstepA hstepB
  refine ⟨2 + Nseek + 2, ?_⟩
  have hABC := reachIn_seq3 (markAdvance3 s mid1 cont1 e1 ++ seekMarkRight e1 m2 sc2)
    (markAdvance3 m2 mid3 recEnd matchSt) (2 + Nseek) 2 _ _ _ hAB hstepC
  rw [key] at hABC
  exact hABC

/-!
**The comparison match verdict, proved.**  `endMatch` confirms `a = b` and restores the tape — the positive conclusion of
the two-cursor comparison.  Next: the mismatch branches and the symbol compare, then wiring the comparison into the scan
loop's match-or-advance — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EndMatch

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EndMatch.endMatch_run
