import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3CursTape
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3MarkAdvance
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Cross
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Seek
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3EndMismatch
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3WriteAlg

/-!
# Entry 483 — generic scan loop: the symmetric mismatch verdict `endMismatchRC` (proved)

The remaining negative verdict of the two-cursor comparison (per the fixed-`U` finding, entry 467): the **config field
continues but the record field ends** (`a > b`).  Here the config cursor advances (cont-case, staying placed), the record
cursor is removed (end-case), so the leftover cursor is the *config* one — we seek **left** back to it and erase, restoring
the tape and landing in the fail (advance-to-next-record) state.

`endMismatchRC … := markAdvance3 (config) ++ crossRight ++ markAdvance3 (record) ++ seekMarkLeft ++ eraseMark3`.

## What is proved (clean axioms, no `sorry`)

* **`endMismatchRC …`** — the config-continues-record-ends mismatch machine.
* **`endMismatchRC_run`** (PROVED) — config last cell `I`, config *continues* (`I` ahead), record last cell `I`, record
  separator `O`, gap marker-free, in bounds: `∃ N, reachIn N (s, cp+d, cursTape tp cp g d) (failSt, cp+d+1, tp)` — mismatch
  confirmed, the tape restored to base `tp`.

## Honest scope

This is the **third (final) length-verdict** of the comparison.  It does **not** yet build the symbol compare, the
match-or-advance wiring, the generic apply, nor a fixed `U` / `EmitsEncodedStepEx3`.  Building those fragment by fragment is
the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EndMismatchRC

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 writeAt3 toNTM3 writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MarkAdvance (markAdvance3 markAdvance3_run_cont markAdvance3_run_end)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Cross (crossRight crossRight_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Seek (seekMarkLeft seekMarkLeft_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EndMismatch (eraseMark3 eraseMark3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteAlg (writeAt3_eq_set)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CursTape
  (cursTape cursTape_length cursTape_cursorL cursTape_cursorR cursTape_other)

private theorem wlen (t : List Sym3) (p : ℕ) (w : Sym3) (hp : p < t.length) :
    (writeAt3 t p w).length = t.length := by
  rw [writeAt3_eq_set t p w hp, List.length_set]

/-- **The config-continues-record-ends mismatch machine.** -/
def endMismatchRC (s a1 a2 a3 b1 b2 b3 c1 c2 c3 d1 d2 failSt : ℕ) : TMachine3 :=
  markAdvance3 s a1 a2 a3 ++ crossRight a2 b1 b2 b3 ++ markAdvance3 b2 c1 c2 c3 ++ seekMarkLeft c3 d1 d2
    ++ eraseMark3 d1 failSt

/-- **The config-continues-record-ends mismatch verdict (PROVED).** -/
theorem endMismatchRC_run (s a1 a2 a3 b1 b2 b3 c1 c2 c3 d1 d2 failSt : ℕ) (tp : List Sym3) (cp g d : ℕ)
    (hg : 2 ≤ g) (hCfield : tp.getD (cp + d) Sym3.O = Sym3.I) (hCcont : tp.getD (cp + d + 1) Sym3.O = Sym3.I)
    (hRfield : tp.getD (cp + g + d) Sym3.O = Sym3.I) (hRsep : tp.getD (cp + g + d + 1) Sym3.O = Sym3.O)
    (hgap : ∀ j, cp + d < j → j < cp + g + d → tp.getD j Sym3.O ≠ Sym3.M) (hbound : cp + g + d + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (endMismatchRC s a1 a2 a3 b1 b2 b3 c1 c2 c3 d1 d2 failSt)) N
      (s, cp + d, cursTape tp cp g d) (failSt, cp + d + 1, tp) := by
  have hclen : (cursTape tp cp g d).length = tp.length := cursTape_length tp cp g d (by omega) (by omega)
  -- T1 : config cursor advanced to cp+d+1 (cont)
  set T1 := writeAt3 (writeAt3 (cursTape tp cp g d) (cp + d) Sym3.I) (cp + d + 1) Sym3.M with hT1def
  have hT1other : ∀ x, x ≠ cp + d → x ≠ cp + d + 1 → T1.getD x Sym3.O = (cursTape tp cp g d).getD x Sym3.O := by
    intro x h1 h2; rw [hT1def, writeAt3_getD, if_neg h2, writeAt3_getD, if_neg h1]
  have hT1len : T1.length = tp.length := by
    rw [hT1def, wlen _ _ _ (by rw [wlen _ _ _ (by rw [hclen]; omega)]; rw [hclen]; omega),
      wlen _ _ _ (by rw [hclen]; omega), hclen]
  have hT1cfg : T1.getD (cp + d + 1) Sym3.O = Sym3.M := by rw [hT1def, writeAt3_getD, if_pos rfl]
  have hMrec : T1.getD (cp + g + d) Sym3.O = Sym3.M := by
    rw [hT1other _ (by omega) (by omega)]; exact cursTape_cursorR tp cp g d
  have hRsep1 : T1.getD (cp + g + d + 1) Sym3.O = Sym3.O := by
    rw [hT1other _ (by omega) (by omega), cursTape_other tp cp g d _ (by omega) (by omega)]; exact hRsep
  -- step A: config cursor advances (cont)
  have hstepA := markAdvance3_run_cont s a1 a2 a3 (cp + d) (cursTape tp cp g d)
    (cursTape_cursorL tp cp g d (by omega))
    (by rw [cursTape_other tp cp g d _ (by omega) (by omega)]; exact hCcont)
  -- step B: cross right to the record cursor
  obtain ⟨Ncr, hstepB⟩ := crossRight_run a2 b1 b2 b3 (cp + d + 1) (g - 2) T1 (by rw [hT1len]; omega)
    (by rw [show cp + d + 1 + 1 + (g - 2) = cp + g + d from by omega]; exact hMrec)
    (fun k hk => by
      rw [hT1other _ (by omega) (by omega), cursTape_other tp cp g d _ (by omega) (by omega)]
      exact hgap (cp + d + 1 + 1 + k) (by omega) (by omega))
    (by rw [hT1len, show cp + d + 1 + 1 + (g - 2) = cp + g + d from by omega]; omega)
  rw [show cp + d + 1 + 1 + (g - 2) = cp + g + d from by omega] at hstepB
  -- step C: record cursor onto its separator (end)
  have hstepC := markAdvance3_run_end b2 c1 c2 c3 (cp + g + d) T1 hMrec hRsep1
  set T2 := writeAt3 (writeAt3 T1 (cp + g + d) Sym3.I) (cp + g + d + 1) Sym3.O with hT2def
  have hT2other : ∀ x, x ≠ cp + g + d → x ≠ cp + g + d + 1 → T2.getD x Sym3.O = T1.getD x Sym3.O := by
    intro x h1 h2; rw [hT2def, writeAt3_getD, if_neg h2, writeAt3_getD, if_neg h1]
  have hT2len : T2.length = tp.length := by
    rw [hT2def, wlen _ _ _ (by rw [wlen _ _ _ (by rw [hT1len]; omega)]; rw [hT1len]; omega),
      wlen _ _ _ (by rw [hT1len]; omega), hT1len]
  have hT2cfg : T2.getD (cp + d + 1) Sym3.O = Sym3.M := by
    rw [hT2other _ (by omega) (by omega)]; exact hT1cfg
  -- step D: seek left back to the config cursor
  obtain ⟨Nsl, hstepD⟩ := seekMarkLeft_run c3 d1 d2 (cp + d + 1) T2 hT2cfg g
    (fun k hk0 hkg => by
      rcases Nat.lt_trichotomy (cp + d + 1 + k) (cp + g + d) with hlt | heq | hgt
      · rw [hT2other _ (by omega) (by omega), hT1other _ (by omega) (by omega),
          cursTape_other tp cp g d _ (by omega) (by omega)]
        exact hgap (cp + d + 1 + k) (by omega) (by omega)
      · rw [heq, hT2def, writeAt3_getD, if_neg (by omega), writeAt3_getD, if_pos rfl]; decide
      · rw [show cp + d + 1 + k = cp + g + d + 1 from by omega, hT2def, writeAt3_getD, if_pos rfl]; decide)
    (by rw [hT2len]; omega)
  rw [show cp + d + 1 + g = cp + g + d + 1 from by omega] at hstepD
  -- step E: erase the leftover config cursor
  have hstepE := eraseMark3_run d1 failSt (cp + d + 1) T2 hT2cfg
  have key : writeAt3 T2 (cp + d + 1) Sym3.I = tp := by
    apply List.ext_getElem
    · rw [wlen _ _ _ (by rw [hT2len]; omega), hT2len]
    · intro n h1 h2
      rw [← List.getD_eq_getElem (d := Sym3.O) _ h1, ← List.getD_eq_getElem (d := Sym3.O) _ h2]
      simp only [hT2def, hT1def, cursTape, writeAt3_getD]
      split_ifs <;> simp_all
  -- chain A ++ B ++ C ++ D ++ E
  have hAB := reachIn_seq3 (markAdvance3 s a1 a2 a3) (crossRight a2 b1 b2 b3) 2 Ncr _ _ _ hstepA hstepB
  have hABC := reachIn_seq3 (markAdvance3 s a1 a2 a3 ++ crossRight a2 b1 b2 b3) (markAdvance3 b2 c1 c2 c3)
    (2 + Ncr) 2 _ _ _ hAB hstepC
  have hABCD := reachIn_seq3 (markAdvance3 s a1 a2 a3 ++ crossRight a2 b1 b2 b3 ++ markAdvance3 b2 c1 c2 c3)
    (seekMarkLeft c3 d1 d2) (2 + Ncr + 2) Nsl _ _ _ hABC hstepD
  refine ⟨2 + Ncr + 2 + Nsl + 1, ?_⟩
  have hABCDE := reachIn_seq3 (markAdvance3 s a1 a2 a3 ++ crossRight a2 b1 b2 b3 ++ markAdvance3 b2 c1 c2 c3
    ++ seekMarkLeft c3 d1 d2) (eraseMark3 d1 failSt) (2 + Ncr + 2 + Nsl) 1 _ _ _ hABCD hstepE
  rw [key] at hABCDE
  exact hABCDE

/-!
**The symmetric mismatch verdict, proved.**  `endMismatchRC` confirms `a > b` (config continues, record ends), erases the
leftover config cursor, and restores the tape — completing the three length-verdicts of the comparison.  Next: the symbol
compare, then wiring match/mismatch into the scan loop — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EndMismatchRC

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EndMismatchRC.endMismatchRC_run
