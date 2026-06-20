import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3CursTape
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3MarkAdvance
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3SeekR
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3WriteAlg

/-!
# Entry 482 — generic scan loop: a comparison mismatch verdict `endMismatchCR` (proved)

A negative verdict of the two-cursor comparison (per the fixed-`U` finding, entry 467): the **config field ends but the
record field continues** (`a < b`).  From the canonical tape with both cursors at their step-`d` cells, the machine: advances
the config cursor onto its separator (`markAdvance3` end-case, entry 472, removing it), seeks to the record cursor
(`seekMarkRight`, 388), advances the record cursor — which *continues* (cont-case, leaving a cursor) — and finally **erases**
that cursor (`eraseMark3`), restoring the tape and landing in the fail (advance-to-next-record) state.

`endMismatchCR … := markAdvance3 (config) ++ seekMarkRight ++ markAdvance3 (record) ++ eraseMark3`.

## What is proved (clean axioms, no `sorry`)

* **`eraseMark3 s fail`** — erase a cursor: at `M`, write `I`, go to `fail`.  **`eraseMark3_run`** (PROVED).
* **`endMismatchCR …`** — the config-ends-record-continues mismatch machine.
* **`endMismatchCR_run`** (PROVED) — config last cell `I`, config separator `O`, record last cell `I`, record *continues*
  (`I` ahead), gap marker-free, in bounds: `∃ N, reachIn N (s, cp+d, cursTape tp cp g d) (failSt, cp+g+d+1, tp)` — mismatch
  confirmed, the tape restored to base `tp`.

## Honest scope

This is **one mismatch verdict** (config ends, record continues).  It does **not** yet build the symmetric mismatch, the
symbol compare, the match-or-advance wiring, the generic apply, nor a fixed `U` / `EmitsEncodedStepEx3`.  Building those
fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EndMismatch

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (Move moveHead)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym
  (Sym3 TMachine3 concreteStep3 readSym3 writeAt3 applyTrans3 toNTM3 writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MarkAdvance (markAdvance3 markAdvance3_run_cont markAdvance3_run_end)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SeekR (seekMarkRight seekMarkRight_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteAlg (writeAt3_eq_set)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CursTape
  (cursTape cursTape_length cursTape_cursorL cursTape_cursorR cursTape_other)

private theorem wlen (t : List Sym3) (p : ℕ) (w : Sym3) (hp : p < t.length) :
    (writeAt3 t p w).length = t.length := by
  rw [writeAt3_eq_set t p w hp, List.length_set]

/-- **Erase a cursor.**  At the marker `M`, write `I` and go to `fail`. -/
def eraseMark3 (s fail : ℕ) : TMachine3 := [((s, Sym3.M), (fail, Sym3.I, (2 : Move)))]

/-- **The cursor erase (PROVED).** -/
theorem eraseMark3_run (s fail j : ℕ) (tp : List Sym3) (hM : tp.getD j Sym3.O = Sym3.M) :
    reachIn (toNTM3 (eraseMark3 s fail)) 1 (s, j, tp) (fail, j, writeAt3 tp j Sym3.I) := by
  refine ⟨(fail, j, writeAt3 tp j Sym3.I), ?_, rfl⟩
  have hMr : readSym3 (s, j, tp) = Sym3.M := hM
  exact ⟨((s, Sym3.M), (fail, Sym3.I, (2 : Move))), by simp [eraseMark3], by simp [hMr],
    by simp [applyTrans3, moveHead]⟩

/-- **The config-ends-record-continues mismatch machine.** -/
def endMismatchCR (s mid1 cont1 e1 m2 sc2 mid3 endM erEntry failSt : ℕ) : TMachine3 :=
  markAdvance3 s mid1 cont1 e1 ++ seekMarkRight e1 m2 sc2 ++ markAdvance3 m2 mid3 erEntry endM
    ++ eraseMark3 erEntry failSt

/-- **The config-ends-record-continues mismatch verdict (PROVED).** -/
theorem endMismatchCR_run (s mid1 cont1 e1 m2 sc2 mid3 endM erEntry failSt : ℕ) (tp : List Sym3) (cp g d : ℕ)
    (hg : 2 ≤ g) (hCfield : tp.getD (cp + d) Sym3.O = Sym3.I) (hCsep : tp.getD (cp + d + 1) Sym3.O = Sym3.O)
    (hRfield : tp.getD (cp + g + d) Sym3.O = Sym3.I) (hRcont : tp.getD (cp + g + d + 1) Sym3.O = Sym3.I)
    (hgap : ∀ j, cp + d < j → j < cp + g + d → tp.getD j Sym3.O ≠ Sym3.M) (hbound : cp + g + d + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (endMismatchCR s mid1 cont1 e1 m2 sc2 mid3 endM erEntry failSt)) N
      (s, cp + d, cursTape tp cp g d) (failSt, cp + g + d + 1, tp) := by
  have hclen : (cursTape tp cp g d).length = tp.length := cursTape_length tp cp g d (by omega) (by omega)
  set T1 := writeAt3 (writeAt3 (cursTape tp cp g d) (cp + d) Sym3.I) (cp + d + 1) Sym3.O with hT1def
  have hT1other : ∀ x, x ≠ cp + d → x ≠ cp + d + 1 → T1.getD x Sym3.O = (cursTape tp cp g d).getD x Sym3.O := by
    intro x h1 h2; rw [hT1def, writeAt3_getD, if_neg h2, writeAt3_getD, if_neg h1]
  have hT1len : T1.length = tp.length := by
    rw [hT1def, wlen _ _ _ (by rw [wlen _ _ _ (by rw [hclen]; omega)]; rw [hclen]; omega),
      wlen _ _ _ (by rw [hclen]; omega), hclen]
  have hT1sep : T1.getD (cp + d + 1) Sym3.O = Sym3.O := by rw [hT1def, writeAt3_getD, if_pos rfl]
  have hMrec : T1.getD (cp + g + d) Sym3.O = Sym3.M := by
    rw [hT1other _ (by omega) (by omega)]; exact cursTape_cursorR tp cp g d
  have hRcont1 : T1.getD (cp + g + d + 1) Sym3.O = Sym3.I := by
    rw [hT1other _ (by omega) (by omega), cursTape_other tp cp g d _ (by omega) (by omega)]; exact hRcont
  -- step A: config cursor onto separator (end)
  have hstepA := markAdvance3_run_end s mid1 cont1 e1 (cp + d) (cursTape tp cp g d)
    (cursTape_cursorL tp cp g d (by omega))
    (by rw [cursTape_other tp cp g d _ (by omega) (by omega)]; exact hCsep)
  -- step B: seek to record cursor
  obtain ⟨Nseek, hstepB⟩ := seekMarkRight_run e1 m2 sc2 T1 (g - 1) (cp + d + 1)
    (by rw [show cp + d + 1 + (g - 1) = cp + g + d from by omega]; exact hMrec)
    (fun k hk => by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0; rw [show cp + d + 1 + 0 = cp + d + 1 from rfl, hT1sep]; decide
      · rw [hT1other _ (by omega) (by omega), cursTape_other tp cp g d _ (by omega) (by omega)]
        exact hgap (cp + d + 1 + k) (by omega) (by omega))
    (by rw [hT1len, show cp + d + 1 + (g - 1) = cp + g + d from by omega]; omega)
  rw [show cp + d + 1 + (g - 1) = cp + g + d from by omega] at hstepB
  -- step C: record cursor advances (cont)
  have hstepC := markAdvance3_run_cont m2 mid3 erEntry endM (cp + g + d) T1 hMrec hRcont1
  set T2 := writeAt3 (writeAt3 T1 (cp + g + d) Sym3.I) (cp + g + d + 1) Sym3.M with hT2def
  have hMcur : T2.getD (cp + g + d + 1) Sym3.O = Sym3.M := by rw [hT2def, writeAt3_getD, if_pos rfl]
  have hT2len : T2.length = tp.length := by
    rw [hT2def, wlen _ _ _ (by rw [wlen _ _ _ (by rw [hT1len]; omega)]; rw [hT1len]; omega),
      wlen _ _ _ (by rw [hT1len]; omega), hT1len]
  -- step D: erase the leftover cursor
  have hstepD := eraseMark3_run erEntry failSt (cp + g + d + 1) T2 hMcur
  -- the final tape is the base tp
  have key : writeAt3 T2 (cp + g + d + 1) Sym3.I = tp := by
    apply List.ext_getElem
    · rw [wlen _ _ _ (by rw [hT2len]; omega), hT2len]
    · intro n h1 h2
      rw [← List.getD_eq_getElem (d := Sym3.O) _ h1, ← List.getD_eq_getElem (d := Sym3.O) _ h2]
      simp only [hT2def, hT1def, cursTape, writeAt3_getD]
      split_ifs <;> simp_all
  -- chain A ++ B ++ C ++ D
  have hAB := reachIn_seq3 (markAdvance3 s mid1 cont1 e1) (seekMarkRight e1 m2 sc2) 2 Nseek _ _ _ hstepA hstepB
  have hABC := reachIn_seq3 (markAdvance3 s mid1 cont1 e1 ++ seekMarkRight e1 m2 sc2)
    (markAdvance3 m2 mid3 erEntry endM) (2 + Nseek) 2 _ _ _ hAB hstepC
  refine ⟨2 + Nseek + 2 + 1, ?_⟩
  have hABCD := reachIn_seq3 (markAdvance3 s mid1 cont1 e1 ++ seekMarkRight e1 m2 sc2 ++ markAdvance3 m2 mid3 erEntry endM)
    (eraseMark3 erEntry failSt) (2 + Nseek + 2) 1 _ _ _ hABC hstepD
  rw [key] at hABCD
  exact hABCD

/-!
**A comparison mismatch verdict, proved.**  `endMismatchCR` confirms `a < b` (config ends, record continues), erases the
leftover cursor, and restores the tape.  Next: the symmetric mismatch (config continues, record ends), the symbol compare,
then wiring match/mismatch into the scan loop — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EndMismatch

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EndMismatch.endMismatchCR_run
