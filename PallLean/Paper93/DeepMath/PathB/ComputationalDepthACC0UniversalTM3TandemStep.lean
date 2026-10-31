import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3AdvanceCross
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3AdvanceCrossL

/-!
# Entry 476 — generic scan loop: one full tandem iteration `tandemStep3` (proved)

The loop body of the two-cursor unary comparison (per the fixed-`U` finding, entry 467): one full tandem iteration fuses
`advanceCrossRight` (474, config cursor → record cursor) and `advanceCrossLeft` (475, record cursor → config cursor).  Both
cursors step right by one, the head returning to the (left) config cursor — the constant-gap tandem walk that compares two
unary fields cell-by-cell.

`tandemStep3 … := advanceCrossRight … crFound … ++ advanceCrossLeft crFound …`.

## What is proved (clean axioms, no `sorry`)

* **`tandemStep3 …`** — the full tandem-iteration machine.
* **`tandemStep3_run`** (PROVED) — config cursor at `cp` (`M`) with its field continuing (`cp+1=I`), record cursor at
  `cp+g` (`M`, `g ≥ 2`) with its field continuing (`cp+g+1=I`), the inter-cursor gap marker-free: `∃ N, reachIn N (s, cp,
  tp) (lcrFound, cp+1, tp₂)` where `tp₂` moves *both* cursors right by one — the head back on the (new) config cursor.

## Honest scope

This is **one tandem iteration** (both fields continuing).  It does **not** yet build the iterated loop (induction on
`min(a,b)`), the four-way end-branch, the symbol compare, the match-or-advance branch, the generic apply, nor a fixed `U` /
`EmitsEncodedStepEx3`.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TandemStep

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 writeAt3 toNTM3 writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3AdvanceCross (advanceCrossRight advanceCrossRight_cont_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3AdvanceCrossL (advanceCrossLeft advanceCrossLeft_cont_run)

/-- **One full tandem iteration.**  Advance the config cursor and cross to the record cursor, then advance the record
cursor and cross back to the config cursor. -/
def tandemStep3 (s smid sCont sEnd crMid crFound crCont lmid lCont lEnd lcrMid lcrFound lcrCont : ℕ) : TMachine3 :=
  advanceCrossRight s smid sCont sEnd crMid crFound crCont
    ++ advanceCrossLeft crFound lmid lCont lEnd lcrMid lcrFound lcrCont

/-- **One tandem iteration advances both cursors (PROVED).** -/
theorem tandemStep3_run (s smid sCont sEnd crMid crFound crCont lmid lCont lEnd lcrMid lcrFound lcrCont : ℕ)
    (tp : List Sym3) (cp g : ℕ) (hg : 2 ≤ g)
    (hM : tp.getD cp Sym3.O = Sym3.M) (hI : tp.getD (cp + 1) Sym3.O = Sym3.I)
    (hMr : tp.getD (cp + g) Sym3.O = Sym3.M) (hIr : tp.getD (cp + g + 1) Sym3.O = Sym3.I)
    (hgap : ∀ j, cp < j → j < cp + g → tp.getD j Sym3.O ≠ Sym3.M) (hbound : cp + g + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (tandemStep3 s smid sCont sEnd crMid crFound crCont lmid lCont lEnd lcrMid lcrFound lcrCont)) N
      (s, cp, tp)
      (lcrFound, cp + 1, writeAt3 (writeAt3 (writeAt3 (writeAt3 tp cp Sym3.I) (cp + 1) Sym3.M) (cp + g) Sym3.I)
        (cp + g + 1) Sym3.M) := by
  -- right half (474): config cursor cp → cp+1, head to the record cursor cp+g
  obtain ⟨N1, hR⟩ := advanceCrossRight_cont_run s smid sCont sEnd crMid crFound crCont cp (g - 2) tp hM hI
    (by rw [show cp + 2 + (g - 2) = cp + g from by omega]; exact hMr)
    (fun k hk => hgap (cp + 2 + k) (by omega) (by omega))
    (by rw [show cp + 2 + (g - 2) = cp + g from by omega]; omega)
  rw [show cp + 2 + (g - 2) = cp + g from by omega] at hR
  set tp1 := writeAt3 (writeAt3 tp cp Sym3.I) (cp + 1) Sym3.M with htp1def
  have htp1 : ∀ x, x ≠ cp → x ≠ cp + 1 → tp1.getD x Sym3.O = tp.getD x Sym3.O := by
    intro x h1 h2; rw [htp1def, writeAt3_getD, if_neg h2, writeAt3_getD, if_neg h1]
  -- left half (475) on tp1: record cursor cp+g → cp+g+1, head back to config cursor cp+1
  obtain ⟨N2, hL⟩ := advanceCrossLeft_cont_run crFound lmid lCont lEnd lcrMid lcrFound lcrCont (cp + 1) (g - 1) tp1
    (by omega)
    (by rw [show cp + 1 + (g - 1) = cp + g from by omega, htp1 _ (by omega) (by omega)]; exact hMr)
    (by rw [show cp + 1 + (g - 1) + 1 = cp + g + 1 from by omega, htp1 _ (by omega) (by omega)]; exact hIr)
    (by rw [htp1def, writeAt3_getD, if_pos rfl])  -- partner config cursor: tp1[cp+1] = M
    (fun k hk0 hkd => by rw [htp1 _ (by omega) (by omega)]; exact hgap (cp + 1 + k) (by omega) (by omega))
    (by rw [show cp + 1 + (g - 1) + 1 = cp + g + 1 from by omega]
        rw [htp1def]; rw [show (writeAt3 (writeAt3 tp cp Sym3.I) (cp + 1) Sym3.M).length = tp.length from by
          rw [writeAt3, List.length_set, List.length_append, List.length_replicate,
            writeAt3, List.length_set, List.length_append, List.length_replicate]; omega]; omega)
  rw [show cp + 1 + (g - 1) = cp + g from by omega] at hL
  refine ⟨N1 + N2, ?_⟩
  have := reachIn_seq3 (advanceCrossRight s smid sCont sEnd crMid crFound crCont)
    (advanceCrossLeft crFound lmid lCont lEnd lcrMid lcrFound lcrCont) N1 N2 _ _ _ hR hL
  rw [htp1def] at this
  exact this

/-!
**One tandem iteration, proved.**  `tandemStep3` advances both cursors of the comparison by one, the head returning to the
config cursor — the loop body.  Next: iterate it (induction on `min(a,b)`), add the four-way end-branch and the symbol
compare — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TandemStep

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TandemStep.tandemStep3_run
