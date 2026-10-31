import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3MarkAdvance
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Cross

/-!
# Entry 474 — generic scan loop: the half-tandem move `advanceCrossRight` (proved)

A two-cursor comparison alternates two operations: *advance a cursor* (`markAdvance3`, entry 472) and *cross to the partner
cursor* (`crossRight`/`crossLeft`, entry 473).  This brick fuses them into the **half-tandem move**: advance the (left)
cursor one cell within its field, then cross right to the partner cursor — the reusable iteration half of the comparison
loop (per the fixed-`U` finding, entry 467).

`advanceCrossRight s smid sCont sEnd crMid crFound crCont := markAdvance3 s smid sCont sEnd ++ crossRight sCont crMid
crFound crCont`.

## What is proved (clean axioms, no `sorry`)

* **`advanceCrossRight …`** — the half-tandem machine.
* **`advanceCrossRight_cont_run`** (PROVED) — cursor at `cp` (`tp[cp]=M`), its field continuing (`tp[cp+1]=I`), the partner
  marker at `cp+2+d` with the cells `cp+2 … cp+1+d` marker-free: `∃ N, reachIn N (s, cp, tp) (crFound, cp+2+d, writeAt3
  (writeAt3 tp cp I) (cp+1) M)` — the cursor moved `cp → cp+1` (old cell restored), the head now on the partner.

## Honest scope

This is the **half-tandem move** of the comparison.  It does **not** yet build the full tandem loop, the four-way
end-branch, the symbol compare, the match-or-advance branch, the generic apply, nor a fixed `U` / `EmitsEncodedStepEx3`.
Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3AdvanceCross

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 writeAt3 toNTM3 writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MarkAdvance (markAdvance3 markAdvance3_run_cont)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Cross (crossRight crossRight_run)

/-- **The half-tandem move.**  Advance the cursor one cell within its field, then cross right to the partner cursor. -/
def advanceCrossRight (s smid sCont sEnd crMid crFound crCont : ℕ) : TMachine3 :=
  markAdvance3 s smid sCont sEnd ++ crossRight sCont crMid crFound crCont

/-- **The half-tandem move advances the cursor and reaches the partner (PROVED).** -/
theorem advanceCrossRight_cont_run (s smid sCont sEnd crMid crFound crCont cp d : ℕ) (tp : List Sym3)
    (hM : tp.getD cp Sym3.O = Sym3.M) (hI : tp.getD (cp + 1) Sym3.O = Sym3.I)
    (hPartner : tp.getD (cp + 2 + d) Sym3.O = Sym3.M)
    (hgap : ∀ k, k < d → tp.getD (cp + 2 + k) Sym3.O ≠ Sym3.M) (hbound : cp + 2 + d < tp.length) :
    ∃ N, reachIn (toNTM3 (advanceCrossRight s smid sCont sEnd crMid crFound crCont)) N
      (s, cp, tp) (crFound, cp + 2 + d, writeAt3 (writeAt3 tp cp Sym3.I) (cp + 1) Sym3.M) := by
  -- the tape after the cursor advances: untouched away from cp and cp+1
  have htp1 : ∀ x, x ≠ cp → x ≠ cp + 1 →
      (writeAt3 (writeAt3 tp cp Sym3.I) (cp + 1) Sym3.M).getD x Sym3.O = tp.getD x Sym3.O := by
    intro x h1 h2; rw [writeAt3_getD, if_neg h2, writeAt3_getD, if_neg h1]
  have hwlen : ∀ (t : List Sym3) (p : ℕ) (w : Sym3), p < t.length → (writeAt3 t p w).length = t.length := by
    intro t p w hp; rw [writeAt3, List.length_set, List.length_append, List.length_replicate]; omega
  have hadv := markAdvance3_run_cont s smid sCont sEnd cp tp hM hI
  set tp1 := writeAt3 (writeAt3 tp cp Sym3.I) (cp + 1) Sym3.M with htp1def
  have hlen0 : (writeAt3 tp cp Sym3.I).length = tp.length := hwlen tp cp Sym3.I (by omega)
  have hlen1 : tp1.length = tp.length := by
    rw [htp1def, hwlen _ (cp + 1) Sym3.M (by rw [hlen0]; omega), hlen0]
  have hMcross : tp1.getD ((cp + 1) + 1 + d) Sym3.O = Sym3.M := by
    rw [show (cp + 1) + 1 + d = cp + 2 + d from by omega, htp1def, htp1 _ (by omega) (by omega)]; exact hPartner
  have hclear : ∀ k, k < d → tp1.getD ((cp + 1) + 1 + k) Sym3.O ≠ Sym3.M := by
    intro k hk
    rw [show (cp + 1) + 1 + k = cp + 2 + k from by omega, htp1def, htp1 _ (by omega) (by omega)]
    exact hgap k hk
  obtain ⟨N2, hcr⟩ := crossRight_run sCont crMid crFound crCont (cp + 1) d tp1 (by rw [hlen1]; omega) hMcross hclear
    (by rw [hlen1]; omega)
  rw [show (cp + 1) + 1 + d = cp + 2 + d from by omega] at hcr
  exact ⟨2 + N2, reachIn_seq3 (markAdvance3 s smid sCont sEnd) (crossRight sCont crMid crFound crCont) 2 N2 _ _ _
    hadv hcr⟩

/-!
**The half-tandem move, proved.**  `advanceCrossRight` advances a cursor and crosses to the partner — the reusable half of
the comparison loop iteration.  Next: the leftward mirror, the full tandem loop with the four-way end-branch, then the
symbol compare and match-or-advance — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3AdvanceCross

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3AdvanceCross.advanceCrossRight_cont_run
