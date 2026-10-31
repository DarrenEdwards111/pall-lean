import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3MarkAdvance
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Cross

/-!
# Entry 475 — generic scan loop: the half-tandem move `advanceCrossLeft` (proved)

The leftward mirror of `advanceCrossRight` (entry 474): advance the (right) cursor one cell within its field, then cross
*left* back to the partner cursor.  Together, `advanceCrossRight` then `advanceCrossLeft` form one full tandem iteration of
the two-cursor comparison (per the fixed-`U` finding, entry 467): both cursors step right by one, the head returning to the
left cursor.

`advanceCrossLeft s smid sCont sEnd crMid crFound crCont := markAdvance3 s smid sCont sEnd ++ crossLeft sCont crMid crFound
crCont`.

## What is proved (clean axioms, no `sorry`)

* **`advanceCrossLeft …`** — the leftward half-tandem machine.
* **`advanceCrossLeft_cont_run`** (PROVED) — record cursor at `pc+d` (`tp[pc+d]=M`, `1 ≤ d`), its field continuing
  (`tp[pc+d+1]=I`), the partner marker at `pc` with the cells strictly between marker-free: `∃ N, reachIn N (s, pc+d, tp)
  (crFound, pc, writeAt3 (writeAt3 tp (pc+d) I) (pc+d+1) M)` — the cursor moved `pc+d → pc+d+1`, the head back on the
  partner.

## Honest scope

This is the **leftward half-tandem move**.  It does **not** yet build the full tandem loop, the four-way end-branch, the
symbol compare, the match-or-advance branch, the generic apply, nor a fixed `U` / `EmitsEncodedStepEx3`.  Building those
fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3AdvanceCrossL

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 writeAt3 toNTM3 writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MarkAdvance (markAdvance3 markAdvance3_run_cont)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Cross (crossLeft crossLeft_run)

/-- **The leftward half-tandem move.**  Advance the cursor one cell, then cross left back to the partner cursor. -/
def advanceCrossLeft (s smid sCont sEnd crMid crFound crCont : ℕ) : TMachine3 :=
  markAdvance3 s smid sCont sEnd ++ crossLeft sCont crMid crFound crCont

/-- **The leftward half-tandem move advances the cursor and returns to the partner (PROVED).** -/
theorem advanceCrossLeft_cont_run (s smid sCont sEnd crMid crFound crCont pc d : ℕ) (tp : List Sym3)
    (hd : 1 ≤ d) (hM : tp.getD (pc + d) Sym3.O = Sym3.M) (hI : tp.getD (pc + d + 1) Sym3.O = Sym3.I)
    (hPartner : tp.getD pc Sym3.O = Sym3.M) (hgap : ∀ k, 0 < k → k < d → tp.getD (pc + k) Sym3.O ≠ Sym3.M)
    (hbound : pc + d + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (advanceCrossLeft s smid sCont sEnd crMid crFound crCont)) N
      (s, pc + d, tp) (crFound, pc, writeAt3 (writeAt3 tp (pc + d) Sym3.I) (pc + d + 1) Sym3.M) := by
  have hwlen : ∀ (t : List Sym3) (p : ℕ) (w : Sym3), p < t.length → (writeAt3 t p w).length = t.length := by
    intro t p w hp; rw [writeAt3, List.length_set, List.length_append, List.length_replicate]; omega
  have htp1 : ∀ x, x ≠ pc + d → x ≠ pc + d + 1 →
      (writeAt3 (writeAt3 tp (pc + d) Sym3.I) (pc + d + 1) Sym3.M).getD x Sym3.O = tp.getD x Sym3.O := by
    intro x h1 h2; rw [writeAt3_getD, if_neg h2, writeAt3_getD, if_neg h1]
  have hadv := markAdvance3_run_cont s smid sCont sEnd (pc + d) tp hM hI
  set tp1 := writeAt3 (writeAt3 tp (pc + d) Sym3.I) (pc + d + 1) Sym3.M with htp1def
  have hlen0 : (writeAt3 tp (pc + d) Sym3.I).length = tp.length := hwlen tp (pc + d) Sym3.I (by omega)
  have hlen1 : tp1.length = tp.length := by
    rw [htp1def, hwlen _ (pc + d + 1) Sym3.M (by rw [hlen0]; omega), hlen0]
  have hMpartner : tp1.getD pc Sym3.O = Sym3.M := by rw [htp1def, htp1 _ (by omega) (by omega)]; exact hPartner
  have hclear : ∀ k, 0 < k → k ≤ d → tp1.getD (pc + k) Sym3.O ≠ Sym3.M := by
    intro k hk0 hkd
    rcases Nat.lt_or_ge k d with hlt | hge
    · rw [htp1def, htp1 _ (by omega) (by omega)]; exact hgap k hk0 hlt
    · have hkeq : k = d := by omega
      subst hkeq
      rw [htp1def, writeAt3_getD, if_neg (by omega), writeAt3_getD, if_pos rfl]; decide
  obtain ⟨N2, hcr⟩ := crossLeft_run sCont crMid crFound crCont pc d tp1 hMpartner hclear (by rw [hlen1]; omega)
  exact ⟨2 + N2, reachIn_seq3 (markAdvance3 s smid sCont sEnd) (crossLeft sCont crMid crFound crCont) 2 N2 _ _ _
    hadv hcr⟩

/-!
**The leftward half-tandem move, proved.**  `advanceCrossLeft` advances the right cursor and crosses back to the partner —
completing the half-tandem pair.  Next: chain `advanceCrossRight` then `advanceCrossLeft` into the full tandem loop with the
four-way end-branch, then the symbol compare and match-or-advance — fragment by verified fragment, not faked.  Not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3AdvanceCrossL

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3AdvanceCrossL.advanceCrossLeft_cont_run
