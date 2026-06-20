import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3MatchTable

/-!
# Entry 464 — universal-TM-table build: the windowed rule-table match loop `matchTable3_run_windowed` (proved)

The matcher (`matchTable3`, entry 410) was proved with a *global* no-marker hypothesis (`∀ j ≠ c-1, ≠ M`), which forbids a
head marker — incompatible with the stitched tape (entry 461), whose simulated tape carries a head marker `M` beyond the
rule table.  This brick re-proves it with a **windowed** clean hypothesis: no marker only in `(c-1, hm)` (the config+rules
window), plus the records all living before `hm`.  A head marker at or beyond `hm` is now permitted — exactly the situation
on the stitched tape, where `fullTape3_matcher_clean` (entry 463) supplies this window.

The proof mirrors entry 410; the two uses of the clean hypothesis (the windowed per-record matcher and the home reset) are
discharged from `hcleanW` because the matcher's working positions (`q ≤ c+a+1`, the record window `≤ c+a+1+d`) all lie below
`hm`.

## What is proved (clean axioms, no `sorry`)

* **`matchTable3_run_windowed`** (PROVED) — with the home marker, the **windowed** clean hypothesis `∀ j, c-1 < j → j < hm →
  ≠ M`, the config key, every record `RecOK`, every record before `hm` (`c+a+1+rec.1 < hm`), and some record matching: `∃ N
  q, reachIn N (base, c, tp) (recMatch, q, tp)` — the loop reaches the match-found state.

## Honest scope

This is the **windowed matcher** (head marker beyond `hm` permitted).  It does **not** yet define the bit-decoding `φ` / `U`
/ `EmitsEncodedStepEx3` (the large but obstruction-free remaining assembly, per entry 456).  Building the rest fragment by
fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MatchTableWin

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3KeyMatch (recordKeyMatch3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3KeyMatchWin (recordKeyMatch3_run_windowed)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ResetHome (resetToHome3 resetToHome3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MatchTable (matchTable3 RecOK RecMatch)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_append_left3 reachIn_seq3)

/-- **The windowed rule-table match loop run (PROVED).**  Same as entry 410 but with a windowed clean hypothesis (no
marker in `(c-1, hm)`) and the records before `hm` — so a head marker beyond `hm` is permitted. -/
theorem matchTable3_run_windowed (recMatch L : ℕ) (tp : List Sym3) (c a hm : ℕ) (cs : Sym3)
    (hc : 1 ≤ c) (hcs : cs = Sym3.O ∨ cs = Sym3.I)
    (hmark : tp.getD (c - 1) Sym3.O = Sym3.M) (hcleanW : ∀ j, c - 1 < j → j < hm → tp.getD j Sym3.O ≠ Sym3.M)
    (hco : ∀ i, i < a → tp.getD (c + i) Sym3.O = Sym3.I) (hcsep : tp.getD (c + a) Sym3.O = Sym3.O)
    (hcsym : tp.getD (c + a + 1) Sym3.O = cs) :
    ∀ (recs : List (ℕ × ℕ × Sym3)) (base : ℕ),
      (∀ rec ∈ recs, RecOK tp c a L rec) → (∀ rec ∈ recs, c + a + 1 + rec.1 < hm) →
      (∃ rec ∈ recs, RecMatch a cs rec) →
      ∃ N q, reachIn (toNTM3 (matchTable3 recMatch L base recs)) N (base, c, tp) (recMatch, q, tp) := by
  intro recs
  induction recs with
  | nil => intro base _ _ hEx; rcases hEx with ⟨x, hmem, -⟩; simp at hmem
  | cons rec rest ih =>
      intro base hOK hHead hEx
      obtain ⟨d, b, rs⟩ := rec
      have hhead := (List.forall_mem_cons.mp hOK).1
      have hOKrest := (List.forall_mem_cons.mp hOK).2
      have hHeadHead := (List.forall_mem_cons.mp hHead).1
      have hHeadrest := (List.forall_mem_cons.mp hHead).2
      simp only [RecOK] at hhead
      obtain ⟨hd, hbudget, hbnd, hcoR, hcsepR, hcsymR⟩ := hhead
      obtain ⟨N1, q, hrun, hq1, hq2⟩ := recordKeyMatch3_run_windowed base recMatch
        (base + L * (2 * d + 16) + 2 * d + 16) d tp hd L c a b cs rs hcs hbudget hbnd
        (fun j hj1 hj2 => hcleanW j (by omega) (by omega)) hco hcsep hcoR hcsepR hcsym hcsymR
      by_cases hmatch : a = b ∧ rs = cs
      · rw [if_pos hmatch] at hrun
        refine ⟨N1, q, ?_⟩
        have hl1 := reachIn_append_left3 _ (resetToHome3 (base + L * (2 * d + 16) + 2 * d + 16)
          (base + L * (2 * d + 16) + 2 * d + 17) (base + L * (2 * d + 16) + 2 * d + 18)
          (base + L * (2 * d + 16) + 2 * d + 19)) N1 _ _ hrun
        exact reachIn_append_left3 _ (matchTable3 recMatch L (base + L * (2 * d + 16) + 2 * d + 19) rest) N1 _ _ hl1
      · rw [if_neg hmatch] at hrun
        obtain ⟨N2, hReset⟩ := resetToHome3_run (base + L * (2 * d + 16) + 2 * d + 16)
          (base + L * (2 * d + 16) + 2 * d + 17) (base + L * (2 * d + 16) + 2 * d + 18)
          (base + L * (2 * d + 16) + 2 * d + 19) (c - 1) (q - (c - 1)) tp hmark
          (fun k hk0 hk => hcleanW (c - 1 + k) (by omega) (by omega)) (by omega)
        rw [show c - 1 + (q - (c - 1)) = q from by omega, show c - 1 + 1 = c from by omega] at hReset
        have hExrest : ∃ rec ∈ rest, RecMatch a cs rec := by
          rcases hEx with ⟨x, hxmem, hxP⟩
          rcases List.mem_cons.mp hxmem with rfl | hxtl
          · exact absurd hxP hmatch
          · exact ⟨x, hxtl, hxP⟩
        obtain ⟨N3, q3, hIH⟩ := ih (base + L * (2 * d + 16) + 2 * d + 19) hOKrest hHeadrest hExrest
        have sAB := reachIn_seq3 (recordKeyMatch3 base recMatch (base + L * (2 * d + 16) + 2 * d + 16) d L)
          (resetToHome3 (base + L * (2 * d + 16) + 2 * d + 16) (base + L * (2 * d + 16) + 2 * d + 17)
            (base + L * (2 * d + 16) + 2 * d + 18) (base + L * (2 * d + 16) + 2 * d + 19))
          N1 N2 _ _ _ hrun hReset
        have sABC := reachIn_seq3 _ (matchTable3 recMatch L (base + L * (2 * d + 16) + 2 * d + 19) rest)
          (N1 + N2) N3 _ _ _ sAB hIH
        exact ⟨N1 + N2 + N3, q3, sABC⟩

/-!
**The windowed rule-table match loop, proved.**  `matchTable3_run_windowed` runs the matcher with the head marker beyond a
window bound `hm` — exactly the stitched-tape situation (entry 463 supplies the window).  Next: define the bit-decoding `φ`,
assemble `U`, and prove `EmitsEncodedStepEx3` — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MatchTableWin

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MatchTableWin.matchTable3_run_windowed
