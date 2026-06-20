import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3KeyMatch

/-!
# Entry 409 — universal-TM-table build: the windowed matcher (proved)

The rule-table match loop (entry 410) maintains a persistent *home* marker at `c-1` (one cell left of the configuration
key) so the inter-record reset `resetToHome3` (entry 408) can seek back to it.  But the field compare (406) and the
single-record matcher (407) assume **no marker anywhere** on the tape (`hM : ∀ j, tp.getD j O ≠ M`), which the home
marker violates.

This brick re-proves both runs with the no-marker hypothesis **windowed**: a marker is forbidden only in the cells the
machine actually shuttles through — `(c, c+a+d]` for the field compare, `(c, c+a+1+d]` for the record matcher — leaving
the home cell `c-1` (and everything left of `c`) free.  These are the *same machines* `fieldCompare3` / `recordKeyMatch3`
under *weaker* hypotheses, so the theorems are strictly stronger; the proofs mirror entries 406/407, threading the window
through the induction (it shifts `c → c+1` and shrinks as the field is consumed).

## What is proved (clean axioms, no `sorry`)

* **`fieldCompare3_run_windowed`** (PROVED) — `fieldCompare3_run` (406) with `hM` replaced by `∀ j, c < j → j ≤ c+a+d →
  tp.getD j O ≠ M` (carried inside the `∀ L s c a b`, so it shifts with the recursion).
* **`recordKeyMatch3_run_windowed`** (PROVED) — `recordKeyMatch3_run` (407) with `hM` replaced by `∀ j, c < j → j ≤
  c+a+1+d → tp.getD j O ≠ M`.

## Honest scope

This is the **hypothesis-windowing** that lets the table loop keep a home marker.  It does **not** yet assemble the loop,
nor apply the matched rule.  Building those fragment by fragment is the genuine remaining construction, **not faked**.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3KeyMatchWin

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FieldStep (fieldStep3 fieldStep3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FieldCompare (fieldCompare3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3BitCompare (bitCompareAtDist3 bitCompareAtDist3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Move (moveRight3 moveRight3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3KeyMatch (recordKeyMatch3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_append_left3 reachIn_seq3)

/-- **The windowed field-compare run (PROVED).**  `fieldCompare3_run` (entry 406) with the no-marker hypothesis windowed
to `(c, c+a+d]`, so a home marker at `c-1` is tolerated.  The window is carried inside the `∀ L s c a b` because it
shifts `c → c+1` as the recursion consumes the field. -/
theorem fieldCompare3_run_windowed (sMatch sFail d : ℕ) (tp : List Sym3) (hd : 1 ≤ d) :
    ∀ (L s c a b : ℕ), min a b < L → c + a + d < tp.length →
      (∀ j, c < j → j ≤ c + a + d → tp.getD j Sym3.O ≠ Sym3.M) →
      (∀ i, i < a → tp.getD (c + i) Sym3.O = Sym3.I) → tp.getD (c + a) Sym3.O = Sym3.O →
      (∀ i, i < b → tp.getD (c + d + i) Sym3.O = Sym3.I) → tp.getD (c + d + b) Sym3.O = Sym3.O →
      ∃ N, reachIn (toNTM3 (fieldCompare3 s sMatch sFail d L)) N (s, c, tp)
        ((if a = b then sMatch else sFail), c + min a b, tp) := by
  intro L
  induction L with
  | zero => intro s c a b hL _ _ _ _ _ _; exact absurd hL (Nat.not_lt_zero _)
  | succ L ih =>
    intro s c a b hL hbnd hWin hco hcs hro hrs
    have hp : c < tp.length := by omega
    have hbound : c + d < tp.length := by omega
    have hno : ∀ k, 0 < k → k ≤ d → tp.getD (c + k) Sym3.O ≠ Sym3.M :=
      fun k hk0 hkd => hWin (c + k) (by omega) (by omega)
    have hbit : tp.getD c Sym3.O = Sym3.O ∨ tp.getD c Sym3.O = Sym3.I := by
      rcases Nat.eq_zero_or_pos a with ha | ha
      · left; have := hcs; rw [ha, Nat.add_zero] at this; exact this
      · right; have := hco 0 ha; rwa [Nat.add_zero] at this
    obtain ⟨N1, hFS⟩ := fieldStep3_run s (s + 2 * d + 15) sMatch sFail c d tp hbit hd hno hp hbound
    rcases Nat.eq_zero_or_pos a with rfl | hapos
    · rcases Nat.eq_zero_or_pos b with rfl | hbpos
      · have hc0 : tp.getD c Sym3.O = Sym3.O := by simpa using hcs
        have hd0 : tp.getD (c + d) Sym3.O = Sym3.O := by simpa using hrs
        rw [hc0, if_pos rfl, hd0, if_pos rfl] at hFS
        have h1 := reachIn_append_left3 (fieldStep3 s (s + 2 * d + 15) sMatch sFail d)
          (moveRight3 (s + 2 * d + 15) (s + 2 * d + 16)) N1 _ _ hFS
        have h2 := reachIn_append_left3 _ (fieldCompare3 (s + 2 * d + 16) sMatch sFail d L) N1 _ _ h1
        rw [if_pos rfl, show c + min 0 0 = c from by omega]
        exact ⟨N1, h2⟩
      · have hc0 : tp.getD c Sym3.O = Sym3.O := by simpa using hcs
        have hdI : tp.getD (c + d) Sym3.O = Sym3.I := by have := hro 0 hbpos; rwa [Nat.add_zero] at this
        rw [hc0, if_pos rfl, hdI, if_neg (by decide : ¬ (Sym3.I = Sym3.O))] at hFS
        have h1 := reachIn_append_left3 (fieldStep3 s (s + 2 * d + 15) sMatch sFail d)
          (moveRight3 (s + 2 * d + 15) (s + 2 * d + 16)) N1 _ _ hFS
        have h2 := reachIn_append_left3 _ (fieldCompare3 (s + 2 * d + 16) sMatch sFail d L) N1 _ _ h1
        rw [if_neg (show ¬ ((0 : ℕ) = b) from by omega), show c + min 0 b = c from by omega]
        exact ⟨N1, h2⟩
    · rcases Nat.eq_zero_or_pos b with rfl | hbpos
      · have hcI : tp.getD c Sym3.O = Sym3.I := by have := hco 0 hapos; rwa [Nat.add_zero] at this
        have hd0 : tp.getD (c + d) Sym3.O = Sym3.O := by simpa using hrs
        rw [hcI, if_neg (by decide : ¬ (Sym3.I = Sym3.O)), hd0,
          if_neg (by decide : ¬ (Sym3.O = Sym3.I))] at hFS
        have h1 := reachIn_append_left3 (fieldStep3 s (s + 2 * d + 15) sMatch sFail d)
          (moveRight3 (s + 2 * d + 15) (s + 2 * d + 16)) N1 _ _ hFS
        have h2 := reachIn_append_left3 _ (fieldCompare3 (s + 2 * d + 16) sMatch sFail d L) N1 _ _ h1
        rw [if_neg (show ¬ (a = 0) from by omega), show c + min a 0 = c from by omega]
        exact ⟨N1, h2⟩
      · have hcI : tp.getD c Sym3.O = Sym3.I := by have := hco 0 hapos; rwa [Nat.add_zero] at this
        have hdI : tp.getD (c + d) Sym3.O = Sym3.I := by have := hro 0 hbpos; rwa [Nat.add_zero] at this
        rw [hcI, if_neg (by decide : ¬ (Sym3.I = Sym3.O)), hdI, if_pos rfl] at hFS
        have hMR := moveRight3_run_eq (s + 2 * d + 15) (s + 2 * d + 16) c tp hp
        obtain ⟨N2, hREC⟩ := ih (s + 2 * d + 16) (c + 1) (a - 1) (b - 1)
          (by omega) (by omega)
          (fun j hj1 hj2 => hWin j (by omega) (by omega))
          (fun i hi => by rw [show c + 1 + i = c + (i + 1) from by omega]; exact hco (i + 1) (by omega))
          (by rw [show c + 1 + (a - 1) = c + a from by omega]; exact hcs)
          (fun i hi => by rw [show c + 1 + d + i = c + d + (i + 1) from by omega]; exact hro (i + 1) (by omega))
          (by rw [show c + 1 + d + (b - 1) = c + d + b from by omega]; exact hrs)
        simp only [show (a - 1 = b - 1) ↔ (a = b) from by omega] at hREC
        rw [show c + 1 + min (a - 1) (b - 1) = c + min a b from by omega] at hREC
        have seqFM := reachIn_seq3 (fieldStep3 s (s + 2 * d + 15) sMatch sFail d)
          (moveRight3 (s + 2 * d + 15) (s + 2 * d + 16)) N1 1 _ _ _ hFS hMR
        have seqAll := reachIn_seq3 _ (fieldCompare3 (s + 2 * d + 16) sMatch sFail d L)
          (N1 + 1) N2 _ _ _ seqFM hREC
        exact ⟨N1 + 1 + N2, seqAll⟩

/-- **The windowed single-record key matcher run (PROVED).**  `recordKeyMatch3_run` (entry 407) with the no-marker
hypothesis windowed to `(c, c+a+1+d]`, so a home marker at `c-1` is tolerated. -/
theorem recordKeyMatch3_run_windowed (base recMatch recFail d : ℕ) (tp : List Sym3) (hd : 1 ≤ d)
    (L c a b : ℕ) (cs rs : Sym3) (hcs : cs = Sym3.O ∨ cs = Sym3.I)
    (hL : min a b < L) (hbnd : c + a + 1 + d < tp.length)
    (hWin : ∀ j, c < j → j ≤ c + a + 1 + d → tp.getD j Sym3.O ≠ Sym3.M)
    (hco : ∀ i, i < a → tp.getD (c + i) Sym3.O = Sym3.I) (hcsep : tp.getD (c + a) Sym3.O = Sym3.O)
    (hro : ∀ i, i < b → tp.getD (c + d + i) Sym3.O = Sym3.I) (hrsep : tp.getD (c + d + b) Sym3.O = Sym3.O)
    (hcsym : tp.getD (c + a + 1) Sym3.O = cs) (hrsym : tp.getD (c + d + b + 1) Sym3.O = rs) :
    ∃ N q, reachIn (toNTM3 (recordKeyMatch3 base recMatch recFail d L)) N (base, c, tp)
      ((if a = b ∧ rs = cs then recMatch else recFail), q, tp) := by
  obtain ⟨N1, hFCraw⟩ := fieldCompare3_run_windowed (base + L * (2 * d + 16)) recFail d tp hd L base c a b
    hL (by omega) (fun j hj1 hj2 => hWin j hj1 (by omega)) hco hcsep hro hrsep
  by_cases hab : a = b
  · rw [if_pos hab, show c + min a b = c + a from by omega] at hFCraw
    have hMR := moveRight3_run_eq (base + L * (2 * d + 16)) (base + L * (2 * d + 16) + 1) (c + a) tp (by omega)
    have hbit' : tp.getD (c + a + 1) Sym3.O = Sym3.O ∨ tp.getD (c + a + 1) Sym3.O = Sym3.I := by
      rw [hcsym]; exact hcs
    have hno' : ∀ k, 0 < k → k ≤ d → tp.getD (c + a + 1 + k) Sym3.O ≠ Sym3.M :=
      fun k hk0 hkd => hWin (c + a + 1 + k) (by omega) (by omega)
    obtain ⟨N3, hBC⟩ := bitCompareAtDist3_run (base + L * (2 * d + 16) + 1) recMatch recFail (c + a + 1) d tp
      hbit' hd hno' (by omega) (by omega)
    have hRsym' : tp.getD (c + a + 1 + d) Sym3.O = rs := by
      rw [show c + a + 1 + d = c + d + b + 1 from by omega]; exact hrsym
    simp only [hcsym, hRsym'] at hBC
    have seq1 := reachIn_seq3 (fieldCompare3 base (base + L * (2 * d + 16)) recFail d L)
      (moveRight3 (base + L * (2 * d + 16)) (base + L * (2 * d + 16) + 1)) N1 1 _ _ _ hFCraw hMR
    have seq2 := reachIn_seq3 _ (bitCompareAtDist3 (base + L * (2 * d + 16) + 1) recMatch recFail d)
      (N1 + 1) N3 _ _ _ seq1 hBC
    simp only [show (a = b ∧ rs = cs) ↔ (rs = cs) from by simp [hab]]
    exact ⟨N1 + 1 + N3, c + a + 1, seq2⟩
  · rw [if_neg hab] at hFCraw
    have h1 := reachIn_append_left3 (fieldCompare3 base (base + L * (2 * d + 16)) recFail d L)
      (moveRight3 (base + L * (2 * d + 16)) (base + L * (2 * d + 16) + 1)) N1 _ _ hFCraw
    have h2 := reachIn_append_left3 _ (bitCompareAtDist3 (base + L * (2 * d + 16) + 1) recMatch recFail d) N1 _ _ h1
    rw [if_neg (show ¬ (a = b ∧ rs = cs) from fun h => hab h.1)]
    exact ⟨N1, c + min a b, h2⟩

/-!
**The windowed matcher, proved.**  `fieldCompare3` and `recordKeyMatch3` run under a no-marker hypothesis confined to the
cells they shuttle through, leaving the config home cell `c-1` free for a persistent marker.  Next: assemble the
rule-table match loop `matchTable3`, threading the matcher and the home reset (`resetToHome3`, entry 408) over the record
list — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3KeyMatchWin

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3KeyMatchWin.fieldCompare3_run_windowed
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3KeyMatchWin.recordKeyMatch3_run_windowed
