import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3CopyBit

/-!
# Entry 412 — universal-TM-table build: the unary field copy `copyField3` (proved)

The apply phase copies the matched rule's new-state field — a unary field — into the configuration.  This brick loops the
single-cell copy (`copyBitAtDist3`, entry 411) over a whole unary field, the copy-side analogue of `fieldCompare3`
(entry 406).

The loop body `copyStep3` refines `copyBitAtDist3` so the two source-bit lineages route to *distinct* targets: a one
(`I`) continues the loop, the separator (`O`) ends it (just as `fieldStep3` split the compare).  The loop `copyField3`
unrolls `copyStep3` + an advance over a budget, copying cells `c, c+1, …, c+m` (the `m` ones and the separator) to the
destination region `c+d, …, c+m+d`.  Because every copy reads its source from the (current) tape and writes a destination
cell, and the destination region must be **disjoint** from the source, we require `m < d`.  The resulting tape is named by
the fold `copyBlock`, defined in exactly the loop's order so the induction aligns with no write-commuting needed.

## What is proved (clean axioms, no `sorry`)

* **`copyStep3 s sCont sDone d`** / **`copyStep3_run`** (PROVED) — copy the source bit to `p+d`, route `I ↦ sCont` /
  `O ↦ sDone`, head back at `p`, tape `= writeAt3 tp (p+d) (tp.getD p O)`.
* **`copyBlock tp c d m`** — the tape after copying cells `c … c+m` to `c+d … c+m+d` (fold in loop order).
* **`copyField3 s sDone d L`** — the budget-`L` corridor `copyStep3 ++ moveRight3 ++ copyField3 …`.
* **`copyField3_run`** (PROVED) — for a unary field (`m` ones then `O` at `c`), `m < L`, `m < d`, `c+m+d < tp.length`:
  `∃ N, reachIn N (s, c, tp) (sDone, c+m, copyBlock tp c d m)` — the field is reproduced at `c+d … c+m+d`, the source
  unchanged.

## Honest scope

This is the **unary field copy** — the new-state copy of the apply phase, rightward (source left of destination).  It does
**not** yet write the symbol, move the simulated head, nor assemble `apply3`; nor a leftward copy variant.  Building those
fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyField

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 readSym3 writeAt3 writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyBit
  (readCarry3 readCarry3_run_O readCarry3_run_I copyArm3 copyArm3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Move (moveRight3 moveRight3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_append_left3 reachIn_append_right3 reachIn_seq3)

/-- Length is preserved by an in-bounds write. -/
private theorem writeAt3_length_eq (tp : List Sym3) (p : ℕ) (w : Sym3) (hp : p < tp.length) :
    (writeAt3 tp p w).length = tp.length := by
  simp only [writeAt3, List.length_set, List.length_append, List.length_replicate]
  omega

/-- **The routing copy step.**  Copy the source bit to the destination `d` away, routing a one (`I`) to `sCont` and the
separator (`O`) to `sDone`.  (`copyBitAtDist3` is the case `sCont = sDone`.) -/
def copyStep3 (s sCont sDone d : ℕ) : TMachine3 :=
  readCarry3 s (s + 1) (s + 2 * d + 3) ++ copyArm3 (s + 1) sDone d Sym3.O ++ copyArm3 (s + 2 * d + 3) sCont d Sym3.I

/-- **The routing copy step run (PROVED).** -/
theorem copyStep3_run (s sCont sDone d p : ℕ) (tp : List Sym3)
    (hbit : tp.getD p Sym3.O = Sym3.O ∨ tp.getD p Sym3.O = Sym3.I)
    (hd : 1 ≤ d) (hp : p < tp.length) (hpd : p + d < tp.length) :
    ∃ N, reachIn (toNTM3 (copyStep3 s sCont sDone d)) N (s, p, tp)
      ((if tp.getD p Sym3.O = Sym3.O then sDone else sCont), p, writeAt3 tp (p + d) (tp.getD p Sym3.O)) := by
  rcases hbit with hb | hb
  · -- source bit O: the separator, route to sDone
    rw [hb, if_pos rfl]
    have hrc := readCarry3_run_O s (s + 1) (s + 2 * d + 3) p tp
      (by rw [show readSym3 (s, p, tp) = tp.getD p Sym3.O from rfl, hb]) hp
    obtain ⟨N, harm⟩ := copyArm3_run (s + 1) sDone d p Sym3.O tp hb hd hp hpd
    have s1 := reachIn_seq3 (readCarry3 s (s + 1) (s + 2 * d + 3)) (copyArm3 (s + 1) sDone d Sym3.O)
      1 N _ _ _ hrc harm
    exact ⟨1 + N, reachIn_append_left3 _ (copyArm3 (s + 2 * d + 3) sCont d Sym3.I) (1 + N) _ _ s1⟩
  · -- source bit I: a one, route to sCont
    rw [hb, if_neg (by decide : ¬ (Sym3.I = Sym3.O))]
    have hrc := readCarry3_run_I s (s + 1) (s + 2 * d + 3) p tp
      (by rw [show readSym3 (s, p, tp) = tp.getD p Sym3.O from rfl, hb]) hp
    obtain ⟨N, harm⟩ := copyArm3_run (s + 2 * d + 3) sCont d p Sym3.I tp hb hd hp hpd
    have hrcL := reachIn_append_left3 (readCarry3 s (s + 1) (s + 2 * d + 3)) (copyArm3 (s + 1) sDone d Sym3.O)
      1 _ _ hrc
    have hrcL2 := reachIn_append_left3 (readCarry3 s (s + 1) (s + 2 * d + 3) ++ copyArm3 (s + 1) sDone d Sym3.O)
      (copyArm3 (s + 2 * d + 3) sCont d Sym3.I) 1 _ _ hrcL
    have harmL := reachIn_append_right3 (readCarry3 s (s + 1) (s + 2 * d + 3) ++ copyArm3 (s + 1) sDone d Sym3.O)
      (copyArm3 (s + 2 * d + 3) sCont d Sym3.I) N _ _ harm
    exact ⟨1 + N, (reachIn_add (toNTM3 (copyStep3 s sCont sDone d)) 1 N _ _).mpr ⟨_, hrcL2, harmL⟩⟩

/-- **The copied tape**, defined in the loop's order: copy cell `c` to `c+d`, then recurse on `c+1`.  `copyBlock tp c d m`
is `tp` with cells `c … c+m` reproduced at `c+d … c+m+d`. -/
def copyBlock (tp : List Sym3) (c d : ℕ) : ℕ → List Sym3
  | 0 => writeAt3 tp (c + d) (tp.getD c Sym3.O)
  | (m + 1) => copyBlock (writeAt3 tp (c + d) (tp.getD c Sym3.O)) (c + 1) d m

/-- **The unary field-copy loop.**  Each iteration: one routing copy step (continue ↦ the advance state), then a
`moveRight3` to the next source cell, then recurse. -/
def copyField3 (s sDone d : ℕ) : ℕ → TMachine3
  | 0 => []
  | (L + 1) =>
      copyStep3 s (s + 4 * d + 5) sDone d ++ moveRight3 (s + 4 * d + 5) (s + 4 * d + 6)
        ++ copyField3 (s + 4 * d + 6) sDone d L

/-- **The unary field-copy run (PROVED).**  Copies the unary field (`m` ones then `O` at `c`) to the destination region
`c+d … c+m+d`, leaving the source unchanged; head ends at `c+m`, tape `= copyBlock tp c d m`. -/
theorem copyField3_run (sDone d : ℕ) :
    ∀ (L s c m : ℕ) (tp : List Sym3), m < L → m < d → c + m + d < tp.length →
      (∀ i, i < m → tp.getD (c + i) Sym3.O = Sym3.I) → tp.getD (c + m) Sym3.O = Sym3.O →
      ∃ N, reachIn (toNTM3 (copyField3 s sDone d L)) N (s, c, tp) (sDone, c + m, copyBlock tp c d m) := by
  intro L
  induction L with
  | zero => intro s c m tp hmL _ _ _ _; exact absurd hmL (Nat.not_lt_zero _)
  | succ L ih =>
    intro s c m tp hmL hmd hbnd hco hcs
    have hp : c < tp.length := by omega
    have hpd : c + d < tp.length := by omega
    have hd : 1 ≤ d := by omega
    cases m with
    | zero =>
        have hc0 : tp.getD c Sym3.O = Sym3.O := by have := hcs; rwa [Nat.add_zero] at this
        obtain ⟨N1, hstep⟩ := copyStep3_run s (s + 4 * d + 5) sDone d c tp (Or.inl hc0) hd hp hpd
        rw [if_pos hc0] at hstep
        have h1 := reachIn_append_left3 (copyStep3 s (s + 4 * d + 5) sDone d)
          (moveRight3 (s + 4 * d + 5) (s + 4 * d + 6)) N1 _ _ hstep
        have h2 := reachIn_append_left3 _ (copyField3 (s + 4 * d + 6) sDone d L) N1 _ _ h1
        exact ⟨N1, h2⟩
    | succ m' =>
        have hcI : tp.getD c Sym3.O = Sym3.I := by have := hco 0 (by omega); rwa [Nat.add_zero] at this
        obtain ⟨N1, hstep⟩ := copyStep3_run s (s + 4 * d + 5) sDone d c tp (Or.inr hcI) hd hp hpd
        rw [if_neg (show tp.getD c Sym3.O ≠ Sym3.O from by rw [hcI]; decide)] at hstep
        have hlen1 : (writeAt3 tp (c + d) (tp.getD c Sym3.O)).length = tp.length :=
          writeAt3_length_eq tp (c + d) _ hpd
        have hmr := moveRight3_run_eq (s + 4 * d + 5) (s + 4 * d + 6) c
          (writeAt3 tp (c + d) (tp.getD c Sym3.O)) (by rw [hlen1]; exact hp)
        obtain ⟨N3, hrec⟩ := ih (s + 4 * d + 6) (c + 1) m' (writeAt3 tp (c + d) (tp.getD c Sym3.O))
          (by omega) (by omega) (by rw [hlen1]; omega)
          (fun i hi => by
            rw [writeAt3_getD, if_neg (by omega), show c + 1 + i = c + (i + 1) from by omega]
            exact hco (i + 1) (by omega))
          (by rw [writeAt3_getD, if_neg (by omega), show c + 1 + m' = c + (m' + 1) from by omega]; exact hcs)
        rw [show c + 1 + m' = c + (m' + 1) from by omega] at hrec
        have sAB := reachIn_seq3 (copyStep3 s (s + 4 * d + 5) sDone d)
          (moveRight3 (s + 4 * d + 5) (s + 4 * d + 6)) N1 1 _ _ _ hstep hmr
        have sABC := reachIn_seq3 _ (copyField3 (s + 4 * d + 6) sDone d L) (N1 + 1) N3 _ _ _ sAB hrec
        exact ⟨N1 + 1 + N3, sABC⟩

/-!
**The unary field copy, proved.**  `copyField3` reproduces a unary field at a destination region `d` away, leaving the
source untouched — the new-state copy of the apply phase.  Next: write the new symbol, move the simulated head, and
assemble `apply3` (and, as needed, a leftward copy) — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyField

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyField.copyField3_run
