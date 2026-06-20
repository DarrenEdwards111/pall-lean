import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3CopyBitLeft

/-!
# Entry 415 — universal-TM-table build: the leftward unary field copy `copyFieldLeft3` (proved)

The apply phase brings the matched rule's new-state field into the configuration, which sits to the **left** of the rule
table.  This brick loops the leftward single-cell copy (`copyBitAtDistLeft3`, entry 414) over a whole unary field — the
leftward mirror of `copyField3` (entry 412).

The loop walks the **source** field rightward (`moveRight3` advances the head `c → c+1`), copying each cell `c+i` to the
destination `c+i-d`.  Because the destination is always `d` cells *behind* the advancing source pointer, the writes never
touch a cell that will still be read — so, unlike the rightward copy (which required `m < d`), the **leftward copy needs
only `d ≤ c`** (room to reach `c-d`).  The resulting tape is named by the fold `copyBlockLeft`, defined in the loop's
order so the induction aligns with no write-commuting.

## What is proved (clean axioms, no `sorry`)

* **`copyStepLeft3 s sCont sDone d`** / **`copyStepLeft3_run`** (PROVED) — copy the source bit to `p-d`, route `I ↦ sCont`
  / `O ↦ sDone`, head back at `p`, tape `= writeAt3 tp (p-d) (tp.getD p O)`.
* **`copyBlockLeft tp c d m`** — the tape after copying cells `c … c+m` to `c-d … c+m-d` (fold in loop order).
* **`copyFieldLeft3 s sDone d L`** / **`copyFieldLeft3_run`** (PROVED) — for a unary field (`m` ones then `O` at `c`),
  `m < L`, `1 ≤ d`, `d ≤ c`, `c+m < tp.length`: `∃ N, reachIn N (s, c, tp) (sDone, c+m, copyBlockLeft tp c d m)`.

## Honest scope

This is the **leftward unary field copy** — the new-state copy in the apply direction.  It does **not** yet carry the
specific rule fields, move the simulated head, nor assemble `apply3`.  Building those fragment by fragment is the genuine
remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyFieldLeft

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 readSym3 writeAt3 writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyBit (readCarry3 readCarry3_run_O readCarry3_run_I)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyBitLeft (copyArmLeft3 copyArmLeft3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Move (moveRight3 moveRight3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_append_left3 reachIn_append_right3 reachIn_seq3)

/-- Length is preserved by an in-bounds write. -/
private theorem writeAt3_length_eq (tp : List Sym3) (p : ℕ) (w : Sym3) (hp : p < tp.length) :
    (writeAt3 tp p w).length = tp.length := by
  simp only [writeAt3, List.length_set, List.length_append, List.length_replicate]
  omega

/-- **The routing leftward copy step.**  Copy the source bit to the destination `d` to the left, routing a one (`I`) to
`sCont` and the separator (`O`) to `sDone`. -/
def copyStepLeft3 (s sCont sDone d : ℕ) : TMachine3 :=
  readCarry3 s (s + 1) (s + 2 * d + 3) ++ copyArmLeft3 (s + 1) sDone d Sym3.O ++ copyArmLeft3 (s + 2 * d + 3) sCont d Sym3.I

/-- **The routing leftward copy step run (PROVED).** -/
theorem copyStepLeft3_run (s sCont sDone d p : ℕ) (tp : List Sym3)
    (hbit : tp.getD p Sym3.O = Sym3.O ∨ tp.getD p Sym3.O = Sym3.I)
    (hd : 1 ≤ d) (hdp : d ≤ p) (hp : p < tp.length) :
    ∃ N, reachIn (toNTM3 (copyStepLeft3 s sCont sDone d)) N (s, p, tp)
      ((if tp.getD p Sym3.O = Sym3.O then sDone else sCont), p, writeAt3 tp (p - d) (tp.getD p Sym3.O)) := by
  rcases hbit with hb | hb
  · rw [hb, if_pos rfl]
    have hrc := readCarry3_run_O s (s + 1) (s + 2 * d + 3) p tp
      (by rw [show readSym3 (s, p, tp) = tp.getD p Sym3.O from rfl, hb]) hp
    obtain ⟨N, harm⟩ := copyArmLeft3_run (s + 1) sDone d p Sym3.O tp hb hd hdp hp
    have s1 := reachIn_seq3 (readCarry3 s (s + 1) (s + 2 * d + 3)) (copyArmLeft3 (s + 1) sDone d Sym3.O)
      1 N _ _ _ hrc harm
    exact ⟨1 + N, reachIn_append_left3 _ (copyArmLeft3 (s + 2 * d + 3) sCont d Sym3.I) (1 + N) _ _ s1⟩
  · rw [hb, if_neg (by decide : ¬ (Sym3.I = Sym3.O))]
    have hrc := readCarry3_run_I s (s + 1) (s + 2 * d + 3) p tp
      (by rw [show readSym3 (s, p, tp) = tp.getD p Sym3.O from rfl, hb]) hp
    obtain ⟨N, harm⟩ := copyArmLeft3_run (s + 2 * d + 3) sCont d p Sym3.I tp hb hd hdp hp
    have hrcL := reachIn_append_left3 (readCarry3 s (s + 1) (s + 2 * d + 3)) (copyArmLeft3 (s + 1) sDone d Sym3.O)
      1 _ _ hrc
    have hrcL2 := reachIn_append_left3 (readCarry3 s (s + 1) (s + 2 * d + 3) ++ copyArmLeft3 (s + 1) sDone d Sym3.O)
      (copyArmLeft3 (s + 2 * d + 3) sCont d Sym3.I) 1 _ _ hrcL
    have harmL := reachIn_append_right3 (readCarry3 s (s + 1) (s + 2 * d + 3) ++ copyArmLeft3 (s + 1) sDone d Sym3.O)
      (copyArmLeft3 (s + 2 * d + 3) sCont d Sym3.I) N _ _ harm
    exact ⟨1 + N, (reachIn_add (toNTM3 (copyStepLeft3 s sCont sDone d)) 1 N _ _).mpr ⟨_, hrcL2, harmL⟩⟩

/-- **The leftward-copied tape**, defined in the loop's order: copy cell `c` to `c-d`, then recurse on `c+1`. -/
def copyBlockLeft (tp : List Sym3) (c d : ℕ) : ℕ → List Sym3
  | 0 => writeAt3 tp (c - d) (tp.getD c Sym3.O)
  | (m + 1) => copyBlockLeft (writeAt3 tp (c - d) (tp.getD c Sym3.O)) (c + 1) d m

/-- **The leftward unary field-copy loop.**  Each iteration: one routing leftward copy step (continue ↦ the advance
state), then a `moveRight3` advancing the *source* head, then recurse. -/
def copyFieldLeft3 (s sDone d : ℕ) : ℕ → TMachine3
  | 0 => []
  | (L + 1) =>
      copyStepLeft3 s (s + 4 * d + 5) sDone d ++ moveRight3 (s + 4 * d + 5) (s + 4 * d + 6)
        ++ copyFieldLeft3 (s + 4 * d + 6) sDone d L

/-- **The leftward unary field-copy run (PROVED).**  Copies the unary field (`m` ones then `O` at `c`) to the destination
region `c-d … c+m-d`, head ending at `c+m`, tape `= copyBlockLeft tp c d m`.  Needs only `d ≤ c` (room to the left). -/
theorem copyFieldLeft3_run (sDone d : ℕ) :
    ∀ (L s c m : ℕ) (tp : List Sym3), m < L → 1 ≤ d → d ≤ c → c + m < tp.length →
      (∀ i, i < m → tp.getD (c + i) Sym3.O = Sym3.I) → tp.getD (c + m) Sym3.O = Sym3.O →
      ∃ N, reachIn (toNTM3 (copyFieldLeft3 s sDone d L)) N (s, c, tp) (sDone, c + m, copyBlockLeft tp c d m) := by
  intro L
  induction L with
  | zero => intro s c m tp hmL _ _ _ _ _; exact absurd hmL (Nat.not_lt_zero _)
  | succ L ih =>
    intro s c m tp hmL hd hdc hbnd hco hcs
    have hp : c < tp.length := by omega
    cases m with
    | zero =>
        have hc0 : tp.getD c Sym3.O = Sym3.O := by have := hcs; rwa [Nat.add_zero] at this
        obtain ⟨N1, hstep⟩ := copyStepLeft3_run s (s + 4 * d + 5) sDone d c tp (Or.inl hc0) hd hdc hp
        rw [if_pos hc0] at hstep
        have h1 := reachIn_append_left3 (copyStepLeft3 s (s + 4 * d + 5) sDone d)
          (moveRight3 (s + 4 * d + 5) (s + 4 * d + 6)) N1 _ _ hstep
        have h2 := reachIn_append_left3 _ (copyFieldLeft3 (s + 4 * d + 6) sDone d L) N1 _ _ h1
        exact ⟨N1, h2⟩
    | succ m' =>
        have hcI : tp.getD c Sym3.O = Sym3.I := by have := hco 0 (by omega); rwa [Nat.add_zero] at this
        obtain ⟨N1, hstep⟩ := copyStepLeft3_run s (s + 4 * d + 5) sDone d c tp (Or.inr hcI) hd hdc hp
        rw [if_neg (show tp.getD c Sym3.O ≠ Sym3.O from by rw [hcI]; decide)] at hstep
        have hlen1 : (writeAt3 tp (c - d) (tp.getD c Sym3.O)).length = tp.length :=
          writeAt3_length_eq tp (c - d) _ (by omega)
        have hmr := moveRight3_run_eq (s + 4 * d + 5) (s + 4 * d + 6) c
          (writeAt3 tp (c - d) (tp.getD c Sym3.O)) (by rw [hlen1]; exact hp)
        obtain ⟨N3, hrec⟩ := ih (s + 4 * d + 6) (c + 1) m' (writeAt3 tp (c - d) (tp.getD c Sym3.O))
          (by omega) hd (by omega) (by rw [hlen1]; omega)
          (fun i hi => by
            rw [writeAt3_getD, if_neg (by omega), show c + 1 + i = c + (i + 1) from by omega]
            exact hco (i + 1) (by omega))
          (by rw [writeAt3_getD, if_neg (by omega), show c + 1 + m' = c + (m' + 1) from by omega]; exact hcs)
        rw [show c + 1 + m' = c + (m' + 1) from by omega] at hrec
        have sAB := reachIn_seq3 (copyStepLeft3 s (s + 4 * d + 5) sDone d)
          (moveRight3 (s + 4 * d + 5) (s + 4 * d + 6)) N1 1 _ _ _ hstep hmr
        have sABC := reachIn_seq3 _ (copyFieldLeft3 (s + 4 * d + 6) sDone d L) (N1 + 1) N3 _ _ _ sAB hrec
        exact ⟨N1 + 1 + N3, sABC⟩

/-!
**The leftward unary field copy, proved.**  `copyFieldLeft3` reproduces a unary field at a destination region `d` to the
left — the new-state copy in the apply direction, needing only `d ≤ c`.  Next: carry the specific rule fields into the
configuration, move the simulated head, and assemble `apply3` — fragment by verified fragment, not faked.  Not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyFieldLeft

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyFieldLeft.copyFieldLeft3_run
