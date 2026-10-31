import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3CopyBit

/-!
# Entry 414 — universal-TM-table build: the leftward single-cell copy `copyBitAtDistLeft3` (proved)

The apply phase copies the matched rule's right-hand side *into* the configuration.  The configuration sits to the **left**
of the rule table (the matcher placed the config key at `c` and the rule at `c+d`), so apply copies **right → left** —
the opposite direction from `copyBitAtDist3` (entry 411, which copies left → right).  This brick is that leftward copy.

It mirrors entry 411 exactly with the two move directions swapped: read the source bit marker-free (`readCarry3`), walk
**left** `d` cells (`moveLeftN3`), write the carried bit at the destination `p-d`, then walk **back right** the fixed `d`
cells (`moveRightN3`) — again no seek, since the return distance is exactly `d`.  Only the destination cell changes; the
source and head are left untouched.

## What is proved (clean axioms, no `sorry`)

* **`copyArmLeft3 s sOut d b`** / **`copyArmLeft3_run`** (PROVED) — one lineage: `tp[p] = b`, `1 ≤ d`, `d ≤ p`, `p <
  tp.length` ⇒ `∃ N, reachIn N (s, p, tp) (sOut, p, writeAt3 tp (p-d) b)`.
* **`copyBitAtDistLeft3 s sOut d`** / **`copyBitAtDistLeft3_run`** (PROVED) — `readCarry3 ++ copyArmLeft3 (O) ++
  copyArmLeft3 (I)`: copies the source bit `tp[p]` into cell `p-d`, head back at `p`, source unchanged.

## Honest scope

This is the **leftward single-cell copy** — the mirror of the rightward copy, the direction the apply phase needs to bring
the rule's RHS into the configuration.  It does **not** yet loop over a field, carry a specific rule field, nor assemble
`apply3`.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyBitLeft

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 readSym3 writeAt3 writeAt3_getD writeAt3_id_of_lt)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveN (moveRightN3 moveRightN3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyBit
  (readCarry3 readCarry3_run_O readCarry3_run_I moveLeftN3 moveLeftN3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Unmark (unmark3 unmark3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_append_left3 reachIn_append_right3 reachIn_seq3)

/-- Length is preserved by an in-bounds write. -/
private theorem writeAt3_length_eq (tp : List Sym3) (p : ℕ) (w : Sym3) (hp : p < tp.length) :
    (writeAt3 tp p w).length = tp.length := by
  simp only [writeAt3, List.length_set, List.length_append, List.length_replicate]
  omega

/-- **One leftward copy lineage.**  Go left `d`, write the carried bit `b` at the destination `p-d`, walk back right the
fixed `d` cells, and write `b` back at the source (an identity), ending at `sOut`. -/
def copyArmLeft3 (s sOut d : ℕ) (b : Sym3) : TMachine3 :=
  moveLeftN3 s d ++ unmark3 (s + d) (s + d + 1) b ++ moveRightN3 (s + d + 1) d ++ unmark3 (s + 2 * d + 1) sOut b

/-- **The leftward copy-lineage run (PROVED).** -/
theorem copyArmLeft3_run (s sOut d p : ℕ) (b : Sym3) (tp : List Sym3) (hb : tp.getD p Sym3.O = b)
    (hd : 1 ≤ d) (hdp : d ≤ p) (hp : p < tp.length) :
    ∃ N, reachIn (toNTM3 (copyArmLeft3 s sOut d b)) N (s, p, tp) (sOut, p, writeAt3 tp (p - d) b) := by
  have hpd : p - d < tp.length := by omega
  have hlen1 : (writeAt3 tp (p - d) b).length = tp.length := writeAt3_length_eq tp (p - d) b hpd
  have r1 := moveLeftN3_run s d p tp hdp hp
  have r2 := unmark3_run (s + d) (s + d + 1) b (p - d) tp
  have r3 := moveRightN3_run (s + d + 1) d (p - d) (writeAt3 tp (p - d) b) (by rw [hlen1]; omega)
  rw [show (p - d) + d = p from by omega, show s + d + 1 + d = s + 2 * d + 1 from by omega] at r3
  have r4 := unmark3_run (s + 2 * d + 1) sOut b p (writeAt3 tp (p - d) b)
  have hfix : writeAt3 (writeAt3 tp (p - d) b) p b = writeAt3 tp (p - d) b := by
    have hp1 : (writeAt3 tp (p - d) b).getD p Sym3.O = b := by rw [writeAt3_getD, if_neg (by omega)]; exact hb
    have hplen : p < (writeAt3 tp (p - d) b).length := by rw [hlen1]; exact hp
    have hid := writeAt3_id_of_lt (writeAt3 tp (p - d) b) p hplen
    rwa [hp1] at hid
  rw [hfix] at r4
  have s12 := reachIn_seq3 (moveLeftN3 s d) (unmark3 (s + d) (s + d + 1) b) d 1 _ _ _ r1 r2
  have s123 := reachIn_seq3 (moveLeftN3 s d ++ unmark3 (s + d) (s + d + 1) b)
    (moveRightN3 (s + d + 1) d) (d + 1) d _ _ _ s12 r3
  have s1234 := reachIn_seq3 (moveLeftN3 s d ++ unmark3 (s + d) (s + d + 1) b ++ moveRightN3 (s + d + 1) d)
    (unmark3 (s + 2 * d + 1) sOut b) (d + 1 + d) 1 _ _ _ s123 r4
  exact ⟨d + 1 + d + 1, s1234⟩

/-- **The leftward single-cell copy-at-distance.**  Read the source bit, then in the matching lineage copy it to the
destination `d` cells to the **left** and return. -/
def copyBitAtDistLeft3 (s sOut d : ℕ) : TMachine3 :=
  readCarry3 s (s + 1) (s + 2 * d + 3) ++ copyArmLeft3 (s + 1) sOut d Sym3.O ++ copyArmLeft3 (s + 2 * d + 3) sOut d Sym3.I

/-- **The leftward single-cell copy run (PROVED).**  Copies the source bit `tp[p]` into cell `p-d`; the head returns to
`p` and the source is unchanged. -/
theorem copyBitAtDistLeft3_run (s sOut d p : ℕ) (tp : List Sym3)
    (hbit : tp.getD p Sym3.O = Sym3.O ∨ tp.getD p Sym3.O = Sym3.I)
    (hd : 1 ≤ d) (hdp : d ≤ p) (hp : p < tp.length) :
    ∃ N, reachIn (toNTM3 (copyBitAtDistLeft3 s sOut d)) N (s, p, tp)
      (sOut, p, writeAt3 tp (p - d) (tp.getD p Sym3.O)) := by
  rcases hbit with hb | hb
  · -- source bit O: the O-lineage copies
    have hrc := readCarry3_run_O s (s + 1) (s + 2 * d + 3) p tp
      (by rw [show readSym3 (s, p, tp) = tp.getD p Sym3.O from rfl, hb]) hp
    obtain ⟨N, harm⟩ := copyArmLeft3_run (s + 1) sOut d p Sym3.O tp hb hd hdp hp
    rw [hb]
    have s1 := reachIn_seq3 (readCarry3 s (s + 1) (s + 2 * d + 3)) (copyArmLeft3 (s + 1) sOut d Sym3.O)
      1 N _ _ _ hrc harm
    exact ⟨1 + N, reachIn_append_left3 _ (copyArmLeft3 (s + 2 * d + 3) sOut d Sym3.I) (1 + N) _ _ s1⟩
  · -- source bit I: the I-lineage copies
    have hrc := readCarry3_run_I s (s + 1) (s + 2 * d + 3) p tp
      (by rw [show readSym3 (s, p, tp) = tp.getD p Sym3.O from rfl, hb]) hp
    obtain ⟨N, harm⟩ := copyArmLeft3_run (s + 2 * d + 3) sOut d p Sym3.I tp hb hd hdp hp
    rw [hb]
    have hrcL := reachIn_append_left3 (readCarry3 s (s + 1) (s + 2 * d + 3)) (copyArmLeft3 (s + 1) sOut d Sym3.O)
      1 _ _ hrc
    have hrcL2 := reachIn_append_left3 (readCarry3 s (s + 1) (s + 2 * d + 3) ++ copyArmLeft3 (s + 1) sOut d Sym3.O)
      (copyArmLeft3 (s + 2 * d + 3) sOut d Sym3.I) 1 _ _ hrcL
    have harmL := reachIn_append_right3 (readCarry3 s (s + 1) (s + 2 * d + 3) ++ copyArmLeft3 (s + 1) sOut d Sym3.O)
      (copyArmLeft3 (s + 2 * d + 3) sOut d Sym3.I) N _ _ harm
    exact ⟨1 + N, (reachIn_add (toNTM3 (copyBitAtDistLeft3 s sOut d)) 1 N _ _).mpr ⟨_, hrcL2, harmL⟩⟩

/-!
**The leftward single-cell copy, proved.**  `copyBitAtDistLeft3` brings a source bit `d` cells to the left, marker-free,
leaving the source and head untouched — the direction apply needs to copy the matched rule's RHS into the configuration.
Next: loop it over a field (the leftward new-state copy), carry the specific rule fields, move the simulated head, and
assemble `apply3` — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyBitLeft

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyBitLeft.copyBitAtDistLeft3_run
