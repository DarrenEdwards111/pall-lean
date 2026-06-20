import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Sym

/-!
# Entry 452 — universal-TM-table build: the rightward tape-shift content `copyBlockRight` / `shiftRightBlock_getD` (proved)

The dual of entry 451, for the state-*growth* case (`newlen > oldlen`): a **rightward** shift.  The existing left-to-right
copier `copyBlock` (entry 412) clobbers on an overlapping right shift (it overwrites a source cell before reading it), so a
genuine right shift must copy **high-to-low**.  This brick defines that right-to-low fold `copyBlockRight` and proves its
content: the block `[c+d, c+m+d]` reads the source shifted right by `d`, every other cell unchanged.

(This is the list-level content of the shift — the math object the state-growth update needs.  The right-to-left *machine*
realising it is a separate build; this characterises the target tape.)

## What is proved (clean axioms, no `sorry`)

* **`copyBlockRight tp c d m`** — the high-to-low fold: write cell `c+m` to `c+m+d`, then recurse on the lower block.
* **`copyBlockRight_getD_outside`** (PROVED) — `1 ≤ d → (k < c+d ∨ c+m+d < k) → (copyBlockRight tp c d m).getD k O =
  tp.getD k O`.
* **`copyBlockRight_getD_inside`** (PROVED) — `1 ≤ d → c+d ≤ k → k ≤ c+m+d → (copyBlockRight tp c d m).getD k O =
  tp.getD (k-d) O`.
* **`shiftRightBlock_getD`** (PROVED) — the shift specialisation.

## Honest scope

This is the **rightward tape-shift content** (list level).  The realising machine is **not built here** (it needs a
right-to-left copy TM, the dual of `copyFieldLeft3`).  It does **not** assemble the state-growth update nor
`EmitsEncodedStep3`.  Building the rest fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TapeShiftRight

open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 writeAt3 writeAt3_getD)

/-- **The rightward shift tape** (high-to-low fold).  Copies cells `c … c+m` to `c+d … c+m+d`, highest first. -/
def copyBlockRight (tp : List Sym3) (c d : ℕ) : ℕ → List Sym3
  | 0 => writeAt3 tp (c + d) (tp.getD c Sym3.O)
  | (m + 1) => copyBlockRight (writeAt3 tp (c + m + 1 + d) (tp.getD (c + m + 1) Sym3.O)) c d m

/-- **The rightward copier preserves cells outside the destination (PROVED).** -/
theorem copyBlockRight_getD_outside (tp : List Sym3) (c d m k : ℕ) (_hd : 1 ≤ d)
    (hk : k < c + d ∨ c + m + d < k) : (copyBlockRight tp c d m).getD k Sym3.O = tp.getD k Sym3.O := by
  induction m generalizing tp with
  | zero =>
      show (writeAt3 tp (c + d) (tp.getD c Sym3.O)).getD k Sym3.O = tp.getD k Sym3.O
      rw [writeAt3_getD, if_neg (by omega)]
  | succ m ih =>
      show (copyBlockRight (writeAt3 tp (c + m + 1 + d) (tp.getD (c + m + 1) Sym3.O)) c d m).getD k Sym3.O
        = tp.getD k Sym3.O
      rw [ih (writeAt3 tp (c + m + 1 + d) (tp.getD (c + m + 1) Sym3.O)) (by omega), writeAt3_getD, if_neg (by omega)]

/-- **The rightward copier writes the source into the destination (PROVED).** -/
theorem copyBlockRight_getD_inside (tp : List Sym3) (c d m k : ℕ) (hd : 1 ≤ d)
    (hk1 : c + d ≤ k) (hk2 : k ≤ c + m + d) : (copyBlockRight tp c d m).getD k Sym3.O = tp.getD (k - d) Sym3.O := by
  induction m generalizing tp with
  | zero =>
      have hke : k = c + d := by omega
      show (writeAt3 tp (c + d) (tp.getD c Sym3.O)).getD k Sym3.O = tp.getD (k - d) Sym3.O
      rw [hke, writeAt3_getD, if_pos rfl, show c + d - d = c from by omega]
  | succ m ih =>
      show (copyBlockRight (writeAt3 tp (c + m + 1 + d) (tp.getD (c + m + 1) Sym3.O)) c d m).getD k Sym3.O
        = tp.getD (k - d) Sym3.O
      rcases Nat.lt_or_ge k (c + m + 1 + d) with hklt | hkge
      · -- k ≤ c+m+d: inside the inner block, source unchanged by the high write
        rw [ih (writeAt3 tp (c + m + 1 + d) (tp.getD (c + m + 1) Sym3.O)) (by omega),
          writeAt3_getD, if_neg (by omega)]
      · -- k = c+m+1+d: the highest cell, written this step, recovers the source
        have hke : k = c + m + 1 + d := by omega
        rw [copyBlockRight_getD_outside (writeAt3 tp (c + m + 1 + d) (tp.getD (c + m + 1) Sym3.O)) c d m k hd
            (by omega), hke, writeAt3_getD, if_pos rfl, show c + m + 1 + d - d = c + m + 1 from by omega]

/-- **The right shift (PROVED).**  For `1 ≤ d`, `copyBlockRight tp c d m` is the tape shift: the block `[c+d, c+m+d]`
reads the source shifted right by `d` (`= tp.getD (k-d)`), every other cell unchanged. -/
theorem shiftRightBlock_getD (tp : List Sym3) (c d m k : ℕ) (hd : 1 ≤ d) :
    (copyBlockRight tp c d m).getD k Sym3.O
      = if c + d ≤ k ∧ k ≤ c + m + d then tp.getD (k - d) Sym3.O else tp.getD k Sym3.O := by
  by_cases hcase : c + d ≤ k ∧ k ≤ c + m + d
  · rw [if_pos hcase]; exact copyBlockRight_getD_inside tp c d m k hd hcase.1 hcase.2
  · rw [if_neg hcase]; exact copyBlockRight_getD_outside tp c d m k hd (by omega)

/-!
**The rightward tape-shift content, proved.**  `copyBlockRight` (the high-to-low fold) is characterised as a right shift —
the math object the state-growth update needs.  Next: the right-to-left machine realising it, the state-update-with-shift,
and the matcher↔lookup correspondence toward `EmitsEncodedStep3` — fragment by verified fragment, not faked.  Not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TapeShiftRight

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TapeShiftRight.shiftRightBlock_getD
