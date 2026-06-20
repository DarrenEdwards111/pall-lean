import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3CopyFieldLeft

/-!
# Entry 451 — universal-TM-table build: the tape-shift content primitive `copyBlockLeft_getD_*_gen` / `shiftLeftBlock_getD` (proved)

The state update needs a **tape shift** because the state field is unary (`encodeNatBits3`), so changing the state value
changes the field length and the rest of the tape must move.  The shift *machine* already exists: `copyBlockLeft` (the
`copyFieldLeft3` fold, entry 415) with `d ≥ 1` reads each source cell *before* it is overwritten, so it performs a genuine
left shift of `[c, c+m]` into `[c-d, c+m-d]`.  What was missing is its content in the **overlapping** case (entry 445 only
covered the disjoint `m < d`).  Re-examining, the `m < d` hypothesis was never used — so this brick proves the **general**
content (any `d`), giving the shift semantics.

## What is proved (clean axioms, no `sorry`)

* **`copyBlockLeft_getD_outside_gen`** (PROVED) — `d ≤ c → (k < c-d ∨ c+m-d < k) → (copyBlockLeft tp c d m).getD k O =
  tp.getD k O` (any `d`, no `m < d`).
* **`copyBlockLeft_getD_inside_gen`** (PROVED) — `d ≤ c → c-d ≤ k → k ≤ c+m-d → (copyBlockLeft tp c d m).getD k O =
  tp.getD (k+d) O` (any `d`).
* **`shiftLeftBlock_getD`** (PROVED) — the shift specialisation (`d ≥ 1`): the block `[c-d, c+m-d]` reads the source
  shifted left by `d`, everything else unchanged.

## Honest scope

This is the **tape-shift content primitive** (leftward).  The machine is `copyFieldLeft3` (entry 415); rightward shift would
need a `copyBlockRight`.  It does **not** yet assemble the state-update-with-shift, nor `EmitsEncodedStep3`.  Building the
rest fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TapeShift

open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 writeAt3 writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyFieldLeft (copyBlockLeft)

/-- **The copier preserves cells outside the destination — general `d` (PROVED).** -/
theorem copyBlockLeft_getD_outside_gen (tp : List Sym3) (c d m k : ℕ) (hdc : d ≤ c)
    (hk : k < c - d ∨ c + m - d < k) : (copyBlockLeft tp c d m).getD k Sym3.O = tp.getD k Sym3.O := by
  induction m generalizing c tp with
  | zero =>
      show (writeAt3 tp (c - d) (tp.getD c Sym3.O)).getD k Sym3.O = tp.getD k Sym3.O
      rw [writeAt3_getD, if_neg (by omega)]
  | succ m ih =>
      show (copyBlockLeft (writeAt3 tp (c - d) (tp.getD c Sym3.O)) (c + 1) d m).getD k Sym3.O = tp.getD k Sym3.O
      rw [ih (writeAt3 tp (c - d) (tp.getD c Sym3.O)) (c + 1) (by omega) (by omega),
        writeAt3_getD, if_neg (by omega)]

/-- **The copier writes the source into the destination — general `d` (PROVED).** -/
theorem copyBlockLeft_getD_inside_gen (tp : List Sym3) (c d m k : ℕ) (hdc : d ≤ c)
    (hk1 : c - d ≤ k) (hk2 : k ≤ c + m - d) : (copyBlockLeft tp c d m).getD k Sym3.O = tp.getD (k + d) Sym3.O := by
  induction m generalizing c tp with
  | zero =>
      have hke : k = c - d := by omega
      show (writeAt3 tp (c - d) (tp.getD c Sym3.O)).getD k Sym3.O = tp.getD (k + d) Sym3.O
      rw [hke, writeAt3_getD, if_pos rfl, show c - d + d = c from by omega]
  | succ m ih =>
      show (copyBlockLeft (writeAt3 tp (c - d) (tp.getD c Sym3.O)) (c + 1) d m).getD k Sym3.O = tp.getD (k + d) Sym3.O
      rcases Nat.eq_or_lt_of_le hk1 with hke | hklt
      · rw [copyBlockLeft_getD_outside_gen (writeAt3 tp (c - d) (tp.getD c Sym3.O)) (c + 1) d m k (by omega)
            (by omega), writeAt3_getD, if_pos (by omega), show k + d = c from by omega]
      · rw [ih (writeAt3 tp (c - d) (tp.getD c Sym3.O)) (c + 1) (by omega) (by omega) (by omega),
          writeAt3_getD, if_neg (by omega)]

/-- **The left shift (PROVED).**  For `1 ≤ d ≤ c`, `copyBlockLeft tp c d m` is the tape shift: the block `[c-d, c+m-d]`
reads the source shifted left by `d` (`= tp.getD (k+d)`), every other cell unchanged. -/
theorem shiftLeftBlock_getD (tp : List Sym3) (c d m k : ℕ) (_hd : 1 ≤ d) (hdc : d ≤ c) :
    (copyBlockLeft tp c d m).getD k Sym3.O
      = if c - d ≤ k ∧ k ≤ c + m - d then tp.getD (k + d) Sym3.O else tp.getD k Sym3.O := by
  by_cases hcase : c - d ≤ k ∧ k ≤ c + m - d
  · rw [if_pos hcase]; exact copyBlockLeft_getD_inside_gen tp c d m k hdc hcase.1 hcase.2
  · rw [if_neg hcase]; exact copyBlockLeft_getD_outside_gen tp c d m k hdc (by omega)

/-!
**The tape-shift content primitive, proved.**  `copyBlockLeft` is now characterised as a left shift for any `d` (the
`m < d` restriction of entry 445 was never needed).  Combined with the `copyFieldLeft3` machine (entry 415), this is the
tape-shift the state update needs when the unary state field changes length.  Next: assemble the state-update-with-shift,
and the matcher↔lookup correspondence toward `EmitsEncodedStep3` — fragment by verified fragment, not faked.  Not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TapeShift

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TapeShift.shiftLeftBlock_getD
