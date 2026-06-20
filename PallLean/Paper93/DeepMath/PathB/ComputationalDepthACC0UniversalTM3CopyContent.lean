import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3CopyFieldLeft

/-!
# Entry 445 — universal-TM-table build: the leftward copier's content `copyBlockLeft_getD_outside/_inside` (proved)

To make the state update home-to-home (and to re-establish the marker invariant after it), we need the content of the
leftward field copier `copyBlockLeft` (entry 415): which cells it changes and to what.  In the disjoint case `m < d`
(destination strictly left of the source, which holds for the state transfer since the rule field is far, `newlen < d'`):

* cells **outside** the destination `[c-d, c+m-d]` are **preserved** (in particular the source `[c, c+m]` and the home
  marker), and
* cells **inside** the destination read the **source** value `tp.getD (k+d) O`.

So if the source is marker-free (a unary field of `I`s and `O`s) the destination is too, and no marker is introduced.

## What is proved (clean axioms, no `sorry`)

* **`copyBlockLeft_getD_outside`** (PROVED) — `m < d → d ≤ c → (k < c-d ∨ c+m-d < k) → (copyBlockLeft tp c d m).getD k O =
  tp.getD k O`.
* **`copyBlockLeft_getD_inside`** (PROVED) — `m < d → d ≤ c → c-d ≤ k → k ≤ c+m-d → (copyBlockLeft tp c d m).getD k O =
  tp.getD (k+d) O`.

## Honest scope

These are the **copier-content** lemmas (disjoint case).  They do **not** by themselves wrap the state update, nor assemble
`EmitsEncodedStep3`.  Building the rest fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyContent

open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 writeAt3 writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyFieldLeft (copyBlockLeft)

/-- **The copier preserves cells outside the destination (PROVED).**  (Disjoint case `m < d`.) -/
theorem copyBlockLeft_getD_outside (tp : List Sym3) (c d m k : ℕ) (hmd : m < d) (hdc : d ≤ c)
    (hk : k < c - d ∨ c + m - d < k) : (copyBlockLeft tp c d m).getD k Sym3.O = tp.getD k Sym3.O := by
  induction m generalizing c tp with
  | zero =>
      show (writeAt3 tp (c - d) (tp.getD c Sym3.O)).getD k Sym3.O = tp.getD k Sym3.O
      rw [writeAt3_getD, if_neg (by omega)]
  | succ m ih =>
      show (copyBlockLeft (writeAt3 tp (c - d) (tp.getD c Sym3.O)) (c + 1) d m).getD k Sym3.O = tp.getD k Sym3.O
      rw [ih (writeAt3 tp (c - d) (tp.getD c Sym3.O)) (c + 1) (by omega) (by omega) (by omega),
        writeAt3_getD, if_neg (by omega)]

/-- **The copier writes the source into the destination (PROVED).**  (Disjoint case `m < d`.) -/
theorem copyBlockLeft_getD_inside (tp : List Sym3) (c d m k : ℕ) (hmd : m < d) (hdc : d ≤ c)
    (hk1 : c - d ≤ k) (hk2 : k ≤ c + m - d) : (copyBlockLeft tp c d m).getD k Sym3.O = tp.getD (k + d) Sym3.O := by
  induction m generalizing c tp with
  | zero =>
      have hke : k = c - d := by omega
      show (writeAt3 tp (c - d) (tp.getD c Sym3.O)).getD k Sym3.O = tp.getD (k + d) Sym3.O
      rw [hke, writeAt3_getD, if_pos rfl, show c - d + d = c from by omega]
  | succ m ih =>
      show (copyBlockLeft (writeAt3 tp (c - d) (tp.getD c Sym3.O)) (c + 1) d m).getD k Sym3.O = tp.getD (k + d) Sym3.O
      rcases Nat.eq_or_lt_of_le hk1 with hke | hklt
      · -- k = c - d: outside the inner copier's destination, recovers the just-written source
        rw [copyBlockLeft_getD_outside (writeAt3 tp (c - d) (tp.getD c Sym3.O)) (c + 1) d m k (by omega) (by omega)
            (by omega), writeAt3_getD, if_pos (by omega), show k + d = c from by omega]
      · -- c - d < k: handled by the inner copier's destination
        rw [ih (writeAt3 tp (c - d) (tp.getD c Sym3.O)) (c + 1) (by omega) (by omega) (by omega) (by omega),
          writeAt3_getD, if_neg (by omega)]

/-!
**The leftward copier's content, proved.**  `copyBlockLeft_getD_outside/_inside` characterise the copier (disjoint case):
outside the destination preserved, inside reads the source.  So a marker-free source yields a marker-free destination.
Next: the home-to-home state update (re-establishing the marker invariant via these), then the master apply and the
matcher↔lookup correspondence toward `EmitsEncodedStep3` — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyContent

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyContent.copyBlockLeft_getD_outside
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyContent.copyBlockLeft_getD_inside
