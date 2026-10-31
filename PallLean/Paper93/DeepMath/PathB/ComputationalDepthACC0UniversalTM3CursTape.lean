import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3TandemStep
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3WriteAlg

/-!
# Entry 478 — generic scan loop: the canonical comparison tape `cursTape` and one canonical step (proved)

To iterate the tandem comparison step (`tandemStep3`, entry 476), the evolving tape is kept in a **canonical form**: the
base tape `tp` (all `I` in the two fields) with the config cursor `M` at `cp+i` and the record cursor `M` at `cp+g+i`.  This
brick fixes that form and proves its cell-value lemmas (used to discharge `tandemStep3`'s hypotheses at each step).

`cursTape tp cp g i := writeAt3 (writeAt3 tp (cp+i) M) (cp+g+i) M`.

## What is proved (clean axioms, no `sorry`)

* **`cursTape tp cp g i`** — the canonical comparison tape.
* **`cursTape_cursorL`/`_cursorR`/`_other`/`_length`** (PROVED) — its cell values: `M` at the two cursors, `= tp`
  elsewhere, length preserved (in bounds).

## Honest scope

This is the **canonical comparison tape** with its cell-value lemmas.  It does **not** yet prove one canonical step (the
nested-write collapse), the iterated loop (induction), the four-way end-branch,
the symbol compare, the match-or-advance branch, the generic apply, nor a fixed `U` / `EmitsEncodedStepEx3`.  Building those
fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CursTape

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 writeAt3 toNTM3 writeAt3_getD writeAt3_id_of_lt)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TandemStep (tandemStep3 tandemStep3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteAlg (writeAt3_eq_set writeAt3_overwrite writeAt3_comm)

/-- **The canonical comparison tape.**  Base `tp` with the config cursor at `cp+i` and the record cursor at `cp+g+i`. -/
def cursTape (tp : List Sym3) (cp g i : ℕ) : List Sym3 :=
  writeAt3 (writeAt3 tp (cp + i) Sym3.M) (cp + g + i) Sym3.M

private theorem wlen (t : List Sym3) (p : ℕ) (w : Sym3) (hp : p < t.length) :
    (writeAt3 t p w).length = t.length := by
  rw [writeAt3_eq_set t p w hp, List.length_set]

theorem cursTape_length (tp : List Sym3) (cp g i : ℕ) (hi : cp + g + i < tp.length) (hg : 1 ≤ g) :
    (cursTape tp cp g i).length = tp.length := by
  rw [cursTape, wlen _ _ _ (by rw [wlen _ _ _ (by omega)]; omega), wlen _ _ _ (by omega)]

theorem cursTape_cursorL (tp : List Sym3) (cp g i : ℕ) (hg : 1 ≤ g) :
    (cursTape tp cp g i).getD (cp + i) Sym3.O = Sym3.M := by
  rw [cursTape, writeAt3_getD, if_neg (by omega), writeAt3_getD, if_pos rfl]

theorem cursTape_cursorR (tp : List Sym3) (cp g i : ℕ) :
    (cursTape tp cp g i).getD (cp + g + i) Sym3.O = Sym3.M := by
  rw [cursTape, writeAt3_getD, if_pos rfl]

theorem cursTape_other (tp : List Sym3) (cp g i x : ℕ) (h1 : x ≠ cp + i) (h2 : x ≠ cp + g + i) :
    (cursTape tp cp g i).getD x Sym3.O = tp.getD x Sym3.O := by
  rw [cursTape, writeAt3_getD, if_neg h2, writeAt3_getD, if_neg h1]

/-!
**The canonical comparison tape, proved.**  `cursTape` packages the two-cursor comparison state (config cursor at `cp+i`,
record cursor at `cp+g+i`), with its cell-value lemmas.  Next: prove one tandem step (`tandemStep3`, 476) maps `cursTape i`
to `cursTape (i+1)` (collapsing the nested writes via the 477 algebra), then iterate it — fragment by verified fragment, not
faked.  Not a separation.
-/
end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CursTape

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CursTape.cursTape_cursorL
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CursTape.cursTape_other
