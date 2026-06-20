import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Sym

/-!
# Entry 477 — generic scan loop: in-bounds tape-write algebra `writeAt3_eq_set` / `_overwrite` / `_comm` (proved)

The two-cursor comparison iterates `tandemStep3` (entry 476), whose output is a nested `writeAt3` expression; iterating it
requires simplifying such expressions (overwriting the same cell, commuting writes at distinct cells).  In bounds, `writeAt3`
adds no padding and coincides with `List.set`, so the standard `List.set` algebra applies.  This brick provides exactly that
reusable algebra.

## What is proved (clean axioms, no `sorry`)

* **`writeAt3_eq_set`** (PROVED) — `p < t.length → writeAt3 t p w = t.set p w` (in bounds, `writeAt3` is `List.set`).
* **`writeAt3_overwrite`** (PROVED) — `p < t.length → writeAt3 (writeAt3 t p a) p b = writeAt3 t p b` (last write wins).
* **`writeAt3_comm`** (PROVED) — `p ≠ q → p < t.length → q < t.length → writeAt3 (writeAt3 t p a) q b = writeAt3 (writeAt3
  t q b) p a` (writes at distinct cells commute).

## Honest scope

This is **reusable tape-write algebra** for assembling the comparison iteration.  It does **not** itself build the iteration,
the comparison, the generic apply, nor a fixed `U` / `EmitsEncodedStepEx3`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteAlg

open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 writeAt3)

/-- **In bounds, `writeAt3` is `List.set` (PROVED).** -/
theorem writeAt3_eq_set (t : List Sym3) (p : ℕ) (w : Sym3) (hp : p < t.length) :
    writeAt3 t p w = t.set p w := by
  unfold writeAt3
  rw [Nat.sub_eq_zero_of_le (by omega : p + 1 ≤ t.length)]
  simp

/-- **Overwriting the same cell keeps the last write (PROVED).** -/
theorem writeAt3_overwrite (t : List Sym3) (p : ℕ) (a b : Sym3) (hp : p < t.length) :
    writeAt3 (writeAt3 t p a) p b = writeAt3 t p b := by
  have hp' : p < (t.set p a).length := by rw [List.length_set]; exact hp
  rw [writeAt3_eq_set t p a hp, writeAt3_eq_set (t.set p a) p b hp', writeAt3_eq_set t p b hp, List.set_set]

/-- **Writes at distinct cells commute (PROVED).** -/
theorem writeAt3_comm (t : List Sym3) (p q : ℕ) (a b : Sym3) (hpq : p ≠ q) (hp : p < t.length) (hq : q < t.length) :
    writeAt3 (writeAt3 t p a) q b = writeAt3 (writeAt3 t q b) p a := by
  have hq' : q < (t.set p a).length := by rw [List.length_set]; exact hq
  have hp' : p < (t.set q b).length := by rw [List.length_set]; exact hp
  rw [writeAt3_eq_set t p a hp, writeAt3_eq_set t q b hq, writeAt3_eq_set (t.set p a) q b hq',
    writeAt3_eq_set (t.set q b) p a hp']
  exact List.set_comm a b hpq

/-!
**The in-bounds tape-write algebra, proved.**  In bounds, `writeAt3` is `List.set`, so overwrites collapse and distinct
writes commute — the algebra needed to iterate the tandem comparison step.  Next: iterate `tandemStep3` (induction), then the
four-way end-branch — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteAlg

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteAlg.writeAt3_eq_set
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteAlg.writeAt3_comm
