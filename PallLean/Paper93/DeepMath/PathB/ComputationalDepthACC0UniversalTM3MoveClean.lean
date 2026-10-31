import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Sym

/-!
# Entry 440 — universal-TM-table build: head-move preserves the clean configuration `moveRight/Left_preserves_clean` (proved)

Chaining the home-to-home phases (entry 439) into the master step sequence requires that each phase leaves the tape in the
*same shape* it found it — specifically that the **marker invariant** (home marker fixed, a single head marker, and no
marker strictly between them) persists across a move, so the *next* phase's hypotheses are met.

This brick proves exactly that for the head moves: the tape produced by `headMoveRight3`/`headMoveLeft3` (the moved tape
written by entries 436/437) still satisfies the home-marker / head-marker / clean-window invariant, with the head marker at
its new position.

## What is proved (clean axioms, no `sorry`)

* **`moveRight_preserves_clean`** (PROVED) — from `home < p`, the home marker, a clean window `(home, p)`, and `p+1` a bit:
  the moved tape `writeAt3 (writeAt3 tp p (tp.getD (p+1) O)) (p+1) M` has the home marker at `home`, the head marker at
  `p+1`, and no marker in `(home, p+1)`.
* **`moveLeft_preserves_clean`** (PROVED) — the symmetric statement for the left move, head marker at `p-1`.

## Honest scope

These are the **invariant-preservation** lemmas that let one home-to-home phase feed the next.  They do **not** by
themselves chain the phases, nor assemble the full step / `EmitsEncodedStep3`.  Building those fragment by fragment is the
genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveClean

open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 writeAt3 writeAt3_getD)

/-- **The right move preserves the clean configuration (PROVED).** -/
theorem moveRight_preserves_clean (tp : List Sym3) (home p : ℕ) (hhp : home < p)
    (hmarkHome : tp.getD home Sym3.O = Sym3.M) (hclean : ∀ j, home < j → j < p → tp.getD j Sym3.O ≠ Sym3.M)
    (hc : tp.getD (p + 1) Sym3.O = Sym3.O ∨ tp.getD (p + 1) Sym3.O = Sym3.I) :
    (writeAt3 (writeAt3 tp p (tp.getD (p + 1) Sym3.O)) (p + 1) Sym3.M).getD home Sym3.O = Sym3.M ∧
    (writeAt3 (writeAt3 tp p (tp.getD (p + 1) Sym3.O)) (p + 1) Sym3.M).getD (p + 1) Sym3.O = Sym3.M ∧
    (∀ j, home < j → j < p + 1 →
      (writeAt3 (writeAt3 tp p (tp.getD (p + 1) Sym3.O)) (p + 1) Sym3.M).getD j Sym3.O ≠ Sym3.M) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [writeAt3_getD, if_neg (by omega), writeAt3_getD, if_neg (by omega)]; exact hmarkHome
  · rw [writeAt3_getD, if_pos rfl]
  · intro j hj1 hj2
    rcases Nat.lt_or_ge j p with hlt | hge
    · rw [writeAt3_getD, if_neg (by omega), writeAt3_getD, if_neg (by omega)]
      exact hclean j hj1 hlt
    · have hjp : j = p := by omega
      rw [hjp, writeAt3_getD, if_neg (by omega), writeAt3_getD, if_pos rfl]
      rcases hc with hb | hb <;> rw [hb] <;> decide

/-- **The left move preserves the clean configuration (PROVED).** -/
theorem moveLeft_preserves_clean (tp : List Sym3) (home p : ℕ) (hhp : home + 2 ≤ p)
    (hmarkHome : tp.getD home Sym3.O = Sym3.M) (hclean : ∀ j, home < j → j < p → tp.getD j Sym3.O ≠ Sym3.M) :
    (writeAt3 (writeAt3 tp p (tp.getD (p - 1) Sym3.O)) (p - 1) Sym3.M).getD home Sym3.O = Sym3.M ∧
    (writeAt3 (writeAt3 tp p (tp.getD (p - 1) Sym3.O)) (p - 1) Sym3.M).getD (p - 1) Sym3.O = Sym3.M ∧
    (∀ j, home < j → j < p - 1 →
      (writeAt3 (writeAt3 tp p (tp.getD (p - 1) Sym3.O)) (p - 1) Sym3.M).getD j Sym3.O ≠ Sym3.M) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [writeAt3_getD, if_neg (by omega), writeAt3_getD, if_neg (by omega)]; exact hmarkHome
  · rw [writeAt3_getD, if_pos rfl]
  · intro j hj1 hj2
    rw [writeAt3_getD, if_neg (by omega), writeAt3_getD, if_neg (by omega)]
    exact hclean j hj1 (by omega)

/-!
**Head moves preserve the clean configuration, proved.**  After a move the marker invariant persists with the head marker
relocated — so one home-to-home phase's output meets the next phase's hypotheses.  Next: chain phases into the master step
sequence, and connect to the abstract step toward `EmitsEncodedStep3` — fragment by verified fragment, not faked.  Not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveClean

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveClean.moveRight_preserves_clean
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveClean.moveLeft_preserves_clean
