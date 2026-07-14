import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinDeleteShift

/-!
# Cook–Levin M1 — the `read a_v` outer-loop algorithm, proved correct

**Correction to an earlier claim.**  I called the outer `v`-round loop "pure orchestration."  That was wrong.
Assembling the inner pieces into one *halting* Boolean-tape machine has a genuine obstacle: the model has **no
end-of-input or head-position detection** (past-input reads `false`, and moving left at `0` stays at `0`).  So each
delete/shift has a real **termination** problem (where does it stop?), and the loop control ("front is the
separator ⇒ done") needs position detection.  That is not orchestration — it needs an end-marker in the encoding or
explicit on-tape counters.  Honest.

What *is* cleanly provable — and is the mathematical heart of the loop — is the **algorithm's correctness**: that
iterating the round (delete the leading counter cell, delete `a_0`) actually brings `a_v` to a fixed position.
Combined with `DeleteShift.run_shift` (each delete is a correct left-shift), this proves the `read a_v` *algorithm*
is correct; only the single-machine sequencing+termination (needing position/end detection) remains.

`readAv_spec`: on `1ᵛ 0 a_0 a_1 …`, iterating `roundStep` `v` times lands the tape with `a_v` at position `1`
(right after the separator), so a final read there returns `a_v = assignment.getD v`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinReadAv

/-- Remove the assignment cell just right of the separator: `1ʲ 0 a rest ↦ 1ʲ 0 rest`. -/
def afterSep : List Bool → List Bool
  | true :: rest => true :: afterSep rest
  | false :: _ :: rest => false :: rest
  | L => L

/-- One round: delete the leading counter `1`, then delete `a_0` (the cell after the separator). -/
def roundStep : List Bool → List Bool
  | true :: rest => afterSep rest
  | L => L

/-- `afterSep` deletes exactly the cell after the separator, past the counter block. -/
theorem afterSep_replicate (j : ℕ) (L : List Bool) :
    afterSep (List.replicate j true ++ false :: L) = List.replicate j true ++ false :: L.drop 1 := by
  induction j with
  | zero =>
    simp only [List.replicate_zero, List.nil_append]
    cases L with
    | nil => rfl
    | cons a rest => rfl
  | succ j ih =>
    have h1 : List.replicate (j + 1) true ++ false :: L
        = true :: (List.replicate j true ++ false :: L) := by simp [List.replicate_succ]
    rw [h1]
    simp only [afterSep]
    rw [ih]
    simp [List.replicate_succ]

/-- **Each round decrements the counter and advances the assignment by one.**  Iterating `v` rounds on
`1ᵛ 0 assignment` yields `0 (assignment.drop v)`. -/
theorem roundStep_iterate (v : ℕ) (assignment : List Bool) :
    roundStep^[v] (List.replicate v true ++ false :: assignment) = false :: assignment.drop v := by
  induction v generalizing assignment with
  | zero => simp
  | succ v ih =>
    rw [Function.iterate_succ_apply]
    have h1 : List.replicate (v + 1) true ++ false :: assignment
        = true :: (List.replicate v true ++ false :: assignment) := by simp [List.replicate_succ]
    rw [h1]
    simp only [roundStep]
    rw [afterSep_replicate, ih]
    congr 1
    rw [List.drop_drop]
    congr 1
    omega

/-- **The `read a_v` algorithm is correct.**  After `v` rounds the tape has `a_v` at position `1`; reading it
returns `assignment.getD v false = a_v`. -/
theorem readAv_spec (v : ℕ) (assignment : List Bool) :
    (roundStep^[v] (List.replicate v true ++ false :: assignment)).getD 1 false
      = assignment.getD v false := by
  rw [roundStep_iterate, List.getD_cons_succ,
    List.getD_eq_getElem?_getD, List.getElem?_drop, List.getD_eq_getElem?_getD]
  congr 2

end PallLean.Paper93.DeepMath.PathB.CookLevinReadAv
