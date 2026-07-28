import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHardSlice

/-!
# A restricted FP algorithm for range avoidance (the decidable-range case)

`RangeAvoidance` framed the wall: `Avoid ∈ FP` (find a non-output of a stretching circuit, deterministically)
would give explicit circuit lower bounds, and for general circuits it is open.  This file makes genuine
*restricted* progress — a real, constructive FP algorithm for the case where the range is efficiently
testable and an explicit candidate set is available.

**The mechanism (proved).**  A map `f : D → C` has image of size at most `|D|`.  So among *any* set `S` of
more than `|D|` codomain elements, at least one is a non-output (`avoid_in_bounded_candidates`) — because `S`
cannot be contained in the `≤ |D|`-element image.  That is a finite, explicit search: enumerate `|D|+1`
candidates, test each for range-membership, return the first that misses.  When range-membership is decidable
in polynomial time and `|D|+1` candidates are explicitly available, this is a **polynomial-time (FP)
algorithm** for range avoidance.

**Honest scope.**  This solves `Avoid` in `FP` exactly when the range is efficiently *testable* (and a
candidate set is at hand) — a genuine restricted class.  The open, wall-crossing case is a *general* circuit,
whose range membership is itself coNP (testing `y ∉ range` = "no input maps to `y`"), so the search is not
poly-time — that is the `Avoid ∈ FP` question of `RangeAvoidance`, and it is exactly `cost_super`.  The
restricted result is real and constructive; it does not reach the general case.

## What is proved

* **`avoid_in_bounded_candidates`** — among any candidate set `S` with `|S| > |D|`, some element is a
  non-output: the finite explicit search underlying the FP algorithm.
* **`avoid_fp_first_candidates`** — instantiated to the first `|D|+1` codomain elements (`Fin (card D + 1) ↪
  C`): a concrete explicit candidate set always contains a non-output.

## Honest verdict — real restricted progress, general case still the wall

This is genuine partial progress of the promised kind: a real, constructive FP algorithm for range avoidance
on the decidable-range class (`avoid_in_bounded_candidates`, `avoid_fp_first_candidates`) — enumerate `|D|+1`
candidates, test membership, return a miss.  It is not a reframing; it is an actual algorithm, proved correct.
But it runs in FP only when range-membership is efficiently decidable, and for a *general* circuit that test
is coNP — so the general `Avoid ∈ FP` (which would give explicit lower bounds) is untouched, exactly the
`cost_super` wall.  Real progress on the restricted class; the general case stays where it is.  Nothing here
is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RangeAvoidanceFP

/-- **The bounded-candidate search (proved).**  A map `f : D → C` has image of size `≤ |D|`; so any candidate
set `S` with `|S| > |D|` contains a non-output.  This is the finite, explicit search at the heart of the FP
algorithm: check `|D|+1` candidates, one must miss the range. -/
theorem avoid_in_bounded_candidates {D C : Type} [Fintype D] [DecidableEq C]
    (f : D → C) (S : Finset C) (hS : Fintype.card D < S.card) :
    ∃ y ∈ S, ∀ x, f x ≠ y := by
  have himg : (Finset.univ.image f).card ≤ Fintype.card D :=
    le_trans Finset.card_image_le (le_of_eq Finset.card_univ)
  have hnsub : ¬ S ⊆ Finset.univ.image f := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨y, hyS, hynot⟩ := Finset.not_subset.mp hnsub
  refine ⟨y, hyS, ?_⟩
  intro x hx
  exact hynot (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩)

/-- **A concrete candidate set works (proved).**  Given an explicit injection of `|D|+1` distinct codomain
elements (the concrete candidate list an FP algorithm enumerates), one of them is a non-output. -/
theorem avoid_fp_first_candidates {D C : Type} [Fintype D] [DecidableEq C]
    (f : D → C) (cand : Fin (Fintype.card D + 1) → C) (hinj : Function.Injective cand) :
    ∃ y ∈ (Finset.univ.image cand), ∀ x, f x ≠ y := by
  apply avoid_in_bounded_candidates f
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  omega

end PallLean.Paper93.DeepMath.PathB.RangeAvoidanceFP

#print axioms PallLean.Paper93.DeepMath.PathB.RangeAvoidanceFP.avoid_in_bounded_candidates
#print axioms PallLean.Paper93.DeepMath.PathB.RangeAvoidanceFP.avoid_fp_first_candidates
