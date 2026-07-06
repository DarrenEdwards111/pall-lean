import Mathlib

/-!
# N-Frame: parity rank-completion SCOUT — the mod-2 detection core

SCOUT FILE for the `sat3X⊕` route (task 5.3; see `PROBE_PORT_FAMILY.md`).  The kernel-form
statements of the parity rank-completion lemma, kept deliberately elementary: functionals are
concrete `F₂` dot products, "free direction" means a constraint-preserving shift vector, and
rank/duality stay on paper.  These are the exact counting facts the `sat3X⊕` eval layer will
instantiate: an affine system's solution count is odd iff the system is consistent with full
rank, so a target literal flips the parity from 0 to 1 exactly when it removes the LAST free
direction — for BOTH values of the literal (the value-independence that defeats the
parity-locked refuge).

  `slice_card_eq` — **PROVED (SLICE)**: a constraint-preserving direction `w` with
        `⟨l, w⟩ = 1` makes the two `l`-slices of the solution set equinumerous.
  `count_even_of_free_direction` — **PROVED (EVEN)**: any surviving free direction forces an
        even solution count — the ⊕-eraser, which detection turns into the baseline signal.
  `count_odd_of_unique` — **PROVED (ODD)**: a unique solution gives count 1.
  `parity_flip` — **PROVED (FLIP)**: solutions `= {a₀, a₀ + w}` and `⟨l*, w⟩ = 1` give an
        even count without the target literal and an odd sliced count WITH it, for both
        slice values.

## Honest scope

Counting facts over `F₂` only — no circuit content.  They become load-bearing through the
`sat3X⊕` eval layer (kit-neutralized blocks + unit-clause pins collapse the family's value to
exactly these counts; see the task-3c audit).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout

open Finset

variable {v : ℕ}

/-- The concrete `F₂` pairing: functional `l` applied to point `a`. -/
def dotp (l a : Fin v → ZMod 2) : ZMod 2 := ∑ i, l i * a i

theorem dotp_add_right (l a w : Fin v → ZMod 2) :
    dotp l (a + w) = dotp l a + dotp l w := by
  unfold dotp
  simp only [Pi.add_apply, mul_add]
  exact Finset.sum_add_distrib

theorem add_self_cancel (w : Fin v → ZMod 2) : w + w = 0 := by
  funext i
  show w i + w i = 0
  have h2 : (2 : ZMod 2) = 0 := by decide
  calc w i + w i = 2 * w i := by ring
    _ = 0 := by rw [h2, zero_mul]

/-- **SLICE (proved)**: a constraint-preserving direction `w` with `⟨l, w⟩ = 1` makes the two
`l`-slices of the solution set equinumerous. -/
theorem slice_card_eq (P : (Fin v → ZMod 2) → Prop) [DecidablePred P]
    (w : Fin v → ZMod 2) (hshift : ∀ a, P a ↔ P (a + w))
    (l : Fin v → ZMod 2) (hlw : dotp l w = 1) (c : ZMod 2) :
    (Finset.univ.filter (fun a => P a ∧ dotp l a = c)).card
      = (Finset.univ.filter (fun a => P a ∧ dotp l a = c + 1)).card := by
  classical
  apply Finset.card_bij (fun a _ => a + w)
  · intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, (hshift a).mp ha.2.1, ?_⟩
    rw [dotp_add_right, ha.2.2, hlw]
  · intro a _ a' _ h
    have h' := congrArg (fun x => x + w) h
    simpa [add_assoc, add_self_cancel] using h'
  · intro b hb
    rw [Finset.mem_filter] at hb
    refine ⟨b + w, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, (hshift (b + w)).mpr ?_, ?_⟩
      · rw [add_assoc, add_self_cancel, add_zero]
        exact hb.2.1
      · rw [dotp_add_right, hb.2.2, hlw]
        have h11 : (1 : ZMod 2) + 1 = 0 := by decide
        rw [add_assoc, h11, add_zero]
    · rw [add_assoc, add_self_cancel, add_zero]

/-- **EVEN (proved)**: any surviving free direction forces an even solution count. -/
theorem count_even_of_free_direction (P : (Fin v → ZMod 2) → Prop) [DecidablePred P]
    (w : Fin v → ZMod 2) (hshift : ∀ a, P a ↔ P (a + w))
    (l : Fin v → ZMod 2) (hlw : dotp l w = 1) :
    (Finset.univ.filter P).card % 2 = 0 := by
  classical
  have hval : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hsplit : Finset.univ.filter P
      = (Finset.univ.filter (fun a => P a ∧ dotp l a = 0))
        ∪ (Finset.univ.filter (fun a => P a ∧ dotp l a = 1)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    constructor
    · intro h
      rcases hval (dotp l a) with h0 | h1
      · exact Or.inl ⟨h, h0⟩
      · exact Or.inr ⟨h, h1⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  have hdisj : Disjoint
      (Finset.univ.filter (fun a => P a ∧ dotp l a = 0))
      (Finset.univ.filter (fun a => P a ∧ dotp l a = 1)) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    rw [Finset.mem_filter] at ha hb
    have h01 := ha.2.2.symm.trans hb.2.2
    exact absurd h01 (by decide)
  have hslice := slice_card_eq P w hshift l hlw 0
  simp only [zero_add] at hslice
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  omega

/-- **ODD (proved)**: a unique solution gives count 1. -/
theorem count_odd_of_unique (P : (Fin v → ZMod 2) → Prop) [DecidablePred P]
    (a₀ : Fin v → ZMod 2) (h : ∀ a, P a ↔ a = a₀) :
    (Finset.univ.filter P).card % 2 = 1 := by
  classical
  have hf : Finset.univ.filter P = {a₀} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact h a
  rw [hf, Finset.card_singleton]

/-- **THE PARITY FLIP (proved, composed)**: if the block system's solutions are exactly the
two points of one last free direction and the target functional splits it, the count is EVEN
without the target literal and ODD with it — for BOTH values `b`.  Value-independence is the
property that defeats the parity-locked refuge. -/
theorem parity_flip (P : (Fin v → ZMod 2) → Prop) [DecidablePred P]
    (w a₀ : Fin v → ZMod 2)
    (hsol : ∀ a, P a ↔ (a = a₀ ∨ a = a₀ + w))
    (l : Fin v → ZMod 2) (hlw : dotp l w = 1) (b : ZMod 2) :
    (Finset.univ.filter P).card % 2 = 0
    ∧ (Finset.univ.filter (fun a => P a ∧ dotp l a = b)).card % 2 = 1 := by
  classical
  have hwne : w ≠ 0 := by
    intro hw0
    rw [hw0] at hlw
    have hd0 : dotp l (0 : Fin v → ZMod 2) = 0 := by
      unfold dotp
      simp
    rw [hd0] at hlw
    exact absurd hlw (by decide)
  have hne : a₀ ≠ a₀ + w := by
    intro hc
    have hc' : a₀ + 0 = a₀ + w := by
      rw [add_zero]
      exact hc
    exact hwne (add_left_cancel hc').symm
  have hdiff : dotp l (a₀ + w) = dotp l a₀ + 1 := by
    rw [dotp_add_right, hlw]
  constructor
  · have hf : Finset.univ.filter P = {a₀, a₀ + w} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact hsol a
    rw [hf, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  · have hkey : ∀ x y : ZMod 2, x ≠ y → x + 1 = y := by decide
    have h10 : ∀ y : ZMod 2, ¬ (y + 1 = y) := by decide
    by_cases hb0 : dotp l a₀ = b
    · have hf : Finset.univ.filter (fun a => P a ∧ dotp l a = b) = {a₀} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨hPa, hda⟩
          rcases (hsol a).mp hPa with h | h
          · exact h
          · exfalso
            rw [h, hdiff, hb0] at hda
            exact h10 b hda
        · intro h
          rw [h]
          exact ⟨(hsol a₀).mpr (Or.inl rfl), hb0⟩
      rw [hf, Finset.card_singleton]
    · have hb1 : dotp l (a₀ + w) = b := by
        rw [hdiff]
        exact hkey _ _ hb0
      have hf : Finset.univ.filter (fun a => P a ∧ dotp l a = b) = {a₀ + w} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨hPa, hda⟩
          rcases (hsol a).mp hPa with h | h
          · exfalso
            rw [h] at hda
            exact hb0 hda
          · exact h
        · intro h
          rw [h]
          exact ⟨(hsol (a₀ + w)).mpr (Or.inr rfl), hb1⟩
      rw [hf, Finset.card_singleton]

end PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout.slice_card_eq
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout.count_even_of_free_direction
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout.count_odd_of_unique
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout.parity_flip
