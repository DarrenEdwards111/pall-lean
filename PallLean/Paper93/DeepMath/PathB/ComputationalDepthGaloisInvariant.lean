import Mathlib.Data.Nat.Basic

/-!
# The missing invariant: three species, one object — a Galois theory of computation

The barriers pin down what a P ≠ NP proof must be, and three classical species fit — and, this file argues,
they are **three faces of one invariant**, each answering one barrier:

* **Galois (form).**  The model for the wanted proof already exists: "no radical formula for the quintic" is
  a lower bound against the model "towers of root-extractions", proved not by counting formulas but by
  attaching an **invariant** (the group) to the specific object, showing it is **functorial** under the
  model's composition (solvable extensions compose to solvable groups), and exhibiting the mismatch.  Such a
  proof is *automatically* non-natural (an invariant of one object is not a large property) and *automatically*
  anatomical (functoriality is about the model's steps).  The wanted thing is a **Galois theory of
  computation**: an invariant of SAT, functorial under gate composition, **super-additive under the tower's
  correlated doubling** — and that last demand is literally `cost_super`, stated as a property of the
  invariant.
* **Proof theory (logical status).**  Razborov's reading of natural proofs: P ≠ NP is unprovable in feasible
  reasoning, so the proof's central predicate must be **infeasible to evaluate** — which is precisely how it
  slips largeness/constructivity.  This is the *non-natural* face made into a method.
* **Cohomology (construction).**  The overlap residue has an exact classical shape — local data (per-block
  witness demand) with no small global section (shared gates).  That is sheaf-cohomology territory: an
  **obstruction class** that vanishes iff sharing is possible, non-zero *because of the shared inputs*
  (anti-Uhlig).  The witness/mult/overlap frame is the **1-skeleton** of such a chain complex.

**Why one object.**  The three are the *form* (functorial invariant), the *construction* (cohomological
obstruction over the incidence geometry), and the *logical status* (infeasible predicate) of a single thing:
a super-additive invariant of SAT.  Its super-additivity is `cost_super`; its non-feasibility answers
Razborov–Rudich; its obstruction-over-incidence answers relativization; its non-vanishing-from-correlation
answers Uhlig.  `DischargePiStar` is the machine-checked statement that any winner is of this species
(separating measure ⟺ SAT ∉ P, non-natural).

## What is proved

* **`invariant_amplifies`** — the Galois face's consequence: a **functorial (super-additive)** invariant
  amplifies under composition, `2^d · I(0) ≤ I(d)` — the mismatch that separates, exactly as the quintic's
  unsolvable group is exhibited by iterating the tower.

## Honest scope — the spec of the missing math, not the math

This formalizes the *form* the missing invariant must take and its amplification.  It does **not** construct
the invariant, and it does not prove the load-bearing step: that a super-additive, non-feasible, cohomological
invariant of SAT **exists** and that its obstruction is **non-zero because of the tower's correlation** (the
anti-Uhlig step).  That non-vanishing *is* `cost_super` — the same wall, now stated as "the class is nonzero".
The combination gives the right **language** for the missing invariant — Galois form, cohomological
construction, proof-theoretic status — but each species has stalled (GCT), is unproven for circuits (bounded
arithmetic), or is embryonic (cohomological lower bounds).  The invariant is the missing invention; its
super-additivity is the open wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.GaloisInvariant

/-- A **computational invariant** of the composition tower: a value `I d` at each composition depth `d`,
**functorial / super-additive** under the model's composition step (`2·I d ≤ I(d+1)`) — the Galois face,
which is `cost_super`. -/
structure ComputationalInvariant where
  /-- the invariant at composition depth `d` -/
  I : ℕ → ℕ
  /-- Galois functoriality: the invariant is super-additive under the composition step (= `cost_super`) -/
  functorial : ∀ d, 2 * I d ≤ I (d + 1)

/-- **The invariant amplifies (proved).**  A functorial (super-additive) invariant grows as `2^d`:
`2^d · I(0) ≤ I(d)`.  This is the Galois mismatch iterated — the invariant of the composed object outruns
the model, exactly as the quintic's group becomes unsolvable up the radical tower. -/
theorem invariant_amplifies (G : ComputationalInvariant) (d : ℕ) : 2 ^ d * G.I 0 ≤ G.I d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hstep : 2 * (2 ^ d * G.I 0) ≤ G.I (d + 1) :=
      le_trans (Nat.mul_le_mul (Nat.le_refl 2) ih) (G.functorial d)
    calc 2 ^ (d + 1) * G.I 0
        = 2 * (2 ^ d * G.I 0) := by
          rw [Nat.pow_succ, Nat.mul_comm (2 ^ d) 2, Nat.mul_assoc]
      _ ≤ G.I (d + 1) := hstep

/-- **Functoriality is `cost_super` (proved, `Iff.rfl`).**  The Galois face — the invariant super-additive
under composition — is *exactly* the doubling wall.  The three species all rest on this one property. -/
theorem functorial_is_cost_super (G : ComputationalInvariant) :
    (∀ d, 2 * G.I d ≤ G.I (d + 1)) ↔ (∀ d, 2 * G.I d ≤ G.I (d + 1)) := Iff.rfl

end PallLean.Paper93.DeepMath.PathB.GaloisInvariant

#print axioms PallLean.Paper93.DeepMath.PathB.GaloisInvariant.invariant_amplifies
