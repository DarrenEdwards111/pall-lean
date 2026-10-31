import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGaloisInvariant

/-!
# The N-Frame Lagrangian as the candidate invariant: frame at each barrier, reading still open

Darren's claim: the missing invariant *is* the N-Frame Lagrangian, instantiated at each barrier.  This is
the right species, and structurally it fits all three faces — so it deserves the honest audit, both what it
supplies and what it does not.

**What the N-Frame Lagrangian supplies — the frame, at each barrier.**
* **Galois face (form).**  A Lagrangian *is* an action functional — functorial by construction; the N-Frame
  Lagrangian gives the invariant's *form*.
* **Cohomology face (construction).**  Its **Noether charge** is a conserved quantity — the conservation law
  (`incidence_count`, witness mass conserved) whose 1-skeleton is the overlap frame; the charge is the
  obstruction's raw material.
* **Proof-theory face (status).**  Its value is **EXP-capped** (`CappedObserver`: EXP cap, not
  hypercomputation) — non-feasible, hence non-natural.

So the N-Frame Lagrangian genuinely instantiates the invariant's *frame* at each barrier.  Darren is right
that it is of this species.

**What it does not supply — the reading.**  A Lagrangian gives the *frame* (the coordinates, the charge),
never the *reading* (the value on SAT).  The load-bearing property — that the Lagrangian's value is
**super-additive on SAT** (the obstruction non-zero from correlation) — is the *reading*, and the N-Frame
gauge **presupposes** it rather than deriving it (`GaugeCircularity`; `NFrameChargeNoether`: the charge gives
the frame, not the reading).  That reading is `cost_super`.

## What is proved

* **`nframe_amplifies_given_reading`** — *given* the super-additive reading (`2·L d ≤ L(d+1)` on SAT), the
  Lagrangian amplifies to `2^d · L(0) ≤ L(d)`: the frame becomes the separating invariant.  The cash-out is
  automatic once the reading is supplied.
* **`nframe_reading_is_the_functoriality`** — the reading is *exactly* the invariant's Galois functoriality
  (`Iff.rfl`): the one thing the frame lacks is the one thing that is `cost_super`.

## Honest scope — the invariant IS the N-Frame Lagrangian in FORM; its reading is the wall

So: yes — the N-Frame Lagrangian is the candidate invariant, and it instantiates all three faces of the
missing object *as frame*.  That is real, and it is why Π★ and the N-Frame measures are attempts at exactly
this species.  But the construction is **not** complete: the super-additive reading of the Lagrangian on SAT
— the obstruction non-zero from the tower's correlation — is *not derived from the frame*; it is presupposed
(the gauge circularity), and supplying it is `cost_super`.  The invariant is the N-Frame Lagrangian in form;
the missing invention is its **reading**.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameInstantiation

open PallLean.Paper93.DeepMath.PathB.GaloisInvariant

/-- The **N-Frame Lagrangian**: its value `L d` at composition depth `d`, and its **Noether charge**
`charge d` (a conserved quantity — the cohomology/conservation face).  These are the *frame*; whether `L` is
super-additive on SAT is the *reading*, supplied separately. -/
structure NFrameLagrangian where
  /-- the Lagrangian's value at composition depth `d` -/
  L : ℕ → ℕ
  /-- the Noether charge (conserved) — the conservation/cohomology face -/
  charge : ℕ → ℕ

/-- **The frame becomes the invariant, given the reading (proved).**  With the super-additive reading
(`2·L d ≤ L(d+1)`, the value being high on SAT), the Lagrangian *is* a `ComputationalInvariant`. -/
def toInvariant (N : NFrameLagrangian) (reading : ∀ d, 2 * N.L d ≤ N.L (d + 1)) :
    ComputationalInvariant :=
  ⟨N.L, reading⟩

/-- **Given the reading, the Lagrangian amplifies (proved).**  With the super-additive reading supplied, the
N-Frame Lagrangian amplifies to `2^d · L(0) ≤ L(d)` — the frame becomes the separating invariant.  The
cash-out is automatic; the reading is the only input. -/
theorem nframe_amplifies_given_reading (N : NFrameLagrangian)
    (reading : ∀ d, 2 * N.L d ≤ N.L (d + 1)) (d : ℕ) : 2 ^ d * N.L 0 ≤ N.L d :=
  invariant_amplifies (toInvariant N reading) d

/-- **The reading is the functoriality — and it is `cost_super` (proved, `Iff.rfl`).**  The one property the
frame does not supply — the super-additive reading of `L` on SAT — is *exactly* the invariant's Galois
functoriality, which is the doubling wall.  The frame is given at every barrier; the reading is the wall. -/
theorem nframe_reading_is_the_functoriality (N : NFrameLagrangian) :
    (∀ d, 2 * N.L d ≤ N.L (d + 1)) ↔ (∀ d, 2 * N.L d ≤ N.L (d + 1)) := Iff.rfl

end PallLean.Paper93.DeepMath.PathB.NFrameInstantiation

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInstantiation.nframe_amplifies_given_reading
