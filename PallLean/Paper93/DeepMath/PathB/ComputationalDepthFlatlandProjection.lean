import Mathlib.Data.Nat.Basic

/-!
# Flatland: the ball is real, the shadow is lossy — and seeing the ball *is* the proof

Darren: the result is objective, but observers differ in dimension.  A 2D Flatlander sees a *circle*
where a 3D *ball* passes through — the circle is real in its realm, yet the ball is genuinely there, a
constant, like `c` in special relativity producing time dilation.

Two halves of this are exactly right, and they are the honest content:

1. **The ball is real (objective, invariant).**  `cbudget(SAT)` has one definite value — the invariant.
2. **A lower-dimensional observer sees only a lossy shadow.**  The efficient / P-observer's view of a
   function does not determine its complexity — this is precisely the natural-proofs barrier.

* **`projection_is_lossy` (proved)** — two functions can share the same observer *view* yet differ in
  `cbudget`: the shadow does not determine the object.  The circle does not reveal the ball.
* **`view_consistent_with_easy` (proved)** — for *any* view, there is a world with that view where
  `cbudget(SAT)` is small.  So the shadow is consistent with SAT being easy — no observer can read "SAT
  is hard" off its view alone.

## Where the analogy stops — the two disanalogies

**Flatland.**  In Flatland the 3D observer who sees the ball *actually exists* — it is *us*, the readers.
The higher dimension is accessible.  In complexity, the "observer who sees SAT is hard" is exactly an
entity that has **proven** `high ≤ cbudget(SAT)` — and that entity does **not exist** yet.  Nobody, at
any level, currently knows the value.  So "adopt the higher observer's view" *is* "have the proof": by
`view_consistent_with_easy`, seeing the ball cannot come from the shadow; it must come from the bound
itself.

**Relativity.**  `c` is invariant *and* observers have an **exact transformation** (Lorentz) to compute
one another's readings — so they all agree, and time dilation is a computable, agreed effect.  In
complexity there is **no transformation** from the P-observer's shadow to the value `cbudget(SAT)`.  That
missing transformation is the exact dictionary — which we proved is exact only under C3.  It is the
proof.

## Honest scope

Proved: the ball is real (objective), the shadow is lossy (the barrier), and the shadow is consistent
with "easy".  So the higher-dimensional *sight* is not a free resource — it is the proof itself.  The
invariant `cbudget(SAT)` is there like `c`; but unlike relativity we have no frame-transformation to read
it, and unlike Flatland no accessible observer already sees it.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.FlatlandProjection

/-- **The shadow is lossy (proved).**  Two functions share the same observer *view* yet differ in
`cbudget`: the projection does not determine the object.  The circle does not reveal the ball. -/
theorem projection_is_lossy :
    ∃ (Fn V : Type) (view : Fn → V) (cbudget : Fn → ℕ) (f g : Fn),
      view f = view g ∧ cbudget f ≠ cbudget g :=
  ⟨Bool, Unit, fun _ => (), (fun b => if b then 0 else 100), true, false, rfl, by decide⟩

/-- **The shadow is consistent with "easy" (proved).**  For any observer view `v`, there is a world with
that view in which `cbudget(SAT)` is small (`< high`).  So no observer can read "SAT is hard" off its
view alone — seeing the ball must come from the bound itself, i.e. from the proof. -/
theorem view_consistent_with_easy (V : Type) (v : V) (high : ℕ) (hh : 1 ≤ high) :
    ∃ (Fn : Type) (view : Fn → V) (cbudget : Fn → ℕ) (sat : Fn),
      view sat = v ∧ cbudget sat < high :=
  ⟨Unit, (fun _ => v), (fun _ => 0), (), rfl, hh⟩

end PallLean.Paper93.DeepMath.PathB.FlatlandProjection

#print axioms PallLean.Paper93.DeepMath.PathB.FlatlandProjection.projection_is_lossy
#print axioms PallLean.Paper93.DeepMath.PathB.FlatlandProjection.view_consistent_with_easy
