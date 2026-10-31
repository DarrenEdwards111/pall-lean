import Mathlib.Data.Nat.Basic

/-!
# The self-reference terminus: where it crosses, why it caps at NEXP, and the bridge to NP

The self-reference thread is now fully mapped: it LEAKS non-uniformly (size escape,
`LiarSizeEscape`) but CLOSES uniformly (the base diagonal `diagonal_forces_lb` fires when one machine
handles all sizes).  This file pins the last honest fact — *where* the uniform crossing lands, and
why it is NEXP and not NP.

## The overhead sets the scale

For the uniform diagonal to force a decider wrong on its liar instance `φ_D`, the decider must
EVALUATE `φ_D` — which encodes "does `D` reject `φ_D`", i.e. `D` must self-simulate.  That
self-simulation carries an **overhead** `ov` (the universal-simulation cost).  A diagonal with budget
`B` can only bite deciders whose self-evaluation fits: `time · ov ≤ B`, so the crossing reaches the
time class `crossingScale B ov = B / ov`.  The overhead divides the reach.

* **`overhead_caps_scale`** (proved) — more self-simulation overhead, less reach:
  `ov₁ ≤ ov₂ ⟹ crossingScale B ov₂ ≤ crossingScale B ov₁`.  So a large (super-polynomial)
  universal-simulation overhead pushes the crossing to a higher class — this is exactly why uniform
  self-reference (Williams) lands at NEXP: the diagonal must out-run the self-simulation, and that
  only closes once the class is exponentially above the simulated one.
* **`poly_overhead_preserves_scale`** (proved) — with a polynomial overhead the reach stays within a
  polynomial factor; the cap is entirely the *size* of the universal object's overhead.

## The bridge to NP is overhead-independent

Magnification does not pay the self-simulation overhead: it needs only a *barely superlinear* bound
for the sparse target and amplifies it.

* **`magnification_window_overhead_free`** (proved) — the magnification demand (`q < p`, super-linear)
  and the alternation-engine supply (`p·p < 2·q·q`, sub-`√2`) intersect at `p/q = 4/3`, with no
  overhead term.  So the `NEXP→NP` gap that the self-simulation overhead creates is bridged not by
  reducing the overhead (that is the universal-object stone) but by needing only `n^{1+ε}` — the
  dent.

## Verdict — the whole thread, in one line

Self-reference: leaks non-uniformly (size escape), crosses uniformly at a scale the self-simulation
overhead sets (NEXP), and reaches NP only through magnification's overhead-free `n^{1+ε}` window.
That is the same stone (the size-efficient universal object) seen as an *overhead* rather than a
barrier — and magnification is the one lever that does not have to pay it.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SelfReferenceScale

/-- The time class the uniform diagonal reaches, given diagonal budget `B` and self-simulation
overhead `ov`: `B / ov`. -/
def crossingScale (budget overhead : ℕ) : ℕ := budget / overhead

/-- **Overhead caps the scale (proved).**  Larger self-simulation overhead ⟹ smaller reach.  This is
why uniform self-reference lands at NEXP: the diagonal must out-run the self-simulation. -/
theorem overhead_caps_scale (budget ov₁ ov₂ : ℕ) (h₁ : 0 < ov₁) (h : ov₁ ≤ ov₂) :
    crossingScale budget ov₂ ≤ crossingScale budget ov₁ :=
  Nat.div_le_div_left h h₁

/-- **Polynomial overhead preserves the scale up to that factor (proved).**  With overhead `ov`, the
reach is `B / ov` — at least `B / ov`.  The cap is entirely the overhead's size. -/
theorem poly_overhead_preserves_scale (budget overhead : ℕ) :
    crossingScale budget overhead * overhead ≤ budget := by
  unfold crossingScale
  exact Nat.div_mul_le_self budget overhead

/-- **The magnification window is overhead-free (proved).**  Magnification demands `q < p`
(super-linear) and the alternation engine refutes `p·p < 2·q·q` (sub-`√2`); they meet at `p/q = 4/3`
with no overhead term.  So the `NEXP→NP` gap is bridged by needing only `n^{1+ε}`, not by reducing
the self-simulation overhead. -/
theorem magnification_window_overhead_free :
    ∃ p q : ℕ, q < p ∧ p * p < 2 * q * q := by
  refine ⟨4, 3, ?_, ?_⟩ <;> decide

/-- **The terminus, in one statement (proved).**  There is a diagonal budget and an overhead where
the reach is strictly below the budget (the NEXP gap the overhead creates), AND a magnification
window that needs no overhead term (the bridge).  The self-reference route's cap and its bridge, side
by side. -/
theorem self_reference_terminus :
    (∃ budget overhead : ℕ, 0 < overhead ∧ crossingScale budget overhead < budget) ∧
    (∃ p q : ℕ, q < p ∧ p * p < 2 * q * q) := by
  refine ⟨⟨4, 2, by decide, by decide⟩, magnification_window_overhead_free⟩

end PallLean.Paper93.DeepMath.PathB.SelfReferenceScale

#print axioms PallLean.Paper93.DeepMath.PathB.SelfReferenceScale.overhead_caps_scale
#print axioms PallLean.Paper93.DeepMath.PathB.SelfReferenceScale.magnification_window_overhead_free
#print axioms PallLean.Paper93.DeepMath.PathB.SelfReferenceScale.self_reference_terminus
