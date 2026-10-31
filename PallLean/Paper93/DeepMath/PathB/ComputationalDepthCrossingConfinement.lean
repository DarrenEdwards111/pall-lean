import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingComplexity

/-!
# Probing the single-tape storage obstruction

Question: is single-tape storage *provably obstructed* — i.e. can a simulation never lower
`crossingEnergy`?  Careful probing says **no, not absolutely** — and this corrects an earlier
over-optimistic claim.

## The corrected picture

* **Redundant crossings are flattenable (no obstruction).**  If a machine re-reads one value across
  boundary `b` a thousand times, it crosses `b` a thousand times.  A simulation can copy that value
  across `b` *once* and read the local copy — turning `Θ(K)` crossings into `Θ(1)`.  So storage *can*
  lower `crossingEnergy`; the copy trick works.
* **Information flow is obstructed (a real, quantitative bound).**  What storage cannot beat is the
  information that genuinely must cross `b`.  Each crossing carries at most `log|State|` bits (the
  control state), so `crossingCount(b) ≥ (information across b) / log|State|`.  Crossings carrying
  *new* information are irreducible; only redundant ones are.

So the obstruction is **partial and quantitative**, not absolute: `crossingEnergy` is flattenable
down to the information-flow floor, no further.  Whether that floor is high for SAT on *every*
single-tape machine is exactly a single-tape crossing/communication lower bound for SAT — which is
poly-equivalent to the separation, and open.

## The formal anchor (the base case of the information-flow bound)

The rigorous heart is that interaction across `b` requires crossing `b`.  Its base case is exact and
proved here: **with zero crossings of `b`, the head is confined to one side** — so the two sides of
`b` never interact.  This is the `K = 0` case of `crossings ≥ info-flow / log|State|`; the full
quantitative bound is the crossing-sequence (Hennie) argument, not carried out here.

* `no_crossing_confined` — if the head starts at `≤ b` and never crosses `b` in `[0,T)`, it stays
  `≤ b` throughout.

Honest verdict: single-tape storage is **not** provably obstructed in general (redundant crossings
flatten); it is obstructed only below the information-flow floor, and whether SAT sits above that
floor for all machines is the open separation.

Nothing here proves a separation or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

variable {M : Machine}

/-- **No crossing ⇒ confinement.**  If the head starts at `≤ b` and never crosses boundary `b`
during `[0,T)`, then it stays `≤ b` for all `t ≤ T`.  So a computation with zero crossings of `b`
has its two sides fully decoupled — the base case of the information-flow bound. -/
theorem no_crossing_confined (c : Cfg M) (b T : ℕ)
    (h0 : (run M 0 c).hd ≤ b) (hz : crossingCount M c b T = 0) :
    ∀ t, t ≤ T → (run M t c).hd ≤ b := by
  classical
  unfold crossingCount at hz
  have hempty : crossingTimes M c b T = ∅ := Finset.card_eq_zero.mp hz
  have hnc : ∀ t, t < T → ¬ crossesAt M c b t := by
    intro t ht hcross
    have hmem : t ∈ crossingTimes M c b T := by
      unfold crossingTimes; rw [Finset.mem_filter, Finset.mem_range]; exact ⟨ht, hcross⟩
    rw [hempty] at hmem; simp at hmem
  intro t
  induction t with
  | zero => intro _; exact h0
  | succ t ih =>
    intro htT
    have hprev : (run M t c).hd ≤ b := ih (by omega)
    by_contra hgt
    push_neg at hgt
    exact hnc t (by omega) (Or.inl ⟨hprev, hgt⟩)

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
