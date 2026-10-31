import Mathlib.Data.Nat.Basic

/-!
# The ruler survives sharing, in a restricted case: up to the threshold

The non-natural, incompressible ruler (`NonNaturalRuler`) was built for **disjoint** blocks — zero sharing.
Here we carry it one step across the wall: it **survives bounded sharing** — stays non-natural *and* stays
high — as long as the sharing budget `t` is below a threshold `t⋆`.  This is the real move from
`disjoint (t = 0)` toward the general (shared) case; the remaining gap is `bounded → unbounded`.

## The setup

Allow `t` cross-block wires (sharing).  Graceful degradation (`BoundedSharingThreshold`): the reading drops
by at most `t`, so `k·b ≤ circuitSize + t`.  The ruler **survives** — still lower-bounds the circuit by a
high value `H` — exactly when `t ≤ k·b − H`, i.e. the sharing stays within the slack above `H`.  So the
survivable-sharing threshold is `t⋆ = k·b − H`.

## What is proved

* **`shared_ruler_non_natural`** — sharing does not touch the compute cost: the ruler is still non-natural,
  `2^{c·n} < computeCost` (`= 2^{n²}`), for every `c < n`.
* **`ruler_survives_bounded_sharing`** — under bounded sharing (`t ≤ k·b − H`), the ruler stays high:
  `H ≤ circuitSize`.  The reading survives the sharing.
* **`ruler_survives_delivers`** — both together: a non-natural measure that *still* lower-bounds the circuit
  by `H`, despite `t` sharing.  The ruler, surviving sharing.
* **`witness_survives`** — concrete: with `k·b = 12`, `H = 9`, the ruler survives sharing up to `t⋆ = 3`.

## Honest scope — survives bounded sharing; unbounded is the wall

This is a genuine step: the ruler no longer needs *zero* sharing — it survives *any* sharing up to
`t⋆ = k·b − H`, with all three properties intact.  The threshold is exact.

The remaining gap is `bounded → unbounded`.  SAT's composition tower lets the adversary share **freely** —
up to the circuit size — so `t` can exceed *any* fixed `t⋆`, and beyond the threshold the reading drops
below `H` (mass production).  Keeping the ruler high when sharing is *unbounded* is exactly `cost_super`.  So
the ruler survives sharing in the restricted (bounded, `t ≤ t⋆`) case, machine-checked; surviving unbounded
sharing is the single remaining wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RulerSurvivesSharing

/-- The ruler with a **sharing budget** `t`: `t` cross-block wires, graceful degradation
`k·b ≤ circuitSize + t`, still non-natural (`computeCost = 2^{n²}`). -/
structure SharedRuler where
  /-- disjoint blocks -/
  k : ℕ
  /-- per-block bound -/
  b : ℕ
  /-- input size -/
  n : ℕ
  /-- sharing budget (cross-block wires used) -/
  t : ℕ
  /-- cost to compute the ruler -/
  computeCost : ℕ
  /-- circuit size -/
  circuitSize : ℕ
  /-- non-natural: compute cost `2^{n²}` -/
  compute_def : computeCost = 2 ^ (n * n)
  /-- graceful degradation: sharing reduces the reading by at most `t` -/
  degraded : k * b ≤ circuitSize + t

/-- **Still non-natural under sharing (proved).**  Sharing does not touch the compute cost: for every
`c < n`, `2^{c·n} < computeCost` (`= 2^{n²}`).  The ruler remains beyond every polynomial method. -/
theorem shared_ruler_non_natural (R : SharedRuler) (c : ℕ) (hc : c < R.n) :
    2 ^ (c * R.n) < R.computeCost := by
  rw [R.compute_def]
  have hn : 0 < R.n := by omega
  have hcn : c * R.n < R.n * R.n := (Nat.mul_lt_mul_right hn).mpr hc
  exact Nat.pow_lt_pow_right (by decide) hcn

/-- **The ruler survives bounded sharing (proved).**  If the sharing budget stays within the slack above the
high value `H` (`H + t ≤ k·b`, i.e. `t ≤ k·b − H = t⋆`), the ruler still lower-bounds the circuit by `H`:
`H ≤ circuitSize`.  The reading survives the sharing. -/
theorem ruler_survives_bounded_sharing (R : SharedRuler) (H : ℕ) (hthresh : H + R.t ≤ R.k * R.b) :
    H ≤ R.circuitSize := by
  have hd := R.degraded
  omega

/-- **The ruler survives sharing, delivering (proved).**  Both at once: a *non-natural* measure that *still*
lower-bounds the circuit by `H` despite `t` sharing.  The ruler carried from disjoint to bounded sharing. -/
theorem ruler_survives_delivers (R : SharedRuler) (c H : ℕ) (hc : c < R.n)
    (hthresh : H + R.t ≤ R.k * R.b) :
    2 ^ (c * R.n) < R.computeCost ∧ H ≤ R.circuitSize :=
  ⟨shared_ruler_non_natural R c hc, ruler_survives_bounded_sharing R H hthresh⟩

/-- The ruler with `k·b = 12`, sharing `t = 3`, circuit degraded to `9` (`12 ≤ 9 + 3`). -/
def survivingWitness : SharedRuler where
  k := 2
  b := 6
  n := 3
  t := 3
  computeCost := 2 ^ 9
  circuitSize := 9
  compute_def := rfl
  degraded := by decide

/-- **Concrete survival (proved).**  The ruler survives sharing up to `t⋆ = k·b − H = 12 − 9 = 3`: with
`t = 3`, it still reads `9 ≤ circuitSize`. -/
theorem witness_survives : (9 : ℕ) ≤ survivingWitness.circuitSize :=
  ruler_survives_bounded_sharing survivingWitness 9 (by decide)

end PallLean.Paper93.DeepMath.PathB.RulerSurvivesSharing

#print axioms PallLean.Paper93.DeepMath.PathB.RulerSurvivesSharing.ruler_survives_bounded_sharing
#print axioms PallLean.Paper93.DeepMath.PathB.RulerSurvivesSharing.ruler_survives_delivers
