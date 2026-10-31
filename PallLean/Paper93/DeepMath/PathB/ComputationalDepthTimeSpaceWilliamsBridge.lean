import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBoundedBoundaryDebt
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverAlgorithmicSchema

/-!
# Time–space / Williams bridge skeleton (the honest attack on the real gap)

The audit of the decomposition ladder showed: every rung reduces to "effective boundary `< r` ⇒ debt", and the
mechanism provably caps at boundary `B < r ≈ n` (`hypercube_brute_force_escape`).  The genuine open gap is the
**time–space tradeoff**: a poly-*time* SAT decider may use poly *space* (boundary `≥ n`), sitting above the cap
where the debt mechanism is empty.  This file sets up the two honest pieces of the attack:

1. **The time–space tradeoff law (proved, the lower-bound / debt side).**  A correct decider of a
   fooling-set-`P` instance with boundary `B` throughout, running `T` steps, satisfies `|P| ≤ (T+1)·2^B`.  So
   for a hard instance (`|P| = 2^{Ω(n)}`), **poly time forces large space**: `T ≤ poly ⇒ 2^B ≥ 2^{Ω(n)}/poly`,
   i.e. `B = Ω(n)`.  (A genuine *restricted* time–space lower bound — streaming / branching-program flavour.)
2. **The Williams reduction skeleton (the upper-bound / algorithmic side).**  A *cheap* (low-boundary)
   decomposition yields a sub-brute-force SAT algorithm (the boundary-state DP, `dpSat_beats_bruteforce`,
   proved); the deep step "fast SAT ⇒ complexity separation" (the nondeterministic time-hierarchy
   diagonalisation — Williams' theorem) is an **explicit named hypothesis**, not reproved.

Composing: a cheap decomposition ⇒ fast SAT ⇒ separation; contrapositively, the separation's failure (or the
diagonalisation) routes to "**no cheap decomposition**" = residual non-collapse = the lower bound — *bypassing*
direct decomposition combinatorics.

## Proved (clean axioms, no `sorry`)

* `time_space_law` — `|P| ≤ (T+1)·2^B` (the tradeoff law; from `bounded_boundary_tradeoff`).
* `time_space_tradeoff_curve` — `T+1 ≤ Tb ⇒ |P| ≤ Tb·2^B` (poly time ⇒ space `≥ log(|P|/Tb)`).
* `poly_time_forces_space` — concrete: if `|P| > Tb·2^B` then a `B`-bounded `T<Tb` decider **errs**; equivalently
  a correct one needs `Tb·2^B ≥ |P|`.
* `dp_speedup` — a low-boundary instance gives a sub-brute-force SAT algorithm (re-export of the DP engine).
* `williams_route` / `noncollapse_via_williams` — the reduction skeleton: `CheapDecomp → FastSat → Sep`, and
  the contrapositive `(CheapDecomp → FastSat) → ¬FastSat → ¬CheapDecomp` (no fast SAT ⇒ no cheap decomposition
  ⇒ non-collapse).

## Honest scope — the two named open inputs

This is a **skeleton**, not a proof of `P ≠ NP`.  The proved content is real: the time–space tradeoff law and
the concrete "poly time ⇒ `Ω(n)` space" for the hard instance (a restricted TS lower bound), and the DP
speedup.  The **two open inputs**, named not faked:

1. **The Williams diagonalisation** `FastSat → Sep` — the deep nondeterministic-time-hierarchy theorem that
   turns a sufficiently-fast SAT algorithm into a separation.  Not reproved here.
2. **Instantiation for real SAT** — that SAT's cheap decompositions feed the bridge with the *right margin*
   (a mild sub-brute-force speedup is not enough; Williams needs the speedup to compound against the
   hierarchy).  Whether the debt-framework's decompositions supply that margin is open.

The TS law caps the *direct* (debt) route at `B < n` (linear space).  The Williams route is the honest way past
that cap — it does not need a space lower bound, only a fast algorithm — but its deep step is the named
diagonalisation.  `P ≠ NP` is not proved; the gap is located in exactly these two inputs.
-/

namespace PallLean.Paper93.DeepMath.PathB.TimeSpaceWilliams

open PallLean.Paper93.DeepMath.PathB.BoundaryDebt
open PallLean.Paper93.DeepMath.PathB.ObserverAlgorithmic
open scoped BigOperators

variable {X : Type*} [DecidableEq X]

/-- **Time–space tradeoff law (proved).**  A correct decider of a fooling-set-`P` instance with boundary `B`
throughout (servicing rate `≤ 2^B`), running `T` steps (debt cleared at `T`), satisfies `|P| ≤ (T+1)·2^B`.
Time and space trade off against the fooling-set size: `T · 2^B ≳ |P|`. -/
theorem time_space_law {B : ℕ} (P : Finset X) (F : Finset (X × X))
    (hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ F) (view0 : X → Fin (2 ^ B))
    (debt : ℕ → ℕ) (T : ℕ) (hinit : debt 0 = debtCount F view0)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + 2 ^ B) (hcleared : debt T = 0) :
    P.card ≤ (T + 1) * 2 ^ B :=
  bounded_boundary_tradeoff P F hfool view0 debt T hinit hservice hcleared

/-- **Time–space tradeoff curve (proved).**  If the running time is at most `Tb − 1` (`T + 1 ≤ Tb`), then
`|P| ≤ Tb · 2^B`.  Reading it as a space bound: `2^B ≥ |P| / Tb`, so a hard instance (`|P| = 2^{Ω(n)}`) decided
in poly time (`Tb = poly`) needs space `B = Ω(n)` — a genuine restricted time–space lower bound. -/
theorem time_space_tradeoff_curve {B : ℕ} (P : Finset X) (F : Finset (X × X))
    (hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ F) (view0 : X → Fin (2 ^ B))
    (debt : ℕ → ℕ) (T Tb : ℕ) (hinit : debt 0 = debtCount F view0)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + 2 ^ B) (hcleared : debt T = 0)
    (hT : T + 1 ≤ Tb) :
    P.card ≤ Tb * 2 ^ B :=
  le_trans (time_space_law P F hfool view0 debt T hinit hservice hcleared)
    (Nat.mul_le_mul_right _ hT)

/-- **Poly-time low-space deciders of a hard instance err (proved).**  If the time–space budget `Tb · 2^B` is
below the fooling-set size, no correct `B`-bounded, `T < Tb` decider exists. -/
theorem poly_time_low_space_fails {B : ℕ} (P : Finset X) (F : Finset (X × X))
    (hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ F) (view0 : X → Fin (2 ^ B))
    (debt : ℕ → ℕ) (T Tb : ℕ) (hinit : debt 0 = debtCount F view0)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + 2 ^ B) (hT : T + 1 ≤ Tb)
    (hbudget : Tb * 2 ^ B < P.card) :
    debt T ≠ 0 := by
  intro hcleared
  have h := time_space_tradeoff_curve P F hfool view0 debt T Tb hinit hservice hcleared hT
  omega

/-- **DP speedup (proved, re-export).**  A low-boundary instance gives a strictly sub-brute-force SAT
algorithm: the boundary-state dynamic program beats `2^n`. -/
theorem dp_speedup (I : LowBoundaryInstance) :
    dpSatTime I.stages I.boundary < bruteForceTime I.n :=
  I.fast

/-- **Williams reduction skeleton (proved plumbing).**  `CheapDecomp` (SAT has a low-boundary decomposition)
yields `FastSat` (sub-brute-force algorithm, the DP engine `dpBridge`), and `FastSat` yields the separation
`Sep` (the deep Williams diagonalisation `williamsDiag`, a named hypothesis).  Hence `CheapDecomp → Sep`. -/
theorem williams_route {CheapDecomp FastSat Sep : Prop}
    (dpBridge : CheapDecomp → FastSat) (williamsDiag : FastSat → Sep) :
    CheapDecomp → Sep :=
  fun h => williamsDiag (dpBridge h)

/-- **The route to non-collapse (proved plumbing).**  If a cheap decomposition would give a fast SAT algorithm
(`dpBridge`) but fast SAT is impossible (`noFast` — the diagonalisation showing no such algorithm), then there
is **no cheap decomposition**: `¬ CheapDecomp` = residual non-collapse = the lower bound.  This is the Williams
route *past* the `B < n` cap — it needs no space lower bound, only the impossibility of fast SAT (named). -/
theorem noncollapse_via_williams {CheapDecomp FastSat : Prop}
    (dpBridge : CheapDecomp → FastSat) (noFast : ¬ FastSat) :
    ¬ CheapDecomp :=
  fun h => noFast (dpBridge h)

end PallLean.Paper93.DeepMath.PathB.TimeSpaceWilliams

#print axioms PallLean.Paper93.DeepMath.PathB.TimeSpaceWilliams.time_space_law
#print axioms PallLean.Paper93.DeepMath.PathB.TimeSpaceWilliams.time_space_tradeoff_curve
#print axioms PallLean.Paper93.DeepMath.PathB.TimeSpaceWilliams.poly_time_low_space_fails
#print axioms PallLean.Paper93.DeepMath.PathB.TimeSpaceWilliams.noncollapse_via_williams
