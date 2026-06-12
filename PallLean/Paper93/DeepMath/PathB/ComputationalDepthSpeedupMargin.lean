import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTimeSpaceWilliamsBridge

/-!
# Quantifying the speedup margin a decomposition delivers (the honest investigation of input (2))

The Williams bridge had two named open inputs: (1) the diagonalisation, (2) whether SAT's cheap decompositions
feed the bridge with a *speedup margin* strong enough to compound against the time hierarchy.  This file
**quantifies input (2)** — it is pure arithmetic, no diagonalisation faked.

A decomposition into `stages` stages of boundary `B` solves the instance in work `dpSatTime stages B =
stages · 2^B` versus brute force `2^n`.  Its **speedup margin** `m` is the savings exponent: savings `= 2^n /
work ≥ 2^m` iff `work ≤ 2^{n−m}`.  Two facts pin it down exactly:

* **Floor (proved, from the time–space law).**  A *correct* decomposition of a fooling-set-`P` instance does at
  least `|P|` work.  So with `|P| = 2^r`, the margin is **capped at `n − r`**: `savings ≥ 2^m ⇒ m + r ≤ n`.
* **Achievability (proved).**  A decomposition with `work ≤ 2^{n−m}` delivers savings `≥ 2^m`.  At the floor
  `work = 2^r` the margin is exactly `n − r`.

So **the speedup margin the decomposition delivers is exactly `n − r`** (variables minus the fooling-set
exponent).  For a bounded-degree-`d` expander Tseitin family, `r ≈ n/d`, so the margin is `n(1 − 1/d) =
Ω(n)` — an **exponential** savings `2^{Ω(n)}`, vastly exceeding the `ω(log n)` Williams needs.

## Proved (clean axioms, no `sorry`)

* `savings_ge_of_work_le` — `work ≤ 2^{n−m} ⇒ 2^m · work ≤ 2^n` (savings `≥ 2^m`).
* `correct_work_ge` — a correct decomposition (`stages = T+1`, boundary `B`) does work `≥ |P|`.
* `margin_le_of_correct` — **the cap**: if a correct decomposition of a `|P| = 2^r` instance delivers savings
  `≥ 2^m`, then `m + r ≤ n` — the margin is at most `n − r`.
* `expander_margin_eq` — at the work-floor (`work = 2^r`), savings is exactly `2^{n−r}` (the margin is
  achieved).

## Honest finding — why the abundant margin does NOT give a separation

The margin is `Ω(n)` (super-abundant), so input (2) is *not* a quantitative bottleneck — and that is exactly
the warning.  The floor `work ≥ 2^r` is the **bounded-boundary** floor; the *unrestricted* decision optimum for
Tseitin is achieved by **Gaussian elimination** (Tseitin = XOR constraints = a linear system over `F₂`),
which is **polynomial time** — i.e. `work = poly`, savings `≈ 2^n / poly`.  Gaussian elimination uses
polynomial *space* (boundary `≫ r`), so it lives **above the `B < n` cap** the debt mechanism respects: it is
consistent with "low-boundary deciders are slow", yet shows **Tseitin SAT ∈ P**.

Therefore:

* The fooling set / margin measures **distinguishability** (proof / communication complexity), **not decision
  hardness**.  Expander Tseitin is *proof-hard* but *decision-easy*.
* Feeding the Williams bridge with Tseitin is **vacuous**: a fast SAT algorithm for it exists (Gaussian
  elimination), so there is nothing to contradict — no separation.
* Williams needs a **decision-hard** family, where the residual non-collapse *also* blocks fast decision.  That
  is general SAT, where non-collapse is the open `P ≠ NP` quantifier.

So quantifying input (2) **dissolves it as a bottleneck and relocates the gap precisely**: not the margin
(abundant), but the requirement that the hard instance be decision-hard, not merely proof-hard — which the
debt framework's instances are not.  `P ≠ NP` is not proved; the honest obstruction is now named exactly.
-/

namespace PallLean.Paper93.DeepMath.PathB.SpeedupMargin

open PallLean.Paper93.DeepMath.PathB.BoundaryDebt
open PallLean.Paper93.DeepMath.PathB.ObserverAlgorithmic
open PallLean.Paper93.DeepMath.PathB.TimeSpaceWilliams
open scoped BigOperators

variable {X : Type*} [DecidableEq X]

/-- **Achievability (proved).**  If the decomposition's work is at most `2^{n−m}`, it delivers a savings factor
of at least `2^m` over brute force: `2^m · work ≤ 2^n`. -/
theorem savings_ge_of_work_le {w n m : ℕ} (hmn : m ≤ n) (hw : w ≤ 2 ^ (n - m)) :
    2 ^ m * w ≤ 2 ^ n := by
  calc 2 ^ m * w ≤ 2 ^ m * 2 ^ (n - m) := Nat.mul_le_mul_left _ hw
    _ = 2 ^ (m + (n - m)) := (pow_add 2 m (n - m)).symm
    _ = 2 ^ n := by rw [Nat.add_sub_of_le hmn]

/-- **Work floor (proved).**  A correct decomposition with `stages = T+1` stages of boundary `B`, deciding a
fooling-set-`P` instance, does at least `|P|` work: `|P| ≤ dpSatTime (T+1) B`. -/
theorem correct_work_ge {B : ℕ} (P : Finset X) (F : Finset (X × X))
    (hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ F) (view0 : X → Fin (2 ^ B))
    (debt : ℕ → ℕ) (T : ℕ) (hinit : debt 0 = debtCount F view0)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + 2 ^ B) (hcleared : debt T = 0) :
    P.card ≤ dpSatTime (T + 1) B := by
  have h := time_space_law P F hfool view0 debt T hinit hservice hcleared
  simpa [dpSatTime] using h

/-- **The margin cap (proved).**  If a *correct* decomposition of a `|P| = 2^r` instance delivers savings
`≥ 2^m` (`2^m · work ≤ 2^n`), then `m + r ≤ n`: the speedup margin is at most `n − r` — variables minus the
fooling-set exponent.  The work-floor `work ≥ |P| = 2^r` is what forbids a larger margin. -/
theorem margin_le_of_correct {B : ℕ} (P : Finset X) (F : Finset (X × X))
    (hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ F) (view0 : X → Fin (2 ^ B))
    (debt : ℕ → ℕ) (T : ℕ) (hinit : debt 0 = debtCount F view0)
    (hservice : ∀ t, debt t ≤ debt (t + 1) + 2 ^ B) (hcleared : debt T = 0)
    {n m r : ℕ} (hPr : P.card = 2 ^ r) (hsav : 2 ^ m * dpSatTime (T + 1) B ≤ 2 ^ n) :
    m + r ≤ n := by
  have hwork : (2 : ℕ) ^ r ≤ dpSatTime (T + 1) B := by
    rw [← hPr]; exact correct_work_ge P F hfool view0 debt T hinit hservice hcleared
  have hpow : (2 : ℕ) ^ (m + r) ≤ 2 ^ n := by
    calc (2 : ℕ) ^ (m + r) = 2 ^ m * 2 ^ r := by rw [pow_add]
      _ ≤ 2 ^ m * dpSatTime (T + 1) B := Nat.mul_le_mul_left _ hwork
      _ ≤ 2 ^ n := hsav
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hpow

/-- **The margin is exactly `n − r` at the floor (proved).**  A decomposition operating at the work-floor
(`dpSatTime stages B = 2^r`) delivers savings exactly `2^{n−r}`: `2^{n−r} · 2^r = 2^n`.  Combined with the cap,
the deliverable margin is precisely `n − r` (`= Ω(n)` for bounded-degree expander Tseitin, where `r ≈ n/d`). -/
theorem expander_margin_eq {r n : ℕ} (hrn : r ≤ n) :
    2 ^ (n - r) * 2 ^ r = 2 ^ n := by
  rw [← pow_add, Nat.sub_add_cancel hrn]

end PallLean.Paper93.DeepMath.PathB.SpeedupMargin

#print axioms PallLean.Paper93.DeepMath.PathB.SpeedupMargin.savings_ge_of_work_le
#print axioms PallLean.Paper93.DeepMath.PathB.SpeedupMargin.correct_work_ge
#print axioms PallLean.Paper93.DeepMath.PathB.SpeedupMargin.margin_le_of_correct
#print axioms PallLean.Paper93.DeepMath.PathB.SpeedupMargin.expander_margin_eq
