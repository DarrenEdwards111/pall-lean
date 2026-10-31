import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingCapacityLowerBound

/-!
# An *explicit* family escaping a richer decision class — Nečiporuk / decomposable deciders

The explicitness wall asks for an **explicit** family with a genuine *decision* lower bound (not counting, not
the `2^r`‑way separator/classifier, and not bounded‑width in disguise — bounded width was boundary).  The
Nečiporuk / crossing‑capacity corpus already supplies exactly this for the **decomposable / communication**
decision model: a `CrossingModel f` compresses the left block into `numStates` states, and the number of states
needed is the number of distinct *crossing residual subfunctions* of `f` — a concrete combinatorial property of
`f`, not a counting or width quantity.

The explicit family is **`StorageAccess`** (indirect storage access — the canonical Nečiporuk‑hard function):
`StorageAccess m (data) (i) = data i`.  It has `2^m` distinct crossing subfunctions (one per table), so **every**
decomposable decider for it needs `≥ 2^m` states — exponential, unconditional, explicit.

## Proved (clean axioms, no `sorry`)

* `storageAccess_decomposable_lb` — every `CrossingModel (StorageAccess m)` has `≥ 2^m` states (restating
  `storageAccess_crossing_lb`).
* `storageAccess_escapes_cheap_decomposable` — **the explicit lower bound**: no decomposable decider of capacity
  `< 2^m` computes `StorageAccess m`.  An explicit family escapes the bounded‑capacity decomposable class.
* `explicit_family_beats_decomposable` — the existence statement: there *is* an explicit family hard for every
  bounded‑capacity decomposable decider.

## Honest scope — explicit and non‑natural, but at the known ceiling

This is genuinely explicit (a named function), a genuine *decision* lower bound (it's about computing
`StorageAccess`, not separating a residual), against a class **richer than width** (decomposable /
communication, measured by distinct subfunctions), and it is **non‑natural** — the Nečiporuk subfunction‑count
argument is not a large/constructive property, so it *evades* the natural‑proofs barrier (`…NaturalProofsBarrier`),
which is exactly why such explicit bounds are provable at all.

But it sits at the **Nečiporuk ceiling**: per block the bound is `2^m` crossing states; summed over `Θ(n/log n)`
blocks (the corpus's `…NeciporukHardFunctionAsymptotic`) it yields formula size `Θ(n²/log n)` — the decades‑old
frontier of explicit formula lower bounds.  It does **not** reach `P/poly` or general poly‑time, and the method
provably tops out here (`crossing_capacity` bounds states by subfunction count, which is `≤ 2^{block}`).  So this
is the strongest *explicit* decision hardness the corpus reaches — real, non‑natural, capped — not `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ExplicitNeciporukHardness

open PallLean.Paper93.DeepMath.PathB

/-- **Explicit decomposable lower bound (proved).**  Every decomposable (crossing‑state) decider for the explicit
`StorageAccess m` needs at least `2^m` states — it has `2^m` distinct crossing subfunctions. -/
theorem storageAccess_decomposable_lb (m : ℕ) (M : CrossingModel (StorageAccess m)) :
    2 ^ m ≤ M.numStates :=
  storageAccess_crossing_lb m M

/-- **The explicit family escapes the bounded‑capacity decomposable class (proved).**  No decomposable decider of
capacity `< 2^m` computes the explicit `StorageAccess m`. -/
theorem storageAccess_escapes_cheap_decomposable (m c : ℕ) (hc : c < 2 ^ m) :
    ¬ ∃ M : CrossingModel (StorageAccess m), M.numStates ≤ c := by
  rintro ⟨M, hM⟩
  have h := storageAccess_crossing_lb m M
  omega

/-- **There is an explicit family hard for every bounded‑capacity decomposable decider (proved).**  For each
capacity bound `c`, taking `m` with `2^m > c` (e.g. `m = c`, since `c < 2^c`), `StorageAccess m` escapes every
decomposable decider of capacity `≤ c`. -/
theorem explicit_family_beats_decomposable (c : ℕ) :
    ∃ m : ℕ, ¬ ∃ M : CrossingModel (StorageAccess m), M.numStates ≤ c :=
  ⟨c, storageAccess_escapes_cheap_decomposable c c (Nat.lt_two_pow_self)⟩

end PallLean.Paper93.DeepMath.PathB.ExplicitNeciporukHardness

#print axioms PallLean.Paper93.DeepMath.PathB.ExplicitNeciporukHardness.storageAccess_escapes_cheap_decomposable
#print axioms PallLean.Paper93.DeepMath.PathB.ExplicitNeciporukHardness.explicit_family_beats_decomposable
