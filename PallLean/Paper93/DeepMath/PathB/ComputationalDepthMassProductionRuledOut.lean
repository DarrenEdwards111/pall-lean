import Mathlib.Data.Nat.Basic

/-!
# Ruling out mass production in a restricted case: the disjoint-support certificate

The one surviving mechanism that could flatten a step is **Uhlig mass production** — computing `k` copies
of a function *cheaper* than `k` independent copies, by sharing sub-circuits across the batch.  If that
never happens for SAT's tower, the gain can't sag and `P ≠ NP`.  In general it is open.  Here we rule it
out in a **restricted case**: when the copies are *disjoint* and cost is captured by an exact lens, there
is provably **no sharing saving**.

## The mechanism, and the certificate that kills it

Mass production is `batch k < k · single`: the `k`-copy circuit undercuts `k` times the single-copy cost.
A **disjoint-support lens** forbids it — a measure `lens` that

* **lower-bounds cost** (`lens k ≤ batch k`) — it is a valid lower bound;
* is **exactly additive across disjoint copies** (`lens k = k · lens 1`) — disjoint inputs leave *no*
  sub-circuit two copies could share, so the measure just adds; and
* is **tight on one copy** (`lens 1 = single`) — the lens captures the single-copy cost exactly.

Given such a lens, `batch k ≥ lens k = k · lens 1 = k · single`: no saving, mass production ruled out.

## What is proved

* **`no_mass_production`** — a disjoint-support lens forces `k · single ≤ batch k` for every `k`: the
  batch cannot beat `k` independent copies.
* **`no_mass_production_final`** — hence `¬ MassProduces`: in the restricted (disjoint + tight) regime
  there is *no* Uhlig saving, so the composition step cannot be flattened this way.
* **`disjointWitness`** — the regime is non-vacuous: a concrete disjoint lens exists (`k` copies at cost
  `5` each, additive).

## Honest scope — exactly the two assumptions SAT's tower violates

This is a real ruling-out, and it is restricted by *precisely* the two hypotheses SAT's composition tower
breaks:

1. **disjointness** (`lens k = k · lens 1`) — SAT's tower copies **share inputs** (composition feeds the
   same variables through), so the copies are *not* disjoint; sharing is exactly what is permitted, and
   `additive` fails.
2. **tightness** (`lens 1 = single`) — every concrete lens **caps** (support at `n`, Khrapchenko at
   `n²`), so on a *hard* base function the lens is not exact; `tight` fails.

So mass production is ruled out for **disjoint copies of lens-captured functions** — the read-once /
bounded-sharing regime (cf. `BoundedSharing`, `SupportLens`).  The open case is **shared-input,
unbounded-sharing copies of a hard function** — which is `cost_super`.  The restriction is honest: we kill
mass production exactly where sharing is structurally impossible, and that is exactly not-SAT.  Nothing
here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MassProductionRuledOut

/-- **Uhlig mass production**: the `k`-copy circuit strictly undercuts `k` independent single copies —
a sharing saving, `batch k < k · single`.  This is the mechanism that could flatten a composition step. -/
def MassProduces (batch : ℕ → ℕ) (single : ℕ) : Prop := ∃ k, batch k < k * single

/-- A **disjoint-support lens** on the batch cost: a valid lower bound that is exactly additive across
disjoint copies and tight on one copy.  Its existence certifies that the copies share nothing. -/
structure DisjointLens (batch : ℕ → ℕ) (single : ℕ) where
  /-- the measure -/
  lens : ℕ → ℕ
  /-- it lower-bounds the batch cost (valid) -/
  valid : ∀ k, lens k ≤ batch k
  /-- disjoint copies ⟹ the measure is exactly additive (no shareable sub-circuit) -/
  additive : ∀ k, lens k = k * lens 1
  /-- the measure is exact on a single copy -/
  tight : lens 1 = single

/-- **Mass production ruled out (restricted, proved).**  A disjoint-support lens forces
`k · single ≤ batch k` for every `k`: the batch cost cannot beat `k` independent copies, so no sharing
saving occurs. -/
theorem no_mass_production (batch : ℕ → ℕ) (single : ℕ) (L : DisjointLens batch single) :
    ∀ k, k * single ≤ batch k := by
  intro k
  calc k * single = k * L.lens 1 := by rw [L.tight]
    _ = L.lens k := (L.additive k).symm
    _ ≤ batch k := L.valid k

/-- **No Uhlig saving in the restricted regime (proved).**  With a disjoint-support lens the step cannot
be flattened by mass production: `¬ MassProduces batch single`. -/
theorem no_mass_production_final (batch : ℕ → ℕ) (single : ℕ)
    (L : DisjointLens batch single) : ¬ MassProduces batch single :=
  fun ⟨k, hk⟩ => absurd (no_mass_production batch single L k) (by omega)

/-- **The regime is non-vacuous (proved).**  A concrete disjoint lens: `k` copies at cost `5` each,
exactly additive — there really is a regime with no mass production. -/
def disjointWitness : DisjointLens (fun k => k * 5) 5 where
  lens := fun k => k * 5
  valid := fun k => Nat.le_refl _
  additive := fun k => by simp
  tight := by simp

end PallLean.Paper93.DeepMath.PathB.MassProductionRuledOut

#print axioms PallLean.Paper93.DeepMath.PathB.MassProductionRuledOut.no_mass_production
#print axioms PallLean.Paper93.DeepMath.PathB.MassProductionRuledOut.no_mass_production_final
