import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CircuitSatSearchable

/-!
# The reach of the exact ACC⁰ SAT speedup, quantified (PROVED)

`acc0circuit_sat_searchable` gives a sub-`2^n` SAT search whenever `circuitTowerSize C + 1 < 2^n`.  This
file pins down **when** that holds.  The key identity is that the collapsed size's successor is *exactly
multiplicative* over `and`/`or`:

  `circuitTowerSize (and a b) + 1 = (circuitTowerSize a + 1) · (circuitTowerSize b + 1)`,

so `circuitTowerSize C + 1` is the **product** of the leaf successors over the `and`/`or`-tree.  Hence:

  `circuitTowerSize_succ_le_pow` — if every bottom (`mod`) gate has `|S|+1 ≤ K` (and `2 ≤ K`), then
  `circuitTowerSize C + 1 ≤ K ^ (leafCount C)`.

  `acc0circuit_sat_searchable_of_pow` — therefore, if `K ^ (leafCount C) < 2^n`, the SAT speedup applies.

So the exact route reaches exactly the circuits whose **leaf-successor product** stays below `2^n` —
i.e. `leafCount C · log K < n`.  This is the honest (restrictive) reach: a *linear-in-`n`* leaf budget.
Beyond it the product towers past `2^n` and the speedup is vacuous — which is precisely why the
unconditional speedup needs the quasipoly Beigel–Tarui route, not the exact one.

## What is proved (clean axioms, no `sorry`)

* `circuitTowerSize_succ_and` / `_or` — the exact multiplicative `+1` identity.
* `circuitTowerSize_succ_le_pow` — `circuitTowerSize C + 1 ≤ K^(leafCount C)` under leaf bound `K`.
* `acc0circuit_sat_searchable_of_pow` — the SAT speedup under the explicit `K^(leafCount C) < 2^n` regime.

## Honest scope

This quantifies the *exact* route's reach; it is restrictive (leaf-product `< 2^n`).  The unconditional
speedup (quasipoly size across unbounded depth/width) is the open Beigel–Tarui content.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CircuitTowerBound

open scoped Classical
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitSatSearchable (circuitTowerSize acc0circuit_sat_searchable)

variable {n : ℕ}

/-- **The exact multiplicative `+1` identity for `and` (proved).** -/
theorem circuitTowerSize_succ_and (a b : ACC0Circuit n) :
    circuitTowerSize (ACC0Circuit.and a b) + 1
      = (circuitTowerSize a + 1) * (circuitTowerSize b + 1) := by
  simp only [circuitTowerSize]; ring

/-- **The exact multiplicative `+1` identity for `or` (proved).** -/
theorem circuitTowerSize_succ_or (a b : ACC0Circuit n) :
    circuitTowerSize (ACC0Circuit.or a b) + 1
      = (circuitTowerSize a + 1) * (circuitTowerSize b + 1) := by
  simp only [circuitTowerSize]; ring

/-- The number of leaf gates (`const`/`var`/`mod`) in the `and`/`or`-tree. -/
def leafCount : ACC0Circuit n → ℕ
  | .const _ => 1
  | .var _ => 1
  | .mod _ _ _ => 1
  | .not c => leafCount c
  | .and a b => leafCount a + leafCount b
  | .or a b => leafCount a + leafCount b

/-- The bottom (`mod`) gates all have `|S|+1 ≤ K`. -/
def LeafBounded (K : ℕ) : ACC0Circuit n → Prop
  | .const _ => True
  | .var _ => True
  | .mod _ S _ => S.card + 1 ≤ K
  | .not c => LeafBounded K c
  | .and a b => LeafBounded K a ∧ LeafBounded K b
  | .or a b => LeafBounded K a ∧ LeafBounded K b

/-- **The collapsed size is bounded by the leaf-successor power (proved).**  With every bottom gate
`|S|+1 ≤ K` and `2 ≤ K`, `circuitTowerSize C + 1 ≤ K ^ (leafCount C)`. -/
theorem circuitTowerSize_succ_le_pow {K : ℕ} (hK : 2 ≤ K) :
    ∀ (C : ACC0Circuit n), LeafBounded K C → circuitTowerSize C + 1 ≤ K ^ leafCount C := by
  intro C
  induction C with
  | const b => intro _; simp [circuitTowerSize, leafCount]; omega
  | var i => intro _; simp [circuitTowerSize, leafCount]; omega
  | mod q S t => intro h; simpa [circuitTowerSize, leafCount] using h
  | not c ih => intro h; simpa [circuitTowerSize, leafCount] using ih h
  | and a b iha ihb =>
    intro h
    rw [circuitTowerSize_succ_and, leafCount, pow_add]
    exact Nat.mul_le_mul (iha h.1) (ihb h.2)
  | or a b iha ihb =>
    intro h
    rw [circuitTowerSize_succ_or, leafCount, pow_add]
    exact Nat.mul_le_mul (iha h.1) (ihb h.2)

/-- **The exact SAT speedup under the explicit regime (proved).**  If every bottom gate has `|S|+1 ≤ K`
(`2 ≤ K`) and `K ^ (leafCount C) < 2^n`, then `Satisfiable (eval C)` is decided by a search over
`< 2^n` count cells. -/
theorem acc0circuit_sat_searchable_of_pow {K : ℕ} (hK : 2 ≤ K) (C : ACC0Circuit n)
    (hlb : LeafBounded K C) (hreg : K ^ leafCount C < 2 ^ n) :
    ∃ (m : ℕ) (mono : Fin m → Finset (Fin n)) (h : ℕ → Bool),
      (NFrameACC0Speedup.Satisfiable (eval C) ↔
          ∃ c ∈ Finset.univ.image (ACC0SymmetricObserver.gateCount
              (fun j x => ACC0PolyToSymAnd.monoAND (mono j) x)), h c = true)
        ∧ (Finset.univ.image (ACC0SymmetricObserver.gateCount
            (fun j x => ACC0PolyToSymAnd.monoAND (mono j) x))).card < 2 ^ n :=
  acc0circuit_sat_searchable C (lt_of_le_of_lt (circuitTowerSize_succ_le_pow hK C hlb) hreg)

/-!
**Reach quantified.**  `circuitTowerSize C + 1` is the product of leaf successors (multiplicative over
`and`/`or`); the speedup applies exactly when that product `≤ K^(leafCount C) < 2^n` — a linear-in-`n`
leaf budget.  Beyond it the product towers and the speedup is vacuous; the unconditional speedup needs
the quasipoly Beigel–Tarui route.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CircuitTowerBound

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CircuitTowerBound.circuitTowerSize_succ_le_pow
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CircuitTowerBound.acc0circuit_sat_searchable_of_pow
