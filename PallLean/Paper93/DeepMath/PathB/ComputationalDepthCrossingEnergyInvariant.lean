import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceMeasureSchema
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingEnergy

/-!
# Crossing energy as a sound observer invariant — soundness discharged, hardness pinned

The open target: *can a carefully chosen time-bounded novelty measure be forced high on SAT?*  This
file takes one concrete time-bounded novelty measure — **crossing energy** `Σ_b crossingCount(b)²`,
which (unlike a plain distinct-rows count) weights the *concentration* of boundary traffic — and
discharges its **soundness half** against the observer-invariant bridge.

## Why soundness is the provable half here

`InvSound` is the calibration that killed earlier candidates (SPDP rank, bond dimension, …): it
demands `Inv D ≤ poly(time_D)` for *every* correct decider, and those measures could be large on a
fast decider (representation-dependent).  Crossing energy is different: `crossingEnergy ≤ S·T²`
holds **universally** (`crossingEnergy_le_space_mul_time_sq`), for every decider and every
representation — it is bounded by time by construction.  So its `InvSound` is not fenced; it is
proved:

* `crossingEnergyInv` — the per-length worst-case crossing energy of `M` at its canonical clock.
* `crossingEnergyInv_invSound` — **every polynomial-time decider of a SAT boundary has
  polynomially-bounded crossing energy.**  (Via `crossingEnergy ≤ (minHalt+1)·minHalt²`,
  `minHalt ≤ T`, and `polyBounded_time_comp`.)

## What remains — the honest crux

* `crossingEnergy_route` — with `InvSound` discharged, the whole route to the separation reduces to
  **one** hypothesis: `InvHard` — every SAT decider (poly or not) has *superpolynomial* crossing
  energy.  That is a crossing-sequence lower bound for SAT.

`InvHard` is **not** proved here; it is separation-strength (by `invariant_bridge`,
`InvSound ∧ InvHard → SAT ∉ P`, so forcing crossing energy high on SAT *is* the separation, not a
discount).  The point of this file is narrower and honest: the soundness half — the part Darren
noted is exactly what we want — is genuinely proved for a concrete novelty measure, so the search is
now pinned to a single, structurally-flavoured target (a crossing lower bound), the kind of quantity
for which combinatorial lower-bound techniques (crossing sequences, Nečiporuk) sometimes exist.  No
claim is made that such a bound is within reach.

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics
open PallLean.Paper93.DeepMath.PathB.ObserverInvariantBridge
open PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema (minHalt minHalt_le)
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-- The crossing-energy invariant: the worst-case, over length-`n` inputs, of the crossing energy of
`M`'s computation run to its canonical uniform halting time. -/
noncomputable def crossingEnergyInv : Invariant := fun M n =>
  Finset.univ.sup fun v : Fin n → Bool =>
    crossingEnergy M (init M (List.ofFn v)) (minHalt M n + 1) (minHalt M n)

/-- **Soundness (the provable half).**  Every polynomial-time decider of a SAT boundary has
polynomially-bounded crossing energy.  Crossing energy is `≤ (minHalt+1)·minHalt²` by construction,
and `minHalt ≤ T` for any halting clock `T`, so a polynomial clock gives a polynomial bound —
uniformly over all inputs, hence over the worst case. -/
theorem crossingEnergyInv_invSound (SATV : NPObs) : InvSound SATV crossingEnergyInv := by
  intro M T hT hD
  have hH : ∀ x, HaltsBy M x (T x.length) := fun x => (hD x).1
  refine polyBounded_of_le ?_ (polyBounded_time_comp 1 3 hT)
  intro n
  apply Finset.sup_le
  intro v _
  have hce : crossingEnergy M (init M (List.ofFn v)) (minHalt M n + 1) (minHalt M n)
      ≤ (minHalt M n + 1) * (minHalt M n) ^ 2 :=
    crossingEnergy_le_space_mul_time_sq _ _ _
  have hmh : minHalt M n ≤ T n := minHalt_le hH n
  calc crossingEnergy M (init M (List.ofFn v)) (minHalt M n + 1) (minHalt M n)
      ≤ (minHalt M n + 1) * (minHalt M n) ^ 2 := hce
    _ ≤ (T n + 1) * (T n) ^ 2 :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hmh 2)
    _ ≤ 1 * (T n + n + 1) ^ 3 := by
        have hb2 : (T n) ^ 2 ≤ (T n + n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        calc (T n + 1) * (T n) ^ 2
            ≤ (T n + n + 1) * (T n + n + 1) ^ 2 := Nat.mul_le_mul (by omega) hb2
          _ = 1 * (T n + n + 1) ^ 3 := by ring

/-- **The route, with soundness discharged.**  Crossing energy being superpolynomial on every SAT
decider (`InvHard`) forces the SAT boundary out of P.  Soundness is proved
(`crossingEnergyInv_invSound`); the sole remaining hypothesis is the crossing lower bound `InvHard`,
which is separation-strength. -/
theorem crossingEnergy_route (SATV : NPObs) (hHard : InvHard SATV crossingEnergyInv) :
    ¬ PolyCollapse SATV :=
  invariant_bridge SATV crossingEnergyInv (crossingEnergyInv_invSound SATV) hHard

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
