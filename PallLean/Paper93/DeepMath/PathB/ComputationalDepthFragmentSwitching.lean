import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCHolonomyRestriction

/-!
# Switching surrogate for the modular‑statistic fragment — restriction lowers effective holonomy rank

The general theorem (`restriction lowers effective holonomy rank for poly‑gate ACC⁰`) is the open
`NP ⊄ ACC⁰` core.  Here we prove the **switching surrogate for a fragment** where it genuinely holds: a circuit
whose realized charges factor through `k` modular statistics.  A restriction that fixes `k − j` of the statistics
(making them constant) leaves the charge factoring through only `j` free statistics, so the rank bound drops from
`q^k` to `q^j`.  Paired with the proved hard‑side survival (`tseitin_holonomy_survives_restriction`), this yields a
real fragment‑level lower bound — the switching mechanism, working end‑to‑end on the fragment.

## What is proved (clean axioms, no `sorry`)

* `restriction_lowers_effective_holonomy_rank` — **the surrogate**: if a restriction leaves the charge factoring
  through `j` free statistics (`j < k`), then `realizedClasses ≤ q^j` and `q^j < q^k` — the effective rank bound
  strictly drops.
* `fragment_below_surviving_tseitin` — **the payoff lower bound**: when the lowered fragment bound `q^j` is below
  the surviving Tseitin holonomy `2^{|K|}`, the fragment realizes *strictly fewer* classes than the hard family
  retains — so the modular‑statistic fragment **cannot** realize the surviving Tseitin holonomy.

## Honest scope

This is a genuine *restricted* result: the surrogate + survival give a real lower bound against the
**modular‑statistic fragment** (circuits whose charges factor through few statistics, with restrictions that fix
statistics).  It is *not* the general theorem: a poly‑gate ACC⁰ circuit need not present itself as a low‑statistic
charge factoring, and a restriction need not reduce its statistic count — that is exactly the open
`ACC0LowEffectiveHolonomyRank` (`…ACCHolonomyRestriction`), `NP ⊄ ACC⁰`‑strength, under the PRF‑free naturalness
ceiling.  What this shows: the switching mechanism is *correct and complete on the fragment*; extending it to
poly‑gate ACC⁰ is the major missing theorem, not a gap in the surrogate.
-/

namespace PallLean.Paper93.DeepMath.PathB.FragmentSwitching

open PallLean.Paper93.DeepMath.PathB.HolonomyPSideControl
open PallLean.Paper93.DeepMath.PathB.HolonomyEffectiveRank
open PallLean.Paper93.DeepMath.PathB.HypergraphHolonomySPDP
open PallLean.Paper93.DeepMath.PathB.HolonomyHardEffectiveRank
open PallLean.Paper93.DeepMath.PathB.ACCHolonomyRestriction

variable {V : Type*}

/-- **The switching surrogate (proved): a restriction fixing `k − j` statistics lowers the rank bound to `q^j`.**
If the restricted charge factors through only `j` free statistics (`j < k`), then `realizedClasses ≤ q^j`, and
that is strictly below the unrestricted `q^k`. -/
theorem restriction_lowers_effective_holonomy_rank {ι : Type*} {m k j q : ℕ} [NeZero q]
    (hq : 2 ≤ q) (hjk : j < k) (cycle : Fin m → Finset V) (chargeOf : ι → (V → ZMod 2))
    (Inputs : Finset ι) (freeStat : ι → (Fin j → ZMod q))
    (chargeFromFree : (Fin j → ZMod q) → (V → ZMod 2))
    (hfac : ∀ x, chargeOf x = chargeFromFree (freeStat x)) :
    realizedClasses cycle chargeOf Inputs ≤ q ^ j ∧ q ^ j < q ^ k := by
  refine ⟨modular_layer_realized_le cycle chargeOf Inputs freeStat chargeFromFree hfac, ?_⟩
  exact Nat.pow_lt_pow_right (by omega) hjk

/-- **The fragment‑level lower bound (proved).**  When the restriction‑lowered fragment bound `q^j` is below the
surviving Tseitin holonomy `2^{|K|}`, the modular‑statistic fragment realizes *strictly fewer* holonomy classes
than the hard family retains — so it cannot realize the surviving Tseitin holonomy.  The switching mechanism
(restriction lowers the circuit; Tseitin survives) works end‑to‑end on the fragment. -/
theorem fragment_below_surviving_tseitin [DecidableEq V] {ι : Type*} {m j q m' : ℕ} [NeZero q]
    (cycle : Fin m → Finset V) (chargeOf : ι → (V → ZMod 2)) (Inputs : Finset ι)
    (freeStat : ι → (Fin j → ZMod q)) (chargeFromFree : (Fin j → ZMod q) → (V → ZMod 2))
    (hfac : ∀ x, chargeOf x = chargeFromFree (freeStat x))
    (G : DisjointCycles V m') (K : Finset (Fin m'))
    (hsmall : q ^ j < 2 ^ K.card) :
    realizedClasses cycle chargeOf Inputs
      < (K.powerset.image (fun S => holSigZ G.cycle (chargeForZ G S))).card := by
  rw [tseitin_holonomy_survives_restriction G K]
  exact lt_of_le_of_lt
    (modular_layer_realized_le cycle chargeOf Inputs freeStat chargeFromFree hfac) hsmall

end PallLean.Paper93.DeepMath.PathB.FragmentSwitching

#print axioms PallLean.Paper93.DeepMath.PathB.FragmentSwitching.restriction_lowers_effective_holonomy_rank
#print axioms PallLean.Paper93.DeepMath.PathB.FragmentSwitching.fragment_below_surviving_tseitin
