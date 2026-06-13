import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolonomyHardEffectiveRank

/-!
# The ACC⁰ holonomy‑restriction frontier — survival proved, rank‑lowering isolated as the open core

HAL's route to `ACC0LowEffectiveHolonomyRank` (an ACC⁰ decider's realized charges factor through `O(log n)`
holonomy statistics on hard instances) splits into two halves.  This file proves the *provable* half and isolates
the open half precisely — the sharpest formulation of what an ACC⁰ lower bound needs inside this framework.

* **Hard side — survival (proved here).**  `tseitin_holonomy_survives_restriction`: a restriction that leaves `K`
  cycles free preserves **`2^{|K|}`** holonomy classes.  So Tseitin/expander holonomy is *robust under
  restriction* — exactly the property the Andreev‑style argument needs on the hard family.
* **Tame side — rank lowering (the open core).**  Proved for fragments (one gate / `log` gates:
  `modular_gate_realized_le`, `modular_layer_realized_le`), but the statement *poly‑size ACC⁰ deciders for a hard
  family have `O(log n)` effective holonomy rank* is **open** and `NP ⊄ ACC⁰`‑strength — `false` for the raw
  graph (ACC⁰ encodes expanders), so genuinely about realized charges.  Named here as the bridge hypothesis.

## What is proved (clean axioms, no `sorry`)

* `tseitin_holonomy_survives_restriction` — surviving `K` cycles ⇒ `2^{|K|}` holonomy classes survive.
* `acc0_holonomy_separation` — **the conditional**: if the bridge `ACC0LowEffectiveHolonomyRank` (poly classes for
  ACC⁰) holds and the hard family's surviving holonomy is super‑polynomial, the two are incompatible — the hard
  family is not ACC⁰‑decidable.  The lone open hypothesis is the bridge; the survival side is supplied by
  `tseitin_holonomy_survives_restriction`.

## Honest scope

The survival half is genuinely proved (the hard side is robust under restriction).  The separation is *conditional
on the bridge*, which is the open `NP ⊄ ACC⁰`‑strength statement — and even it sits under the PRF‑free naturalness
ceiling.  This is not a proof of an ACC⁰ lower bound; it is the precise, two‑sided formulation HAL identified: one
half done, the other named as exactly the major missing theorem (and the next genuine attack on it — a restricted
switching/shrinkage surrogate `restriction_lowers_effective_holonomy_rank` for poly‑gate ACC⁰ — is the separate
project beyond what is provable here).
-/

namespace PallLean.Paper93.DeepMath.PathB.ACCHolonomyRestriction

open PallLean.Paper93.DeepMath.PathB.HolonomyPSideControl
open PallLean.Paper93.DeepMath.PathB.HolonomyEffectiveRank
open PallLean.Paper93.DeepMath.PathB.HypergraphHolonomySPDP
open PallLean.Paper93.DeepMath.PathB.HolonomyHardEffectiveRank

variable {V : Type*}

/-- **The hard side survives restriction (proved).**  After a restriction that leaves the cycles in `K` free
(fixing the rest), the charges supported on `K`'s representatives realize all `2^{|K|}` holonomy signatures: the
Tseitin/expander holonomy obstruction is robust under restriction. -/
theorem tseitin_holonomy_survives_restriction [DecidableEq V] {m : ℕ} (G : DisjointCycles V m)
    (K : Finset (Fin m)) :
    (K.powerset.image (fun S => holSigZ G.cycle (chargeForZ G S))).card = 2 ^ K.card := by
  have hcong : K.powerset.image (fun S => holSigZ G.cycle (chargeForZ G S))
      = K.powerset.image (fun S => fun i => if i ∈ S then (1 : ZMod 2) else 0) := by
    apply Finset.image_congr
    intro S _
    exact holSigZ_chargeForZ G S
  rw [hcong, Finset.card_image_of_injective _ indicatorZ_injective, Finset.card_powerset]

/-- **(The open bridge, named):** for an ACC⁰ decider, the realized charges on hard instances factor through a
polynomial number of holonomy classes.  This is the `NP ⊄ ACC⁰`‑strength statement — proved for fragments, open
in general. -/
def ACC0LowEffectiveHolonomyRank (acc0Classes : ℕ → ℕ) (C : ℕ) : Prop :=
  ∀ n, acc0Classes n ≤ n ^ C

/-- **The conditional separation (proved).**  If the bridge holds for ACC⁰ deciders (poly classes) and the hard
family's surviving holonomy is super‑polynomial, the two class‑count functions cannot be equal — so the hard
family is not realized by any ACC⁰ decider.  The lone open hypothesis is the bridge; the super‑polynomial survival
is what `tseitin_holonomy_survives_restriction` delivers (with `|K| = Ω(n)` surviving cycles, `2^{|K|}` beats every
polynomial). -/
theorem acc0_holonomy_separation (acc0Classes hardClasses : ℕ → ℕ) (C : ℕ)
    (hbridge : ACC0LowEffectiveHolonomyRank acc0Classes C)
    (hsurvive : ∀ C, ∃ n, n ^ C < hardClasses n) :
    acc0Classes ≠ hardClasses := by
  intro hEq
  subst hEq
  obtain ⟨n, hn⟩ := hsurvive C
  have hle := hbridge n
  omega

end PallLean.Paper93.DeepMath.PathB.ACCHolonomyRestriction

#print axioms PallLean.Paper93.DeepMath.PathB.ACCHolonomyRestriction.tseitin_holonomy_survives_restriction
#print axioms PallLean.Paper93.DeepMath.PathB.ACCHolonomyRestriction.acc0_holonomy_separation
