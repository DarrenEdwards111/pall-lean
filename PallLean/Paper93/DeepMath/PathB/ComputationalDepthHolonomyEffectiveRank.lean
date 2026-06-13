import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolonomyPSideControl

/-!
# Effective cycle rank of realized charges — and a concrete modular‑gate layer test

The tame side reduced to a **rank bound on the *realized* charges**, not the raw constraint graph (an ACC⁰ circuit
can encode an expander, so the raw cycle rank is `Ω(n)`).  The right quantity is the **effective holonomy rank**:
the dimension of the holonomy‑signature subspace the circuit's *actual* charges span — equivalently
`log₂` of the number of holonomy classes it realizes.  This file defines it and tests a concrete modular‑gate
layer against it.

A computation maps each input `x` to a charge `chargeOf x`; the realized classes are
`realizedClasses = #{ holSig (chargeOf x) : x ∈ Inputs }`.

## What is proved (clean axioms, no `sorry`)

* `realized_le_of_factorThroughStat` — **the structural bound**: if the charge depends on the input only through a
  statistic `stat : ι → S` (`chargeOf = chargeFromStat ∘ stat`), then the realized holonomy classes number `≤ #`
  realized statistics `≤ |S|`.  The effective rank is bounded by the *statistic*, not the graph.
* `modular_gate_realized_le` — **a single `MOD q` gate is tame**: a charge depending only on a `ZMod q`‑valued
  statistic realizes `≤ q` holonomy classes — effective rank `≤ log₂ q`, *constant* for fixed `q`.
* `modular_layer_realized_le` — **a `k`‑gate layer**: a charge depending on `k` modular statistics (values in
  `Fin k → ZMod q`) realizes `≤ q^k` classes — effective rank `≤ k · log₂ q`, **additive in the gate count**.

## Verdict — the tame side, concretely confirmed; the gap, concretely located

A modular‑gate layer's *realized* charges have effective holonomy rank `≤ (#gates) · log₂(modulus)`: **low and
additive**, matching the composition subadditivity (`…HolonomyCompositionRank`).  So few modular gates are provably
tame — the framework genuinely controls a modular layer through its statistic, exactly the AC⁰[p] success in
holonomy form, and *without* the feature‑counting blow‑up.

But `k = poly(n)` gates give effective rank up to `poly · log q` — `O(log n)` (the A1 threshold) only if the total
modular‑statistic count is `O(log n)`.  An ACC⁰ circuit on an NP‑hard instance can force the realized charges to
high effective rank (expander charges need `Ω(n)` independent statistics).  So the open step is now *concretely*
pinned: **poly‑time ⇒ the realized charges factor through `O(log n)` modular statistics on hard instances** — false
in general, true would be `ACC0LowRealizedGodelSPDP`, and still under the PRF‑free naturalness ceiling
(`…DynamicSPDPNaturalnessRange`).  The effective‑rank notion turns "low cycle rank" from a graph property into the
right *computational* one — the realized charges' statistic count — and the modular‑layer test confirms it behaves
exactly as the AC⁰[p]/ACC⁰ frontier predicts.
-/

namespace PallLean.Paper93.DeepMath.PathB.HolonomyEffectiveRank

open PallLean.Paper93.DeepMath.PathB.HolonomyPSideControl

variable {V : Type*}

/-- The number of **holonomy classes** a computation realizes: distinct holonomy signatures over its inputs.
`log₂` of this is the *effective cycle rank* of the realized charges. -/
def realizedClasses {ι : Type*} {m : ℕ} (cycle : Fin m → Finset V) (chargeOf : ι → (V → ZMod 2))
    (Inputs : Finset ι) : ℕ :=
  (Inputs.image (fun x => holSigZ cycle (chargeOf x))).card

/-- **Effective rank is bounded by the statistic (proved).**  If the charge depends on the input only through a
statistic `stat : ι → S`, the realized holonomy classes number at most the realized statistics `≤ |stat image|`. -/
theorem realized_le_of_factorThroughStat {ι S : Type*} [DecidableEq S] {m : ℕ}
    (cycle : Fin m → Finset V) (chargeOf : ι → (V → ZMod 2)) (Inputs : Finset ι)
    (stat : ι → S) (chargeFromStat : S → (V → ZMod 2))
    (hfac : ∀ x, chargeOf x = chargeFromStat (stat x)) :
    realizedClasses cycle chargeOf Inputs ≤ (Inputs.image stat).card := by
  unfold realizedClasses
  have hsub : Inputs.image (fun x => holSigZ cycle (chargeOf x))
      ⊆ (Inputs.image stat).image (fun s => holSigZ cycle (chargeFromStat s)) := by
    intro sig hsig
    rw [Finset.mem_image] at hsig
    obtain ⟨x, hx, rfl⟩ := hsig
    rw [hfac x, Finset.mem_image]
    exact ⟨stat x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, rfl⟩
  calc (Inputs.image (fun x => holSigZ cycle (chargeOf x))).card
      ≤ ((Inputs.image stat).image (fun s => holSigZ cycle (chargeFromStat s))).card :=
        Finset.card_le_card hsub
    _ ≤ (Inputs.image stat).card := Finset.card_image_le

/-- **A single `MOD q` gate is tame (proved): `≤ q` holonomy classes.**  A charge depending only on a
`ZMod q`‑valued statistic realizes at most `q` classes — effective rank `≤ log₂ q`, constant for fixed `q`. -/
theorem modular_gate_realized_le {ι : Type*} {m q : ℕ} [NeZero q]
    (cycle : Fin m → Finset V) (chargeOf : ι → (V → ZMod 2)) (Inputs : Finset ι)
    (stat : ι → ZMod q) (chargeFromStat : ZMod q → (V → ZMod 2))
    (hfac : ∀ x, chargeOf x = chargeFromStat (stat x)) :
    realizedClasses cycle chargeOf Inputs ≤ q := by
  refine le_trans (realized_le_of_factorThroughStat cycle chargeOf Inputs stat chargeFromStat hfac) ?_
  calc (Inputs.image stat).card ≤ Fintype.card (ZMod q) := Finset.card_le_univ _
    _ = q := ZMod.card q

/-- **A `k`‑gate modular layer (proved): `≤ q^k` holonomy classes.**  A charge depending on `k` modular statistics
realizes at most `q^k` classes — effective rank `≤ k · log₂ q`, additive in the gate count `k` (matching the
composition subadditivity). -/
theorem modular_layer_realized_le {ι : Type*} {m k q : ℕ} [NeZero q]
    (cycle : Fin m → Finset V) (chargeOf : ι → (V → ZMod 2)) (Inputs : Finset ι)
    (stat : ι → (Fin k → ZMod q)) (chargeFromStat : (Fin k → ZMod q) → (V → ZMod 2))
    (hfac : ∀ x, chargeOf x = chargeFromStat (stat x)) :
    realizedClasses cycle chargeOf Inputs ≤ q ^ k := by
  refine le_trans (realized_le_of_factorThroughStat cycle chargeOf Inputs stat chargeFromStat hfac) ?_
  calc (Inputs.image stat).card ≤ Fintype.card (Fin k → ZMod q) := Finset.card_le_univ _
    _ = q ^ k := by rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

end PallLean.Paper93.DeepMath.PathB.HolonomyEffectiveRank

#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyEffectiveRank.realized_le_of_factorThroughStat
#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyEffectiveRank.modular_gate_realized_le
#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyEffectiveRank.modular_layer_realized_le
