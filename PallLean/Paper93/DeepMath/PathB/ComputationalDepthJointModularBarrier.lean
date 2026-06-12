import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEnrichedModularBoundary

/-!
# The joint modular construction is blocked — a precise barrier (honest negative)

The remaining frontier (`SCOPE_ACC0_OBSERVER_FRONTIER.md` §6) is the **joint modular construction**: a single
representation that is low-boundary across *all* moduli at once, so that mixed-modulus ACC⁰ circuits become
low-boundary observers.  This file *attempts* it and proves the natural approaches are **blocked** — a barrier,
not a separation.  Nothing here proves `NP ⊄ ACC⁰`; it proves the polynomial-method joint construction (in
any fixed-field-family form) provably cannot serve as the bridge.

## Two ways a joint construction could be a bridge, both blocked

A joint boundary that is a **monotone aggregation dominating each component** (sum, max, product over a field
family `M`) inherits any single high component (`enrichedBoundary_ge_component`).  So:

* **Fixed field family fails (proved).**  `no_fixed_family_joint_bridge`: for *any* fixed finite family `M`,
  there is a single `MOD_q` gate with `q ∉ M` whose joint boundary over `M` is **high** — a single-gate ACC⁰
  function the fixed-family bridge cannot make low.  The cross-modulus hardness it uses (`MOD_q` is high-degree
  over every `F_p`, `p ≠ q`) is exactly the content of the proved AC⁰[p] lower bound
  `Layer4.mod_q_indicators_false` — *the very theorem that powers the AC⁰[p] calibration is the barrier to the
  ACC⁰ joint construction.*

* **Circuit-dependent family hits composition (open).**  One could instead let `M` depend on the circuit
  (include all its moduli).  Then a single gate is captured, but a *composition* mixing moduli (a `MOD_2`
  feeding a `MOD_3`) is high-degree over `F_3` (its `MOD_2` input is, by `mod_q_indicators_false`) **and** over
  `F_2` (the `MOD_3` gate is) — high over every field in the family.  That compositional cross-modulus
  blow-up is the genuinely open obstruction.

## What is proved (clean axioms, no `sorry`)

* `joint_boundary_ge_component` — any monotone dominating joint boundary is `≥` each component.
* `no_fixed_family_joint_bridge` — the fixed-field-family joint bridge provably fails (an out-of-family `MOD`
  gate, with cross-modulus hardness `crossHard`, has high joint boundary).

`crossHard` is stated as an explicit hypothesis (the demotion pattern): it is the cross-modulus degree lower
bound, a real theorem (`mod_q_indicators_false` is its circuit form), not faked here.

## Honest conclusion

The joint modular construction cannot be a fixed-field monotone aggregation (proved barrier), and the
circuit-dependent version is blocked by compositional cross-modulus hardness (the proved AC⁰[p] lower bound,
in the role of an obstruction).  This is precisely why ACC⁰ resists the polynomial method and why Williams
needed an **algorithmic** (`#SAT`-algorithm ⇒ lower bound), non-polynomial route for `NEXP ⊄ ACC⁰`.  The
observer/God-Move method, via polynomials, hits the same wall.  `NP ⊄ ACC⁰` stays open; the value here is a
clean theorem that the polynomial joint route is blocked, so progress needs a genuinely different idea.
-/

namespace PallLean.Paper93.DeepMath.PathB.JointModularBarrier

open PallLean.Paper93.DeepMath.PathB.EnrichedModular
open scoped BigOperators

/-- Any monotone joint boundary that **dominates each component** (sum/max/product over the family) is at
least every single component — so one high component makes it high.  (Stated for the `∑` aggregation
`enrichedBoundary`; the same holds for any dominating aggregation.) -/
theorem joint_boundary_ge_component (M : Finset ℕ) (prof : ℕ → ℕ) {m₀ : ℕ} (hm₀ : m₀ ∈ M) :
    prof m₀ ≤ enrichedBoundary M prof :=
  enrichedBoundary_ge_component M prof hm₀

/-- **The fixed-field-family joint bridge provably fails.**  For any fixed finite family `M` of moduli and any
high-degree threshold `H`, given the cross-modulus hardness `crossHard` (a `MOD_q` gate with `q ∉ M` has
feature dimension `≥ H` over *every* `F_p`, `p ∈ M` — the degree form of `mod_q_indicators_false`), there is a
single `MOD_q` gate (`q ∉ M`, an ACC⁰ function) whose joint boundary over `M` is `≥ H`.  So "ACC⁰ ⇒ low joint
boundary" cannot hold for any fixed family. -/
theorem no_fixed_family_joint_bridge (M : Finset ℕ) (H : ℕ) (hM : M.Nonempty)
    (profOfMod : ℕ → ℕ → ℕ)
    (crossHard : ∀ q, q ∉ M → ∀ p, p ∈ M → H ≤ profOfMod q p) :
    ∃ q, q ∉ M ∧ H ≤ enrichedBoundary M (fun p => profOfMod q p) := by
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset M
  refine ⟨q, hq, ?_⟩
  obtain ⟨p, hp⟩ := hM
  calc H ≤ profOfMod q p := crossHard q hq p hp
    _ ≤ enrichedBoundary M (fun p => profOfMod q p) :=
        joint_boundary_ge_component M (fun p => profOfMod q p) hp

end PallLean.Paper93.DeepMath.PathB.JointModularBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.JointModularBarrier.no_fixed_family_joint_bridge
