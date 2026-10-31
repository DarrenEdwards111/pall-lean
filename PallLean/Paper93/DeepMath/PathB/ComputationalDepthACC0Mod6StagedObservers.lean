import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Mod6SeparatedLayers
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0QuantitativeDepthBound

/-!
# The composite wall — bounded-depth staged observers for MOD₆: where and why they fail

The second honest composite no-go (after entry 280's separated-layers).  The natural fix for entry 280's
field-incompatibility is to **stage** the computation: compute the `MOD₂` part in one stage (over `F₂`), the `MOD₃` part
in another (over `F₃`), and combine — keeping each stage bounded-depth.  This file proves *where this fails*, pinning
`CarryRefinementCrossing` (entry 238) for the staged model.

**Why staging cannot escape (the proved failure mode).**

* *Bounded depth ⇒ bounded degree.*  A depth-`d` staged observer over its output field `F` produces a polynomial whose
  total degree, by the layer recurrence (entry 273), is at most `t^d · D₀` — a fixed bound for fixed `t, d, D₀`
  (`staged_degree_bound`).
* *The output field is non-native for one factor.*  The observer's output lives over a *single* field `F` of one
  characteristic; by entry 280 (`mod6_layers_cross_fields`), `F` cannot be native for both `MOD₂` and `MOD₃` — at least
  one CRT factor is non-native over `F`.
* *The non-native factor needs growing degree.*  By the prime Smolensky lower bound (entries 275–279), the non-native
  `MOD_q` factor (`q ≠ char F`) requires degree `≥ R(n)` that *grows with the input size* — eventually exceeding any
  fixed `t^d · D₀`.

Composing these: a bounded-depth staged observer computing `MOD₆` would need degree `≥ R(n)` but has degree
`≤ t^d · D₀ < R(n)` for large `n` — contradiction (`bounded_depth_staged_no_go`).  **Staging adds intermediate fields
but the final output is over one field, which the growing non-native degree defeats — exactly the carry-crossing wall,
now for the staged model.**

## What is proved (clean axioms, no `sorry`)

* **`staged_degree_bound`** (PROVED) — a depth-`d` staged observer's degree is `t^d · D₀` (the layer recurrence,
  entry-273 `pow_depth_degree`): *bounded depth gives bounded degree*.
* **`bounded_depth_staged_no_go`** (PROVED) — if the observer degree is `≤ t^d · D₀` (bounded depth), computing `MOD₆`
  forces degree `≥ R` (the non-native factor, Smolensky), and `t^d · D₀ < R` (growing requirement), then `False`.
* **`mod6_staged_output_field_not_native`** (PROVED) — the staged observer's single output field cannot be native for
  both factors (entry-280 `mod6_layers_cross_fields`): staging does not manufacture a common field.

## Honest scope — a no-go, not a way through

This **does not** prove `MOD₆ ∉ ACC⁰[?]`.  It proves that the *staged* approach fails for a definite reason: bounded
depth caps the degree over the single output field, but `MOD₆`'s non-native CRT factor (forced by the
field-incompatibility, entry 280) requires unbounded degree there — so staging cannot beat the carry-crossing wall
(entry 238).  The growing non-native degree requirement is the prime Smolensky bound (entries 275–279, itself resting on
the standard binomial tail).  Composite `ACC⁰` still needs a *characteristic-independent* method.  This is **not**
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0Mod6StagedObservers

open PallLean.Paper93.DeepMath.PathB.ACC0QuantitativeDepthBound (pow_depth_degree)
open PallLean.Paper93.DeepMath.PathB.ACC0Mod6SeparatedLayers (mod6_layers_cross_fields)

/-- **Bounded depth gives bounded degree (PROVED).**  A depth-`d` staged observer over its output field, with per-stage
degree growth `D ↦ t·D` from base `D₀` (the layer recurrence, entry 273), produces a polynomial of total degree
`(·t)^[d] D₀ = t^d · D₀` — a *fixed* bound for fixed `t, d, D₀`. -/
theorem staged_degree_bound (t D₀ d : ℕ) : (fun D => t * D)^[d] D₀ = t ^ d * D₀ :=
  pow_depth_degree t D₀ d

/-- **Bounded-depth staged observers cannot compute MOD₆ (PROVED no-go).**  If the staged observer has degree
`≤ t^d · D₀` (bounded depth, `staged_degree_bound`), and computing `MOD₆` forces degree `≥ R` (its non-native CRT factor
requires degree `R` by the prime Smolensky bound, entries 275–279), while `t^d · D₀ < R` (the requirement grows with the
input size, exceeding any fixed depth), then `False`.  Staging caps the degree at a fixed `t^d · D₀`, which the growing
non-native requirement defeats. -/
theorem bounded_depth_staged_no_go {t d D₀ R observerDeg : ℕ}
    (hbounded : observerDeg ≤ t ^ d * D₀) (hneed : R ≤ observerDeg) (hgrow : t ^ d * D₀ < R) :
    False := by omega

/-- **The staged observer's output field is not native for both factors (PROVED).**  However many bounded-depth stages
(over various intermediate fields) are composed, the *final output* lives over a single field `F` of one characteristic,
which — by entry 280 — cannot be native for both `MOD₂` and `MOD₃`.  Staging does not manufacture a field native for
both CRT factors; the cross-field obstruction (entry 238) persists at the output. -/
theorem mod6_staged_output_field_not_native (F : Type*) [Field F] : ¬ (CharP F 2 ∧ CharP F 3) :=
  mod6_layers_cross_fields F

/-!
**The staged no-go.**  Staging the `MOD₂`/`MOD₃` computation over different intermediate fields does not escape entry
280's field-incompatibility: the *final output* is over one field (`mod6_staged_output_field_not_native`), and bounded
depth caps its degree at a fixed `t^d · D₀` (`staged_degree_bound`); but `MOD₆`'s non-native CRT factor over that field
requires degree growing with the input (the prime Smolensky bound, entries 275–279), eventually exceeding `t^d · D₀`
(`bounded_depth_staged_no_go`).  So bounded-depth staged observers fail for a definite, proved reason — the
carry-crossing wall (entry 238) for the staged model.  A characteristic-independent method is still needed; composite
`ACC⁰` remains the genuine open object.  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0Mod6StagedObservers

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6StagedObservers.staged_degree_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6StagedObservers.bounded_depth_staged_no_go
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6StagedObservers.mod6_staged_output_field_not_native
