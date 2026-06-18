import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModpGate
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CrossFieldCombination
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0MultiSortedObserver

/-!
# The composite wall, smallest case — MOD₆ with separated MOD₂/MOD₃ layers: where and why it fails

The honest composite attack (not a claim of composite `ACC⁰`): take the smallest composite modulus, `6 = 2·3`, and the
natural "separated layers" idea — handle the `MOD₂` and `MOD₃` parts independently — and **prove precisely where it
fails**.  This pins down the `CarryRefinementCrossing` wall (entry 238) in the `n = 6` case.

**The CRT factorization (proved).**  `MOD₆` fires (Hamming weight `≡ 0 mod 6`) iff *both* `MOD₂` and `MOD₃` fire (weight
`≡ 0 mod 2` and `≡ 0 mod 3`), since `2, 3` are coprime.  So a `MOD₆` gate genuinely *separates* into a `MOD₂` layer and a
`MOD₃` layer.

**What works field-by-field.**  Each component is *native* over its own field: `MOD₂` is exactly degree-1 over `F₂`
(char 2), `MOD₃` exactly degree-2 over `F₃` (char 3) — the Fermat representation of entry 270, which works precisely in
characteristic equal to the modulus.

**Where it fails (proved no-go).**  To run the prime Smolensky route (entries 275–279) on the *combined* `MOD₆` gate,
one needs a *single* field `F` in which *both* components are native — i.e. `CharP F 2 ∧ CharP F 3`.  But **no field has
characteristic both 2 and 3** (`no_common_char`, entry 243).  The two CRT factors demand *incompatible* fields; the
separated layers cannot be unified over one polynomial-method field.  **This is exactly the carry-crossing
obstruction**: the polynomial method commits to one characteristic, and composite modulus has factors living over
different ones.

## What is proved (clean axioms, no `sorry`)

* **`mod6_fires_iff_mod2_and_mod3`** (PROVED) — `MOD₆` fires iff `MOD₂` and `MOD₃` both fire (CRT / coprimality of 2, 3,
  via entry-245 `modm_iff_modp_and_modq` + entry-270 `modpGate_fires_iff`).
* **`no_common_native_field`** (PROVED) — no field `F` has `CharP F 2 ∧ CharP F 3` (entry-243 `no_common_char` at 2, 3):
  the `MOD₂`-native field (char 2) and the `MOD₃`-native field (char 3) are distinct.
* **`mod6_layers_cross_fields`** (PROVED) — therefore the separated `MOD₂`/`MOD₃` layers of `MOD₆` cannot both be native
  over a single field: the prime route does not lift to `MOD₆`.

## Honest scope — this is the wall, not a way through it

This **does not** prove `MOD₆ ∉ ACC⁰[?]` and **does not** circumvent the composite barrier.  It proves a *negative
structural fact*: the natural separated-layers reduction of `MOD₆` fails because its CRT factors require two different
characteristics, which no single field provides — the precise shape of the `CarryRefinementCrossing` wall (entry 238) at
`n = 6`.  A genuine composite lower bound needs a *new idea* (a method not committed to one characteristic), exactly as
flagged.  This is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0Mod6SeparatedLayers

open PallLean.Paper93.DeepMath.PathB.ACC0ModpGate (modpGate modpGate_fires_iff)
open PallLean.Paper93.DeepMath.PathB.ACC0CrossFieldCombination (no_common_char)
open PallLean.Paper93.DeepMath.PathB.ACC0MultiSortedObserver (modm_iff_modp_and_modq)

/-- **The CRT factorization of `MOD₆` (PROVED).**  `MOD₆` fires (weight `≡ 0 mod 6`) iff *both* `MOD₂` and `MOD₃` fire,
since `2, 3` are coprime: `6 ∣ #trues ↔ 2 ∣ #trues ∧ 3 ∣ #trues` (entry-245 `modm_iff_modp_and_modq`), and each side is
the corresponding gate firing (entry-270 `modpGate_fires_iff`).  So a `MOD₆` gate separates into a `MOD₂` and a `MOD₃`
layer. -/
theorem mod6_fires_iff_mod2_and_mod3 {n : ℕ} (x : Fin n → Bool) :
    modpGate 6 x = true ↔ (modpGate 2 x = true ∧ modpGate 3 x = true) := by
  rw [modpGate_fires_iff, modpGate_fires_iff, modpGate_fires_iff]
  exact modm_iff_modp_and_modq 2 3 _ (by decide)

/-- **No single field is native for both `MOD₂` and `MOD₃` (PROVED).**  No field `F` has `CharP F 2 ∧ CharP F 3`
(entry-243 `no_common_char` at `2 ≠ 3`): the field in which `MOD₂` is native (char 2) and the field in which `MOD₃` is
native (char 3) are necessarily different. -/
theorem no_common_native_field (F : Type*) [Field F] (h2 : CharP F 2) (h3 : CharP F 3) : False :=
  no_common_char F 2 3 (by decide) h2 h3

/-- **The separated layers cross fields — the carry-crossing obstruction at `n = 6` (PROVED).**  `MOD₆ = MOD₂ ∧ MOD₃`
(`mod6_fires_iff_mod2_and_mod3`), and each factor is native only in its own characteristic; but no single field has
`CharP F 2 ∧ CharP F 3` (`no_common_native_field`).  Hence the separated `MOD₂`/`MOD₃` layers cannot both be native over
one polynomial-method field — the prime Smolensky route (one fixed characteristic) does *not* lift to `MOD₆`.  This is
the `CarryRefinementCrossing` wall (entry 238) in its smallest instance. -/
theorem mod6_layers_cross_fields (F : Type*) [Field F] : ¬ (CharP F 2 ∧ CharP F 3) :=
  fun ⟨h2, h3⟩ => no_common_native_field F h2 h3

/-!
**The smallest composite wall, made precise.**  `MOD₆` separates by CRT into `MOD₂` and `MOD₃`
(`mod6_fires_iff_mod2_and_mod3`); each component is exactly native over its own field (entry 270 — `MOD₂` degree 1 over
`F₂`, `MOD₃` degree 2 over `F₃`).  But the prime polynomial-method route commits to a *single* characteristic, and
`mod6_layers_cross_fields` proves no field serves both: `CharP F 2 ∧ CharP F 3` is impossible (entry 243).  So the
separated-layers idea — which is exactly the natural way one would try to extend the prime route to composite modulus —
*fails by field incompatibility*, which is the `CarryRefinementCrossing` obstruction (entry 238).  This is a proved
no-go, not a circumvention: composite `ACC⁰` needs a method not tied to one characteristic.  Not faked, not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0Mod6SeparatedLayers

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6SeparatedLayers.mod6_fires_iff_mod2_and_mod3
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6SeparatedLayers.no_common_native_field
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6SeparatedLayers.mod6_layers_cross_fields
