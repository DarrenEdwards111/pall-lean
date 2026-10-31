import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Mod6StagedObservers

/-!
# The composite wall — product-field observers with explicit carry state for MOD₆: where and why they fail

The third honest composite no-go (after entries 280, 281), and the one whose failure mode is literally
`CarryRefinementCrossing`'s namesake.  Entries 280/281 showed that *separating* or *staging* across `F₂` and `F₃` fails
because the polynomial method commits to one characteristic.  The natural next idea: **track both fields at once via an
explicit carry state** — work over the product `ZMod 2 × ZMod 3 ≃ ZMod 6`, carrying the `MOD₂` and `MOD₃` residues
together.  This file proves *why that fails*: the carry state lands you in a ring that is **not a field**, where the
Smolensky machinery has no traction.

**Why the carry crossing fails (proved).**

* *The carry ring is not a field.*  `ZMod 6 ≃ ZMod 2 × ZMod 3` (CRT) has **zero divisors**: `2 · 3 = 0` with `2 ≠ 0`,
  `3 ≠ 0` (equivalently `(1,0)·(0,1) = 0` in the product).  The product of two fields of different characteristic is a
  ring with zero divisors — *not a field*.
* *Fermat fails on the carry ring.*  The degree-halving engine (entry 266) rests on Fermat's little theorem
  `y^{p-1} = [y ≠ 0]`, which needs a *field*.  Over `ZMod 6`, `2^{6-1} = 2 ≠ 1` though `2 ≠ 0`: the Fermat indicator is
  simply false.  No degree-halving, no rank/dimension arguments — the whole method (entries 264–279, *all* over
  `[Field F]` / `[Fact p.Prime]`) cannot be instantiated at the carry state.

So the carry that would couple the two component fields crosses into their product *ring*, losing the field property the
method is built on.  **This is exactly the `CarryRefinementCrossing` obstruction** (entry 238): the carry does not refine
into a single-field computation.

## What is proved (clean axioms, no `sorry`)

* **`carry_state_has_zero_divisors`** (PROVED) — `ZMod 6` has zero divisors (`2 · 3 = 0`, `2 ≠ 0`, `3 ≠ 0`): the carry
  ring is not an integral domain.
* **`prodField_carry_has_zero_divisors`** (PROVED) — the same in the product form `ZMod 2 × ZMod 3`
  (`(1,0)·(0,1) = 0`).
* **`carry_state_not_domain`** (PROVED) — `ZMod 6` is **not** an integral domain (hence not a field).
* **`fermat_fails_on_carry`** (PROVED) — `(2 : ZMod 6) ≠ 0` yet `(2 : ZMod 6)^{6-1} ≠ 1`: Fermat's little theorem, the
  degree-halving engine, fails over the carry ring.
* **`product_field_carry_state_no_traction`** (PROVED) — packages the two obstructions: the carry state is not a field
  *and* Fermat fails there, so the field-essential Smolensky method has no traction.

## Honest scope — a no-go, not a way through

This **does not** prove `MOD₆ ∉ ACC⁰[?]`.  It proves that the carry-state idea fails for a definite reason: tracking
both characteristics forces the product ring `ZMod 6`, which is not a field and where Fermat (the engine of the whole
polynomial method) is false.  The carry does not refine into a single field — the precise content of
`CarryRefinementCrossing` (entry 238).  A genuine composite lower bound needs a method that works over such a ring (or
avoids fields entirely) — a *new idea*.  This is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0Mod6CarryState

/-- **The carry ring has zero divisors (PROVED).**  In `ZMod 6 ≃ ZMod 2 × ZMod 3`, `2 · 3 = 0` with `2 ≠ 0`, `3 ≠ 0`:
the carry state (tracking both residues) lives in a ring with zero divisors — not an integral domain. -/
theorem carry_state_has_zero_divisors : ∃ a b : ZMod 6, a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0 :=
  ⟨2, 3, by decide, by decide, by decide⟩

/-- **The product carry ring has zero divisors (PROVED).**  In `ZMod 2 × ZMod 3`, `(1,0) · (0,1) = 0` with both factors
nonzero — the CRT idempotents witness that the product of the two component fields is not a field. -/
theorem prodField_carry_has_zero_divisors :
    ∃ a b : ZMod 2 × ZMod 3, a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0 :=
  ⟨(1, 0), (0, 1), by decide, by decide, by decide⟩

/-- **The carry ring is not an integral domain (PROVED).**  From the zero divisor `2 · 3 = 0`: `ZMod 6` cannot be a
domain (hence not a field), so the field-only Smolensky machinery cannot run over the carry state. -/
theorem carry_state_not_domain : ¬ IsDomain (ZMod 6) := by
  intro h
  haveI := h
  obtain ⟨a, b, ha, hb, hab⟩ := carry_state_has_zero_divisors
  rcases mul_eq_zero.mp hab with h0 | h0
  · exact ha h0
  · exact hb h0

/-- **Fermat fails on the carry ring (PROVED).**  `(2 : ZMod 6) ≠ 0` yet `(2 : ZMod 6)^{6-1} = 2 ≠ 1`: Fermat's little
theorem `y^{p-1} = 1` (for `y ≠ 0`) — the engine of the degree-halving / Fermat indicator (entry 266) — is *false* over
`ZMod 6`, because `6` is not prime.  The polynomial method's core device does not exist on the carry state. -/
theorem fermat_fails_on_carry : (2 : ZMod 6) ≠ 0 ∧ (2 : ZMod 6) ^ (6 - 1) ≠ 1 :=
  ⟨by decide, by decide⟩

/-- **Product-field-with-carry observers have no traction (PROVED).**  The carry state lives in `ZMod 6 ≃ ZMod 2 × ZMod 3`,
which (i) has zero divisors — *not a field* — and (ii) where Fermat's little theorem fails.  Since the entire Smolensky
polynomial method (entries 264–279) is developed over fields (`[Field F]` / `[Fact p.Prime]`) and rests on the Fermat
indicator, it cannot be instantiated at the carry state.  The carry that would couple the two component fields crosses
into their product *ring*, losing the field property — the `CarryRefinementCrossing` obstruction (entry 238). -/
theorem product_field_carry_state_no_traction :
    (∃ a b : ZMod 6, a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0)
      ∧ ((2 : ZMod 6) ≠ 0 ∧ (2 : ZMod 6) ^ (6 - 1) ≠ 1) :=
  ⟨carry_state_has_zero_divisors, fermat_fails_on_carry⟩

/-!
**The carry-state no-go.**  Tracking both characteristics via an explicit carry forces the product ring
`ZMod 6 ≃ ZMod 2 × ZMod 3`, which is *not a field* (`carry_state_has_zero_divisors`, `carry_state_not_domain`) and where
Fermat — the engine of the degree-halving (entry 266) — is *false* (`fermat_fails_on_carry`).  Every layer of the
Smolensky method (entries 264–279) requires a field; none of it survives the crossing into the carry ring
(`product_field_carry_state_no_traction`).  So product-field observers with explicit carry state fail for the most
literal reason — the carry does not refine into a single field — which is the `CarryRefinementCrossing` wall (entry 238)
itself.  Composite `ACC⁰` needs a method that lives over such a ring or avoids fields; a new idea.  Not faked, not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0Mod6CarryState

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6CarryState.carry_state_has_zero_divisors
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6CarryState.carry_state_not_domain
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6CarryState.fermat_fails_on_carry
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6CarryState.product_field_carry_state_no_traction
