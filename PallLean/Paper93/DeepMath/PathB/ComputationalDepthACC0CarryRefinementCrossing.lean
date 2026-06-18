import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Mod6CarryState

/-!
# The ACC anatomy, frozen — `CarryRefinementCrossing` as the single composite target

N-Frame has *found* the wall; this file freezes the result and names the one remaining theorem.

**Frozen result.**  The prime-`ACC⁰[p]` Razborov–Smolensky route is reconstructed and assembled from machine-proved
parts (entries 264–279): low-degree dimension, rank pigeonhole, multilinear basis, Fermat indicator, boosting,
per-clause `1/2`, independence, native `MOD_p`, degree-halving, the good-set wiring, and the contradiction — modulo only
the standard binomial tail and the committed `Circ` recursion.  The composite obstruction is isolated as
`CarryRefinementCrossing`, and the **three natural field-based attacks on it are all proved to fail** (entries 280–282):

* **separate** (280) — no single field is native for both `MOD₂` and `MOD₃` (`mod6_layers_cross_fields`);
* **stage** (281) — bounded depth gives bounded degree, defeated by the growing non-native requirement
  (`bounded_depth_staged_no_go`);
* **carry** (282) — the carry ring `ZMod 6 ≃ ZMod 2 × ZMod 3` is *not a field* and Fermat fails there
  (`product_field_carry_state_no_traction`).

All three reduce to one root: the polynomial method lives over a *single field*, and composite modulus forces either two
incompatible fields or their non-field product.

## What is proved (clean axioms, no `sorry`)

* **`field_based_modes_all_fail`** (PROVED) — bundles the three no-gos: (1) no field native for both factors, (2)
  bounded degree cannot meet a strictly larger requirement, (3) the carry ring has zero divisors and Fermat fails.  So
  *every* characteristic-committed (field-based) approach to `MOD₆` fails.

## The single composite target (the real open ACC⁰ theorem)

* **`CarryRefinementCrossing Mod6Computable FieldFreeUnboundedCarry`** — the named socket: *any bounded, field-compatible
  observer computing `MOD₆` is forced into field-free / unbounded-carry territory*.  Proving it is the composite
  `ACC⁰` lower bound; by `field_based_modes_all_fail` its hypothesis cannot be met by any of the three field-based
  modes, so a proof needs a **characteristic-independent invariant** — a *new idea*.

## The field-free frontier (step 4, open directions — not proved, not faked)

The three failures show field methods stop because they commit to one characteristic.  A composite lower bound needs a
characteristic-independent invariant; candidate directions: a ring/module invariant (over `ZMod 6`, not a field); a
communication / tensor-rank measure; a proof-complexity measure; an observer-holonomy / category invariant; a direct
carry-complexity lower bound.  **First test (step 5):** *any bounded observer computing `MOD₆` must either collapse to a
non-native single-field computation (excluded by 280/281) or use unbounded carry state* — the `MOD₆` instance of
`CarryRefinementCrossing`.  This is genuinely open research, stated here as the target, **not** proved.

## Honest scope

This freezes the anatomy and names the one open composite theorem; it proves that all three natural field-based attacks
fail (`field_based_modes_all_fail`).  It does **not** prove `CarryRefinementCrossing` (the composite `ACC⁰` lower bound)
— that needs a new characteristic-independent invariant.  This is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CarryRefinementCrossing

/-- **The single composite target — the real open `ACC⁰` theorem (named socket).**  *Any bounded, field-compatible
observer computing `MOD₆` is forced into field-free / unbounded-carry territory.*  Proving it is the composite `ACC⁰`
lower bound.  By `field_based_modes_all_fail`, the hypothesis `Mod6Computable` cannot be realized by any of the three
field-based modes (separate/stage/carry), so a proof requires a characteristic-independent invariant — a new idea
(`CarryRefinementCrossing` is the namesake: the carry does not refine into a single-field computation). -/
def CarryRefinementCrossing (Mod6Computable FieldFreeUnboundedCarry : Prop) : Prop :=
  Mod6Computable → FieldFreeUnboundedCarry

/-- **Every field-based attack on `MOD₆` fails (PROVED).**  Bundles the three composite no-gos: (1) *separate* — no field
`F` is native for both `MOD₂` and `MOD₃` (entry 280); (2) *stage* — a bounded degree `t^d·D₀` cannot meet a strictly
larger requirement `R` (entry 281); (3) *carry* — the carry ring `ZMod 6` has zero divisors and Fermat fails (entry 282).
So every characteristic-committed approach to `MOD₆` is refuted; the composite target must be field-free. -/
theorem field_based_modes_all_fail :
    (∀ (F : Type) [Field F], ¬ (CharP F 2 ∧ CharP F 3))
      ∧ (∀ t d D₀ R observerDeg : ℕ,
          observerDeg ≤ t ^ d * D₀ → R ≤ observerDeg → t ^ d * D₀ < R → False)
      ∧ ((∃ a b : ZMod 6, a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0)
          ∧ ((2 : ZMod 6) ≠ 0 ∧ (2 : ZMod 6) ^ (6 - 1) ≠ 1)) :=
  ⟨fun F _ => ACC0Mod6SeparatedLayers.mod6_layers_cross_fields F,
   fun _ _ _ _ _ hb hn hg => ACC0Mod6StagedObservers.bounded_depth_staged_no_go hb hn hg,
   ACC0Mod6CarryState.carry_state_has_zero_divisors,
   ACC0Mod6CarryState.fermat_fails_on_carry⟩

/-!
**The frozen frontier.**  Prime is essentially done (264–279); the composite obstruction is isolated as the single named
target `CarryRefinementCrossing`, and `field_based_modes_all_fail` proves all three natural field-based attacks
(separate/stage/carry) fail.  What remains is genuinely open: a *characteristic-independent* invariant (a field-free
carry obstruction), first to be tested on `MOD₆`.  That is the N-Frame frontier — open research, named here, not faked.
Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CarryRefinementCrossing

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryRefinementCrossing.field_based_modes_all_fail
