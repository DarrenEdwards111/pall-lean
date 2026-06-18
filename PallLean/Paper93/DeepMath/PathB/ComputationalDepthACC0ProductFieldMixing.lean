import Mathlib

/-!
# Product-field mixing — the MOD₆ one-layer laboratory: one layer composes without collapse; depth is the wall

This is the smallest honest test of cross-field circuit mixing (the irreducible core of `ACC0_ANATOMY.md`): can an
`ACC⁰` circuit mixing `MOD_2` and `MOD_3` gates be tracked by a product-field observer (residues mod 2 *and* mod 3)
without collapsing to `F_2` or `F_3`?  The MOD₆ case (`MOD_6 = MOD_2 ∧ MOD_3`) is the laboratory.

The finding splits cleanly by **depth**:

* **One layer composes *without* collapse (PROVED).**  A single layer of mixed `MOD_2`/`MOD_3` gates feeding a Boolean
  combiner has output determined by the **product observer state** `(count mod 2, count mod 3)` — equivalently
  `count mod 6` (CRT, `ZMod 6 ≅ ZMod 2 × ZMod 3`).  The gate outputs are *bits*; the combiner is a *Boolean* operation on
  bits, which touches **no** field arithmetic — so nothing forces a common characteristic.  The observer has `≤ 6`
  cells (bounded, no blow-up).  This is a genuine partial crossing: depth-1 mixing is fine.
* **Depth ≥ 2 is the wall (socket).**  A `MOD_3` gate *fed by* a `MOD_2` output (or vice versa) must arithmetize the
  non-native `MOD_2` bit over `F_3` — and `MOD_2` (parity) is not low-degree over `F_3` (Smolensky / in-arc
  `Layer3.parity_function_lower_bound`, entry 244).  So the cross-field collapse is forced *only* by nesting different-
  modulus gates — the depth composition, not the one-layer mix.

So the MOD₆ laboratory **localizes the wall further**: the cross-field mixing obstruction lives specifically at
**depth ≥ 2 nesting of different-modulus `MOD` gates**, not at single-layer mixing (which the product observer handles).

⚠️ **No crossing.**  The proved part is the one-layer no-collapse fact.  The depth-2 nested representation — making the
product observer compose *through* a non-native gate without collapsing — is the open core, not built here.

## What is proved (clean axioms, no `sorry`)

* **`mixedOut comb k := comb (decide (k % 2 = 0)) (decide (k % 3 = 0))`** — a one-layer mixed `MOD_2`/`MOD_3` output
  (Boolean combiner of the two gate-output bits at count `k`).
* **`mixedOut_determined`** (PROVED, **no axioms**) — determined by the product observer state: equal residues mod 2 and
  mod 3 give equal output.  No collapse to a single field.
* **`mixedOut_determined_by_mod6`** (PROVED) — equivalently determined by `count mod 6` (CRT product observer
  `ZMod 6 ≅ ZMod 2 × ZMod 3`).
* **`mixedOut_cells_le_six`** (PROVED) — the one-layer mixed observer has `≤ 6` cells: bounded, no blow-up.

## The depth obstruction (named, not proved)

A depth-≥2 nesting (`MOD_q` fed by a non-native `MOD_p` output, `p ≠ q`) forces arithmetizing `MOD_p` over `F_q`, which
is Smolensky-blocked (`Layer3.parity_function_lower_bound` for `MOD_2` over `F_p`; `Layer4.mod_q_indicators_false`
generally, entry 244).  Whether a product-field observer can compose *through* such a nesting without collapsing is the
open `ACC⁰[composite]` core (entry-238 `CarryRefinementCrossing`).  Not built here.

## Honest scope

This proves that **one layer** of mixed `MOD_2`/`MOD_3` gates is tracked by the product observer (count mod 6) without
collapse, with bounded cells — a genuine partial crossing localizing the wall to depth.  It does **not** build the
depth-≥2 nested representation, where Smolensky blocks the non-native arithmetization.  So the MOD₆ laboratory refines
the localization: the cross-field mixing wall is at depth nesting, not single-layer mixing.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ProductFieldMixing

/-- A one-layer mixed `MOD_2`/`MOD_3` output at count `k`: a Boolean combiner of the two gate-output bits
`[k ≡ 0 mod 2]` and `[k ≡ 0 mod 3]`. -/
def mixedOut (comb : Bool → Bool → Bool) (k : ℕ) : Bool :=
  comb (decide (k % 2 = 0)) (decide (k % 3 = 0))

/-- **One-layer mixing composes without collapse (PROVED, no axioms).**  The mixed output is determined by the *product*
observer state `(count mod 2, count mod 3)`: equal residues mod 2 and mod 3 give equal output.  The gate outputs are
bits and the combiner is Boolean, so nothing forces a single field. -/
theorem mixedOut_determined (comb : Bool → Bool → Bool) (k k' : ℕ)
    (h2 : k % 2 = k' % 2) (h3 : k % 3 = k' % 3) :
    mixedOut comb k = mixedOut comb k' := by
  unfold mixedOut; rw [h2, h3]

/-- **Equivalently, determined by `count mod 6` (PROVED).**  The CRT product observer `ZMod 6 ≅ ZMod 2 × ZMod 3` reads
the one-layer mixed output; `count mod 6` determines both residues (`6 = 2·3`). -/
theorem mixedOut_determined_by_mod6 (comb : Bool → Bool → Bool) (k k' : ℕ)
    (h : k % 6 = k' % 6) : mixedOut comb k = mixedOut comb k' := by
  apply mixedOut_determined
  · have e2 : ∀ j : ℕ, j % 6 % 2 = j % 2 := fun j => Nat.mod_mod_of_dvd j (by norm_num)
    rw [← e2 k, ← e2 k', h]
  · have e3 : ∀ j : ℕ, j % 6 % 3 = j % 3 := fun j => Nat.mod_mod_of_dvd j (by norm_num)
    rw [← e3 k, ← e3 k', h]

/-- **The one-layer mixed observer has `≤ 6` cells (PROVED).**  Its values are determined by `count mod 6`
(`mixedOut_determined_by_mod6`), so the distinct outputs over a period are bounded by 6 — no blow-up, no collapse. -/
theorem mixedOut_cells_le_six (comb : Bool → Bool → Bool) :
    (Finset.image (fun k => mixedOut comb k) (Finset.range 6)).card ≤ 6 := by
  calc (Finset.image (fun k => mixedOut comb k) (Finset.range 6)).card
      ≤ (Finset.range 6).card := Finset.card_image_le
    _ = 6 := Finset.card_range 6

/-!
**The depth obstruction (named, not proved).**  The one-layer result above composes the per-prime observers through a
Boolean combiner with no collapse.  At **depth ≥ 2** — a `MOD_q` gate fed by a non-native `MOD_p` output — the inner
bit must be arithmetized over `F_q`, where it is high-degree (Smolensky: `Layer3.parity_function_lower_bound` /
`Layer4.mod_q_indicators_false`, entry 244).  Whether the product observer composes *through* such a nesting without
collapsing is the open `ACC⁰[composite]` core (entry-238 `CarryRefinementCrossing`).  Not built here.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ProductFieldMixing

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ProductFieldMixing.mixedOut_determined
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ProductFieldMixing.mixedOut_determined_by_mod6
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ProductFieldMixing.mixedOut_cells_le_six
