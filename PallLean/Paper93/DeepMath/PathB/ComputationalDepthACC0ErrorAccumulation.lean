import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SamplingExistence

/-!
# Across-depth error accumulation: composed error grows *linearly* in the gate count, not exponentially

`…ACC0LayerCompose` showed the *degree* of a composed Beigel–Tarui approximant grows by a factor `t` per layer
(`(log s)^{O(d)}` overall — polynomial in `log`).  This file is the *error* counterpart, the other half of the RS
depth composition: composing approximants, the **error grows only linearly in the number of gates** (a union bound),
so a poly-size circuit stays majority-correct with a small per-gate error.

The composite approximant errs at an input `x` only if *some* gate's approximant errs at `x` (correctness composes:
where every gate is correct, the composite is correct).  So the composite error set is contained in the union of the
per-gate error sets, and

```
|composite error|  ≤  ∑_g |error_g|  ≤  (#gates) · e .
```

This is the heart of why *constant* depth works: a depth-`d`, size-`s` circuit has `s` gates, so total error `≤ s·e`;
taking the per-gate error `e < |X| / (2s)` (achievable with the boosting degree polylog) keeps the composite
*majority-correct*.  Linear-in-`s` error, polylog degree (`…ACC0LayerCompose`) — together, the RS depth composition.

## What is proved (clean axioms, no `sorry`)

* `error_union_bound` — `|⋃_g Err g| ≤ (#gates) · e` when each `|Err g| ≤ e` (the union bound).
* `composite_error_bound` — if the composite is correct wherever no gate errs, its error set has size `≤ (#gates)·e`.
* **`exists_majority_correct_composite`** — if `2·(#gates)·e < |X|` (total error `< 1/2`), the composite agrees with
  the target on a **strict majority** of inputs.

## Honest scope

This is the abstract error-accumulation (union-bound) mechanism, over arbitrary per-gate error sets.  The full RS
depth composition combines it with: the degree composition (`…ACC0LayerCompose`); discharging the "composite correct
where all gates correct" hypothesis for the actual gate substitution (the per-point composition); the per-gate
boosting that makes `e` small (`…ACC0ProbabilisticBoost`, `e = 2^{-t}·|X|`); and the `MOD` layer.  Iterating into the
full `ACC⁰ → SYM∘AND` normal form is the rest of the Beigel–Tarui/Yao front half, **Wall 1**.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md` and `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ErrorAccumulation

open Finset

variable {X G : Type*} [Fintype X] [Fintype G] [DecidableEq X]

omit [Fintype X] in
/-- **Union bound (proved): the inputs failing *some* gate number `≤ (#gates)·e`.**  Error accumulates *linearly* in
the gate count. -/
theorem error_union_bound (Err : G → Finset X) (e : ℕ) (hErr : ∀ g, (Err g).card ≤ e) :
    (Finset.univ.biUnion Err).card ≤ Fintype.card G * e := by
  calc (Finset.univ.biUnion Err).card
      ≤ ∑ g : G, (Err g).card := Finset.card_biUnion_le
    _ ≤ ∑ _g : G, e := Finset.sum_le_sum (fun g _ => hErr g)
    _ = Fintype.card G * e := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **The composite error set is contained in the gate-error union (proved).**  Where no gate errs, the composite is
correct (`hcomp`), so the composite errs only where some gate errs. -/
theorem composite_error_subset (Err : G → Finset X) (comp target : X → Bool)
    (hcomp : ∀ x, (∀ g, x ∉ Err g) → comp x = target x) :
    (Finset.univ.filter (fun x => comp x ≠ target x)) ⊆ Finset.univ.biUnion Err := by
  intro x hx
  rw [Finset.mem_filter] at hx
  rw [Finset.mem_biUnion]
  by_contra hne
  push_neg at hne
  exact hx.2 (hcomp x (fun g => hne g (Finset.mem_univ g)))

/-- **Composite error bound (proved): `|composite error| ≤ (#gates)·e`.** -/
theorem composite_error_bound (Err : G → Finset X) (comp target : X → Bool)
    (hcomp : ∀ x, (∀ g, x ∉ Err g) → comp x = target x)
    (e : ℕ) (hErr : ∀ g, (Err g).card ≤ e) :
    (Finset.univ.filter (fun x => comp x ≠ target x)).card ≤ Fintype.card G * e :=
  le_trans (Finset.card_le_card (composite_error_subset Err comp target hcomp))
    (error_union_bound Err e hErr)

/-- **Majority-correct composite (proved): if total error `< 1/2`, the composite agrees with the target on a strict
majority of inputs.**  `2·(#gates)·e < |X|` ⇒ `|X| < 2·|correct|`.  Linear error accumulation keeps the composite
majority-correct across the whole circuit. -/
theorem exists_majority_correct_composite (Err : G → Finset X) (comp target : X → Bool)
    (hcomp : ∀ x, (∀ g, x ∉ Err g) → comp x = target x)
    (e : ℕ) (hErr : ∀ g, (Err g).card ≤ e)
    (hsmall : 2 * (Fintype.card G * e) < Fintype.card X) :
    Fintype.card X < 2 * (Finset.univ.filter (fun x => comp x = target x)).card := by
  have hbad := composite_error_bound Err comp target hcomp e hErr
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset X)) (fun x => comp x = target x)
  rw [Finset.card_univ] at hpart
  simp only [ne_eq] at hbad
  omega

end PallLean.Paper93.DeepMath.PathB.ACC0ErrorAccumulation

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ErrorAccumulation.error_union_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ErrorAccumulation.composite_error_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ErrorAccumulation.exists_majority_correct_composite
