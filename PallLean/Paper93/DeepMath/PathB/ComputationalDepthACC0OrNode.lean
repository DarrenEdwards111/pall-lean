import Mathlib

/-!
# The `OR`-gate laws (De Morgan), standalone — completing `{MOD, AND, OR}` (PROVED)

The mixed `MOD`/`AND` tower (`ACC0MixedTowerValue`/`Degree`) handled `MOD` (Toda) and `AND` (product).
`OR` is the **De Morgan** gate `1 − ∏(1 − ·)`; rather than rebuild the towers with a fourth node, here are
its two laws **generically**, reusable in any tower:

  `dvd_prod_sub_gen` — `∏ f ≡ ∏ g (mod M)` from termwise (the product congruence, generic).
  `or_node_dvd` — the `OR` **value congruence**: `(1 − ∏(1 − f)) ≡ (1 − ∏(1 − g)) (mod M)` from termwise
    `f ≡ g (mod M)` — so an `OR` node over Toda/product representations is `≡` its Boolean output.
  `or_node_deg` — the `OR` **degree law**: `deg(1 − ∏(1 − q)) ≤ ∑ deg q` (same as `AND`).

So `OR` joins `MOD` (Toda, degree `3^k(p−1)`) and `AND` (product, degree `≤` fan-in) with identical
value-congruence and degree behaviour: every gate of ACC⁰[p] is now covered by a Toda-integer law.

## What is proved (clean axioms, no `sorry`)

* `dvd_prod_sub_gen` — generic product divisibility transfer.
* `or_node_dvd` — `OR`-node value congruence.
* `or_node_deg` — `OR`-node degree `≤ ∑` child degrees.

## Honest scope

The `OR`-gate laws (value congruence + degree), generic and standalone — completing the per-gate
integer-route laws for `{MOD, AND, OR}`.  Assembling a full mixed `MOD`/`AND`/`OR` tower, the
exact-quasipoly `2^k` choice, and the `SYM∘AND`/`NEXP ⊄ ACC⁰` cash-out remain the Beigel–Tarui wall.
(Unbounded `AND`/`OR` degree is the no-go — needs RS.)  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0OrNode

open MvPolynomial

variable {α : Type*}

/-- **Generic product divisibility transfer (proved): `∏ f ≡ ∏ g (mod M)` from termwise.** -/
theorem dvd_prod_sub_gen {M : ℤ} (f g : α → ℤ) :
    (L : List α) → (∀ a ∈ L, M ∣ (f a - g a)) → M ∣ ((L.map f).prod - (L.map g).prod)
  | [], _ => by simp
  | a :: t, h => by
      simp only [List.map_cons, List.prod_cons]
      have h1 := h a (by simp)
      have h2 := dvd_prod_sub_gen f g t (fun x hx => h x (by simp [hx]))
      have he : f a * (t.map f).prod - g a * (t.map g).prod
          = f a * ((t.map f).prod - (t.map g).prod) + (f a - g a) * (t.map g).prod := by ring
      rw [he]; exact dvd_add (h2.mul_left _) (h1.mul_right _)

/-- **`OR`-node value congruence (proved): `(1 − ∏(1 − f)) ≡ (1 − ∏(1 − g)) (mod M)`** from termwise
`f ≡ g (mod M)`.  An `OR` node over Toda/product reps equals its Boolean `OR` output mod `M`. -/
theorem or_node_dvd {M : ℤ} (f g : α → ℤ) (L : List α) (h : ∀ a ∈ L, M ∣ (f a - g a)) :
    M ∣ ((1 - (L.map (fun a => 1 - f a)).prod) - (1 - (L.map (fun a => 1 - g a)).prod)) := by
  have hd := dvd_prod_sub_gen (fun a => 1 - f a) (fun a => 1 - g a) L (fun a ha => by
    rw [show (1 - f a) - (1 - g a) = -(f a - g a) from by ring]; exact (h a ha).neg_right)
  rw [show (1 - (L.map (fun a => 1 - f a)).prod) - (1 - (L.map (fun a => 1 - g a)).prod)
    = -((L.map (fun a => 1 - f a)).prod - (L.map (fun a => 1 - g a)).prod) from by ring]
  exact hd.neg_right

/-- **`OR`-node degree law (proved): `deg(1 − ∏(1 − q)) ≤ ∑ deg q`** (same as `AND`). -/
theorem or_node_deg {σ : Type*} (ts : List (MvPolynomial σ ℤ)) :
    (1 - (ts.map (fun q => 1 - q)).prod : MvPolynomial σ ℤ).totalDegree ≤ (ts.map totalDegree).sum := by
  refine le_trans (totalDegree_sub _ _) (max_le (by rw [totalDegree_one]; exact Nat.zero_le _) ?_)
  refine le_trans (totalDegree_list_prod _) ?_
  rw [List.map_map]
  refine List.sum_le_sum (fun q _ => ?_)
  refine le_trans (totalDegree_sub _ _) ?_
  rw [totalDegree_one]; omega

/-!
**`OR`-gate laws proved.**  `OR` (De Morgan) has the same value-congruence and degree behaviour as `AND`,
so it joins `MOD` (Toda) and `AND` (product) — every ACC⁰[p] gate now has its integer-route law.  The
full mixed `MOD`/`AND`/`OR` tower assembly, the exact-quasipoly `2^k` choice, and the cash-out remain the
Beigel–Tarui wall.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0OrNode

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0OrNode.or_node_dvd
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0OrNode.or_node_deg
