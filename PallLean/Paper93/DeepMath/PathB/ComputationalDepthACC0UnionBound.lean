import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Amplify

/-!
# Brick (union bound) — existence of one globally-good random-form choice (proved)

The probabilistic-method completion of the Razborov–Smolensky `OR` approximator.  Each test input `x ≠ 0` is "killed" (the
`t`-fold approximator errs on it) by only `(p^{n-1})^t` of the coefficient tuples (Brick amplify).  Union-bounding over a
finite set `X` of test inputs: if `|X| · (p^{n-1})^t < (p^n)^t` — i.e. the bad tuples are fewer than the total `(p^n)^t` —
then some coefficient tuple `a` is good for *every* `x ∈ X` simultaneously (some linear form is nonzero on each `x`).

This turns the per-input error bound into one *fixed* degree-`t(p-1)` polynomial correct on all of `X` at once.  The
threshold is met whenever `|X| < p^t` (e.g. `X` = the nonzero Boolean inputs, `|X| ≤ 2^n`, and `t` with `p^t > 2^n`).

## What is proved (clean axioms, no `sorry`)

* **`exists_good_form`** (PROVED) — given `X` of nonzero vectors with `X.card · (p^{n-1})^t < (p^n)^t`, there is a tuple
  `a : Fin t → (Fin n → F_p)` with `∀ x ∈ X, ∃ j, ∑ᵢ xᵢ (aⱼ)ᵢ ≠ 0` (correct, via Fermat, on every `x ∈ X`).

## Honest scope

This is the **existence** of a good coefficient choice (the union bound + pigeonhole over a given test set).  It does **not**
package the resulting object as a single `MvPolynomial` `OR`-approximator with its degree certificate wired to the circuit
model, the prime-power composition, nor `composite_BT_degree`.  General YBT remains open.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UnionBound

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0Amplify (card_allBad_eq)

/-- **Union bound (PROVED): a globally-good random-form choice exists.**  If the bad tuples are fewer than the total, some
coefficient tuple `a` makes a nonzero linear form on every `x ∈ X`. -/
theorem exists_good_form (p n t : ℕ) [Fact p.Prime] (X : Finset (Fin n → ZMod p)) (hX : ∀ x ∈ X, x ≠ 0)
    (hlt : X.card * (p ^ (n - 1)) ^ t < (p ^ n) ^ t) :
    ∃ a : Fin t → (Fin n → ZMod p), ∀ x ∈ X, ∃ j, ∑ i, x i * (a j) i ≠ 0 := by
  -- The bad set has card `≤ |X| · (p^{n-1})^t` (union bound + amplify).
  have hBcard : (X.biUnion (fun x => Finset.univ.filter
        (fun a : Fin t → (Fin n → ZMod p) => ∀ j, ∑ i, x i * (a j) i = 0))).card
      ≤ X.card * (p ^ (n - 1)) ^ t := by
    calc (X.biUnion (fun x => Finset.univ.filter
            (fun a : Fin t → (Fin n → ZMod p) => ∀ j, ∑ i, x i * (a j) i = 0))).card
        ≤ ∑ x ∈ X, (Finset.univ.filter
            (fun a : Fin t → (Fin n → ZMod p) => ∀ j, ∑ i, x i * (a j) i = 0)).card :=
          Finset.card_biUnion_le
      _ = ∑ _x ∈ X, (p ^ (n - 1)) ^ t :=
          Finset.sum_congr rfl (fun x hx => card_allBad_eq p n t x (hX x hx))
      _ = X.card * (p ^ (n - 1)) ^ t := by rw [Finset.sum_const, smul_eq_mul]
  -- The total is `(p^n)^t`, strictly larger, so the bad set is not everything.
  have hUcard : (Finset.univ : Finset (Fin t → (Fin n → ZMod p))).card = (p ^ n) ^ t := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin,
      Fintype.card_fin]
  have hne : (X.biUnion (fun x => Finset.univ.filter
        (fun a : Fin t → (Fin n → ZMod p) => ∀ j, ∑ i, x i * (a j) i = 0))) ≠ Finset.univ := by
    intro h
    rw [h, hUcard] at hBcard
    exact absurd (lt_of_lt_of_le hlt hBcard) (lt_irrefl _)
  -- Pick a tuple outside the bad set: it is good on every `x ∈ X`.
  obtain ⟨a, haB⟩ : ∃ a, a ∉ (X.biUnion (fun x => Finset.univ.filter
      (fun a : Fin t → (Fin n → ZMod p) => ∀ j, ∑ i, x i * (a j) i = 0))) := by
    by_contra h
    push_neg at h
    exact hne (Finset.eq_univ_iff_forall.mpr h)
  refine ⟨a, fun x hxX => ?_⟩
  by_contra hc
  push_neg at hc
  exact haB (Finset.mem_biUnion.mpr ⟨x, hxX, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩⟩)

/-!
**Union bound, proved.**  When the bad tuples (`≤ |X| · (p^{n-1})^t`) are fewer than the total (`(p^n)^t`) — equivalently
`|X| < p^t` — a single coefficient tuple computes `OR` correctly on every `x ∈ X` at degree `t(p-1)`.  With `card_allBad_eq`
and `orApprox`, this is the existence of the RS approximate `OR` polynomial.  Remaining (open, not faked): packaging as one
`MvPolynomial` with degree certificate, prime-power composition, circuit assembly.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UnionBound

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UnionBound.exists_good_form
