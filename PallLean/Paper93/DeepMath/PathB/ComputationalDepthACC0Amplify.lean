import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Balancedness

/-!
# Brick (amplify) — `t`-fold amplification: the bad set shrinks to `p^{-t}` (proved)

The amplification step of the Razborov–Smolensky `OR` approximator.  A single random linear form errs (vanishes on a
nonzero input) with probability `1/p` (Brick balancedness).  Taking `t` *independent* forms and combining them by `OR`
(`1 - ∏ⱼ(1 - ℓⱼ)`) errs on a fixed nonzero `x` only when **all** `t` forms vanish — and since the forms are independent,
that happens for exactly `(p^{n-1})^t` of the `(p^n)^t` coefficient tuples, i.e. a `p^{-t}` fraction.

This is the genuine independence-multiplies-error fact: the all-bad `t`-tuples are the product of the single-form bad sets,
so their count is the `t`-th power of the single bad count.

## What is proved (clean axioms, no `sorry`)

* **`card_allBad_eq`** (PROVED) — for `x ≠ 0`,
  `(univ.filter (fun a : Fin t → (Fin n → F_p) => ∀ j, ∑ᵢ xᵢ (aⱼ)ᵢ = 0)).card = (p^{n-1})^t` —
  the bad set of `t` independent forms is a `p^{-t}` fraction of all `(p^n)^t` tuples.

## Honest scope

This is the **amplification count** (bad set `= (p^{n-1})^t`, i.e. fraction `p^{-t}`).  It does **not** assemble the union
bound / existence of one globally-good polynomial (next step: `2^n · p^{-t} < 1`), prime-power composition, nor
`composite_BT_degree`.  General YBT remains open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0Amplify

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0Balancedness (card_linearForm_eq_zero)

/-- **`t`-fold amplification (PROVED): the all-bad `t`-tuples are a `p^{-t}` fraction.**
For `x ≠ 0`, the number of `t`-tuples of coefficient vectors on which *every* linear form vanishes is `(p^{n-1})^t`. -/
theorem card_allBad_eq (p n t : ℕ) [Fact p.Prime] (x : Fin n → ZMod p) (hx : x ≠ 0) :
    (Finset.univ.filter
        (fun a : Fin t → (Fin n → ZMod p) => ∀ j, ∑ i, x i * (a j) i = 0)).card
      = (p ^ (n - 1)) ^ t := by
  have hset : (Finset.univ.filter
        (fun a : Fin t → (Fin n → ZMod p) => ∀ j, ∑ i, x i * (a j) i = 0))
      = Fintype.piFinset
          (fun _ : Fin t => Finset.univ.filter (fun b : Fin n → ZMod p => ∑ i, x i * b i = 0)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
  rw [hset, Fintype.card_piFinset]
  simp only [card_linearForm_eq_zero p n x hx]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-!
**`t`-fold amplification, proved.**  The bad set of `t` independent linear forms is `(p^{n-1})^t` — a `p^{-t}` fraction of
all `(p^n)^t` tuples.  So `t` independent forms compute `OR` correctly on each nonzero input with probability `≥ 1 - p^{-t}`,
at degree `t(p-1)`.  Remaining (open, not faked): the union bound giving one globally-good polynomial, and the rest of YBT.
Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0Amplify

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Amplify.card_allBad_eq
