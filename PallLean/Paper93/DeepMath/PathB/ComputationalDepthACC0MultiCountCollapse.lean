import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0MiniBTTwoCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModGateCrossLayer

/-!
# The k-count collapse: any cross-layer multi-count structure is exactly single-count SYM∘AND (PROVED)

The across-depth capstone.  `ACC0MiniBTTwoCount` collapses *two* counts to one (mixed-radix); my
`topGate_crossLayer_hasMultiSymRep` shows any constant-depth cross-layer ACC⁰ structure is
`HasMultiSymRep` (a joint function of `k` distinct-layer counts).  This file closes the loop: **any**
`k`-count structure collapses to a single-count `SYM∘AND`, exactly, by iterating the mixed-radix merge.

  `multiCount_factors` — for any `k` bottom layers, there is a **single** layer `S` and a decoder `dec`
  such that all `k` counts are recovered from the one count `satCount S`: `satCount (supp i) x =
  dec (satCount S x) i`.

  `hasMultiSymRep_collapses` — hence `HasMultiSymRep F → HasSymAndRep F`: every cross-layer multi-count
  function is *exactly* a single-count `SYM∘AND`.

Combined with `topGate_crossLayer_hasMultiSymRep`, this gives the front-half collapse at the function
level: every constant-depth ACC⁰ structure (symmetric tops over `AND` bottoms, any number of layers)
is **exactly** a single-count `SYM∘AND` — no approximation.

## What is proved (clean axioms, no `sorry`)

* `multiCount_factors` — all `k` layer-counts factor through one count (iterated mixed-radix).
* `hasMultiSymRep_collapses` — `HasMultiSymRep F → HasSymAndRep F`.

## Honest scope

The collapse is **exact** but the single layer `S` it builds has size the **iterated mixed-radix
product** of the `k` layer sizes — a tower (`ACC0MiniBTSize`).  So this is exact, not quasipolynomial:
keeping the collapsed size quasipoly across unbounded depth is the open Beigel–Tarui content.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0MultiCountCollapse

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0Mod6SymAndDepth2
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0MiniBTTwoCount
open PallLean.Paper93.DeepMath.PathB.ACC0SymAndComposition
open PallLean.Paper93.DeepMath.PathB.ACC0ModGateCrossLayer (HasMultiSymRep)

variable {n : ℕ}

/-- **All `k` layer-counts factor through a single count (proved).**  For any family of `k` bottom
layers `supp`, there is one layer `S` and a decoder `dec` with `satCount (supp i) x = dec (satCount S x)
i` for every `x` and `i` — built by iterating the mixed-radix merge of `ACC0MiniBTTwoCount`. -/
theorem multiCount_factors :
    ∀ (k : ℕ) (t : Fin k → ℕ) (supp : (i : Fin k) → Fin (t i) → Finset (Fin n)),
      ∃ (T : ℕ) (S : Fin T → Finset (Fin n)) (dec : ℕ → Fin k → ℕ),
        ∀ x i, satCount (supp i) x = dec (satCount S x) i := by
  intro k
  induction k with
  | zero =>
    intro t supp
    exact ⟨0, Fin.elim0, fun _ => Fin.elim0, fun x i => i.elim0⟩
  | succ k ih =>
    intro t supp
    -- collapse the tail (indices `i.succ`) to one layer `S'` via the IH
    obtain ⟨T', S', dec', hdec'⟩ := ih (fun i => t i.succ) (fun i => supp i.succ)
    -- merge layer `0` (size `t 0`) with `S'` (size `T'`) by the mixed radix `T'+1`
    let se : (Fin (t 0) × Fin (T' + 1)) ⊕ Fin T' → Finset (Fin n) :=
      Sum.elim (fun p => supp 0 p.1) S'
    have hcard : Fintype.card ((Fin (t 0) × Fin (T' + 1)) ⊕ Fin T') = t 0 * (T' + 1) + T' := by
      simp [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    let e : Fin (t 0 * (T' + 1) + T') ≃ ((Fin (t 0) × Fin (T' + 1)) ⊕ Fin T') :=
      (Fintype.equivFinOfCardEq hcard).symm
    have hcount : ∀ x, satCountF se x = (T' + 1) * satCountF (supp 0) x + satCountF S' x := by
      intro x
      show satCountF (Sum.elim (fun p : Fin (t 0) × Fin (T' + 1) => supp 0 p.1) S') x = _
      rw [satCountF_sumElim, satCountF_replicate]
    have hc2 : ∀ x, satCountF S' x < T' + 1 := by
      intro x
      have := satCountF_le_card S' x
      rw [Fintype.card_fin] at this; omega
    refine ⟨t 0 * (T' + 1) + T', fun jx => se (e jx),
      fun s => Fin.cases (s / (T' + 1)) (fun i => dec' (s % (T' + 1)) i), fun x i => ?_⟩
    -- the new single count equals the mixed-radix value
    have hsc : satCount (fun jx => se (e jx)) x = satCountF se x := by
      rw [satCount_eq_satCountF]
      exact Equiv.sum_comp e (fun u => if monoAND (se u) x = true then 1 else 0)
    have hval : satCount (fun jx => se (e jx)) x
        = (T' + 1) * satCount (supp 0) x + satCount S' x := by
      rw [hsc, hcount x, satCount_eq_satCountF (supp 0) x, satCount_eq_satCountF S' x]
    refine Fin.cases ?_ ?_ i
    · -- index 0: recover `c₀ = c⋆ / (T'+1)`
      simp only [Fin.cases_zero, hval]
      rw [Nat.mul_add_div (show 0 < T' + 1 by omega),
        Nat.div_eq_of_lt (by rw [satCount_eq_satCountF]; exact hc2 x), add_zero]
    · -- index `i.succ`: recover the tail via `c⋆ % (T'+1) = c'`
      intro i
      simp only [Fin.cases_succ, hval]
      rw [Nat.mul_add_mod_self_left,
        Nat.mod_eq_of_lt (by rw [satCount_eq_satCountF]; exact hc2 x)]
      exact hdec' x i

/-- **The k-count collapse (proved): every cross-layer multi-count function is single-count `SYM∘AND`.**
`HasMultiSymRep F → HasSymAndRep F`. -/
theorem hasMultiSymRep_collapses {F : (Fin n → Bool) → Bool} (h : HasMultiSymRep F) :
    HasSymAndRep F := by
  obtain ⟨k, t, supp, j, hF⟩ := h
  obtain ⟨T, S, dec, hdec⟩ := multiCount_factors k t supp
  refine ⟨T, S, fun s => j (dec s), fun x => ?_⟩
  rw [hF x]
  congr 1
  funext i
  exact hdec x i

/-!
**k-count collapse proved.**  Any cross-layer multi-count structure (hence, via
`topGate_crossLayer_hasMultiSymRep`, any constant-depth ACC⁰ structure over `AND` bottoms) collapses
*exactly* to a single-count `SYM∘AND`.  The collapsed layer size is the iterated mixed-radix product (a
tower, `ACC0MiniBTSize`): exact, not quasipolynomial.  Quasipoly-across-depth is the open Beigel–Tarui
content.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0MultiCountCollapse

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MultiCountCollapse.multiCount_factors
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MultiCountCollapse.hasMultiSymRep_collapses
