import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRazborovSmolenskyAmp

/-!
# Beigel–Tarui, rung 5: the Razborov–Smolensky union bound

Rung 4 (`…RazborovSmolenskyAmp`) proved that on a *fixed* nonzero input, the `t`-tuples of subsets that all fail are a
`2^{-t}` fraction.  This file runs the **union bound over inputs**: since there are fewer than `2ⁿ` nonzero inputs, for
`t > n` a fixed `t`-tuple of subsets exists that **fires on every nonzero input simultaneously** — so the RS
approximator with those subsets computes `OR` *exactly* on all inputs.

The count: the tuples that fail on *some* nonzero input lie in `⋃_{x ≠ 0} allFail x`, whose size is at most
`(#nonzero) · 2^{t(n-1)} < 2ⁿ · 2^{t(n-1)} ≤ 2^{n + t(n-1)}`.  For `t > n` this is `< 2^{nt}`, the total number of
tuples, so a "good" tuple (firing everywhere) exists.

  `mem_allFail` — membership: a tuple is in `allFail x` iff every subset has zero sum on `x`.
  `badT_bound` — **PROVED**: `2^t · #(tuples failing on some nonzero input) ≤ 2ⁿ · (2ⁿ)^t` (union bound + rung 4).
  `exists_good_family` — **PROVED, the union bound**: for `t > n`, some `t`-tuple of subsets fires on *every* nonzero
        input.
  `exists_exact_orApprox` — **PROVED, the capstone**: for `t > n`, a *fixed* list of `t` subsets makes the RS
        approximator (rung 2) compute `OR` exactly on all inputs.

## Honest scope

This yields a *fixed* low-degree-form approximator correct on all inputs — but with `t = n+1`, so its degree is
`(n+1)(p-1)`, higher than `OR`'s exact degree `n`.  It is an **existence** result (derandomising the choice of subsets
over all inputs at once), not a degree win for `OR` itself.  The genuine Beigel–Tarui / Razborov–Smolensky *degree*
gain comes from applying the *small-`t`* approximators (rung 2's degree `t(p-1)`, rung 4's `2^{-t}` error) **per gate**
through a depth-`d` circuit — error `≤ 1/(10·size)` per gate, union over the `size` gates — giving degree `polylog` for
the whole circuit with bounded total error, then folding into one `SYM∘AND` with `m` quasipolynomial.  That per-gate
composition is the remaining Beigel–Tarui content; this file completes the single-`OR` union bound.  Nothing here is the
Beigel–Tarui reduction, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

variable {p n : ℕ} [Fact p.Prime]

open scoped Classical

/-- A tuple is all-fail on `x` iff every one of its subsets has zero sum on `x`. -/
theorem mem_allFail {x : Fin n → Bool} {t : ℕ} {f : Fin t → Finset (Fin n)} :
    f ∈ allFail (p := p) x t ↔ ∀ j, ssum (p := p) (f j) x = 0 := by
  simp [allFail, Fintype.mem_piFinset]

/-- **The union bound count (proved)**: `2^t` times the number of `t`-tuples failing on *some* nonzero input is at most
`2ⁿ · (2ⁿ)^t` — the union over the `< 2ⁿ` nonzero inputs of rung 4's per-input bound. -/
theorem badT_bound (t : ℕ) :
    2 ^ t * ((Finset.univ.filter (fun x : Fin n → Bool => ∃ i, x i = true)).biUnion
        (fun x => allFail (p := p) x t)).card ≤ 2 ^ n * (2 ^ n) ^ t := by
  set NZ := Finset.univ.filter (fun x : Fin n → Bool => ∃ i, x i = true) with hNZ
  calc 2 ^ t * (NZ.biUnion (fun x => allFail (p := p) x t)).card
      ≤ 2 ^ t * ∑ x ∈ NZ, (allFail (p := p) x t).card :=
        Nat.mul_le_mul_left _ Finset.card_biUnion_le
    _ = ∑ x ∈ NZ, 2 ^ t * (allFail (p := p) x t).card := Finset.mul_sum _ _ _
    _ ≤ ∑ _x ∈ NZ, (2 ^ n) ^ t := by
        apply Finset.sum_le_sum
        intro x hx
        rw [hNZ, Finset.mem_filter] at hx
        exact amplification x hx.2 t
    _ = NZ.card * (2 ^ n) ^ t := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 ^ n * (2 ^ n) ^ t := by
        apply Nat.mul_le_mul_right
        calc NZ.card ≤ (Finset.univ : Finset (Fin n → Bool)).card := Finset.card_filter_le _ _
          _ = 2 ^ n := by rw [Finset.card_univ]; simp

/-- **The union bound (proved)**: for `t > n`, there is a fixed `t`-tuple of subsets that fires on *every* nonzero input
— derandomising rung 4's amplification over all inputs simultaneously. -/
theorem exists_good_family (t : ℕ) (hnt : n < t) :
    ∃ f : Fin t → Finset (Fin n),
      ∀ x : Fin n → Bool, (∃ i, x i = true) → ∃ j, ssum (p := p) (f j) x ≠ 0 := by
  set NZ := Finset.univ.filter (fun x : Fin n → Bool => ∃ i, x i = true) with hNZ
  set BadT := NZ.biUnion (fun x => allFail (p := p) x t) with hBadT
  have htot : (Finset.univ : Finset (Fin t → Finset (Fin n))).card = (2 ^ n) ^ t := by
    rw [Finset.card_univ]; simp [Fintype.card_finset]
  have hlt : BadT.card < (2 ^ n) ^ t := by
    have h1 : 2 ^ n * (2 ^ n) ^ t < 2 ^ t * (2 ^ n) ^ t :=
      Nat.mul_lt_mul_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) hnt) (le_refl _)
        (pow_pos (pow_pos two_pos n) t)
    exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt (badT_bound t) h1)
  have hss : BadT ⊂ Finset.univ := by
    rw [Finset.ssubset_univ_iff]
    intro h; rw [h, htot] at hlt; exact lt_irrefl _ hlt
  obtain ⟨f, _, hf⟩ := Finset.exists_of_ssubset hss
  refine ⟨f, fun x hx => ?_⟩
  have hxNZ : x ∈ NZ := by rw [hNZ, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hx⟩
  rw [hBadT, Finset.mem_biUnion] at hf
  push_neg at hf
  have hfx := hf x hxNZ
  rw [mem_allFail] at hfx
  push_neg at hfx
  exact hfx

/-- **The capstone (proved)**: for `t > n`, a *fixed* list of `t` subsets makes the RS approximator (`orApprox`, rung 2)
compute `OR` exactly on every Boolean input — `0` on the all-`false` input, `1` on every nonzero input. -/
theorem exists_exact_orApprox (t : ℕ) (hnt : n < t) :
    ∃ subsets : List (Finset (Fin n)), subsets.length = t ∧
      ∀ x : Fin n → Bool,
        orApprox (p := p) subsets x = (if (∃ i, x i = true) then 1 else 0 : ZMod p) := by
  obtain ⟨f, hf⟩ := exists_good_family (p := p) t hnt
  refine ⟨List.ofFn f, List.length_ofFn, fun x => ?_⟩
  by_cases hx : ∃ i, x i = true
  · rw [if_pos hx]
    obtain ⟨j, hj⟩ := hf x hx
    exact orApprox_fires _ x ⟨f j, List.mem_ofFn.mpr ⟨j, rfl⟩, hj⟩
  · rw [if_neg hx]
    push_neg at hx
    exact orApprox_zero _ x (fun i => by simpa using hx i)

end PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.exists_good_family
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.exists_exact_orApprox
