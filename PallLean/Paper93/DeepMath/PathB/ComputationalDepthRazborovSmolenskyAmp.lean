import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRazborovSmolenskyProb

/-!
# Beigel–Tarui, rung 4: the Razborov–Smolensky amplification

Rung 3 (`…RazborovSmolenskyProb`) proved that on any fixed nonzero input, at least half the subsets fire
(`Pr[fire] ≥ 1/2`).  This file **amplifies** that: with `t` independent subsets, the probability (over the choice of
subsets) that **none** fires on a fixed nonzero input drops to `≤ 2^{-t}`.

The argument is a product: the `t`-tuples of subsets that *all* fail on `x` are exactly the tuples landing in the
"bad" (zero-sum) set at every coordinate, so their count is `(#bad)^t`.  Raising rung 3's `2·(#bad) ≤ 2ⁿ` to the `t`-th
power gives `2^t · (#bad)^t ≤ (2ⁿ)^t` — i.e. the all-fail tuples are a `2^{-t}` fraction of all `(2ⁿ)^t` tuples.

  `allFail` — the `t`-tuples of subsets that *all* have zero sum on `x` (as a `Fintype.piFinset`).
  `allFail_card` — **PROVED**: `#allFail = (#bad)^t` (a product count).
  `amplification` — **PROVED, the amplification**: for any nonzero input, `2^t · #allFail ≤ (2ⁿ)^t` — the all-fail
        `t`-tuples are a `2^{-t}` fraction of all tuples; the failure probability decays geometrically in `t`.

## Honest scope

This is the geometric `2^{-t}` failure decay — the amplification step.  With rung 2's `orApprox_fires` it says: a
`t`-subset RS approximator (degree `t·(p-1)`) is wrong on a fixed nonzero input for only a `2^{-t}` fraction of subset
choices.  What remains for Beigel–Tarui: (i) the **union bound over inputs** — since there are `< 2ⁿ` nonzero inputs, for
`t > n` a union bound gives a *single* subset-family firing on **all** of them at once (an existence argument;
degree `(n+1)(p-1)`), or, keeping `t` small, a family correct on all but a `2ⁿ·2^{-t}` fraction; (ii) applying the
low-degree approximators **per gate** through a depth-`d` circuit (error `≤ 1/(10·size)` per gate, union over gates) to
get degree `polylog` for the whole circuit; and (iii) folding into one `SYM∘AND` with `m` quasipolynomial.  This file
supplies the amplification the union bound runs on.  Nothing here is the Beigel–Tarui reduction, `NEXP ⊄ ACC⁰`, or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

variable {p n : ℕ} [Fact p.Prime]

open scoped Classical

/-- The `t`-tuples of subsets that *all* have zero sum on `x` — the tuples on which a `t`-subset approximator fails. -/
noncomputable def allFail (x : Fin n → Bool) (t : ℕ) : Finset (Fin t → Finset (Fin n)) :=
  Fintype.piFinset (fun _ : Fin t => Finset.univ.filter (fun S : Finset (Fin n) => ssum (p := p) S x = 0))

/-- **Product count (proved)**: the number of all-fail `t`-tuples is `(#bad)^t`. -/
theorem allFail_card (x : Fin n → Bool) (t : ℕ) :
    (allFail (p := p) x t).card
      = (Finset.univ.filter (fun S : Finset (Fin n) => ssum (p := p) S x = 0)).card ^ t := by
  rw [allFail, Fintype.card_piFinset]
  simp [Finset.prod_const]

/-- **The amplification (proved)**: for any nonzero Boolean input, the `t`-tuples of subsets that *all* fail number at
most a `2^{-t}` fraction of all `(2ⁿ)^t` tuples — `2^t · #allFail ≤ (2ⁿ)^t`.  The failure probability of a `t`-subset
approximator decays geometrically in `t`. -/
theorem amplification (x : Fin n → Bool) (hx : ∃ i, x i = true) (t : ℕ) :
    2 ^ t * (allFail (p := p) x t).card ≤ (2 ^ n) ^ t := by
  obtain ⟨i₀, hi⟩ := hx
  have hbad : 2 * (Finset.univ.filter (fun S : Finset (Fin n) => ssum (p := p) S x = 0)).card ≤ 2 ^ n :=
    subset_sum_zero_card_le (p := p) x i₀ (xf_ne_zero (p := p) hi)
  rw [allFail_card]
  calc 2 ^ t * (Finset.univ.filter (fun S : Finset (Fin n) => ssum (p := p) S x = 0)).card ^ t
      = (2 * (Finset.univ.filter (fun S : Finset (Fin n) => ssum (p := p) S x = 0)).card) ^ t := by
        rw [mul_pow]
    _ ≤ (2 ^ n) ^ t := Nat.pow_le_pow_left hbad t

end PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.allFail_card
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.amplification
