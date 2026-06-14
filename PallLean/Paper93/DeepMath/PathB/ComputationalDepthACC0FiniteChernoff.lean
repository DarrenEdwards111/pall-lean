import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ProbabilisticBoost

/-!
# A self-contained finite Chernoff bound (for the boosting → quasipoly sampling step)

The boosting step (`…ACC0ProbabilisticBoost`) produces a *full* family of forms that is majority-correct at every
input, but of *exponential* size.  The last gate of the Beigel–Tarui front half is the **sampling**: extract a
*quasipolynomial* subfamily that is still majority-correct everywhere, by a Chernoff concentration + union bound.
Mathlib's Chernoff/Hoeffding live in the measure-theoretic `ProbabilityTheory` framework; this file instead proves a
**self-contained, purely combinatorial Chernoff lower-tail bound** that stays in the `Finset`/`ℕ`/`ℝ` counting world
of the rest of the construction — no measure theory, no `exp`.

The bound is the classical Markov-on-a-product (Chernoff) argument, finite form.  Sampling `r` items from a finite
population `P` (a sample is `σ : Fin r → P`), with a "good" set `G ⊆ P`, the number of samples whose good-count is a
*minority* (`2·good ≤ r`) is bounded for every real multiplier `c ≥ 1`:

```
#{σ : Fin r → P | 2·#{i | σ i ∈ G} ≤ r}  ≤  ((|G|/c) + c·(|P| − |G|))^r .
```

The engine is the counting identity `∑_{σ : Fin r → P} ∏_i f(σ i) = (∑_x f x)^r` (`Finset.sum_prod_piFinset`) — the
finite analogue of independence/`E[∏] = ∏ E`.  When the good fraction exceeds `1/2`, choosing `c` makes the base
`< |P|`, so the minority-count fraction decays geometrically in `r` — exactly the concentration the union bound needs.
The corollary `finite_chernoff_majority` records the clean `c = 2`, good-fraction-`≥ 3/4` case (base `≤ 7|P|/8`).

## What is proved (clean axioms, no `sorry`)

* `finite_chernoff_lower` — the finite Chernoff lower-tail count bound, for every `c ≥ 1`.
* `finite_chernoff_majority` — the `c = 2` corollary: if `4|G| ≥ 3|P|`, the minority-count samples are `≤ (7|P|/8)^r`,
  geometric decay (base `7/8 < 1` relative to `|P|`).

## Honest scope — what this is and what remains

This is the concentration engine, self-contained.  It is **not** the finished sampling step.  To extract a
quasipolynomial majority-correct subfamily one must still: (1) instantiate `P` as the boosted form-tuples and `G` as
the per-input correct set (`|G| ≥ 3|P|/4` from `…ACC0ProbabilisticBoost`, `t ≥ 2`); (2) take the **union bound** over
the `2^n` inputs — `∑_v #{bad at v} ≤ 2^n·(7|P|/8)^r < |P|^r` for `r = O(n)`, giving a sample correct at *every* input
by pigeonhole.  Step (2) plus the parity-vs-`monoAND` basis bridge is the remaining assembly of the Beigel–Tarui
front half, **Wall 1** — routine given this bound, but not done here, and not faked.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md` and `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0FiniteChernoff

open Finset

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- **Self-contained finite Chernoff (lower tail), proved.**  For any real multiplier `c ≥ 1`, the number of samples
`σ : Fin r → P` whose good-count `#{i | σ i ∈ G}` is a minority (`2·good ≤ r`) is at most
`((|G|/c) + c·(|P| − |G|))^r`.  The classical Markov-on-a-product Chernoff argument, in finite counting form. -/
theorem finite_chernoff_lower (r : ℕ) (G : Finset P) (c : ℝ) (hc : 1 ≤ c) :
    ((Finset.univ.filter
        (fun σ : Fin r → P => 2 * (Finset.univ.filter (fun i => σ i ∈ G)).card ≤ r)).card : ℝ)
      ≤ ((G.card : ℝ) / c + c * ((Fintype.card P : ℝ) - G.card)) ^ r := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
  set d : ℝ := (c ^ 2)⁻¹ with hd
  have hd0 : 0 < d := by rw [hd]; positivity
  -- abbreviations
  set good : (Fin r → P) → ℕ := fun σ => (Finset.univ.filter (fun i => σ i ∈ G)).card with hgood
  set w : P → ℝ := fun x => if x ∈ G then d else 1 with hw
  -- the product over coordinates collapses to `d ^ good`
  have hprod : ∀ σ : Fin r → P, ∏ i, w (σ i) = d ^ good σ := by
    intro σ
    rw [hgood, hw]
    rw [← Finset.prod_filter, Finset.prod_const]
  -- the population sum
  have hwsum : (∑ x : P, w x) = (G.card : ℝ) * d + ((Fintype.card P : ℝ) - G.card) := by
    rw [hw, Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one]
    have hf1 : (Finset.univ.filter (fun x => x ∈ G)).card = G.card := by
      congr 1; ext x; simp
    have hf2 : (Finset.univ.filter (fun x => ¬ x ∈ G)).card = Fintype.card P - G.card := by
      have hpart := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset P)) (fun x => x ∈ G)
      rw [hf1, Finset.card_univ] at hpart
      omega
    rw [hf1, hf2, Nat.cast_sub (Finset.card_le_univ G), mul_comm]
  -- independence: ∑ over samples of the product = (population sum)^r
  have hpi : ∑ σ : Fin r → P, ∏ i, w (σ i) = (∑ x : P, w x) ^ r := by
    have h := Finset.sum_prod_piFinset (ι := Fin r) (Finset.univ : Finset P)
      (fun (_ : Fin r) (x : P) => w x)
    rw [Fintype.piFinset_univ] at h
    rw [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- the Chernoff chain
  calc ((Finset.univ.filter (fun σ : Fin r → P => 2 * good σ ≤ r)).card : ℝ)
      = ∑ _σ ∈ Finset.univ.filter (fun σ : Fin r → P => 2 * good σ ≤ r), (1 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ σ ∈ Finset.univ.filter (fun σ : Fin r → P => 2 * good σ ≤ r), c ^ r * d ^ good σ := by
        apply Finset.sum_le_sum
        intro σ hσ
        have hle : 2 * good σ ≤ r := (Finset.mem_filter.mp hσ).2
        have hdg : d ^ good σ = (c ^ (2 * good σ))⁻¹ := by
          rw [hd, inv_pow, ← pow_mul, mul_comm]
        rw [hdg, ← div_eq_mul_inv, one_le_div (pow_pos hc0 _)]
        exact pow_le_pow_right₀ hc hle
    _ ≤ ∑ σ : Fin r → P, c ^ r * d ^ good σ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro σ _ _
        exact mul_nonneg (pow_nonneg hc0.le r) (pow_nonneg hd0.le _)
    _ = c ^ r * ∑ σ : Fin r → P, ∏ i, w (σ i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun σ _ => by rw [hprod σ])
    _ = c ^ r * (∑ x : P, w x) ^ r := by rw [hpi]
    _ = c ^ r * ((G.card : ℝ) * d + ((Fintype.card P : ℝ) - G.card)) ^ r := by rw [hwsum]
    _ = ((G.card : ℝ) / c + c * ((Fintype.card P : ℝ) - G.card)) ^ r := by
        rw [← mul_pow]
        congr 1
        rw [hd]
        field_simp

/-- **Majority corollary (proved): geometric decay when the good fraction is `≥ 3/4`.**  With `c = 2` and
`4|G| ≥ 3|P|`, the minority-count samples number at most `(7|P|/8)^r` — base `7/8 < 1` relative to `|P|`, the decay
the union bound over the `2^n` inputs consumes. -/
theorem finite_chernoff_majority (r : ℕ) (G : Finset P) (hG : 3 * Fintype.card P ≤ 4 * G.card) :
    ((Finset.univ.filter
        (fun σ : Fin r → P => 2 * (Finset.univ.filter (fun i => σ i ∈ G)).card ≤ r)).card : ℝ)
      ≤ (7 / 8 * (Fintype.card P : ℝ)) ^ r := by
  refine le_trans (finite_chernoff_lower r G 2 (by norm_num)) ?_
  have hcast : (3 : ℝ) * Fintype.card P ≤ 4 * G.card := by exact_mod_cast hG
  have hGle : (G.card : ℝ) ≤ (Fintype.card P : ℝ) := by exact_mod_cast Finset.card_le_univ G
  have hbase : (0 : ℝ) ≤ (G.card : ℝ) / 2 + 2 * ((Fintype.card P : ℝ) - G.card) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) G.card, Nat.cast_nonneg (α := ℝ) (Fintype.card P)]
  have hle : (G.card : ℝ) / 2 + 2 * ((Fintype.card P : ℝ) - G.card) ≤ 7 / 8 * (Fintype.card P : ℝ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) G.card]
  exact pow_le_pow_left₀ hbase hle r

end PallLean.Paper93.DeepMath.PathB.ACC0FiniteChernoff

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FiniteChernoff.finite_chernoff_lower
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FiniteChernoff.finite_chernoff_majority
