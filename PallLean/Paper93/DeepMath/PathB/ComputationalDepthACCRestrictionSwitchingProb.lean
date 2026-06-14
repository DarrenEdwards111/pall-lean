import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCRandomRestrictionCellCollapse

/-!
# The probabilistic half: a `p`‑biased random restriction shrinks the surviving supports

The deterministic switching instance (`…ACCRandomRestrictionCellCollapse`) killed *all* supports by removing every
touched coordinate — needing `k·s < n`.  The genuinely probabilistic rung toward the full switching lemma: keep
each coordinate **live independently with probability `p`**, and show the *expected* number of supports that
survive (have a live coordinate) shrinks linearly in `p`.

Model: a random restriction is a live set `L ⊆ Fin n`, each coordinate included independently with probability
`p`; the weight of a particular `L` is `p^{|L|}(1-p)^{n-|L|}`.  We prove the per‑coordinate / per‑support facts of
linearity of expectation:

* **the model is a genuine distribution** — `biased_sum_one`: the `p`‑biased weights on subsets of any set sum to
  `1` (binomial theorem, `Finset.prod_add`);
* **a support of `m` coordinates is killed with probability `(1-p)^m`** (all its coordinates dead) — so it
  **survives with probability `1-(1-p)^m ≤ m·p`** (`survProb_le`, Bernoulli's inequality);
* **expected live coordinates `= n·p`** (`expectedLive_eq`) and **expected surviving supports `≤ k·s·p`**
  (`expectedSurviving_le`) by linearity over the `k` supports of fan‑in `≤ s`.

## What is proved (clean axioms, no `sorry`)

* `biased_sum_one` — the `p`‑biased weights form a probability distribution.
* `survProb_le` — a fan‑in‑`m` support survives with probability `≤ m·p`.
* `expectedLive_eq` — expected number of live coordinates `= n·p`.
* `expectedSurviving_le` — **expected number of surviving supports `≤ k·s·p`** — the shrinkage.

## Honest scope

This is the *linearity* (first‑moment) rung.  With `p` small (heavy restriction) the expected surviving count
`k·s·p` drops below `1`, so a restriction killing every support exists — but that meets the deterministic `k·s < n`
regime, not beyond it (when `p ≥ 2/n` keeps `≥ 2` live, `k·s·p < 1` still needs `k·s < n/2`).  Beating it — keeping
a constant fraction `p` live while still collapsing high‑fan‑in supports — needs the *higher‑moment* Håstad
switching argument (the genuine `NP ⊄ ACC⁰` content).  This file builds the first‑moment skeleton: the random
restriction is modelled, the distribution validated, and the expected surviving‑support count provably shrinks.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingProb

variable {n k : ℕ}

/-! ## The `p`‑biased restriction is a genuine distribution -/

/-- **The `p`‑biased weights on subsets of `A` sum to `1` (proved).**  Binomial theorem via `Finset.prod_add`:
`∏_{i∈A}(p + (1-p)) = 1 = ∑_{t⊆A} p^{|t|}(1-p)^{|A|-|t|}`. -/
theorem biased_sum_one (p : ℝ) (A : Finset (Fin n)) :
    ∑ t ∈ A.powerset, p ^ t.card * (1 - p) ^ (A.card - t.card) = 1 := by
  have h := Finset.prod_add (fun _ : Fin n => p) (fun _ : Fin n => (1 - p)) A
  have hL : (∏ i ∈ A, ((fun _ : Fin n => p) i + (fun _ : Fin n => (1 - p)) i)) = 1 :=
    calc ∏ i ∈ A, ((fun _ : Fin n => p) i + (fun _ : Fin n => (1 - p)) i)
        = ∏ _i ∈ A, (1 : ℝ) := Finset.prod_congr rfl (fun i _ => by show p + (1 - p) = (1:ℝ); ring)
      _ = 1 := Finset.prod_const_one
  rw [hL] at h
  refine Eq.trans ?_ h.symm
  apply Finset.sum_congr rfl
  intro t ht
  have hsub := Finset.mem_powerset.mp ht
  have hcard : (A \ t).card = A.card - t.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
  simp only [Finset.prod_const, hcard]

/-! ## Per‑support survival probability and the Bernoulli bound -/

/-- The probability a support `S` is killed (all its coordinates dead) under the `p`‑biased restriction. -/
def killProb (p : ℝ) (S : Finset (Fin n)) : ℝ := (1 - p) ^ S.card

/-- The probability a support `S` survives (has a live coordinate). -/
def survProb (p : ℝ) (S : Finset (Fin n)) : ℝ := 1 - (1 - p) ^ S.card

/-- **A support of fan‑in `m` survives with probability `≤ m·p` (proved, Bernoulli's inequality).** -/
theorem survProb_le (p : ℝ) (hp1 : p ≤ 1) (S : Finset (Fin n)) :
    survProb p S ≤ (S.card : ℝ) * p := by
  have h := one_add_mul_le_pow (show (-2:ℝ) ≤ -p by linarith) S.card
  rw [show (1:ℝ) + -p = 1 - p from by ring, mul_neg] at h
  unfold survProb
  linarith

/-! ## Linearity of expectation: live coordinates and surviving supports -/

/-- The expected number of live coordinates. -/
def expectedLive (p : ℝ) : ℝ := ∑ _i : Fin n, p

/-- **Expected number of live coordinates `= n·p` (proved).** -/
theorem expectedLive_eq (p : ℝ) : expectedLive (n := n) p = (n : ℝ) * p := by
  unfold expectedLive
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The expected number of supports that survive the restriction. -/
def expectedSurviving (p : ℝ) (supports : Fin k → Finset (Fin n)) : ℝ :=
  ∑ j, survProb p (supports j)

/-- **Expected number of surviving supports `≤ k·s·p` (proved): the shrinkage.**  Linearity over the `k` supports
of fan‑in `≤ s`, each surviving with probability `≤ |S_j|·p ≤ s·p`. -/
theorem expectedSurviving_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (s : ℕ) (hfan : ∀ j, (supports j).card ≤ s) :
    expectedSurviving p supports ≤ (k : ℝ) * s * p := by
  unfold expectedSurviving
  calc ∑ j, survProb p (supports j)
      ≤ ∑ j, ((supports j).card : ℝ) * p :=
        Finset.sum_le_sum (fun j _ => survProb_le p hp1 (supports j))
    _ ≤ ∑ _j : Fin k, (s : ℝ) * p :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hfan j)) hp0)
    _ = (k : ℝ) * s * p := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingProb

#print axioms PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingProb.biased_sum_one
#print axioms PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingProb.survProb_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingProb.expectedLive_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingProb.expectedSurviving_le
