import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SatSocketReduction

/-!
# Collapsing the socket to the bare regime: the first moment of `survivingCount`

`…ACC0SatSocketReduction` reduced the master socket to a single expectation hypothesis
`Exp p (survivingCount) ≤ r`.  This file **discharges that hypothesis**, identifying the measure expectation of the
surviving‑gate count with the first‑moment sum `∑_j survProb p (S_j)` and bounding it by `k·s·p`.  The socket then
follows from the *bare arithmetic regime* `k·s·p ≤ r` and `(n+1)^r < 2^n` — no probabilistic hypothesis left.

The two standard facts about the `p`‑biased product measure, proved here in full:

* **the per‑support marginal** `prDisjoint`: `Pr(S disjoint from L) = (1-p)^{|S|}` — the coordinates of `S` are all
  dead with probability `(1-p)^{|S|}`, by factoring the measure over `S` and `Sᶜ` and using `biased_sum_one Sᶜ`;
* **linearity of the discrete expectation** `exp_sum` over the support indicators, giving
  `exp_survivingCount_eq`: `Exp p (survivingCount) = ∑_j survProb p (S_j) = expectedSurviving p supports`.

Composing with `expectedSurviving_le` (`∑_j survProb ≤ k·s·p`, Bernoulli) and `socket_of_expectation` yields
`socket_of_regime` and `speedup_of_regime`.

## What is proved (clean axioms, no `sorry`)

* `prDisjoint` — `Pr p (Disjoint S ·) = (1-p)^{|S|}` (the per‑support marginal).
* `exp_indicator_eq_survProb` — `Exp p (survival indicator of S) = survProb p S = 1 - (1-p)^{|S|}`.
* `exp_sum` — linearity of `Exp` over a finite sum of functions.
* `exp_survivingCount_eq` — **`Exp p (survivingCount) = expectedSurviving p supports`** (the identification).
* `exp_survivingCount_le` — **`Exp p (survivingCount) ≤ k·s·p`** (the first moment).
* `socket_of_regime` — **the socket from the bare regime**: `k·s·p ≤ r` and `(n+1)^r < 2^n` ⇒ the socket.
* `speedup_of_regime` — the same regime gives a restriction whose cell search beats brute force.

## Honest scope

The expectation hypothesis of `socket_of_expectation` is now eliminated: the socket holds whenever the fan‑in `s`,
keep‑probability `p`, gate count `k` and threshold `r` satisfy `k·s·p ≤ r` and `(n+1)^r < 2^n`.  This is still the
cell‑search cost model, and the regime `k·s·p ≤ r` is exactly the *first‑moment* regime (heavy restriction, `p`
small) — beating it (constant `p` while collapsing high‑fan‑in gates) is the higher‑moment Håstad content, the
genuine `NP ⊄ ACC⁰` frontier.  Proves nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SatFirstMoment

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingProb
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingChebyshev
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Master
open PallLean.Paper93.DeepMath.PathB.ACC0SatSocketReduction

variable {n k : ℕ}

/-! ## The per‑support marginal -/

/-- **The per‑support marginal (proved): `Pr(S disjoint from L) = (1-p)^{|S|}`.**  The event `Disjoint S L` is
`L ⊆ Sᶜ`; factoring `weight p L = (1-p)^{|S|}·p^{|L|}(1-p)^{|Sᶜ|-|L|}` over `L ⊆ Sᶜ` and summing with
`biased_sum_one Sᶜ` gives `(1-p)^{|S|}`. -/
theorem prDisjoint (p : ℝ) (S : Finset (Fin n)) :
    Pr p (fun L => Disjoint S L) = (1 - p) ^ S.card := by
  have key : Pr p (fun L => Disjoint S L)
      = ∑ L ∈ Sᶜ.powerset, p ^ L.card * (1 - p) ^ (n - L.card) := by
    unfold Pr weight
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext L
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨_, hdis⟩
      intro i hi
      rw [Finset.mem_compl]
      intro hiS
      exact (Finset.disjoint_left.mp hdis hiS) hi
    · intro hL
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.disjoint_left]
      intro i hiS hiL
      have hic := hL hiL
      rw [Finset.mem_compl] at hic
      exact hic hiS
  rw [key]
  have hcompl : Sᶜ.card = n - S.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  have hScard : S.card ≤ n := by
    have h := Finset.card_le_card (Finset.subset_univ S)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have hkey : ∀ L ∈ Sᶜ.powerset,
      p ^ L.card * (1 - p) ^ (n - L.card)
        = (1 - p) ^ S.card * (p ^ L.card * (1 - p) ^ (Sᶜ.card - L.card)) := by
    intro L hL
    rw [Finset.mem_powerset] at hL
    have hLc : L.card ≤ Sᶜ.card := Finset.card_le_card hL
    have hexp : n - L.card = S.card + (Sᶜ.card - L.card) := by omega
    rw [hexp, pow_add]
    ring
  rw [Finset.sum_congr rfl hkey, ← Finset.mul_sum, biased_sum_one p Sᶜ, mul_one]

/-! ## Expectation of a survival indicator -/

/-- **The survival indicator's expectation (proved): `Exp p (1_{S survives}) = survProb p S`.** -/
theorem exp_indicator_eq_survProb (p : ℝ) (S : Finset (Fin n)) :
    Exp p (fun L => if ¬ Disjoint S L then (1 : ℝ) else 0) = survProb p S := by
  have hone : Exp p (fun _ : Finset (Fin n) => (1 : ℝ)) = 1 := by
    unfold Exp
    simp only [mul_one]
    exact total p
  -- the survival indicator is `1` minus the kill indicator (pointwise), so its expectation splits
  have hsplit : Exp p (fun L => if ¬ Disjoint S L then (1 : ℝ) else 0)
      = Exp p (fun _ : Finset (Fin n) => (1 : ℝ))
        - Exp p (fun L => if Disjoint S L then (1 : ℝ) else 0) := by
    unfold Exp
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro L _
    by_cases hd : Disjoint S L <;> simp [hd]
  -- the kill indicator's expectation is the disjointness probability
  have hkill : Exp p (fun L => if Disjoint S L then (1 : ℝ) else 0) = (1 - p) ^ S.card := by
    have h1 : Exp p (fun L => if Disjoint S L then (1 : ℝ) else 0)
        = Pr p (fun L => Disjoint S L) := by
      unfold Exp Pr
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro L _
      by_cases hd : Disjoint S L <;> simp [hd]
    rw [h1, prDisjoint]
  rw [hsplit, hone, hkill]
  rfl

/-! ## Linearity of expectation -/

/-- **Linearity of the discrete expectation (proved) over a finite sum of functions.** -/
theorem exp_sum {ι : Type*} (s : Finset ι) (p : ℝ) (g : ι → Finset (Fin n) → ℝ) :
    Exp p (fun L => ∑ j ∈ s, g j L) = ∑ j ∈ s, Exp p (fun L => g j L) := by
  unfold Exp
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-! ## The first moment of the surviving‑gate count -/

/-- **The identification (proved): `Exp p (survivingCount) = expectedSurviving p supports`.**  Write the surviving
count as a sum of survival indicators, apply linearity, and evaluate each indicator's expectation. -/
theorem exp_survivingCount_eq (p : ℝ) (supports : Fin k → Finset (Fin n)) :
    Exp p (fun L => (survivingCount supports L : ℝ)) = expectedSurviving p supports := by
  have hcard : (fun L : Finset (Fin n) => (survivingCount supports L : ℝ))
      = (fun L => ∑ j, (if ¬ Disjoint (supports j) L then (1 : ℝ) else 0)) := by
    funext L
    unfold survivingCount
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hd : Disjoint (supports j) L <;> simp [hd]
  rw [hcard, exp_sum]
  unfold expectedSurviving
  apply Finset.sum_congr rfl
  intro j _
  exact exp_indicator_eq_survProb p (supports j)

/-- **The first moment (proved): `Exp p (survivingCount) ≤ k·s·p`.** -/
theorem exp_survivingCount_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (s : ℕ) (hfan : ∀ j, (supports j).card ≤ s) :
    Exp p (fun L => (survivingCount supports L : ℝ)) ≤ (k : ℝ) * s * p := by
  rw [exp_survivingCount_eq]
  exact expectedSurviving_le p hp0 hp1 supports s hfan

/-! ## The socket from the bare regime -/

/-- **The socket from the bare regime (proved).**  If the fan‑in is `≤ s`, the threshold `r` satisfies
`(n+1)^r < 2^n`, and the first‑moment regime `k·s·p ≤ r` holds, then a restriction leaving few surviving gates
exists — the master socket, with no probabilistic hypothesis remaining. -/
theorem socket_of_regime (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (s : ℕ) (hfan : ∀ j, (supports j).card ≤ s)
    (r : ℕ) (hreg : (n + 1) ^ r < 2 ^ n) (hksp : (k : ℝ) * s * p ≤ (r : ℝ)) :
    NFrameGivesACC0SatSpeedupSocket supports :=
  socket_of_expectation p hp0 hp1 supports r hreg
    (le_trans (exp_survivingCount_le p hp0 hp1 supports s hfan) hksp)

/-- **The speedup from the bare regime (proved): chaining to the master.** -/
theorem speedup_of_regime (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (s : ℕ) (hfan : ∀ j, (supports j).card ≤ s)
    (r : ℕ) (hreg : (n + 1) ^ r < 2 ^ n) (hksp : (k : ℝ) * s * p ≤ (r : ℝ)) :
    ∃ L : Finset (Fin n),
      (Finset.univ.image (weightVec (fun j => supports j ∩ L))).card < 2 ^ n :=
  speedup_of_socket supports (socket_of_regime p hp0 hp1 supports s hfan r hreg hksp)

end PallLean.Paper93.DeepMath.PathB.ACC0SatFirstMoment

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatFirstMoment.prDisjoint
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatFirstMoment.exp_survivingCount_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatFirstMoment.socket_of_regime
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatFirstMoment.speedup_of_regime
