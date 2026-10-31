import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SatFirstMoment
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCRestrictionSwitchingVariance

/-!
# The second moment: identifying `Exp((survivingCount − E)²)` with the variance, and Chebyshev concentration

`…ACC0SatFirstMoment` collapsed the socket to the first‑moment regime `k·s·p ≤ r`.  The variance file
(`…ACCRestrictionSwitchingVariance`) computed the *abstract* variance `∑_{j,l} Cov(X_j,X_l) ≤ d·k·s·p` (bounded
overlap), and the Chebyshev file proved `Pr((g−Eg)² ≥ t²) ≤ Exp((g−Eg)²)/t²`.  The missing link — called "routine"
in the Chebyshev docstring — is the **identification of the measure variance `Exp((survivingCount − E)²)` with the
abstract `∑_{j,l} cov`**.  This file proves that identification in full and feeds it into Chebyshev to obtain a
genuine concentration statement for the surviving‑gate count.

The clean route is through the **kill** indicators `kind S L = 1[S disjoint from L]` (not survival): the product
`kind A · kind B = 1[Disjoint (A∪B)]` is a *single* disjointness event, so `Exp(kind A · kind B) = (1-p)^{|A∪B|} =
killProb(A∪B)` directly (via `prDisjoint`), with no inclusion–exclusion.  Since `cov` is *defined* as
`killProb(S∪T) − killProb S · killProb T`, expanding `Exp(K²) − (EK)²` for the kill count `K = ∑_j kind(S_j)` gives
`∑_{j,l} cov = variance` immediately.  Finally `survivingCount = k − K`, so the two have equal centred squares.

## What is proved (clean axioms, no `sorry`)

* `exp_indicator_eq_pr`, `pr_compl` — `Exp p (1_E) = Pr p E`; `Pr p E + Pr p (¬E) = 1`.
* `exp_const_sub`, `exp_sub_sq` — expectation linearity: `Exp(c−g) = c−Exp g`, `Exp((g−Eg)²) = Exp(g²)−(Eg)²`.
* `exp_kind`, `exp_kind_mul` — `Exp(kind S) = killProb S`, `Exp(kind A · kind B) = killProb(A∪B)`.
* `kill_variance_eq`, `survivingCount_variance_eq` — **`Exp p ((survivingCount − E)²) = variance p supports`**.
* `survivingCount_concentration` — **`Pr(|survivingCount − E| "≥" t) ≤ d·k·s·p / t²`** (Chebyshev, bounded overlap).
* `most_restrictions_good` — **`Pr((survivingCount − E)² < t²) ≥ 1 − d·k·s·p/t²`**: at constant `p`, almost every
  restriction keeps the surviving count within `t` of its mean.

## Honest scope

This computes the second moment over the exact measure and turns it into concentration: for bounded‑overlap
supports, a *constant* live fraction `p` leaves the surviving count tightly concentrated at its mean `≤ k·s·p`, so
**almost every** restriction is good — a high‑probability (robustness) upgrade of the first‑moment *existence*.  It
does **not** lower the existence threshold below the first moment (the minimum of `survivingCount` is always `≤` its
mean, so existence at `r ≈ k·s·p` is already free); concentration controls the *measure* of good restrictions, not
a smaller witness.  Pushing the threshold itself past constant `p` needs the **exponential** switching tail
`Pr(survivingCount ≥ t) ≤ (O(p·s))^t`, beyond the second moment — the genuine `NP ⊄ ACC⁰` content, and exactly the
overlap term `cov_nonneg` exposes.  Still the cell‑search model; proves nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SatSecondMoment

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingProb
open PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingVariance
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingChebyshev
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline
open PallLean.Paper93.DeepMath.PathB.ACC0SatFirstMoment

variable {n k : ℕ}

/-! ## Expectation of indicators and linearity -/

/-- **Expectation of a `0/1` indicator equals the event probability (proved).** -/
theorem exp_indicator_eq_pr (p : ℝ) (E : Finset (Fin n) → Prop) :
    Exp p (fun L => if E L then (1 : ℝ) else 0) = Pr p E := by
  unfold Exp Pr
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro L _
  by_cases hd : E L <;> simp [hd]

/-- **Complementary events partition the measure (proved): `Pr p E + Pr p (¬E) = 1`.** -/
theorem pr_compl (p : ℝ) (E : Finset (Fin n) → Prop) :
    Pr p E + Pr p (fun L => ¬ E L) = 1 := by
  unfold Pr
  rw [← total p, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro L _
  by_cases hd : E L <;> simp [hd]

/-- **Expectation linearity (proved): `Exp p (c − g) = c − Exp p g`.** -/
theorem exp_const_sub (p : ℝ) (c : ℝ) (g : Finset (Fin n) → ℝ) :
    Exp p (fun L => c - g L) = c - Exp p g := by
  unfold Exp
  rw [Finset.sum_congr rfl (fun L _ => by ring :
        ∀ L ∈ (Finset.univ : Finset (Fin n)).powerset,
          weight p L * (c - g L) = c * weight p L - weight p L * g L),
      Finset.sum_sub_distrib, ← Finset.mul_sum, total p, mul_one]

/-- **Expectation linearity (proved): `Exp p ((g − Eg)²) = Exp p (g²) − (Eg)²`.** -/
theorem exp_sub_sq (p : ℝ) (g : Finset (Fin n) → ℝ) :
    Exp p (fun L => (g L - Exp p g) ^ 2) = Exp p (fun L => (g L) ^ 2) - (Exp p g) ^ 2 := by
  have htot : ∑ L ∈ (Finset.univ : Finset (Fin n)).powerset, weight p L = 1 := total p
  unfold Exp
  generalize hE : (∑ L ∈ (Finset.univ : Finset (Fin n)).powerset, weight p L * g L) = E
  have expand : ∀ L ∈ (Finset.univ : Finset (Fin n)).powerset,
      weight p L * (g L - E) ^ 2
        = weight p L * (g L) ^ 2 - 2 * E * (weight p L * g L) + E ^ 2 * weight p L :=
    fun L _ => by ring
  rw [Finset.sum_congr rfl expand, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      show (∑ L ∈ (Finset.univ : Finset (Fin n)).powerset, 2 * E * (weight p L * g L)) = 2 * E * E from by
        rw [← Finset.mul_sum, hE],
      show (∑ L ∈ (Finset.univ : Finset (Fin n)).powerset, E ^ 2 * weight p L) = E ^ 2 from by
        rw [← Finset.mul_sum, htot, mul_one]]
  ring

/-! ## The kill indicator and its expectations -/

/-- The kill indicator: `1` if the support `S` is disjoint from the live set `L` (all of `S` dead). -/
def kind (S : Finset (Fin n)) (L : Finset (Fin n)) : ℝ := if Disjoint S L then 1 else 0

/-- **`Exp p (kind S) = killProb p S` (proved).** -/
theorem exp_kind (p : ℝ) (S : Finset (Fin n)) :
    Exp p (fun L => kind S L) = killProb p S := by
  have hpr : Exp p (fun L => kind S L) = Pr p (fun L => Disjoint S L) := by
    unfold Exp Pr kind
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro L _
    by_cases hd : Disjoint S L <;> simp [hd]
  rw [hpr, prDisjoint]
  rfl

/-- **`Exp p (kind A · kind B) = killProb p (A ∪ B)` (proved): the product is a single disjointness event.** -/
theorem exp_kind_mul (p : ℝ) (A B : Finset (Fin n)) :
    Exp p (fun L => kind A L * kind B L) = killProb p (A ∪ B) := by
  have hpr : Exp p (fun L => kind A L * kind B L) = Pr p (fun L => Disjoint (A ∪ B) L) := by
    unfold Exp Pr kind
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro L _
    by_cases hA : Disjoint A L <;> by_cases hB : Disjoint B L <;>
      simp [hA, hB, Finset.disjoint_union_left]
  rw [hpr, prDisjoint]
  rfl

/-! ## The variance of the kill count, and the identification with `variance` -/

/-- **The variance of the kill count equals the abstract variance (proved).**  Expanding `Exp(K²) − (EK)²` for
`K = ∑_j kind(S_j)` and using `exp_kind_mul`, each summand is `killProb(S_j∪S_l) − killProb S_j · killProb S_l =
cov`, so the total is `∑_{j,l} cov = variance`. -/
theorem kill_variance_eq (p : ℝ) (supports : Fin k → Finset (Fin n)) :
    Exp p (fun L => ((∑ j, kind (supports j) L)
        - Exp p (fun L => ∑ j, kind (supports j) L)) ^ 2)
      = variance p supports := by
  -- the mean of the kill count
  have hEK : Exp p (fun L => ∑ j, kind (supports j) L) = ∑ j, killProb p (supports j) := by
    rw [exp_sum]
    exact Finset.sum_congr rfl (fun j _ => exp_kind p (supports j))
  -- the second moment of the kill count
  have hEKsq : Exp p (fun L => (∑ j, kind (supports j) L) ^ 2)
      = ∑ j, ∑ l, killProb p (supports j ∪ supports l) := by
    have hsq : (fun L => (∑ j, kind (supports j) L) ^ 2)
        = (fun L => ∑ j, ∑ l, kind (supports j) L * kind (supports l) L) := by
      funext L
      rw [sq, Finset.sum_mul_sum]
    rw [hsq, exp_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [exp_sum]
    exact Finset.sum_congr rfl (fun l _ => exp_kind_mul p (supports j) (supports l))
  rw [exp_sub_sq p (fun L => ∑ j, kind (supports j) L), hEK, hEKsq, sq, Finset.sum_mul_sum]
  unfold variance cov
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_sub_distrib]

/-- **The identification (proved): `Exp p ((survivingCount − E)²) = variance p supports`.**  Since
`survivingCount = k − (kill count)`, the surviving count and the kill count have identical centred squares, so the
measure variance of `survivingCount` is the kill‑count variance, `= variance`. -/
theorem survivingCount_variance_eq (p : ℝ) (supports : Fin k → Finset (Fin n)) :
    Exp p (fun L => ((survivingCount supports L : ℝ)
        - Exp p (fun L => (survivingCount supports L : ℝ))) ^ 2)
      = variance p supports := by
  -- survivingCount = k − kill count, pointwise
  have hXK : ∀ L, (survivingCount supports L : ℝ) = (k : ℝ) - ∑ j, kind (supports j) L := by
    intro L
    have hSC : (survivingCount supports L : ℝ)
        = ∑ j, (if ¬ Disjoint (supports j) L then (1 : ℝ) else 0) := by
      unfold survivingCount
      rw [Finset.card_filter, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hd : Disjoint (supports j) L <;> simp [hd]
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin k)),
        (if ¬ Disjoint (supports j) L then (1 : ℝ) else 0)
          + (if Disjoint (supports j) L then (1 : ℝ) else 0) = 1 := by
      intro j _
      by_cases hd : Disjoint (supports j) L <;> simp [hd]
    have hsum_real : (survivingCount supports L : ℝ) + ∑ j, kind (supports j) L = (k : ℝ) := by
      rw [hSC]
      unfold kind
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hterm, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    linarith
  -- mean of survivingCount = k − mean of kill count
  have hEX : Exp p (fun L => (survivingCount supports L : ℝ))
      = (k : ℝ) - Exp p (fun L => ∑ j, kind (supports j) L) := by
    rw [show (fun L => (survivingCount supports L : ℝ))
          = (fun L => (k : ℝ) - ∑ j, kind (supports j) L) from funext hXK]
    exact exp_const_sub p (k : ℝ) (fun L => ∑ j, kind (supports j) L)
  -- the centred squares agree pointwise
  have hsq_eq : (fun L => ((survivingCount supports L : ℝ)
        - Exp p (fun L => (survivingCount supports L : ℝ))) ^ 2)
      = (fun L => ((∑ j, kind (supports j) L)
        - Exp p (fun L => ∑ j, kind (supports j) L)) ^ 2) := by
    funext L
    rw [hXK L, hEX]
    ring
  rw [hsq_eq]
  exact kill_variance_eq p supports

/-! ## Chebyshev concentration for the surviving‑gate count -/

/-- **Chebyshev concentration (proved): `Pr(|survivingCount − E| "≥" t) ≤ d·k·s·p / t²`** for bounded‑overlap
supports.  Plugging the variance identification and `variance_boundedOverlap_le` into `chebyshev_of_variance_le`. -/
theorem survivingCount_concentration (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (s d : ℕ) (hfan : ∀ j, (supports j).card ≤ s)
    (hov : ∀ v, (Finset.univ.filter (fun l => v ∈ supports l)).card ≤ d)
    (t : ℝ) (ht : 0 < t) :
    Pr p (fun L => t ^ 2 ≤ ((survivingCount supports L : ℝ)
        - Exp p (fun L => (survivingCount supports L : ℝ))) ^ 2)
      ≤ ((d : ℝ) * k * s * p) / t ^ 2 := by
  apply chebyshev_of_variance_le p hp0 hp1 (fun L => (survivingCount supports L : ℝ)) t ht
  rw [survivingCount_variance_eq]
  exact variance_boundedOverlap_le p hp0 hp1 supports s d hfan hov

/-- **Almost every restriction is good (proved).**  The complementary bound: at bounded overlap, the fraction of
restrictions whose surviving count stays within `t` of its mean is `≥ 1 − d·k·s·p/t²` — a high‑probability upgrade
of the first‑moment existence, valid at *constant* `p`. -/
theorem most_restrictions_good (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (s d : ℕ) (hfan : ∀ j, (supports j).card ≤ s)
    (hov : ∀ v, (Finset.univ.filter (fun l => v ∈ supports l)).card ≤ d)
    (t : ℝ) (ht : 0 < t) :
    1 - ((d : ℝ) * k * s * p) / t ^ 2
      ≤ Pr p (fun L => ((survivingCount supports L : ℝ)
          - Exp p (fun L => (survivingCount supports L : ℝ))) ^ 2 < t ^ 2) := by
  have hconc := survivingCount_concentration p hp0 hp1 supports s d hfan hov t ht
  have hcompl : (fun L => ((survivingCount supports L : ℝ)
        - Exp p (fun L => (survivingCount supports L : ℝ))) ^ 2 < t ^ 2)
      = (fun L => ¬ (t ^ 2 ≤ ((survivingCount supports L : ℝ)
        - Exp p (fun L => (survivingCount supports L : ℝ))) ^ 2)) := by
    funext L
    simp [not_le]
  rw [hcompl]
  have hpart := pr_compl p (fun L => t ^ 2 ≤ ((survivingCount supports L : ℝ)
      - Exp p (fun L => (survivingCount supports L : ℝ))) ^ 2)
  linarith

end PallLean.Paper93.DeepMath.PathB.ACC0SatSecondMoment

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatSecondMoment.survivingCount_variance_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatSecondMoment.survivingCount_concentration
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatSecondMoment.most_restrictions_good
