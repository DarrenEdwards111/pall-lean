import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SatSecondMoment

/-!
# The exponential tail: factorial‑moment method and the `(s·p)^t` tail for independent supports

The second‑moment file gave concentration but, as noted there, **could not lower the existence threshold** past the
first moment — because survival events are *positively correlated* (`cov_nonneg`), so `Pr(all of T survive) ≥
∏ survProb`, the wrong direction for a clean exponential upper bound.  This file pushes to the **exponential tail**
`Pr(survivingCount ≥ t) ≤ (…)^t`, via the factorial‑moment (Bonferroni–Markov) method, and proves the genuine
`(s·p)^t` decay in the one regime where it actually holds: **pairwise‑disjoint (independent) supports**.

The chain:

1. `pr_ge_le_factorial_moment` — `Pr(t ≤ X) ≤ Exp(C(X,t))` (since `C(X,t) ≥ 1 ⟺ X ≥ t`, Markov on the binomial
   coefficient — the factorial‑moment method, the first step of every exponential‑tail argument).
2. `factorial_moment_eq` — the **elementary‑symmetric identity** `Exp(C(survivingCount,t)) = ∑_{|T|=t} Pr(all of T
   survive)` (the binomial coefficient counts `t`‑subsets of the surviving set).
3. `pr_ge_le_sum_jointSurv` — combining (1)+(2): `Pr(t ≤ survivingCount) ≤ ∑_{|T|=t} Pr(all of T survive)`.
4. `exp_prod_kind_disjoint` — **independence of kill indicators**: for pairwise‑disjoint supports,
   `Exp(∏_{j∈U} kind S_j) = ∏_{j∈U} killProb S_j` (the product of kill indicators is a single disjointness event of
   the *disjoint union*, whose card is `∑ |S_j|`).
5. `exp_prod_surv_disjoint`, `jointSurv_disjoint_eq_prod` — the multilinear expansion turns kill‑independence into
   **survival independence**: `Pr(all of T survive) = ∏_{j∈T} survProb S_j` for disjoint `T`.
6. `exp_tail_disjoint` — **the exponential tail**: for pairwise‑disjoint supports of fan‑in `≤ s`,
   `Pr(t ≤ survivingCount) ≤ C(k,t)·(s·p)^t`.

## Honest scope — this is the *independent* tail, not Håstad's

The `(s·p)^t` decay is genuine but it (i) **requires independence** (pairwise‑disjoint supports — `cov_disjoint`),
and (ii) carries the **clause‑count factor `C(k,t)`**.  For *overlapping* supports the product step fails: `cov_nonneg`
says survival is positively correlated, so `Pr(all survive) ≥ ∏ survProb` and the `(s·p)^t` bound is *false* in
general — this is the precise wall.  Håstad's celebrated **clause‑count‑free** `(5·p·w)^t` switching tail evades both
defects, but it is a statement about **decision‑tree depth** of the restricted function, proved by the
*encoding/canonical‑labelling* argument (the `…Switching*` arc — `SwitchingDecoder`, `SwitchingHastad`, …), not about
gate survival.  That clause‑count‑free tail is the genuine `NP ⊄ ACC⁰` content and remains open here.  Everything in
this file is the cell‑search model; it proves nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SatExpTail

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingProb
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingChebyshev
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline
open PallLean.Paper93.DeepMath.PathB.ACC0SatFirstMoment
open PallLean.Paper93.DeepMath.PathB.ACC0SatSecondMoment

variable {n k : ℕ}

/-! ## Monotonicity and constant‑multiple linearity of `Exp` -/

/-- **Monotonicity of `Exp` (proved): `f ≤ g` pointwise ⇒ `Exp f ≤ Exp g`.** -/
theorem exp_mono (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f g : Finset (Fin n) → ℝ)
    (h : ∀ L, f L ≤ g L) : Exp p f ≤ Exp p g := by
  unfold Exp
  apply Finset.sum_le_sum
  intro L _
  exact mul_le_mul_of_nonneg_left (h L) (weight_nonneg p hp0 hp1 L)

/-- **Expectation linearity (proved): `Exp p (a · g) = a · Exp p g`.** -/
theorem exp_const_mul (p : ℝ) (a : ℝ) (g : Finset (Fin n) → ℝ) :
    Exp p (fun L => a * g L) = a * Exp p g := by
  unfold Exp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro L _
  ring

/-! ## The factorial‑moment method -/

/-- **The factorial‑moment bound (proved): `Pr(t ≤ X) ≤ Exp(C(X,t))`.**  The binomial coefficient `C(X,t) ≥ 1`
exactly when `X ≥ t` (and is `≥ 0` always), so the `0/1` indicator of `{X ≥ t}` is dominated by `C(X,t)`. -/
theorem pr_ge_le_factorial_moment (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (t : ℕ) :
    Pr p (fun L => t ≤ survivingCount supports L)
      ≤ Exp p (fun L => (Nat.choose (survivingCount supports L) t : ℝ)) := by
  rw [← exp_indicator_eq_pr]
  apply exp_mono p hp0 hp1
  intro L
  by_cases h : t ≤ survivingCount supports L
  · simp only [h, if_true]
    have : 1 ≤ Nat.choose (survivingCount supports L) t := Nat.choose_pos h
    exact_mod_cast this
  · simp only [h, if_false]
    positivity

/-- **The elementary‑symmetric identity (proved): `Exp(C(survivingCount,t)) = ∑_{|T|=t} Pr(all of T survive)`.**
The binomial coefficient `C(|survivors|,t)` counts the `t`‑subsets of the surviving set, i.e. sums the indicator
`1[T ⊆ survivors]` over all `t`‑subsets `T`; taking `Exp` turns each into `Pr(all of T survive)`. -/
theorem factorial_moment_eq (p : ℝ) (supports : Fin k → Finset (Fin n)) (t : ℕ) :
    Exp p (fun L => (Nat.choose (survivingCount supports L) t : ℝ))
      = ∑ T ∈ (Finset.univ : Finset (Fin k)).powersetCard t,
          Pr p (fun L => ∀ j ∈ T, ¬ Disjoint (supports j) L) := by
  have hpoint : (fun L => (Nat.choose (survivingCount supports L) t : ℝ))
      = (fun L => ∑ T ∈ (Finset.univ : Finset (Fin k)).powersetCard t,
          (if (∀ j ∈ T, ¬ Disjoint (supports j) L) then (1 : ℝ) else 0)) := by
    funext L
    have hsv : survivingCount supports L
        = (Finset.univ.filter (fun j => ¬ Disjoint (supports j) L)).card := rfl
    rw [hsv, ← Finset.card_powersetCard,
      show (Finset.univ.filter (fun j => ¬ Disjoint (supports j) L)).powersetCard t
          = ((Finset.univ : Finset (Fin k)).powersetCard t).filter
              (· ⊆ Finset.univ.filter (fun j => ¬ Disjoint (supports j) L)) from by
        ext T
        simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.subset_univ, true_and]
        tauto,
      Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro T _
    by_cases hT : T ⊆ Finset.univ.filter (fun j => ¬ Disjoint (supports j) L)
    · have hall : ∀ j ∈ T, ¬ Disjoint (supports j) L := by
        intro j hj
        have := hT hj
        simp only [Finset.mem_filter] at this
        exact this.2
      rw [if_pos hT, if_pos hall, Nat.cast_one]
    · have hall : ¬ (∀ j ∈ T, ¬ Disjoint (supports j) L) := by
        intro hall
        apply hT
        intro j hj
        simp only [Finset.mem_filter]
        exact ⟨Finset.mem_univ j, hall j hj⟩
      rw [if_neg hT, if_neg hall, Nat.cast_zero]
  rw [hpoint, exp_sum]
  apply Finset.sum_congr rfl
  intro T _
  unfold Exp Pr
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro L _
  by_cases hd : (∀ j ∈ T, ¬ Disjoint (supports j) L) <;> simp [hd]

/-- **The inclusion bound (proved): `Pr(t ≤ survivingCount) ≤ ∑_{|T|=t} Pr(all of T survive)`.** -/
theorem pr_ge_le_sum_jointSurv (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (t : ℕ) :
    Pr p (fun L => t ≤ survivingCount supports L)
      ≤ ∑ T ∈ (Finset.univ : Finset (Fin k)).powersetCard t,
          Pr p (fun L => ∀ j ∈ T, ¬ Disjoint (supports j) L) := by
  rw [← factorial_moment_eq]
  exact pr_ge_le_factorial_moment p hp0 hp1 supports t

/-! ## Independence for pairwise‑disjoint supports -/

/-- **Kill‑indicator independence (proved): `Exp(∏_{j∈U} kind S_j) = ∏_{j∈U} killProb S_j`** for pairwise‑disjoint
supports.  The product of kill indicators is the indicator of a *single* disjointness event — disjointness from the
union `⋃_{j∈U} S_j` — whose card is `∑_{j∈U} |S_j|` (disjointness), so the probability factorises. -/
theorem exp_prod_kind_disjoint (p : ℝ) (supports : Fin k → Finset (Fin n)) (U : Finset (Fin k))
    (hdis : ∀ j ∈ U, ∀ l ∈ U, j ≠ l → Disjoint (supports j) (supports l)) :
    Exp p (fun L => ∏ j ∈ U, kind (supports j) L) = ∏ j ∈ U, killProb p (supports j) := by
  have hprod : ∀ L, (∏ j ∈ U, kind (supports j) L)
      = if (Disjoint (U.biUnion supports) L) then (1 : ℝ) else 0 := by
    intro L
    by_cases hdj : Disjoint (U.biUnion supports) L
    · rw [if_pos hdj]
      apply Finset.prod_eq_one
      intro j hj
      unfold kind
      rw [if_pos ((Finset.disjoint_biUnion_left U supports L).mp hdj j hj)]
    · rw [if_neg hdj]
      rw [Finset.disjoint_biUnion_left] at hdj
      push_neg at hdj
      obtain ⟨j, hj, hnd⟩ := hdj
      apply Finset.prod_eq_zero hj
      unfold kind
      rw [if_neg hnd]
  rw [show (fun L => ∏ j ∈ U, kind (supports j) L)
        = (fun L => if (Disjoint (U.biUnion supports) L) then (1 : ℝ) else 0) from funext hprod]
  have hExpPr : Exp p (fun L => if (Disjoint (U.biUnion supports) L) then (1 : ℝ) else 0)
      = Pr p (fun L => Disjoint (U.biUnion supports) L) := by
    unfold Exp Pr
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro L _
    by_cases hd : Disjoint (U.biUnion supports) L <;> simp [hd]
  rw [hExpPr, prDisjoint]
  unfold killProb
  rw [Finset.prod_pow_eq_pow_sum, Finset.card_biUnion hdis]

/-- **Survival independence (proved): `Exp(∏_{j∈T} (1 − kind S_j)) = ∏_{j∈T} survProb S_j`** for pairwise‑disjoint
supports.  Multilinear expansion `∏(1−kind) = ∑_{U⊆T} ∏_{j∈U}(−kind)` plus kill‑independence on each `U`. -/
theorem exp_prod_surv_disjoint (p : ℝ) (supports : Fin k → Finset (Fin n)) (T : Finset (Fin k))
    (hdis : ∀ j ∈ T, ∀ l ∈ T, j ≠ l → Disjoint (supports j) (supports l)) :
    Exp p (fun L => ∏ j ∈ T, (1 - kind (supports j) L)) = ∏ j ∈ T, survProb p (supports j) := by
  have hLHSfun : (fun L => ∏ j ∈ T, (1 - kind (supports j) L))
      = (fun L => ∑ U ∈ T.powerset, ∏ j ∈ U, (- kind (supports j) L)) := by
    funext L
    rw [Finset.prod_congr rfl (fun j _ => by ring :
          ∀ j ∈ T, (1 : ℝ) - kind (supports j) L = (- kind (supports j) L) + 1),
        Finset.prod_add]
    apply Finset.sum_congr rfl
    intro U _
    rw [Finset.prod_const_one, mul_one]
  have hRHS : (∏ j ∈ T, survProb p (supports j))
      = ∑ U ∈ T.powerset, ∏ j ∈ U, (- killProb p (supports j)) := by
    rw [Finset.prod_congr rfl (fun j _ => by unfold survProb killProb; ring :
          ∀ j ∈ T, survProb p (supports j) = (- killProb p (supports j)) + 1),
        Finset.prod_add]
    apply Finset.sum_congr rfl
    intro U _
    rw [Finset.prod_const_one, mul_one]
  rw [hLHSfun, exp_sum, hRHS]
  apply Finset.sum_congr rfl
  intro U hU
  have hUsub : U ⊆ T := Finset.mem_powerset.mp hU
  have hU_disj : ∀ j ∈ U, ∀ l ∈ U, j ≠ l → Disjoint (supports j) (supports l) :=
    fun j hj l hl hne => hdis j (hUsub hj) l (hUsub hl) hne
  calc Exp p (fun L => ∏ j ∈ U, (- kind (supports j) L))
      = Exp p (fun L => (-1) ^ U.card * ∏ j ∈ U, kind (supports j) L) := by
        congr 1
        funext L
        rw [Finset.prod_congr rfl (fun j _ => (neg_one_mul (kind (supports j) L)).symm :
              ∀ j ∈ U, - kind (supports j) L = (-1) * kind (supports j) L),
            Finset.prod_mul_distrib, Finset.prod_const]
    _ = (-1) ^ U.card * Exp p (fun L => ∏ j ∈ U, kind (supports j) L) := exp_const_mul p _ _
    _ = (-1) ^ U.card * ∏ j ∈ U, killProb p (supports j) := by
        rw [exp_prod_kind_disjoint p supports U hU_disj]
    _ = ∏ j ∈ U, (- killProb p (supports j)) := by
        rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro j _
        rw [neg_one_mul]

/-- **Joint survival factorises (proved): `Pr(all of T survive) = ∏_{j∈T} survProb S_j`** for pairwise‑disjoint
supports.  The all‑survive indicator is `∏_{j∈T}(1 − kind S_j)`; apply `exp_prod_surv_disjoint`. -/
theorem jointSurv_disjoint_eq_prod (p : ℝ) (supports : Fin k → Finset (Fin n)) (T : Finset (Fin k))
    (hdis : ∀ j ∈ T, ∀ l ∈ T, j ≠ l → Disjoint (supports j) (supports l)) :
    Pr p (fun L => ∀ j ∈ T, ¬ Disjoint (supports j) L) = ∏ j ∈ T, survProb p (supports j) := by
  have hindprod : ∀ L, (∏ j ∈ T, (1 - kind (supports j) L))
      = if (∀ j ∈ T, ¬ Disjoint (supports j) L) then (1 : ℝ) else 0 := by
    intro L
    by_cases hall : (∀ j ∈ T, ¬ Disjoint (supports j) L)
    · rw [if_pos hall]
      apply Finset.prod_eq_one
      intro j hj
      unfold kind
      rw [if_neg (hall j hj)]
      ring
    · rw [if_neg hall]
      push_neg at hall
      obtain ⟨j, hj, hd⟩ := hall
      apply Finset.prod_eq_zero hj
      unfold kind
      rw [if_pos hd]
      ring
  have hExpPr : Pr p (fun L => ∀ j ∈ T, ¬ Disjoint (supports j) L)
      = Exp p (fun L => ∏ j ∈ T, (1 - kind (supports j) L)) := by
    unfold Exp Pr
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro L _
    dsimp only
    rw [hindprod L]
    by_cases hd : (∀ j ∈ T, ¬ Disjoint (supports j) L) <;> simp [hd]
  rw [hExpPr]
  exact exp_prod_surv_disjoint p supports T hdis

/-! ## The exponential tail for independent supports -/

/-- **The exponential tail (proved): `Pr(t ≤ survivingCount) ≤ C(k,t)·(s·p)^t`** for pairwise‑disjoint supports of
fan‑in `≤ s`.  By `pr_ge_le_sum_jointSurv` and `jointSurv_disjoint_eq_prod`, the tail is `∑_{|T|=t} ∏ survProb`, and
each `survProb ≤ s·p` (Bernoulli) gives `∏ ≤ (s·p)^t`; there are `C(k,t)` terms. -/
theorem exp_tail_disjoint (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (s : ℕ) (hfan : ∀ j, (supports j).card ≤ s)
    (hdisall : ∀ j l, j ≠ l → Disjoint (supports j) (supports l)) (t : ℕ) :
    Pr p (fun L => t ≤ survivingCount supports L) ≤ (Nat.choose k t : ℝ) * ((s : ℝ) * p) ^ t := by
  refine le_trans (pr_ge_le_sum_jointSurv p hp0 hp1 supports t) ?_
  calc ∑ T ∈ (Finset.univ : Finset (Fin k)).powersetCard t,
          Pr p (fun L => ∀ j ∈ T, ¬ Disjoint (supports j) L)
      = ∑ T ∈ (Finset.univ : Finset (Fin k)).powersetCard t, ∏ j ∈ T, survProb p (supports j) := by
        apply Finset.sum_congr rfl
        intro T _
        exact jointSurv_disjoint_eq_prod p supports T (fun j _ l _ hne => hdisall j l hne)
    _ ≤ ∑ T ∈ (Finset.univ : Finset (Fin k)).powersetCard t, ((s : ℝ) * p) ^ t := by
        apply Finset.sum_le_sum
        intro T hT
        have hTcard : T.card = t := (Finset.mem_powersetCard.mp hT).2
        calc ∏ j ∈ T, survProb p (supports j)
            ≤ ∏ j ∈ T, ((s : ℝ) * p) := by
              apply Finset.prod_le_prod
              · intro j _
                have hle : (1 - p) ^ (supports j).card ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
                unfold survProb
                linarith
              · intro j _
                refine le_trans (survProb_le p hp1 (supports j)) ?_
                exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfan j) hp0
          _ = ((s : ℝ) * p) ^ T.card := by rw [Finset.prod_const]
          _ = ((s : ℝ) * p) ^ t := by rw [hTcard]
    _ = (Nat.choose k t : ℝ) * ((s : ℝ) * p) ^ t := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard, Finset.card_univ,
            Fintype.card_fin]

end PallLean.Paper93.DeepMath.PathB.ACC0SatExpTail

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatExpTail.pr_ge_le_sum_jointSurv
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatExpTail.exp_prod_kind_disjoint
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatExpTail.jointSurv_disjoint_eq_prod
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatExpTail.exp_tail_disjoint
