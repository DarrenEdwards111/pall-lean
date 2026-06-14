import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCRestrictionSwitchingProb

/-!
# The second moment: covariance of survival, and a variance bound for Chebyshev

The first‑moment file (`…ACCRestrictionSwitchingProb`) bounded `E[#surviving] ≤ k·s·p`.  Chebyshev concentration —
the step that lets the random restriction keep a *constant* live fraction — needs the **second moment**.

Write `X = ∑_j X_j` for the number of surviving supports, `X_j` the survival indicator of `S_j`.  The covariance
of two survival indicators equals that of the *kill* indicators (`surv = 1 − kill`), and the kill events are
"all coordinates dead": `P(S killed) = (1-p)^{|S|}`, `P(S, T both killed) = P(S∪T killed) = (1-p)^{|S∪T|}`.  Hence

  `Cov(X_S, X_T) = P(S∪T killed) − P(S killed)·P(T killed) = (1-p)^{|S∪T|} − (1-p)^{|S|+|T|}`.

Since `|S∪T| ≤ |S|+|T|` and `0 ≤ 1-p ≤ 1`, this is **`≥ 0`** (overlapping supports are positively correlated) and
**`= 0` when `S, T` are disjoint** (independence).  So for a pairwise‑disjoint support family the variance is a
pure sum of single‑support variances, `Var[X] = ∑_j Cov(X_j, X_j) ≤ ∑_j P(S_j survives) = E[X] ≤ k·s·p`.

## What is proved (clean axioms, no `sorry`)

* `cov`, `cov_eq` — the covariance closed form `(1-p)^{|S∪T|} − (1-p)^{|S|+|T|}`.
* `cov_nonneg` — overlapping supports are positively correlated.
* `cov_disjoint` — disjoint supports are uncorrelated (independence).
* `cov_self_le` — `Cov(X_S, X_S) ≤ P(S survives)` (an indicator's variance is `≤` its mean).
* `variance`, `variance_disjoint_le` — **`Var[X] ≤ k·s·p`** for pairwise‑disjoint supports — the Chebyshev input.

## Honest scope

This is the second‑moment skeleton.  The variance bound `Var[X] ≤ k·s·p` plugs straight into Chebyshev
(`P(|X − E[X]| ≥ t) ≤ Var/t²`), which is what upgrades "few supports survive in expectation" to "few survive with
high probability" at *constant* `p` — the move that beats the first‑moment `k·s < n` regime.  The clean variance
bound holds for **pairwise‑disjoint** supports (genuine independence).  For overlapping supports `cov_nonneg`
exposes the obstruction: positive correlation inflates the variance, and controlling it is exactly the
higher‑moment Håstad switching content (`NP ⊄ ACC⁰`‑strength).  So the structure is laid bare: the second moment is
computed, the disjoint case is Chebyshev‑ready, and the overlap term is named as the remaining frontier.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingVariance

open PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingProb

variable {n k : ℕ}

/-! ## The covariance of two survival indicators -/

/-- The covariance of the survival indicators of `S` and `T` — equivalently of the kill indicators:
`P(S∪T killed) − P(S killed)·P(T killed)`. -/
def cov (p : ℝ) (S T : Finset (Fin n)) : ℝ :=
  killProb p (S ∪ T) - killProb p S * killProb p T

/-- **The covariance closed form (proved): `(1-p)^{|S∪T|} − (1-p)^{|S|+|T|}`.** -/
theorem cov_eq (p : ℝ) (S T : Finset (Fin n)) :
    cov p S T = (1 - p) ^ (S ∪ T).card - (1 - p) ^ (S.card + T.card) := by
  unfold cov killProb
  rw [← pow_add]

/-- **Overlapping supports are positively correlated (proved): `0 ≤ Cov`.** -/
theorem cov_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S T : Finset (Fin n)) :
    0 ≤ cov p S T := by
  rw [cov_eq]
  have hle : (1 - p) ^ (S.card + T.card) ≤ (1 - p) ^ (S ∪ T).card :=
    pow_le_pow_of_le_one (by linarith) (by linarith) (Finset.card_union_le S T)
  linarith

/-- **Disjoint supports are uncorrelated (proved): `Cov = 0`** — the survival indicators are independent. -/
theorem cov_disjoint (p : ℝ) (S T : Finset (Fin n)) (h : Disjoint S T) : cov p S T = 0 := by
  rw [cov_eq, Finset.card_union_of_disjoint h, sub_self]

/-- The covariance of a support with itself is its survival‑indicator variance. -/
theorem cov_self (p : ℝ) (S : Finset (Fin n)) : cov p S S = killProb p S * survProb p S := by
  unfold cov survProb killProb
  rw [Finset.union_self]
  ring

/-- **A survival indicator's variance is `≤` its mean (proved): `Cov(X_S, X_S) ≤ P(S survives)`.** -/
theorem cov_self_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset (Fin n)) :
    cov p S S ≤ survProb p S := by
  rw [cov_self]
  have hk1 : killProb p S ≤ 1 := by
    unfold killProb; exact pow_le_one₀ (by linarith) (by linarith)
  have hs0 : 0 ≤ survProb p S := by
    unfold survProb killProb at *; linarith
  exact mul_le_of_le_one_left hs0 hk1

/-! ## The variance of the surviving‑support count -/

/-- The variance of `X = ∑_j X_j` (number of surviving supports): `Var[X] = ∑_j ∑_l Cov(X_j, X_l)`. -/
def variance (p : ℝ) (supports : Fin k → Finset (Fin n)) : ℝ :=
  ∑ j, ∑ l, cov p (supports j) (supports l)

/-- **The variance bound (proved): `Var[X] ≤ k·s·p` for pairwise‑disjoint supports** — the Chebyshev input.  Off
the diagonal the covariances vanish (independence), so the variance is the sum of single‑support variances, each
`≤` its mean, summing to `≤ E[X] ≤ k·s·p`. -/
theorem variance_disjoint_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (s : ℕ) (hfan : ∀ j, (supports j).card ≤ s)
    (hdis : ∀ j l, j ≠ l → Disjoint (supports j) (supports l)) :
    variance p supports ≤ (k : ℝ) * s * p := by
  have hinner : ∀ j, ∑ l, cov p (supports j) (supports l) = cov p (supports j) (supports j) := by
    intro j
    rw [Finset.sum_eq_single j]
    · intro l _ hlj; exact cov_disjoint p _ _ (hdis j l (Ne.symm hlj))
    · intro h; exact absurd (Finset.mem_univ j) h
  unfold variance
  rw [Finset.sum_congr rfl (fun j _ => hinner j)]
  calc ∑ j, cov p (supports j) (supports j)
      ≤ ∑ j, survProb p (supports j) :=
        Finset.sum_le_sum (fun j _ => cov_self_le p hp0 hp1 _)
    _ ≤ (k : ℝ) * s * p := expectedSurviving_le p hp0 hp1 supports s hfan

/-! ## Bounded overlap: extending the variance bound past independence -/

/-- **The per‑pair covariance is bounded by the overlap (proved): `Cov(X_S, X_T) ≤ |S∩T|·p`.**  Factoring
`Cov = (1-p)^{|S∪T|}·(1 − (1-p)^{|S∩T|})`, the first factor is `≤ 1` and the second is `≤ |S∩T|·p` (Bernoulli). -/
theorem cov_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S T : Finset (Fin n)) :
    cov p S T ≤ ((S ∩ T).card : ℝ) * p := by
  have hcard : S.card + T.card = (S ∪ T).card + (S ∩ T).card :=
    (Finset.card_union_add_card_inter S T).symm
  have hfactor : cov p S T = (1 - p) ^ (S ∪ T).card * survProb p (S ∩ T) := by
    unfold cov survProb killProb
    rw [← pow_add, hcard, pow_add]; ring
  rw [hfactor]
  have h1 : (1 - p) ^ (S ∪ T).card ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have h3 : 0 ≤ survProb p (S ∩ T) := by
    unfold survProb
    have : (1 - p) ^ (S ∩ T).card ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    linarith
  calc (1 - p) ^ (S ∪ T).card * survProb p (S ∩ T)
      ≤ 1 * survProb p (S ∩ T) := mul_le_mul_of_nonneg_right h1 h3
    _ = survProb p (S ∩ T) := one_mul _
    _ ≤ ((S ∩ T).card : ℝ) * p := survProb_le p hp1 _

/-- **The variance bound for bounded overlap (proved): `Var[X] ≤ d·k·s·p`** when each coordinate lies in at most
`d` supports.  By `cov_le` the variance is `≤ p·∑_{j,l}|S_j∩S_l|`, and double counting bounds
`∑_{j,l}|S_j∩S_l| = ∑_v deg(v)² ≤ d·∑_v deg(v) = d·∑_j|S_j| ≤ d·k·s`.  (Disjoint supports are the case `d = 1`.) -/
theorem variance_boundedOverlap_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (s d : ℕ) (hfan : ∀ j, (supports j).card ≤ s)
    (hov : ∀ v, (Finset.univ.filter (fun l => v ∈ supports l)).card ≤ d) :
    variance p supports ≤ (d : ℝ) * k * s * p := by
  have hdc : ∑ j : Fin k, ∑ l : Fin k, (supports j ∩ supports l).card ≤ d * k * s := by
    have perj : ∀ j : Fin k, ∑ l : Fin k, (supports j ∩ supports l).card ≤ d * s := by
      intro j
      calc ∑ l : Fin k, (supports j ∩ supports l).card
          = ∑ l : Fin k, ∑ v ∈ supports j, (if v ∈ supports l then 1 else 0) := by
            apply Finset.sum_congr rfl; intro l _
            rw [← Finset.filter_mem_eq_inter, Finset.card_filter]
        _ = ∑ v ∈ supports j, ∑ l : Fin k, (if v ∈ supports l then 1 else 0) := Finset.sum_comm
        _ = ∑ v ∈ supports j, (Finset.univ.filter (fun l => v ∈ supports l)).card := by
            apply Finset.sum_congr rfl; intro v _; rw [Finset.card_filter]
        _ ≤ ∑ _v ∈ supports j, d := Finset.sum_le_sum (fun v _ => hov v)
        _ = (supports j).card * d := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ s * d := Nat.mul_le_mul (hfan j) (le_refl d)
        _ = d * s := Nat.mul_comm s d
    calc ∑ j : Fin k, ∑ l : Fin k, (supports j ∩ supports l).card
        ≤ ∑ _j : Fin k, d * s := Finset.sum_le_sum (fun j _ => perj j)
      _ = k * (d * s) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ = d * k * s := by ring
  unfold variance
  calc ∑ j, ∑ l, cov p (supports j) (supports l)
      ≤ ∑ j, ∑ l, ((supports j ∩ supports l).card : ℝ) * p :=
        Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun l _ => cov_le p hp0 hp1 _ _))
    _ = (∑ j, ∑ l, ((supports j ∩ supports l).card : ℝ)) * p := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_mul]
    _ = ((∑ j : Fin k, ∑ l : Fin k, (supports j ∩ supports l).card : ℕ) : ℝ) * p := by
        push_cast; ring
    _ ≤ ((d * k * s : ℕ) : ℝ) * p := by
        apply mul_le_mul_of_nonneg_right _ hp0; exact_mod_cast hdc
    _ = (d : ℝ) * k * s * p := by push_cast; ring

end PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingVariance

#print axioms PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingVariance.cov_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingVariance.cov_nonneg
#print axioms PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingVariance.cov_disjoint
#print axioms PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingVariance.variance_disjoint_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingVariance.cov_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingVariance.variance_boundedOverlap_le
