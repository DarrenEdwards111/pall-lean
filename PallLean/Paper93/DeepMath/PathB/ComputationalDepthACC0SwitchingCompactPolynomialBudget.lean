import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SwitchingCircuitLinearGap

/-!
# Dyadic absorption of the compact term-multiplicity overhead

At scale `r = 2^a q`, the compact label contributes at most `(20r+1)^m`.  The theorem
below turns this polynomial factor into one dyadic bit per unit of `r`, subject only to an
explicit finite inequality in `a` and the fixed term bound `m`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCompactPolynomialBudget

open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellRatio
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingLinearGap
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCircuitLinearGap
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellBuckets
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellAveraging
open PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout

/-- Every positive natural is bounded by the corresponding power of two. -/
theorem self_le_two_pow (q : ℕ) : q ≤ 2 ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
      cases q with
      | zero => simp
      | succ q =>
          rw [pow_succ]
          omega

theorem succ_sq_le_four_pow (k : ℕ) : (k + 1) ^ 2 ≤ 4 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      calc
        (k + 1 + 1) ^ 2 ≤ 4 * (k + 1) ^ 2 := by
          simp only [pow_two]
          nlinarith [Nat.zero_le k]
        _ ≤ 4 * 4 ^ k := Nat.mul_le_mul_left 4 ih
        _ = 4 ^ (k + 1) := by rw [pow_succ]; ring

/-- A compact multiplicity label is absorbed by one dyadic bit per scale unit.

The constant `20` is the upper endpoint of the switching shell.  Writing the scale as
`r = 2^a q` gives `20r+1 ≤ 32·2^a·q`; the three factors cost respectively `5m`,
`am`, and at most `qm` exponent bits. -/
theorem compactPolynomial_le_dyadic (m a q : ℕ) (hq : 0 < q)
    (hbudget : 5 * m + a * m + m ≤ 2 ^ a) :
    (20 * (2 ^ a * q) + 1) ^ m ≤ 2 ^ (2 ^ a * q) := by
  have hbase : 20 * (2 ^ a * q) + 1 ≤ 32 * (2 ^ a * q) := by
    have hpos : 0 < 2 ^ a * q := Nat.mul_pos (pow_pos (by norm_num) _) hq
    omega
  have hqpow : q ^ m ≤ (2 ^ q) ^ m := Nat.pow_le_pow_left (self_le_two_pow q) m
  have hexp : 5 * m + a * m + q * m ≤ 2 ^ a * q := by
    calc
      5 * m + a * m + q * m ≤ (5 * m + a * m + m) * q := by
        have hq1 : 1 ≤ q := hq
        calc
          5 * m + a * m + q * m ≤ (5 * m + a * m) * q + q * m := by
            exact Nat.add_le_add (Nat.le_mul_of_pos_right _ hq) le_rfl
          _ = (5 * m + a * m + m) * q := by ring
      _ ≤ 2 ^ a * q := Nat.mul_le_mul_right q hbudget
  calc
    (20 * (2 ^ a * q) + 1) ^ m ≤ (32 * (2 ^ a * q)) ^ m :=
      Nat.pow_le_pow_left hbase m
    _ = 2 ^ (5 * m) * (2 ^ (a * m) * q ^ m) := by
      rw [mul_pow, mul_pow, show 32 = 2 ^ 5 by norm_num, pow_mul, pow_mul]
    _ ≤ 2 ^ (5 * m) * (2 ^ (a * m) * (2 ^ q) ^ m) := by
      gcongr
    _ = 2 ^ (5 * m + a * m + q * m) := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      omega
    _ ≤ 2 ^ (2 ^ a * q) := Nat.pow_le_pow_right (by norm_num) hexp

/-- A fully explicit scale choice, requiring no residual numerical premise. -/
theorem compactPolynomial_explicitScale (m q : ℕ) (hq : 0 < q) :
    (20 * (2 ^ (2 * m + 6) * q) + 1) ^ m ≤
      2 ^ (2 ^ (2 * m + 6) * q) := by
  apply compactPolynomial_le_dyadic m (2 * m + 6) q hq
  have hsq := succ_sq_le_four_pow m
  calc
    5 * m + (2 * m + 6) * m + m ≤ 64 * (m + 1) ^ 2 := by nlinarith
    _ ≤ 64 * 4 ^ m := Nat.mul_le_mul_left 64 hsq
    _ = 2 ^ (2 * m + 6) := by
      rw [show 64 = 2 ^ 6 by norm_num, show 4 ^ m = 2 ^ (2 * m) by
        rw [show 4 = 2 ^ 2 by norm_num, pow_mul]]
      rw [← pow_add]
      congr 1
      omega

/-- At density `K/n = 1/200`, each downward shell step costs at most `1/199`. -/
theorem amplified4000_choose_shell_ratio (r t : ℕ) (hr : 0 < r) (ht : t ≤ 20 * r) :
    (((4000 * r).choose (20 * r - t) : ℚ) / (4000 * r).choose (20 * r))
      ≤ ((1 : ℚ) / 199) ^ t := by
  have hK : 20 * r ≤ 4000 * r := by omega
  have hbase := choose_shell_ratio (n := 4000 * r) (K := 20 * r) (t := t) hK ht
  have hratio :
      ((20 * r : ℕ) : ℚ) / (((4000 * r - 20 * r + 1 : ℕ) : ℚ)) ≤
        (1 : ℚ) / 199 := by
    rw [show 4000 * r - 20 * r + 1 = 3980 * r + 1 by omega]
    apply (div_le_iff₀ (show (0 : ℚ) < ((3980 * r + 1 : ℕ) : ℚ) by positivity)).2
    norm_num
    linarith
  exact hbase.trans (pow_le_pow_left₀ (by positivity) hratio t)

/-- Exact integer budget behind the width-30 compact tail at density `1/200`.
The fifteen exponent bits comprise eight saved bits, five shell-count bits, one compact-polynomial
bit, and one simultaneous-gate-union bit per scale unit. -/
theorem width30_compact_exponential_budget (r : ℕ) (hr : 0 < r) :
    2 ^ (15 * r + 1) * 60 ^ (10 * r) ≤ 199 ^ (10 * r) := by
  have htwo : 2 ≤ 2 ^ r := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ r)
  have hbase : 2 ^ 16 * 60 ^ 10 ≤ 199 ^ 10 := by norm_num
  calc
    2 ^ (15 * r + 1) * 60 ^ (10 * r)
        = 2 * (2 ^ 15) ^ r * (60 ^ 10) ^ r := by
          rw [pow_add, pow_mul, pow_mul]
          ring
    _ ≤ 2 ^ r * (2 ^ 15) ^ r * (60 ^ 10) ^ r := by gcongr
    _ = (2 ^ 16 * 60 ^ 10) ^ r := by rw [← mul_pow, ← mul_pow]; ring
    _ ≤ (199 ^ 10) ^ r := Nat.pow_le_pow_left hbase r
    _ = 199 ^ (10 * r) := by rw [pow_mul]

/-- Rational geometric tail after reserving one scale bit for the compact polynomial and one for
the simultaneous gate union.  The remaining eight bits per scale are genuine exceptional-mass
saving. -/
theorem width30_compact_geometric_budget (r : ℕ) (hr : 0 < r) :
    (2 : ℚ) ^ (10 * r + 1) *
        (∑ t ∈ Finset.Icc (10 * r) (20 * r), ((60 : ℚ) / 199) ^ t) ≤ 1 := by
  have hbase0 : (0 : ℚ) ≤ (60 : ℚ) / 199 := by positivity
  have hbase1 : (60 : ℚ) / 199 ≤ 1 := by norm_num
  have hterm : ∀ t ∈ Finset.Icc (10 * r) (20 * r),
      ((60 : ℚ) / 199) ^ t ≤ ((60 : ℚ) / 199) ^ (10 * r) := by
    intro t ht
    exact pow_le_pow_of_le_one hbase0 hbase1 (Finset.mem_Icc.mp ht).1
  have hsum := Finset.sum_le_sum hterm
  have hcard : (Finset.Icc (10 * r) (20 * r)).card ≤ 20 * r + 1 := by simp
  calc
    (2 : ℚ) ^ (10 * r + 1) *
        (∑ t ∈ Finset.Icc (10 * r) (20 * r), ((60 : ℚ) / 199) ^ t)
      ≤ 2 ^ (10 * r + 1) *
          ((Finset.Icc (10 * r) (20 * r)).card *
            ((60 : ℚ) / 199) ^ (10 * r)) := by
              gcongr
              simpa using hsum
    _ ≤ 2 ^ (10 * r + 1) *
          ((2 ^ (5 * r) : ℕ) * ((60 : ℚ) / 199) ^ (10 * r)) := by
            gcongr
            exact_mod_cast hcard.trans (shell_count_le_pow r)
    _ ≤ 1 := by
      rw [div_pow]
      rw [show (2 : ℚ) ^ (10 * r + 1) *
          ((2 ^ (5 * r) : ℕ) * (60 ^ (10 * r) / 199 ^ (10 * r))) =
          (2 ^ (10 * r + 1) * (2 ^ (5 * r) : ℕ) * 60 ^ (10 * r)) /
            199 ^ (10 * r) by field_simp]
      apply (div_le_iff₀ (by positivity : (0 : ℚ) < (199 : ℚ) ^ (10 * r))).2
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      norm_num only [one_mul]
      rw [← pow_add]
      simpa [show 10 * r + 1 + 5 * r = 15 * r + 1 by ring] using
        (show ((2 ^ (15 * r + 1) * 60 ^ (10 * r) : ℕ) : ℚ) ≤
            199 ^ (10 * r) by
          exact_mod_cast width30_compact_exponential_budget r hr)

/-- Explicit scale simultaneously absorbing the fixed term-count polynomial and the gate union. -/
def compactCircuitScale (m G q : ℕ) : ℕ := 2 ^ (2 * m + 6) * (G * q)

theorem compactCircuitScale_pos {m G q : ℕ} (hG : 0 < G) (hq : 0 < q) :
    0 < compactCircuitScale m G q := by
  exact Nat.mul_pos (pow_pos (by norm_num) _) (Nat.mul_pos hG hq)

/-- The two exponent bits reserved in `width30_compact_geometric_budget` pay exactly for all
term-multiplicity labels and for unioning all `G` genuine gate-bad events. -/
theorem gate_mul_compactPolynomial_le (m G q t : ℕ) (hG : 0 < G) (hq : 0 < q)
    (ht : t ≤ 20 * compactCircuitScale m G q) :
    G * (t + 1) ^ m ≤ 2 ^ (2 * compactCircuitScale m G q) := by
  let r := compactCircuitScale m G q
  have hr : 0 < r := compactCircuitScale_pos hG hq
  have hpoly0 := compactPolynomial_explicitScale m (G * q) (Nat.mul_pos hG hq)
  have hrdef : 2 ^ (2 * m + 6) * (G * q) = r := rfl
  have hpoly : (t + 1) ^ m ≤ 2 ^ r := by
    calc
      (t + 1) ^ m ≤ (20 * r + 1) ^ m := Nat.pow_le_pow_left (by omega) m
      _ ≤ 2 ^ r := by simpa [r, compactCircuitScale] using hpoly0
  have hGr : G ≤ r := by
    dsimp [r, compactCircuitScale]
    calc
      G ≤ G * q := Nat.le_mul_of_pos_right G hq
      _ ≤ 2 ^ (2 * m + 6) * (G * q) :=
        Nat.le_mul_of_pos_left _ (pow_pos (by norm_num) _)
  have hGpow : G ≤ 2 ^ r := hGr.trans (self_le_two_pow r)
  calc
    G * (t + 1) ^ m ≤ 2 ^ r * 2 ^ r := Nat.mul_le_mul hGpow hpoly
    _ = 2 ^ (2 * r) := by rw [← pow_add]; congr 1; omega

/-- Normalized rational form of the complete compact circuit shell budget. -/
theorem width30_compact_normalized_shellBudget (m G q : ℕ)
    (hG : 0 < G) (hq : 0 < q) (r : ℕ) (hr : r = compactCircuitScale m G q) :
    (2 : ℚ) ^ (8 * r + 1) * G *
        (∑ t ∈ Finset.Icc (10 * r) (20 * r),
          ((4000 * r).choose (20 * r - t) : ℕ) * 60 ^ t * (t + 1) ^ m)
      ≤ (4000 * r).choose (20 * r) := by
  have hrpos : 0 < r := by simpa [hr] using compactCircuitScale_pos hG hq
  have hK : 20 * r ≤ 4000 * r := by omega
  have hfull : (0 : ℚ) < (4000 * r).choose (20 * r) := by
    exact_mod_cast Nat.choose_pos hK
  have hterm : ∀ t ∈ Finset.Icc (10 * r) (20 * r),
      (G : ℚ) * (4000 * r).choose (20 * r - t) * 60 ^ t * (t + 1) ^ m ≤
        (4000 * r).choose (20 * r) * 2 ^ (2 * r) * ((60 : ℚ) / 199) ^ t := by
    intro t ht
    have htK : t ≤ 20 * r := (Finset.mem_Icc.mp ht).2
    have hratio := amplified4000_choose_shell_ratio r t hrpos htK
    have hover := gate_mul_compactPolynomial_le m G q t hG hq (by simpa [hr] using htK)
    have hoverQ : (G : ℚ) * (t + 1) ^ m ≤ 2 ^ (2 * r) := by
      rw [hr]
      exact_mod_cast hover
    calc
      (G : ℚ) * (4000 * r).choose (20 * r - t) * 60 ^ t * (t + 1) ^ m
          = ((G : ℚ) * (t + 1) ^ m) *
            (((4000 * r).choose (20 * r - t) : ℚ) /
              (4000 * r).choose (20 * r)) *
            (4000 * r).choose (20 * r) * 60 ^ t := by
              field_simp [ne_of_gt hfull]
      _ ≤ 2 ^ (2 * r) * ((1 : ℚ) / 199) ^ t *
            (4000 * r).choose (20 * r) * 60 ^ t := by gcongr
      _ = (4000 * r).choose (20 * r) * 2 ^ (2 * r) * ((60 : ℚ) / 199) ^ t := by
            simp_rw [div_pow]
            field_simp [pow_ne_zero]
            ring
  have hsum := Finset.sum_le_sum hterm
  have hsum' : (G : ℚ) *
      (∑ t ∈ Finset.Icc (10 * r) (20 * r),
        ((4000 * r).choose (20 * r - t) : ℕ) * 60 ^ t * (t + 1) ^ m) ≤
      (4000 * r).choose (20 * r) * 2 ^ (2 * r) *
        ∑ t ∈ Finset.Icc (10 * r) (20 * r), ((60 : ℚ) / 199) ^ t := by
    simpa [Finset.mul_sum, mul_assoc] using hsum
  have hgeom := width30_compact_geometric_budget r hrpos
  calc
    (2 : ℚ) ^ (8 * r + 1) * G *
        (∑ t ∈ Finset.Icc (10 * r) (20 * r),
          ((4000 * r).choose (20 * r - t) : ℕ) * 60 ^ t * (t + 1) ^ m)
      ≤ 2 ^ (8 * r + 1) *
          ((4000 * r).choose (20 * r) * 2 ^ (2 * r) *
            ∑ t ∈ Finset.Icc (10 * r) (20 * r), ((60 : ℚ) / 199) ^ t) := by
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_left hsum' (by positivity)
    _ = (4000 * r).choose (20 * r) *
          (2 ^ (10 * r + 1) *
            ∑ t ∈ Finset.Icc (10 * r) (20 * r), ((60 : ℚ) / 199) ^ t) := by
              rw [show 10 * r + 1 = (8 * r + 1) + 2 * r by ring, pow_add]
              ring
    _ ≤ (4000 * r).choose (20 * r) := by nlinarith

/-- Exact natural-number shell inequality consumed by `circuitBad_card_le_compactShellSum`. -/
theorem width30_compact_shellBudget (m G q : ℕ) (hG : 0 < G) (hq : 0 < q)
    (r : ℕ) (hr : r = compactCircuitScale m G q) :
    G * (∑ t ∈ Finset.Icc (10 * r) (20 * r),
        (4000 * r).choose (20 * r - t) *
          2 ^ (4000 * r - (20 * r - t)) * (30 ^ t * (t + 1) ^ m)) *
        2 ^ (8 * r + 1)
      ≤ (4000 * r).choose (20 * r) * 2 ^ (4000 * r - 20 * r) := by
  have hnormQ := width30_compact_normalized_shellBudget m G q hG hq r hr
  have hnorm :
      2 ^ (8 * r + 1) * G *
          (∑ t ∈ Finset.Icc (10 * r) (20 * r),
            (4000 * r).choose (20 * r - t) * 60 ^ t * (t + 1) ^ m)
        ≤ (4000 * r).choose (20 * r) := by
    exact_mod_cast hnormQ
  have hfactor :
      (∑ t ∈ Finset.Icc (10 * r) (20 * r),
        (4000 * r).choose (20 * r - t) *
          2 ^ (4000 * r - (20 * r - t)) * (30 ^ t * (t + 1) ^ m)) =
      2 ^ (4000 * r - 20 * r) *
        (∑ t ∈ Finset.Icc (10 * r) (20 * r),
          (4000 * r).choose (20 * r - t) * 60 ^ t * (t + 1) ^ m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have htK : t ≤ 20 * r := (Finset.mem_Icc.mp ht).2
    rw [show 4000 * r - (20 * r - t) = (4000 * r - 20 * r) + t by omega,
      pow_add]
    rw [show 60 ^ t = 2 ^ t * 30 ^ t by rw [← mul_pow]; norm_num]
    ring
  rw [hfactor]
  calc
    G * (2 ^ (4000 * r - 20 * r) *
        ∑ t ∈ Finset.Icc (10 * r) (20 * r),
          (4000 * r).choose (20 * r - t) * 60 ^ t * (t + 1) ^ m) *
        2 ^ (8 * r + 1)
      = 2 ^ (4000 * r - 20 * r) *
          (2 ^ (8 * r + 1) * G *
            ∑ t ∈ Finset.Icc (10 * r) (20 * r),
              (4000 * r).choose (20 * r - t) * 60 ^ t * (t + 1) ^ m) := by ring
    _ ≤ 2 ^ (4000 * r - 20 * r) * (4000 * r).choose (20 * r) :=
      Nat.mul_le_mul_left _ hnorm
    _ = (4000 * r).choose (20 * r) * 2 ^ (4000 * r - 20 * r) := by ring

/-- **Actual simultaneous width-30 compact switching certificate.**  The bad set is the genuine
union of canonical maximum-depth events, and the selected complete bucket gains `8r` exponent bits. -/
theorem width30_compact_selectedBucket_activeGap
    (m G q r : ℕ) (hG : 0 < G) (hq : 0 < q) (hr : r = compactCircuitScale m G q)
    (gates : Fin G → List (Clause (4000 * r)))
    (hnd : ∀ g, (gates g).Nodup)
    (hwidth : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ 30)
    (hterms : ∀ g, (gates g).length ≤ m) :
    ∃ i : Fin ((4000 * r).choose (20 * r)),
      goodBadWork (4000 * r) (4000 * r - 20 * r)
        (2 ^ (4000 * r - 20 * r))
        (concreteBadCount (K := 20 * r) (circuitBad gates (20 * r) (10 * r)) i)
        (10 * r - 1) ≤ 2 ^ (4000 * r - 8 * r) := by
  have hrpos : 0 < r := by simpa [hr] using compactCircuitScale_pos hG hq
  have hKn : 20 * r ≤ 4000 * r := by omega
  have hstars : ∀ ρ ∈ circuitBad gates (20 * r) (10 * r), stars ρ = 20 * r :=
    fun ρ hρ => circuitBad_stars gates (20 * r) (10 * r) ρ hρ
  have hcard := circuitBad_card_le_compactShellSum gates (20 * r) (10 * r)
    hnd hwidth hterms
  have htail : (circuitBad gates (20 * r) (10 * r)).card * 2 ^ (8 * r + 1) ≤
      (4000 * r).choose (20 * r) * 2 ^ (4000 * r - 20 * r) := by
    apply le_trans (Nat.mul_le_mul_right _ hcard)
    simpa [mul_assoc] using width30_compact_shellBudget m G q hG hq r hr
  have hsum := sum_concreteBadCount
    (Bad := circuitBad gates (20 * r) (10 * r)) hstars
  apply aggregateTail_to_selectedBucket_activeGap (4000 * r) ((4000 * r).choose (20 * r))
    (4000 * r - 20 * r) (8 * r) (10 * r - 1)
  · exact Nat.choose_pos hKn
  · omega
  · exact Nat.sub_le _ _
  · omega
  · rw [hsum]
    exact htail
  · omega

end PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCompactPolynomialBudget

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCompactPolynomialBudget.self_le_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCompactPolynomialBudget.compactPolynomial_le_dyadic
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCompactPolynomialBudget.compactPolynomial_explicitScale
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCompactPolynomialBudget.amplified4000_choose_shell_ratio
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCompactPolynomialBudget.width30_compact_exponential_budget
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCompactPolynomialBudget.width30_compact_geometric_budget
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCompactPolynomialBudget.gate_mul_compactPolynomial_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCompactPolynomialBudget.width30_compact_normalized_shellBudget
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCompactPolynomialBudget.width30_compact_shellBudget
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCompactPolynomialBudget.width30_compact_selectedBucket_activeGap
