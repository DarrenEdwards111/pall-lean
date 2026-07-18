import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRandCommDisc
import Mathlib.Algebra.Order.Chebyshev

/-!
# Lindsey's lemma and the inner-product randomized lower bound

The spectral witness for `RandCommDisc`: INNER PRODUCT `IP x y = ⟨x,y⟩ mod 2` has discrepancy
`2^{-n/2}`, so by the discrepancy method its randomized communication complexity is `Ω(n)`.  This
completes the randomized regime — the reduction (`disc_method`) now has an *unconditional* witness.

The Hadamard sign matrix `hadEntry x y = (-1)^{⟨x,y⟩} = ∏ᵢ (-1)^{xᵢyᵢ}` has orthogonal rows
(`had_ortho`: `∑ₓ H x y · H x y' = 2^n·[y=y']`, a character sum evaluated coordinatewise via
`sum_prod_bool`).  **Lindsey's lemma** (`lindsey_sq`): every submatrix sum obeys
`(∑_{A×B} H)² ≤ |A|·|B|·2^n` — Cauchy–Schwarz (`sq_sum_le_card_mul_sum_sq`) against the
`∑ₓ (∑_{y∈B} H)² = |B|·2^n` bound from orthogonality.

Since `IP` is the parity of `⟨x,y⟩`, `sgn(IP x y) = −hadEntry x y` (`sgn_IP`), so under the uniform
distribution its rectangle bias is `(2^n·2^n)⁻¹·(∑_{A×B} H)`, whose square is `≤ (2^n)⁻¹`
(`ip_disc`: `|bias| ≤ 2^{-n/2}`).  Feeding `disc_method`/`disc_bits` gives `ip_randomized_lb`: a
`c`-bit protocol with error `≤ ε` forces `1 − 2ε ≤ 2^c · 2^{-n/2}`, i.e. `c ≥ n/2 − O(1)` — a
linear randomized lower bound, now unconditional.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.LindseyIP

open Finset
open PallLean.Paper93.DeepMath.PathB.RandCommDisc (sgn bias errμ DistProtocol disc_method disc_bits)

variable {n : ℕ}

/-! ## The Hadamard sign matrix and orthogonality -/

/-- Sum over all Boolean vectors of a product over coordinates factors coordinatewise. -/
theorem sum_prod_bool (F : Fin n → Bool → ℝ) :
    ∑ x : Fin n → Bool, ∏ i, F i (x i) = ∏ i, ∑ b : Bool, F i b := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- The Hadamard sign entry `(-1)^{⟨x,y⟩}` as a coordinatewise product. -/
noncomputable def hadEntry (x y : Fin n → Bool) : ℝ := ∏ i, (if x i && y i then (-1 : ℝ) else 1)

/-- **Row orthogonality of the Hadamard matrix.** -/
theorem had_ortho (y y' : Fin n → Bool) :
    ∑ x : Fin n → Bool, hadEntry x y * hadEntry x y' = if y = y' then (2 ^ n : ℝ) else 0 := by
  have hfac : ∀ x : Fin n → Bool, hadEntry x y * hadEntry x y'
      = ∏ i, ((if x i && y i then (-1:ℝ) else 1) * (if x i && y' i then (-1:ℝ) else 1)) := by
    intro x; rw [hadEntry, hadEntry, ← Finset.prod_mul_distrib]
  simp_rw [hfac]
  rw [sum_prod_bool (fun i b => (if b && y i then (-1:ℝ) else 1) * (if b && y' i then (-1:ℝ) else 1))]
  have hcoord : ∀ i : Fin n,
      (∑ b : Bool, (if b && y i then (-1:ℝ) else 1) * (if b && y' i then (-1:ℝ) else 1))
        = if y i = y' i then (2:ℝ) else 0 := by
    intro i; rw [Fintype.sum_bool]; cases y i <;> cases y' i <;> norm_num
  rw [Finset.prod_congr rfl (fun i _ => hcoord i)]
  by_cases hyy : y = y'
  · subst hyy; simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hyy
    rw [if_neg hyy, Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]

/-- Sum over all `x` of the squared row sum over `B` equals `|B|·2^n`. -/
theorem sq_sum_rowSum (B : Finset (Fin n → Bool)) :
    ∑ x : Fin n → Bool, (∑ y ∈ B, hadEntry x y) ^ 2 = (B.card : ℝ) * 2 ^ n := by
  have h1 : ∀ x : Fin n → Bool, (∑ y ∈ B, hadEntry x y) ^ 2
      = ∑ y ∈ B, ∑ y' ∈ B, hadEntry x y * hadEntry x y' := by
    intro x; rw [sq, Finset.sum_mul_sum]
  simp_rw [h1]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun y _ => Finset.sum_comm)]
  simp_rw [had_ortho]
  rw [Finset.sum_congr rfl (fun y hy => by
    rw [Finset.sum_ite_eq B y (fun _ => (2:ℝ)^n), if_pos hy])]
  rw [Finset.sum_const, nsmul_eq_mul]

/-- **Lindsey's lemma (squared form).**  Every submatrix sum of the Hadamard matrix satisfies
`(∑_{A×B} H)² ≤ |A|·|B|·2^n`. -/
theorem lindsey_sq (A B : Finset (Fin n → Bool)) :
    (∑ x ∈ A, ∑ y ∈ B, hadEntry x y) ^ 2 ≤ (A.card : ℝ) * B.card * 2 ^ n := by
  have hcs : (∑ x ∈ A, ∑ y ∈ B, hadEntry x y) ^ 2
      ≤ (A.card : ℝ) * ∑ x ∈ A, (∑ y ∈ B, hadEntry x y) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hle : ∑ x ∈ A, (∑ y ∈ B, hadEntry x y) ^ 2
      ≤ ∑ x : Fin n → Bool, (∑ y ∈ B, hadEntry x y) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun x _ _ => sq_nonneg _)
  rw [sq_sum_rowSum] at hle
  calc (∑ x ∈ A, ∑ y ∈ B, hadEntry x y) ^ 2
      ≤ (A.card : ℝ) * ∑ x ∈ A, (∑ y ∈ B, hadEntry x y) ^ 2 := hcs
    _ ≤ (A.card : ℝ) * ((B.card : ℝ) * 2 ^ n) := mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)
    _ = (A.card : ℝ) * B.card * 2 ^ n := by ring

/-! ## Inner product -/

/-- The number of coordinates where both bits are `1`. -/
def ipCard (x y : Fin n → Bool) : ℕ := (Finset.univ.filter (fun i => (x i && y i) = true)).card

/-- `hadEntry` is `(-1)` to the number of shared `1`-coordinates. -/
theorem hadEntry_eq (x y : Fin n → Bool) : hadEntry x y = (-1 : ℝ) ^ ipCard x y := by
  rw [hadEntry, ipCard, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

/-- **Inner product mod 2:** `⟨x,y⟩` is odd. -/
def IP (x y : Fin n → Bool) : Bool := decide (Odd (ipCard x y))

/-- The sign of `IP` is the negated Hadamard entry. -/
theorem sgn_IP (x y : Fin n → Bool) : sgn (IP x y) = - hadEntry x y := by
  rw [hadEntry_eq]
  by_cases h : Odd (ipCard x y)
  · have hIP : IP x y = true := by simp [IP, h]
    rw [Odd.neg_one_pow h]
    simp only [sgn, hIP]
    norm_num
  · have hev : Even (ipCard x y) := Nat.not_odd_iff_even.mp h
    have hIP : IP x y = false := by simp [IP, h]
    rw [Even.neg_one_pow hev]
    simp only [sgn, hIP]
    norm_num

/-! ## The uniform distribution and the discrepancy bound -/

/-- The uniform distribution on `(Fin n → Bool)²`. -/
noncomputable def unif : (Fin n → Bool) × (Fin n → Bool) → ℝ :=
  fun _ => ((2 : ℝ) ^ n * (2 : ℝ) ^ n)⁻¹

theorem unif_apply (p : (Fin n → Bool) × (Fin n → Bool)) :
    unif p = ((2 : ℝ) ^ n * (2 : ℝ) ^ n)⁻¹ := rfl

theorem unif_sum : ∑ p : (Fin n → Bool) × (Fin n → Bool), unif p = 1 := by
  simp_rw [unif_apply]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  push_cast
  field_simp

/-- **Inner product has discrepancy `≤ 2^{-n/2}`.**  Every rectangle's uniform bias is bounded by
Lindsey's lemma. -/
theorem ip_disc (a b : (Fin n → Bool) → Bool) :
    |bias unif IP a b| ≤ Real.sqrt (((2 : ℝ) ^ n)⁻¹) := by
  set A := univ.filter (fun x : Fin n → Bool => a x = true) with hA
  set B := univ.filter (fun y : Fin n → Bool => b y = true) with hB
  have hset : (univ : Finset ((Fin n → Bool) × (Fin n → Bool))).filter
      (fun p => a p.1 = true ∧ b p.2 = true) = A ×ˢ B := by
    ext ⟨x, y⟩; simp [hA, hB, Finset.mem_filter, Finset.mem_product]
  have hbias : bias unif IP a b
      = -((2:ℝ)^n * (2:ℝ)^n)⁻¹ * ∑ x ∈ A, ∑ y ∈ B, hadEntry x y := by
    rw [bias, hset, Finset.sum_product, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    show unif (x, y) * sgn (IP x y) = -((2:ℝ)^n * (2:ℝ)^n)⁻¹ * hadEntry x y
    rw [sgn_IP, unif_apply]
    ring
  -- squared bound
  have h2 : (0 : ℝ) < (2:ℝ)^n := by positivity
  have hAle : (A.card : ℝ) ≤ (2:ℝ)^n := by
    rw [show ((2:ℝ)^n) = ((Fintype.card (Fin n → Bool) : ℕ) : ℝ) from by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; push_cast; ring]
    exact_mod_cast Finset.card_le_univ A
  have hBle : (B.card : ℝ) ≤ (2:ℝ)^n := by
    rw [show ((2:ℝ)^n) = ((Fintype.card (Fin n → Bool) : ℕ) : ℝ) from by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; push_cast; ring]
    exact_mod_cast Finset.card_le_univ B
  have hSsq : (∑ x ∈ A, ∑ y ∈ B, hadEntry x y) ^ 2 ≤ (2:ℝ)^n * (2:ℝ)^n * 2^n := by
    calc (∑ x ∈ A, ∑ y ∈ B, hadEntry x y) ^ 2 ≤ (A.card : ℝ) * B.card * 2 ^ n := lindsey_sq A B
      _ ≤ (2:ℝ)^n * (2:ℝ)^n * 2^n := by
          apply mul_le_mul (mul_le_mul hAle hBle (Nat.cast_nonneg _) (le_of_lt h2)) le_rfl
            (by positivity) (by positivity)
  have hne : (2:ℝ)^n ≠ 0 := by positivity
  have hbias_sq : (bias unif IP a b) ^ 2 ≤ ((2:ℝ)^n)⁻¹ := by
    rw [hbias]
    have hsq : (-((2:ℝ)^n * (2:ℝ)^n)⁻¹ * ∑ x ∈ A, ∑ y ∈ B, hadEntry x y) ^ 2
        = (((2:ℝ)^n * (2:ℝ)^n)⁻¹) ^ 2 * (∑ x ∈ A, ∑ y ∈ B, hadEntry x y) ^ 2 := by ring
    rw [hsq]
    calc (((2:ℝ)^n * (2:ℝ)^n)⁻¹) ^ 2 * (∑ x ∈ A, ∑ y ∈ B, hadEntry x y) ^ 2
        ≤ (((2:ℝ)^n * (2:ℝ)^n)⁻¹) ^ 2 * ((2:ℝ)^n * (2:ℝ)^n * 2^n) :=
          mul_le_mul_of_nonneg_left hSsq (by positivity)
      _ = ((2:ℝ)^n)⁻¹ := by field_simp
  calc |bias unif IP a b| = Real.sqrt ((bias unif IP a b) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (((2:ℝ)^n)⁻¹) := Real.sqrt_le_sqrt hbias_sq

/-! ## The randomized lower bound -/

/-- **Inner product's randomized communication complexity is `Ω(n)`.**  A `c`-bit protocol for `IP`
with `uniform`-error `≤ ε` forces `1 − 2ε ≤ 2^c · 2^{-n/2}`; so beating error `1/2` demands
`c ≥ n/2 − O(1)`.  Now unconditional (via Lindsey), the discrepancy method's canonical witness. -/
theorem ip_randomized_lb (c : ℕ) (P : DistProtocol (Fin n → Bool) (Fin n → Bool) (2 ^ c))
    (ε : ℝ) (hε : errμ P IP unif ≤ ε) :
    1 - 2 * ε ≤ (2 ^ c : ℕ) * Real.sqrt (((2 : ℝ) ^ n)⁻¹) :=
  disc_bits IP unif unif_sum P (Real.sqrt (((2 : ℝ) ^ n)⁻¹)) (fun a b => ip_disc a b) ε hε

end PallLean.Paper93.DeepMath.PathB.LindseyIP
