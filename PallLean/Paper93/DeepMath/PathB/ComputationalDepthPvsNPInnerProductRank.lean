import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPLogRankLowerBound
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Inner Product: the communication lower bound the fooling/rank gap is built for

Equality is the *easy* case for the algebraic-rank method: its communication matrix is the identity, whose
`2^n` ones on the diagonal are literally a fooling set, so fooling and rank agree.  **Inner product**
`IP(x,y) = ⟨x,y⟩ mod 2` is the canonical case where the two methods come apart: `IP` has no transparent large
fooling set, but its (signed) communication matrix is the **Sylvester–Hadamard matrix**, which has **full rank
`2^n`** over `ℚ`.  So the algebraic-rank lower bound (`rank_le_card_transcript`) delivers the tight `2^n`
transcript bound where a fooling-set argument does not present itself.

This is the payoff of the rank method: it lower-bounds field rank, which for `IP` is exponentially larger than
its largest monochromatic rectangle.

## Construction

* `phiMatrix φ f` / `phi_rank_le_card_transcript` — the rank bound generalised from the `0/1` indicator matrix
  to an arbitrary field representation `φ : Bool → ℚ` of the decided function (the block decomposition is
  monochromatic-on-rectangles for *any* `φ ∘ f`, hence rank `≤ 1` per transcript).
* `H` — the Sylvester–Hadamard sign matrix `H x y = ∏ᵢ (-1)^{xᵢ yᵢ}`, and `H_eq_sgn_IP : H = φ_sign ∘ IP`.
* `H_mul_transpose : H * Hᵀ = 2^n • 1` — Hadamard orthogonality, by the product/sum factorisation over the
  hypercube.
* `rank_H : rank_ℚ(H) = 2^n` — from `H Hᵀ = 2^n • 1` (`det H ≠ 0`, so `H` is a unit).
* `ip_rank_lower_bound : 2^n ≤ #transcripts` for any protocol computing `IP`.

## Honest scope

Deterministic two-party communication complexity for inner product, via the field-rank method — the case that
the rank/fooling separation exists for.  It does **not** reach `P` (`IP ∈ P`; a `P`-time machine is not a
bounded-communication protocol).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPInnerProductRank

open PallLean.Paper93.DeepMath.PathB.PvsNPInteractiveCoupling
open PallLean.Paper93.DeepMath.PathB.PvsNPLogRankLowerBound
open scoped BigOperators
open Matrix

/-! ## The rank bound for a general field representation `φ ∘ f` -/

/-- The field representation of `f` by `φ : Bool → ℚ`: entry `(a,b)` is `φ (f a b)`. -/
noncomputable def phiMatrix {p q : Nat} (φ : Bool → ℚ) (f : (Fin p → Bool) → (Fin q → Bool) → Bool) :
    Matrix (Fin p → Bool) (Fin q → Bool) ℚ :=
  fun a b => φ (f a b)

open Classical in
/-- The block of `phiMatrix φ f` supported on transcript `τ`'s rectangle. -/
noncomputable def phiBlock {p q : Nat} (P : CommProtocol p q) (φ : Bool → ℚ)
    (f : (Fin p → Bool) → (Fin q → Bool) → Bool) (τ : P.Transcript) :
    Matrix (Fin p → Bool) (Fin q → Bool) ℚ :=
  fun a b => if P.transcript a b = τ then φ (f a b) else 0

theorem phiMatrix_eq_sum {p q : Nat} (P : CommProtocol p q) (φ : Bool → ℚ)
    (f : (Fin p → Bool) → (Fin q → Bool) → Bool) :
    phiMatrix φ f = ∑ τ : P.Transcript, phiBlock P φ f τ := by
  classical
  funext a b
  rw [Matrix.sum_apply]
  simp only [phiBlock]
  rw [Finset.sum_ite_eq Finset.univ (P.transcript a b) (fun _ => φ (f a b))]
  simp [phiMatrix]

theorem phiBlock_rank_le_one {p q : Nat} (P : CommProtocol p q) (φ : Bool → ℚ)
    (f : (Fin p → Bool) → (Fin q → Bool) → Bool) (hcomp : ∀ a b, P.eval a b = f a b)
    (τ : P.Transcript) : (phiBlock P φ f τ).rank ≤ 1 := by
  classical
  set v : ℚ := φ (P.out τ) with hv
  set w : (Fin p → Bool) → ℚ := fun a => if ∃ b, P.transcript a b = τ then v else 0 with hw
  set u : (Fin q → Bool) → ℚ := fun b => if ∃ a, P.transcript a b = τ then (1 : ℚ) else 0 with hu
  have hblock : phiBlock P φ f τ = Matrix.vecMulVec w u := by
    funext a b
    simp only [phiBlock, Matrix.vecMulVec_apply, hw, hu]
    by_cases hτ : P.transcript a b = τ
    · rw [if_pos hτ, if_pos ⟨b, hτ⟩, if_pos ⟨a, hτ⟩, mul_one]
      have hf : f a b = P.out τ := by
        rw [← hcomp a b]; show P.out (P.transcript a b) = P.out τ; rw [hτ]
      rw [hf, ← hv]
    · rw [if_neg hτ]
      by_cases hxb : ∃ b', P.transcript a b' = τ
      · by_cases hxa : ∃ a', P.transcript a' b = τ
        · exfalso
          apply hτ
          obtain ⟨b', hb'⟩ := hxb
          obtain ⟨a', ha'⟩ := hxa
          have hmid : P.transcript a b' = P.transcript a' b := hb'.trans ha'.symm
          have hr := P.rectangle a a' b' b hmid
          rw [hr]; exact hb'
        · rw [if_neg hxa, mul_zero]
      · rw [if_neg hxb, zero_mul]
  rw [hblock]
  exact Matrix.rank_vecMulVec_le w u

/-- **The algebraic communication lower bound for any field representation.**  `rank_ℚ(φ ∘ f) ≤ #transcripts`. -/
theorem phi_rank_le_card_transcript {p q : Nat} (P : CommProtocol p q) (φ : Bool → ℚ)
    (f : (Fin p → Bool) → (Fin q → Bool) → Bool) (hcomp : ∀ a b, P.eval a b = f a b) :
    (phiMatrix φ f).rank ≤ Fintype.card P.Transcript := by
  classical
  rw [phiMatrix_eq_sum P φ f]
  calc (∑ τ : P.Transcript, phiBlock P φ f τ).rank
      ≤ ∑ τ : P.Transcript, (phiBlock P φ f τ).rank := matrix_rank_sum_le _ _
    _ ≤ ∑ _τ : P.Transcript, 1 := Finset.sum_le_sum (fun τ _ => phiBlock_rank_le_one P φ f hcomp τ)
    _ = Fintype.card P.Transcript := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

/-! ## Inner product and its Hadamard matrix -/

/-- The `±1` sign of a bit: `false ↦ 1`, `true ↦ -1`. -/
def sgn (b : Bool) : ℚ := if b then -1 else 1

/-- The per-coordinate Hadamard entry `(-1)^{a·b}`. -/
def ent (a b : Bool) : ℚ := if a && b then -1 else 1

/-- Number of coordinates where both `x` and `y` are `1` — the integer inner product `⟨x,y⟩`. -/
def ipCount {n : Nat} (x y : Fin n → Bool) : Nat :=
  (Finset.univ.filter (fun i => x i && y i)).card

/-- Inner product mod 2. -/
def IP (n : Nat) (x y : Fin n → Bool) : Bool := decide (Odd (ipCount x y))

/-- The Sylvester–Hadamard matrix `H x y = (-1)^{⟨x,y⟩} = ∏ᵢ (-1)^{xᵢ yᵢ}`. -/
noncomputable def H (n : Nat) : Matrix (Fin n → Bool) (Fin n → Bool) ℚ :=
  fun x y => ∏ i, ent (x i) (y i)

/-- The Hadamard matrix is the sign representation of inner product. -/
theorem H_eq_sgn_IP (n : Nat) (x y : Fin n → Bool) : H n x y = sgn (IP n x y) := by
  have hprod : (∏ i, ent (x i) (y i)) = (-1 : ℚ) ^ (ipCount x y) := by
    simp only [ent, ipCount]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  rw [H, hprod]
  rcases Nat.even_or_odd (ipCount x y) with he | ho
  · rw [he.neg_one_pow]; simp [sgn, IP, Nat.not_odd_iff_even.mpr he]
  · rw [ho.neg_one_pow]; simp [sgn, IP, ho]

/-- **Hadamard orthogonality** `H · Hᵀ = 2^n · 1`, by the product/sum factorisation over the hypercube. -/
theorem H_mul_transpose (n : Nat) :
    H n * (H n)ᵀ = (2 : ℚ) ^ n • (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℚ) := by
  ext x z
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hsum : (∑ y : Fin n → Bool, H n x y * (H n)ᵀ y z)
      = ∏ i : Fin n, ∑ b : Bool, (ent (x i) b * ent (z i) b) := by
    rw [← Finset.sum_prod_piFinset Finset.univ (fun i b => ent (x i) b * ent (z i) b),
      Fintype.piFinset_univ]
    apply Finset.sum_congr rfl
    intro y _
    rw [Matrix.transpose_apply, H, H, ← Finset.prod_mul_distrib]
  rw [hsum]
  have hinner : ∀ i : Fin n,
      (∑ b : Bool, ent (x i) b * ent (z i) b) = if x i = z i then (2 : ℚ) else 0 := by
    intro i
    rw [Fintype.sum_bool]
    cases hx : x i <;> cases hz : z i <;> simp [ent] <;> norm_num
  rw [Finset.prod_congr rfl (fun i _ => hinner i)]
  by_cases hxz : x = z
  · subst hxz
    have hL : (∏ i : Fin n, (if x i = x i then (2 : ℚ) else 0)) = 2 ^ n := by
      rw [Finset.prod_congr rfl (fun i _ => if_pos rfl), Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
    rw [hL, if_pos rfl, mul_one]
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ z i := by
      by_contra h; push_neg at h; exact hxz (funext h)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi), if_neg hxz, mul_zero]

/-- **The Hadamard matrix has full rank `2^n`.** -/
theorem rank_H (n : Nat) : (H n).rank = 2 ^ n := by
  have hmul := H_mul_transpose n
  have h1 : (H n).det * (H n).det = ((2 : ℚ) ^ n) ^ Fintype.card (Fin n → Bool) := by
    have hc := congrArg Matrix.det hmul
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one, mul_one] at hc
  have hdet : (H n).det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact (pow_ne_zero _ (pow_ne_zero _ (by norm_num : (2 : ℚ) ≠ 0))) h1.symm
  have hunit : IsUnit (H n) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  rw [Matrix.rank_of_isUnit _ hunit, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-! ## The inner-product lower bound -/

/-- **Inner product needs `2^n` transcripts.**  For any protocol computing `IP`, the signed communication
matrix is the full-rank Hadamard matrix, so the algebraic-rank bound forces `2^n ≤ #transcripts` — the case
where the rank method beats fooling. -/
theorem ip_rank_lower_bound (n : Nat) (P : CommProtocol n n)
    (hcomp : ∀ a b, P.eval a b = IP n a b) :
    2 ^ n ≤ Fintype.card P.Transcript := by
  have hH : phiMatrix sgn (IP n) = H n := by
    funext x y; simp only [phiMatrix]; exact (H_eq_sgn_IP n x y).symm
  have h := phi_rank_le_card_transcript P sgn (IP n) hcomp
  rw [hH, rank_H] at h
  exact h

/-- **Bounded-round / bounded-width corollary.**  A `rounds`-round width-`|State|` protocol for `IP` needs
`width ^ rounds ≥ 2^n`. -/
theorem ip_rounds_width_tradeoff (n rounds : Nat) (State : Type) [Fintype State]
    (P : CommProtocol n n) (hcard : @Fintype.card P.Transcript P.fintype = (Fintype.card State) ^ rounds)
    (hcomp : ∀ a b, P.eval a b = IP n a b) :
    2 ^ n ≤ (Fintype.card State) ^ rounds := by
  rw [← hcard]; exact ip_rank_lower_bound n P hcomp

end PallLean.Paper93.DeepMath.PathB.PvsNPInnerProductRank

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPInnerProductRank.phi_rank_le_card_transcript
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPInnerProductRank.H_mul_transpose
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPInnerProductRank.rank_H
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPInnerProductRank.ip_rank_lower_bound
