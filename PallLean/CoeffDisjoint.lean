import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic
/-!
# Coefficient of product with disjoint variable support

Key lemma for identity minor Kronecker δ proof:

If `p` only uses variables in set `A` and `q` only uses variables in set `B`,
and `A ∩ B = ∅`, then:

  `coeff (mA + mB) (p * q) = coeff mA p * coeff mB q`

where `mA` is supported on `A` and `mB` is supported on `B`.

We prove this via the `coeff_mul` convolution formula, showing the only
contributing antidiagonal pair is `(mA, mB)`.
-/

namespace CoeffDisjoint

open MvPolynomial Finsupp

variable {σ : Type*} [DecidableEq σ] {F : Type*} [CommSemiring F]

/-- A polynomial "uses only" variables in `S` if its support monomials
    are all supported within `S`. -/
def usesOnly (p : MvPolynomial σ F) (S : Set σ) : Prop :=
  ∀ m ∈ p.support, ∀ x ∈ m.support, x ∈ S

/-- A monomial is "supported in" `S` if all its nonzero indices are in `S`. -/
def monomSupportedIn (m : σ →₀ ℕ) (S : Set σ) : Prop :=
  ∀ x ∈ m.support, x ∈ S

/-- Key lemma: if p uses only S-vars and m has support outside S,
    then coeff m p = 0. -/
theorem coeff_eq_zero_of_not_supported
    {p : MvPolynomial σ F} {S : Set σ} {m : σ →₀ ℕ}
    (hp : usesOnly p S) (hm : ∃ x ∈ m.support, x ∉ S) :
    coeff m p = 0 := by
  by_contra h
  push_neg at h
  have hmem : m ∈ p.support := MvPolynomial.mem_support_iff.mpr h
  obtain ⟨x, hxm, hxS⟩ := hm
  exact hxS (hp m hmem x hxm)

set_option maxHeartbeats 800000 in
/-- If p uses only A-vars, q uses only B-vars, A ∩ B = ∅,
    and we decompose m = mA + mB with mA on A and mB on B,
    then coeff m (p * q) = coeff mA p * coeff mB q.

    This is the disjoint variable coefficient factorization. -/
theorem coeff_mul_disjoint
    {p q : MvPolynomial σ F} {A B : Set σ}
    (hp : usesOnly p A) (hq : usesOnly q B)
    (hdisj : Disjoint A B)
    {mA mB : σ →₀ ℕ}
    (hmA : monomSupportedIn mA A) (hmB : monomSupportedIn mB B) :
    coeff (mA + mB) (p * q) = coeff mA p * coeff mB q := by
  -- Use coeff_mul: coeff m (p*q) = ∑_{(a,b) ∈ m.antidiagonal} coeff a p * coeff b q
  rw [coeff_mul]
  -- Only the pair (mA, mB) contributes; all others vanish.
  -- We show: for (a, b) ∈ antidiagonal(mA + mB), if (a,b) ≠ (mA, mB)
  -- then coeff a p = 0 or coeff b q = 0.
  apply Finset.sum_eq_single (mA, mB)
  · -- All other antidiagonal pairs contribute 0
    intro ⟨a, b⟩ hab hne
    rw [Finset.mem_antidiagonal] at hab
    -- hab : a + b = mA + mB, and (a,b) ≠ (mA, mB)
    -- Since a + b = mA + mB, either a ≠ mA or b ≠ mB.
    -- If a ≠ mA: there exists x where a(x) ≠ mA(x).
    -- Case 1: x ∈ A → then a(x) > mA(x) → b(x) < mB(x) but x ∉ B (disjoint)
    --   so mB(x) = 0, contradiction with b(x) < mB(x) and a(x) > mA(x)
    --   Actually: if x ∈ A, mB(x) = 0 (since mB supported in B, disjoint from A)
    --   So a(x) + b(x) = mA(x) + 0 = mA(x). If a(x) ≠ mA(x) then b(x) ≠ 0
    --   and x ∉ B (disjoint), so coeff b q = 0.
    -- Case 2: x ∉ A → then a(x) = anything, but mA(x) = 0 (mA on A)
    --   So a(x) + b(x) = 0 + mB(x), giving a(x) + b(x) = mB(x).
    --   If a(x) ≠ 0 then x ∈ a.support but x ∉ A, so coeff a p = 0.
    by_cases ha : a = mA
    · -- Then b ≠ mB, but a + b = mA + mB gives b = mB. Contradiction.
      subst ha
      have : b = mB := add_left_cancel hab
      exact absurd (by exact Prod.ext rfl this) hne
    · -- a ≠ mA. Find x where a(x) ≠ mA(x).
      have hne_fun : ∃ x, a x ≠ mA x := by
        by_contra hall
        push_neg at hall
        exact ha (Finsupp.ext hall)
      obtain ⟨x, hax⟩ := hne_fun
      -- From a + b = mA + mB pointwise: a(x) + b(x) = mA(x) + mB(x)
      have hsum : a x + b x = mA x + mB x := by
        have := DFunLike.congr_fun hab x; simp [Finsupp.add_apply] at this; exact this
      by_cases hxA : x ∈ A
      · -- x ∈ A, so x ∉ B (disjoint), so mB(x) = 0
        have hxnB : x ∉ B := Set.disjoint_left.mp hdisj hxA
        have hmBx : mB x = 0 := by
          by_contra h; exact hxnB (hmB x (Finsupp.mem_support_iff.mpr h))
        -- So a(x) + b(x) = mA(x). Since a(x) ≠ mA(x), b(x) ≠ 0.
        -- So x ∈ b.support but x ∉ B, so coeff b q = 0.
        have hbx : b x ≠ 0 := by omega
        have hx_bsupp : x ∈ b.support := Finsupp.mem_support_iff.mpr hbx
        have : coeff b q = 0 := coeff_eq_zero_of_not_supported hq ⟨x, hx_bsupp, hxnB⟩
        simp [this]
      · -- x ∉ A, so mA(x) = 0
        have hmAx : mA x = 0 := by
          by_contra h; exact hxA (hmA x (Finsupp.mem_support_iff.mpr h))
        -- a(x) + b(x) = 0 + mB(x) = mB(x). Since a(x) ≠ 0 (because a(x) ≠ mA(x) = 0),
        -- x ∈ a.support but x ∉ A, so coeff a p = 0.
        have hax' : a x ≠ 0 := by omega
        have hx_asupp : x ∈ a.support := Finsupp.mem_support_iff.mpr hax'
        have : coeff a p = 0 := coeff_eq_zero_of_not_supported hp ⟨x, hx_asupp, hxA⟩
        simp [this]
  · -- (mA, mB) ∈ antidiagonal(mA + mB)
    simp [Finset.mem_antidiagonal]

end CoeffDisjoint
