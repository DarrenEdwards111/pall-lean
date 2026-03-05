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
abbrev usesOnly (p : MvPolynomial σ F) (S : Set σ) : Prop :=
  ∀ m ∈ p.support, ∀ x ∈ m.support, x ∈ S

/-- A monomial is "supported in" `S` if all its nonzero indices are in `S`. -/
abbrev monomSupportedIn (m : σ →₀ ℕ) (S : Set σ) : Prop :=
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

/-- usesOnly is monotone in the set -/
theorem usesOnly_mono {p : MvPolynomial σ F} {A B : Set σ} (hp : usesOnly p A) (h : A ⊆ B) :
    usesOnly p B :=
  fun m hm x hx => h (hp m hm x hx)

/-- Product of two polynomials uses only the union of their variable sets -/
theorem usesOnly_mul {p q : MvPolynomial σ F} {A B : Set σ}
    (hp : usesOnly p A) (hq : usesOnly q B) :
    usesOnly (p * q) (A ∪ B) := by
  intro m hm x hx
  rw [MvPolynomial.mem_support_iff] at hm
  -- m ∈ (p*q).support means coeff m (p*q) ≠ 0
  -- By coeff_mul, ∑ coeff a p * coeff b q ≠ 0 for (a,b) ∈ antidiagonal m
  -- So ∃ (a,b), coeff a p ≠ 0 ∧ coeff b q ≠ 0 ∧ a + b = m
  -- x ∈ m.support means m x ≠ 0, so a x ≠ 0 ∨ b x ≠ 0
  -- If a x ≠ 0 then x ∈ a.support and a ∈ p.support → x ∈ A
  -- If b x ≠ 0 then x ∈ b.support and b ∈ q.support → x ∈ B
  have hx_vars : x ∈ (p * q).vars :=
    (MvPolynomial.mem_vars x).mpr ⟨m, MvPolynomial.mem_support_iff.mpr hm, hx⟩
  have hsub := MvPolynomial.vars_mul p q hx_vars
  rw [Finset.mem_union] at hsub
  rcases hsub with hpv | hqv
  · left
    obtain ⟨m', hm', hx'⟩ := (MvPolynomial.mem_vars x).mp hpv
    exact hp m' hm' x hx'
  · right
    obtain ⟨m', hm', hx'⟩ := (MvPolynomial.mem_vars x).mp hqv
    exact hq m' hm' x hx'

/-- monomSupportedIn is monotone -/
theorem monomSupportedIn_mono {m : σ →₀ ℕ} {A B : Set σ}
    (hm : monomSupportedIn m A) (h : A ⊆ B) : monomSupportedIn m B :=
  fun x hx => h (hm x hx)

/-- Sum of two monomials supported in A ∪ B -/
theorem monomSupportedIn_add {mA mB : σ →₀ ℕ} {A B : Set σ}
    (hmA : monomSupportedIn mA A) (hmB : monomSupportedIn mB B) :
    monomSupportedIn (mA + mB) (A ∪ B) := by
  intro x hx
  rw [Finsupp.mem_support_iff] at hx
  simp only [Finsupp.add_apply] at hx
  by_cases h1 : mA x ≠ 0
  · left; exact hmA x (Finsupp.mem_support_iff.mpr h1)
  · push_neg at h1
    have h2 : mB x ≠ 0 := by omega
    right; exact hmB x (Finsupp.mem_support_iff.mpr h2)

/-- Finsupp.sum of a list equals the foldl -/
noncomputable def listFinsuppSum (ms : List (σ →₀ ℕ)) : σ →₀ ℕ :=
  ms.foldr (· + ·) 0

theorem listFinsuppSum_nil : listFinsuppSum ([] : List (σ →₀ ℕ)) = 0 := rfl

theorem listFinsuppSum_cons (hd : σ →₀ ℕ) (rest : List (σ →₀ ℕ)) :
    listFinsuppSum (hd :: rest) = hd + listFinsuppSum rest := rfl

theorem monomSupportedIn_listFinsuppSum {ms : List (σ →₀ ℕ)} {S : Set σ}
    (h : ∀ m ∈ ms, monomSupportedIn m S) :
    monomSupportedIn (listFinsuppSum ms) S := by
  induction ms with
  | nil => intro x hx; simp [listFinsuppSum] at hx
  | cons hd rest ih =>
    -- Debug: check what h looks like after induction
    rw [listFinsuppSum_cons]
    intro x hx
    -- h should be: ∀ m ∈ hd :: rest, monomSupportedIn m S
    -- but let's check by extracting what we need via List.forall_mem_cons
    have ⟨hhd_sup, hrest_all⟩ := List.forall_mem_cons.mp h
    rw [Finsupp.mem_support_iff, Finsupp.add_apply] at hx
    by_cases hhd : hd x ≠ 0
    · exact hhd_sup _ (Finsupp.mem_support_iff.mpr hhd)
    · push_neg at hhd
      have : (listFinsuppSum rest) x ≠ 0 := by omega
      exact ih hrest_all _ (Finsupp.mem_support_iff.mpr this)

theorem foldl_add_acc (ms : List (σ →₀ ℕ)) (acc : σ →₀ ℕ) :
    ms.foldl (· + ·) acc = acc + ms.foldl (· + ·) 0 := by
  induction ms generalizing acc with
  | nil => simp [List.foldl]
  | cons hd rest ih =>
    simp only [List.foldl, zero_add]
    rw [ih (acc + hd), ih hd]
    abel

theorem foldl_add_eq_foldr (ms : List (σ →₀ ℕ)) :
    ms.foldl (· + ·) (0 : σ →₀ ℕ) = listFinsuppSum ms := by
  induction ms with
  | nil => rfl
  | cons hd rest ih =>
    simp only [List.foldl, listFinsuppSum_cons, zero_add]
    rw [foldl_add_acc rest hd, ih]

/-- foldl-sum of monomials is supported in the union of individual supports -/
theorem monomSupportedIn_foldl_add {ms : List (σ →₀ ℕ)} {S : Set σ}
    (h : ∀ m ∈ ms, monomSupportedIn m S) :
    monomSupportedIn (ms.foldl (· + ·) 0) S := by
  rw [foldl_add_eq_foldr]
  exact monomSupportedIn_listFinsuppSum h

/-- Product of polynomials uses only the union of their variable sets -/
theorem usesOnly_list_prod {ps : List (MvPolynomial σ F)} {S : Set σ}
    (h : ∀ p ∈ ps, usesOnly p S) :
    usesOnly ps.prod S := by
  induction ps with
  | nil =>
    intro m hm x hx
    have hxv : x ∈ (1 : MvPolynomial σ F).vars := by
      simp only [List.prod_nil] at hm
      exact (MvPolynomial.mem_vars x).mpr ⟨m, hm, hx⟩
    simp [MvPolynomial.vars_one] at hxv
  | cons phd rest ih =>
    have ⟨hhd, hrest⟩ := List.forall_mem_cons.mp h
    simp only [List.prod_cons]
    intro m hm x hx
    have hxv : x ∈ (phd * rest.prod).vars :=
      (MvPolynomial.mem_vars x).mpr ⟨m, hm, hx⟩
    rcases Finset.mem_union.mp (MvPolynomial.vars_mul phd rest.prod hxv) with hp' | hr
    · obtain ⟨m', hm', hx'⟩ := (MvPolynomial.mem_vars x).mp hp'
      exact hhd m' hm' x hx'
    · obtain ⟨m', hm', hx'⟩ := (MvPolynomial.mem_vars x).mp hr
      exact ih hrest m' hm' x hx'

/-- If every element of a list evaluates to 0 at x, then foldr sum evaluates to 0 at x -/
theorem listFinsuppSum_zero_at {ms : List (σ →₀ ℕ)} {x : σ}
    (h : ∀ m ∈ ms, m x = 0) :
    (listFinsuppSum ms) x = 0 := by
  induction ms with
  | nil => rfl
  | cons hd rest ih =>
    have ⟨hhd, hrest⟩ := List.forall_mem_cons.mp h
    rw [listFinsuppSum_cons, Finsupp.add_apply, hhd, ih hrest, add_zero]

end CoeffDisjoint
