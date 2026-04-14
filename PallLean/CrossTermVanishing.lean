/-
  CrossTermVanishing.lean -- Leibniz cross-terms vanish at first-of-block tag monomials

  Key result: For first-of-block S and T, the coefficient of tagMonomial T
  in mlProj(iterDerivList S compiledPoly) equals the coefficient in
  mlProj(boolFactorDerivProd S), namely 2^|S∩T|.

  This bridges from boolFactorFullProd linear independence to compiledPoly
  linear independence, eliminating the axiom identity_construction_np_lower_bound.
-/
import PallLean.CompiledBoolFactorBridge
import PallLean.BlockedBoolRank
import Mathlib.Tactic

namespace CrossTermVanishing

open MvPolynomial SPDP MultilinearSPDP SymmetricPower PaperFaithfulSeparation TuringMachine

/-! ## Step 1: Coefficient preservation for products -/

/-- Coefficient preservation: if every non-constant monomial b of Q with b ≤ m
has coeff 0, then coeff(m, p * Q) = coeff(m, p) * coeff(0, Q). -/
theorem coeff_mul_of_no_submono {n : ℕ}
    (p Q : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ)
    (hQ : ∀ b : Fin n →₀ ℕ, b ≠ 0 → (∀ i, b i ≤ m i) →
      MvPolynomial.coeff b Q = 0) :
    MvPolynomial.coeff m (p * Q) = MvPolynomial.coeff m p * MvPolynomial.coeff 0 Q := by
  rw [CompiledBoolFactorBridge.coeff_mul_constant_term]
  suffices h : ∑ x ∈ (Finset.antidiagonal m).filter (fun x => x.2 ≠ 0),
      MvPolynomial.coeff x.1 p * MvPolynomial.coeff x.2 Q = 0 by
    linarith
  apply Finset.sum_eq_zero
  intro ⟨a, b⟩ hmem
  simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hmem
  obtain ⟨hab, hb_ne⟩ := hmem
  have hb_le : ∀ i, b i ≤ m i := by
    intro i
    have := congr_fun (congr_arg DFunLike.coe hab) i
    simp only [Finsupp.coe_add, Pi.add_apply] at this
    omega
  rw [hQ b hb_ne hb_le, mul_zero]

/-! ## Step 2: No-submonomials property -/

def NoSubmonomials {n : ℕ} (Q : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ) : Prop :=
  ∀ b : Fin n →₀ ℕ, b ≠ 0 → (∀ i, b i ≤ m i) → MvPolynomial.coeff b Q = 0

theorem noSubmono_one {n : ℕ} (m : Fin n →₀ ℕ) :
    NoSubmonomials (1 : MvPolynomial (Fin n) ℚ) m := by
  intro b hb _
  simp only [MvPolynomial.coeff_one]
  rw [if_neg (Ne.symm hb)]

theorem noSubmono_mul {n : ℕ} (Q₁ Q₂ : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ)
    (h₁ : NoSubmonomials Q₁ m) (h₂ : NoSubmonomials Q₂ m) :
    NoSubmonomials (Q₁ * Q₂) m := by
  intro b hb hle
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro ⟨a, c⟩ hmem
  simp only [Finset.mem_antidiagonal] at hmem
  have ha_le : ∀ i, a i ≤ m i := by
    intro i; have := congr_fun (congr_arg DFunLike.coe hmem) i
    simp only [Finsupp.coe_add, Pi.add_apply] at this; have := hle i; omega
  have hc_le : ∀ i, c i ≤ m i := by
    intro i; have := congr_fun (congr_arg DFunLike.coe hmem) i
    simp only [Finsupp.coe_add, Pi.add_apply] at this; have := hle i; omega
  by_cases ha : a = 0
  · have hcb : c = b := by have := hmem; rw [ha] at this; simpa using this
    rw [hcb, h₂ b hb hle, mul_zero]
  · rw [h₁ a ha ha_le, zero_mul]

/-! ## Step 3: Consecutive pair exclusion -/

theorem no_consec_in_three_mult {n : ℕ}
    (T : Finset (Fin n)) (hT : ∀ v ∈ T, 3 ∣ v.val)
    (j : Fin n) (hj1 : j.val + 1 < n)
    (hj_in : j ∈ T) (hj1_in : (⟨j.val + 1, hj1⟩ : Fin n) ∈ T) : False := by
  obtain ⟨a, ha⟩ := hT j hj_in
  obtain ⟨b, hb⟩ := hT ⟨j.val + 1, hj1⟩ hj1_in
  simp at hb; omega

/-! ## Step 4: Adjacency factors have NoSubmonomials for first-of-block T -/

theorem noSubmono_adj_factor {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (T : Finset (Fin n)) (hT : ∀ v ∈ T, 3 ∣ v.val) :
    NoSubmonomials
      ((1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩)
      (tagMonomial T) := by
  intro b hb hle
  have hcoeff_sub : MvPolynomial.coeff b
      ((1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩) =
      MvPolynomial.coeff b (1 : MvPolynomial (Fin n) ℚ) -
      MvPolynomial.coeff b (MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩) := by
    simp [sub_eq_add_neg, map_add, map_neg]
  rw [hcoeff_sub]
  have hb0 : MvPolynomial.coeff b (1 : MvPolynomial (Fin n) ℚ) = 0 := by
    rw [MvPolynomial.coeff_one, if_neg (Ne.symm hb)]
  rw [hb0, zero_sub, neg_eq_zero]
  have hXX : (MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩ : MvPolynomial (Fin n) ℚ) =
      MvPolynomial.monomial (Finsupp.single i 1 + Finsupp.single ⟨i.val + 1, hi⟩ 1) 1 := by
    rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]
  rw [hXX, MvPolynomial.coeff_monomial]
  split_ifs with hbeq
  · exfalso
    set j := (⟨i.val + 1, hi⟩ : Fin n) with hj_def
    have hij : i ≠ j := by intro h; simp [hj_def, Fin.ext_iff] at h
    have hbi : 1 ≤ b i := by
      have h2 := DFunLike.congr_fun hbeq i
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
        Finsupp.single_apply, if_neg (Ne.symm hij)] at h2; omega
    have hbi1 : 1 ≤ b j := by
      have h2 := DFunLike.congr_fun hbeq j
      simp only [Finsupp.coe_add, Pi.add_apply] at h2
      rw [Finsupp.single_apply, if_neg hij, Finsupp.single_eq_same] at h2; omega
    have hi_in : i ∈ T := by
      have h := hle i; rw [tagMonomial_apply] at h
      split_ifs at h with hmem; exact hmem; exfalso; omega
    have hj_in : j ∈ T := by
      have h := hle j; rw [tagMonomial_apply] at h
      split_ifs at h with hmem; exact hmem; exfalso; omega
    exact no_consec_in_three_mult T hT i hi hi_in (hj_def ▸ hj_in)
  · rfl

theorem noSubmono_cadj_factor {n : ℕ} (c : ℚ) (i : Fin n) (hi : i.val + 1 < n)
    (T : Finset (Fin n)) (hT : ∀ v ∈ T, 3 ∣ v.val) :
    NoSubmonomials
      ((1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.C c * (MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩))
      (tagMonomial T) := by
  intro b hb hle
  have hadj := noSubmono_adj_factor i hi T hT b hb hle
  have hb1 : MvPolynomial.coeff b (1 : MvPolynomial (Fin n) ℚ) = 0 := by
    rw [MvPolynomial.coeff_one, if_neg (Ne.symm hb)]
  have hXiXj : MvPolynomial.coeff b
      (MvPolynomial.X i * MvPolynomial.X (⟨i.val + 1, hi⟩ : Fin n) : MvPolynomial (Fin n) ℚ) = 0 := by
    have hcoeff_sub : MvPolynomial.coeff b
        ((1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩) =
        MvPolynomial.coeff b (1 : MvPolynomial (Fin n) ℚ) -
        MvPolynomial.coeff b (MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩) := by
      simp [sub_eq_add_neg, map_add, map_neg]
    rw [hcoeff_sub] at hadj; linarith
  have hcoeff : MvPolynomial.coeff b
      ((1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.C c * (MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩)) =
      MvPolynomial.coeff b (1 : MvPolynomial (Fin n) ℚ) -
      c * MvPolynomial.coeff b (MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩) := by
    simp [sub_eq_add_neg, map_add, map_neg, MvPolynomial.coeff_C_mul]
  rw [hcoeff, hb1, hXiXj, mul_zero, sub_zero]

/-! ## Step 5: Coefficient preservation through iterDerivList

Key lemma: coeff(m, iterDerivList S (f * Q)) = coeff(m, iterDerivList S f)
when Q has constant term 1 and all Q and its iterated derivatives have
NoSubmonomials and zero constant term (for derivatives).

We prove TWO mutually recursive claims by induction on |S|:
- claimA: coeff(0, R) = 1 → NoSubmonomials R m → ... → coeff(m, iterDerivList S (f*R)) = coeff(m, iterDerivList S f)
- claimB: coeff(0, R) = 0 → NoSubmonomials R m → ... → coeff(m, iterDerivList S (f*R)) = 0

The recursion bottoms out because |S| decreases strictly. -/

/-- Predicate: R and all its pderiv's (up to depth d) have NoSubmonomials w.r.t. m,
and all pderiv's have constant term 0. -/
def GoodToDepth {n : ℕ} (R : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ) : ℕ → Prop
  | 0 => NoSubmonomials R m
  | d + 1 => NoSubmonomials R m ∧
    ∀ s : Fin n, MvPolynomial.coeff 0 (MvPolynomial.pderiv s R) = 0 ∧
      GoodToDepth (MvPolynomial.pderiv s R) m d

/-- GoodToDepth at depth d+1 implies GoodToDepth at depth d. -/
theorem goodToDepth_of_succ {n : ℕ} (R : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ) (d : ℕ)
    (h : GoodToDepth R m (d + 1)) : GoodToDepth R m d := by
  induction d generalizing R with
  | zero => exact h.1
  | succ d ih =>
    constructor
    · exact h.1
    · intro s
      exact ⟨(h.2 s).1, ih _ (h.2 s).2⟩

/-- GoodToDepth at depth d+1 implies pderiv s R has GoodToDepth at depth d. -/
theorem goodToDepth_pderiv {n : ℕ} (R : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ) (d : ℕ) (s : Fin n)
    (h : GoodToDepth R m (d + 1)) : GoodToDepth (MvPolynomial.pderiv s R) m d :=
  (h.2 s).2

/-- Joint inductive claim: if R has NoSubmonomials and GoodToDepth d for |S| ≤ d,
then coeff(m, iterDerivList S (f * R)) = coeff(m, iterDerivList S f) * coeff(0, R). -/
theorem coeff_iterDeriv_mul_good {n : ℕ}
    (m : Fin n →₀ ℕ) (S : List (Fin n)) (d : ℕ) (hd : S.length ≤ d)
    (f R : MvPolynomial (Fin n) ℚ)
    (hR : GoodToDepth R m d) :
    MvPolynomial.coeff m (iterDerivList S (f * R)) =
    MvPolynomial.coeff m (iterDerivList S f) * MvPolynomial.coeff 0 R := by
  induction d generalizing S f R with
  | zero =>
    -- |S| ≤ 0, so S = []
    have hnil : S = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    simp only [IterDerivHelpers.iterDerivList_nil]
    exact coeff_mul_of_no_submono f R m hR
  | succ d ih =>
    cases S with
    | nil =>
      simp only [IterDerivHelpers.iterDerivList_nil]
      exact coeff_mul_of_no_submono f R m hR.1
    | cons s rest =>
      simp only [IterDerivHelpers.iterDerivList_cons]
      rw [MvPolynomial.pderiv_mul, IterDerivHelpers.iterDerivList_add]
      -- Goal: coeff m (iterDerivList rest (pderiv s f * R) + iterDerivList rest (f * pderiv s R))
      --     = coeff m (iterDerivList rest (pderiv s f)) * coeff 0 R
      -- Distribute coeff over addition
      have hadd := MvPolynomial.coeff_add m
        (iterDerivList rest (MvPolynomial.pderiv s f * R))
        (iterDerivList rest (f * MvPolynomial.pderiv s R))
      rw [hadd]
      -- Term 1: iterDerivList rest (pderiv s f * R)
      have h1 := ih rest (by simp at hd; omega) (MvPolynomial.pderiv s f) R
        (goodToDepth_of_succ R m d hR)
      -- Term 2: iterDerivList rest (f * pderiv s R)
      have hR' := goodToDepth_pderiv R m d s hR
      have h2 := ih rest (by simp at hd; omega) f (MvPolynomial.pderiv s R) hR'
      rw [h1, h2, (hR.2 s).1, mul_zero, add_zero]

/-- Main coefficient preservation: when R has constant term 1, GoodToDepth,
coeff(m, iterDerivList S (f*R)) = coeff(m, iterDerivList S f). -/
theorem coeff_iterDeriv_mul_inert {n : ℕ}
    (m : Fin n →₀ ℕ) (S : List (Fin n))
    (f R : MvPolynomial (Fin n) ℚ)
    (hR_const : MvPolynomial.coeff 0 R = 1)
    (hR_good : GoodToDepth R m S.length) :
    MvPolynomial.coeff m (iterDerivList S (f * R)) =
    MvPolynomial.coeff m (iterDerivList S f) := by
  have := coeff_iterDeriv_mul_good m S S.length (le_refl _) f R hR_good
  rw [this, hR_const, mul_one]


/-! ## Step 6: GoodToDepth closure properties -/

/-- GoodToDepth is closed under addition. -/
theorem goodToDepth_add {n : ℕ} (R₁ R₂ : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ) (d : ℕ)
    (h₁ : GoodToDepth R₁ m d) (h₂ : GoodToDepth R₂ m d) :
    GoodToDepth (R₁ + R₂) m d := by
  induction d generalizing R₁ R₂ with
  | zero =>
    intro b hb hle
    rw [MvPolynomial.coeff_add, h₁ b hb hle, h₂ b hb hle, add_zero]
  | succ d ih =>
    constructor
    · intro b hb hle
      rw [MvPolynomial.coeff_add, h₁.1 b hb hle, h₂.1 b hb hle, add_zero]
    · intro s
      constructor
      · rw [map_add (MvPolynomial.pderiv s), MvPolynomial.coeff_add, (h₁.2 s).1, (h₂.2 s).1, add_zero]
      · rw [map_add (MvPolynomial.pderiv s)]
        exact ih _ _ (h₁.2 s).2 (h₂.2 s).2

/-- GoodToDepth is closed under scalar multiplication. -/
theorem goodToDepth_smul {n : ℕ} (c : ℚ) (R : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ) (d : ℕ)
    (h : GoodToDepth R m d) :
    GoodToDepth (MvPolynomial.C c * R) m d := by
  induction d generalizing R with
  | zero =>
    intro b hb hle
    rw [MvPolynomial.coeff_C_mul, h b hb hle, mul_zero]
  | succ d ih =>
    constructor
    · intro b hb hle
      rw [MvPolynomial.coeff_C_mul, h.1 b hb hle, mul_zero]
    · intro s
      constructor
      · simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C]
        rw [zero_mul, zero_add, MvPolynomial.coeff_C_mul, (h.2 s).1, mul_zero]
      · simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C]
        rw [zero_mul, zero_add]
        exact ih _ (h.2 s).2

/-- Constant term of a product equals product of constant terms (at monomial 0). -/
theorem coeff_zero_mul {n : ℕ} (p q : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff 0 (p * q) = MvPolynomial.coeff 0 p * MvPolynomial.coeff 0 q := by
  have h1 : MvPolynomial.coeff 0 (p * q) = MvPolynomial.constantCoeff (p * q) := rfl
  have h2 : MvPolynomial.constantCoeff (p * q) =
      MvPolynomial.constantCoeff p * MvPolynomial.constantCoeff q := map_mul _ p q
  rw [h1, h2]; rfl

/-- A polynomial has "GoodAllDepths" if it satisfies GoodToDepth at every depth,
    and all its partial derivatives have constant term 0. -/
def GoodAllDepths {n : ℕ} (R : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ) : Prop :=
  (∀ d : ℕ, GoodToDepth R m d) ∧
  (∀ s : Fin n, MvPolynomial.coeff 0 (MvPolynomial.pderiv s R) = 0)

/-- GoodAllDepths implies GoodToDepth at any depth. -/
theorem goodAllDepths_to_depth {n : ℕ} (R : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ)
    (h : GoodAllDepths R m) (d : ℕ) : GoodToDepth R m d := h.1 d

/-- GoodAllDepths is preserved by pderiv. -/
theorem goodAllDepths_pderiv {n : ℕ} (R : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ) (s : Fin n)
    (h : GoodAllDepths R m) : GoodAllDepths (MvPolynomial.pderiv s R) m := by
  constructor
  · intro d
    exact goodToDepth_pderiv R m d s (h.1 (d + 1))
  · intro s'
    exact ((h.1 2).2 s).2.2 s' |>.1

/-- GoodAllDepths is closed under addition. -/
theorem goodAllDepths_add {n : ℕ} (R₁ R₂ : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ)
    (h₁ : GoodAllDepths R₁ m) (h₂ : GoodAllDepths R₂ m) :
    GoodAllDepths (R₁ + R₂) m := by
  constructor
  · intro d
    exact goodToDepth_add R₁ R₂ m d (h₁.1 d) (h₂.1 d)
  · intro s
    rw [map_add (MvPolynomial.pderiv s), MvPolynomial.coeff_add, h₁.2 s, h₂.2 s, add_zero]

/-- Core lemma: for polynomials with GoodAllDepths, the product has GoodToDepth at any depth.
    Proved by strong induction on d, universally quantified over all pairs.
    The key insight: pderiv of a GoodAllDepths poly is also GoodAllDepths, so the induction
    hypothesis applies to the derivative terms in the Leibniz expansion. -/
private theorem goodToDepth_mul_aux {n : ℕ} (d : ℕ) :
    ∀ (R₁ R₂ : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ),
    GoodAllDepths R₁ m → GoodAllDepths R₂ m →
    GoodToDepth (R₁ * R₂) m d := by
  induction d with
  | zero =>
    intro R₁ R₂ m h₁ h₂
    exact noSubmono_mul R₁ R₂ m (h₁.1 0) (h₂.1 0)
  | succ d ih =>
    intro R₁ R₂ m h₁ h₂
    constructor
    · exact noSubmono_mul R₁ R₂ m (h₁.1 0) (h₂.1 0)
    · intro s
      constructor
      · rw [MvPolynomial.pderiv_mul, MvPolynomial.coeff_add,
          coeff_zero_mul, coeff_zero_mul, h₁.2 s, h₂.2 s, zero_mul, mul_zero, add_zero]
      · rw [MvPolynomial.pderiv_mul]
        apply goodToDepth_add
        · exact ih _ _ m (goodAllDepths_pderiv R₁ m s h₁) h₂
        · exact ih _ _ m h₁ (goodAllDepths_pderiv R₂ m s h₂)

/-- GoodAllDepths is closed under polynomial multiplication. -/
theorem goodAllDepths_mul {n : ℕ}
    (R₁ R₂ : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ)
    (h₁ : GoodAllDepths R₁ m) (h₂ : GoodAllDepths R₂ m) :
    GoodAllDepths (R₁ * R₂) m := by
  constructor
  · intro d
    exact goodToDepth_mul_aux d R₁ R₂ m h₁ h₂
  · intro s
    rw [MvPolynomial.pderiv_mul, MvPolynomial.coeff_add,
      coeff_zero_mul, coeff_zero_mul, h₁.2 s, h₂.2 s, zero_mul, mul_zero, add_zero]

/-! ## Step 7: Restricted GoodToDepth for derivative lists with first-of-block variables

The unrestricted GoodToDepth (requiring NoSubmonomials for derivatives in ALL directions)
cannot hold for individual rest factors when some of their variables are in the tag set T.
E.g., the adjacency factor 1 - X_i X_{i+1} with i ∈ T has pderiv (i+1) = -X_i, and
X_i has a nonzero coefficient at single i 1 ≤ tagMonomial T.

However, the iterDerivList in our application only differentiates along first-of-block
variables (multiples of 3). For such variables s, pderiv s of the adjacency factor
1 - X_s X_{s+1} gives -X_{s+1}, and s+1 ∉ T (not a multiple of 3).

We define GoodToDepthRestricted, which only requires the GoodToDepth properties for
variables in a given set V. We then prove the coefficient preservation theorem for
derivative lists whose elements are all in V. -/

/-- Restricted version of GoodToDepth: only requires NoSubmonomials and derivative
    properties along variables in V. -/
def GoodToDepthR {n : ℕ} (R : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ)
    (V : Finset (Fin n)) : ℕ → Prop
  | 0 => NoSubmonomials R m
  | d + 1 => NoSubmonomials R m ∧
    ∀ s ∈ V, MvPolynomial.coeff 0 (MvPolynomial.pderiv s R) = 0 ∧
      GoodToDepthR (MvPolynomial.pderiv s R) m V d

/-- GoodToDepthR at depth d+1 implies depth d. -/
theorem goodToDepthR_of_succ {n : ℕ} (R : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ)
    (V : Finset (Fin n)) (d : ℕ) (h : GoodToDepthR R m V (d + 1)) :
    GoodToDepthR R m V d := by
  induction d generalizing R with
  | zero => exact h.1
  | succ d ih =>
    constructor
    · exact h.1
    · intro s hs
      exact ⟨(h.2 s hs).1, ih _ (h.2 s hs).2⟩

/-- GoodToDepthR at depth d+1 implies pderiv s R has GoodToDepthR at depth d,
    for s ∈ V. -/
theorem goodToDepthR_pderiv {n : ℕ} (R : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ)
    (V : Finset (Fin n)) (d : ℕ) (s : Fin n) (hs : s ∈ V)
    (h : GoodToDepthR R m V (d + 1)) : GoodToDepthR (MvPolynomial.pderiv s R) m V d :=
  (h.2 s hs).2

/-- Coefficient preservation for iterDerivList using restricted GoodToDepthR,
    when all elements of the derivative list S are in V. -/
theorem coeff_iterDeriv_mul_goodR {n : ℕ}
    (m : Fin n →₀ ℕ) (S : List (Fin n)) (V : Finset (Fin n))
    (hSV : ∀ s ∈ S, s ∈ V)
    (d : ℕ) (hd : S.length ≤ d)
    (f R : MvPolynomial (Fin n) ℚ)
    (hR : GoodToDepthR R m V d) :
    MvPolynomial.coeff m (iterDerivList S (f * R)) =
    MvPolynomial.coeff m (iterDerivList S f) * MvPolynomial.coeff 0 R := by
  induction d generalizing S f R with
  | zero =>
    have hnil : S = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    simp only [IterDerivHelpers.iterDerivList_nil]
    exact coeff_mul_of_no_submono f R m hR
  | succ d ih =>
    cases S with
    | nil =>
      simp only [IterDerivHelpers.iterDerivList_nil]
      exact coeff_mul_of_no_submono f R m hR.1
    | cons s rest =>
      simp only [IterDerivHelpers.iterDerivList_cons]
      rw [MvPolynomial.pderiv_mul, IterDerivHelpers.iterDerivList_add]
      rw [MvPolynomial.coeff_add]
      have hs_in_V : s ∈ V := hSV s (by simp)
      have hrest_in_V : ∀ s' ∈ rest, s' ∈ V :=
        fun s' hs' => hSV s' (by simp [hs'])
      have h1 := ih rest hrest_in_V (by simp at hd; omega) (MvPolynomial.pderiv s f) R
        (goodToDepthR_of_succ R m V d hR)
      have hR' := goodToDepthR_pderiv R m V d s hs_in_V hR
      have h2 := ih rest hrest_in_V (by simp at hd; omega) f (MvPolynomial.pderiv s R) hR'
      rw [h1, h2, (hR.2 s hs_in_V).1, mul_zero, add_zero]

/-- Main coefficient preservation with restricted GoodToDepthR: when R has constant term 1
    and satisfies GoodToDepthR along V, and all elements of S are in V,
    coeff(m, iterDerivList S (f*R)) = coeff(m, iterDerivList S f). -/
theorem coeff_iterDeriv_mul_inertR {n : ℕ}
    (m : Fin n →₀ ℕ) (S : List (Fin n)) (V : Finset (Fin n))
    (hSV : ∀ s ∈ S, s ∈ V)
    (f R : MvPolynomial (Fin n) ℚ)
    (hR_const : MvPolynomial.coeff 0 R = 1)
    (hR_good : GoodToDepthR R m V S.length) :
    MvPolynomial.coeff m (iterDerivList S (f * R)) =
    MvPolynomial.coeff m (iterDerivList S f) := by
  have := coeff_iterDeriv_mul_goodR m S V hSV S.length (le_refl _) f R hR_good
  rw [this, hR_const, mul_one]

/-! ## Step 8: GoodAllDepthsR and closure under multiplication -/

/-- A polynomial satisfies GoodToDepthR at all depths, restricted to V. -/
def GoodAllDepthsR {n : ℕ} (R : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ)
    (V : Finset (Fin n)) : Prop :=
  (∀ d : ℕ, GoodToDepthR R m V d) ∧
  (∀ s ∈ V, MvPolynomial.coeff 0 (MvPolynomial.pderiv s R) = 0)

/-- GoodAllDepthsR is preserved by pderiv for s ∈ V. -/
theorem goodAllDepthsR_pderiv {n : ℕ} (R : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ)
    (V : Finset (Fin n)) (s : Fin n) (hs : s ∈ V)
    (h : GoodAllDepthsR R m V) : GoodAllDepthsR (MvPolynomial.pderiv s R) m V := by
  constructor
  · intro d
    exact goodToDepthR_pderiv R m V d s hs (h.1 (d + 1))
  · intro s' hs'
    exact ((h.1 2).2 s hs).2.2 s' hs' |>.1

/-- GoodToDepthR is closed under addition. -/
theorem goodToDepthR_add {n : ℕ} (R₁ R₂ : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ)
    (V : Finset (Fin n)) (d : ℕ)
    (h₁ : GoodToDepthR R₁ m V d) (h₂ : GoodToDepthR R₂ m V d) :
    GoodToDepthR (R₁ + R₂) m V d := by
  induction d generalizing R₁ R₂ with
  | zero =>
    intro b hb hle
    rw [MvPolynomial.coeff_add, h₁ b hb hle, h₂ b hb hle, add_zero]
  | succ d ih =>
    constructor
    · intro b hb hle
      rw [MvPolynomial.coeff_add, h₁.1 b hb hle, h₂.1 b hb hle, add_zero]
    · intro s hs
      constructor
      · rw [map_add (MvPolynomial.pderiv s), MvPolynomial.coeff_add,
          (h₁.2 s hs).1, (h₂.2 s hs).1, add_zero]
      · rw [map_add (MvPolynomial.pderiv s)]
        exact ih _ _ (h₁.2 s hs).2 (h₂.2 s hs).2

/-- Core lemma: products of GoodAllDepthsR polynomials have GoodToDepthR at any depth. -/
private theorem goodToDepthR_mul_aux {n : ℕ} (d : ℕ) :
    ∀ (R₁ R₂ : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ) (V : Finset (Fin n)),
    GoodAllDepthsR R₁ m V → GoodAllDepthsR R₂ m V →
    GoodToDepthR (R₁ * R₂) m V d := by
  induction d with
  | zero =>
    intro R₁ R₂ m V h₁ h₂
    exact noSubmono_mul R₁ R₂ m (h₁.1 0) (h₂.1 0)
  | succ d ih =>
    intro R₁ R₂ m V h₁ h₂
    constructor
    · exact noSubmono_mul R₁ R₂ m (h₁.1 0) (h₂.1 0)
    · intro s hs
      constructor
      · rw [MvPolynomial.pderiv_mul, MvPolynomial.coeff_add,
          coeff_zero_mul, coeff_zero_mul, h₁.2 s hs, h₂.2 s hs, zero_mul, mul_zero, add_zero]
      · rw [MvPolynomial.pderiv_mul]
        apply goodToDepthR_add
        · exact ih _ _ m V (goodAllDepthsR_pderiv R₁ m V s hs h₁) h₂
        · exact ih _ _ m V h₁ (goodAllDepthsR_pderiv R₂ m V s hs h₂)

/-- GoodAllDepthsR is closed under polynomial multiplication. -/
theorem goodAllDepthsR_mul {n : ℕ}
    (R₁ R₂ : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ) (V : Finset (Fin n))
    (h₁ : GoodAllDepthsR R₁ m V) (h₂ : GoodAllDepthsR R₂ m V) :
    GoodAllDepthsR (R₁ * R₂) m V := by
  constructor
  · intro d
    exact goodToDepthR_mul_aux d R₁ R₂ m V h₁ h₂
  · intro s hs
    rw [MvPolynomial.pderiv_mul, MvPolynomial.coeff_add,
      coeff_zero_mul, coeff_zero_mul, h₁.2 s hs, h₂.2 s hs, zero_mul, mul_zero, add_zero]

/-- GoodAllDepthsR for a list product. -/
theorem goodAllDepthsR_list_prod {n : ℕ}
    (L : List (MvPolynomial (Fin n) ℚ)) (m : Fin n →₀ ℕ) (V : Finset (Fin n))
    (hL : ∀ p ∈ L, GoodAllDepthsR p m V) :
    GoodAllDepthsR L.prod m V := by
  induction L with
  | nil =>
    simp only [List.prod_nil]
    constructor
    · intro d
      induction d with
      | zero => exact noSubmono_one m
      | succ d ih =>
        constructor
        · exact noSubmono_one m
        · intro s _
          simp only [MvPolynomial.pderiv_one]
          exact ⟨by simp [MvPolynomial.coeff_zero], (goodAllDepthsR_zero m V).1 d⟩
    · intro s _
      simp [MvPolynomial.pderiv_one, MvPolynomial.coeff_zero]
  | cons p rest ih =>
    simp only [List.prod_cons]
    exact goodAllDepthsR_mul p rest.prod m V
      (hL p (by simp))
      (ih (fun q hq => hL q (by simp [hq])))
where
  goodAllDepthsR_zero (m : Fin n →₀ ℕ) (V : Finset (Fin n)) :
      GoodAllDepthsR (0 : MvPolynomial (Fin n) ℚ) m V := by
    constructor
    · intro d
      induction d with
      | zero => intro b _ _; simp [MvPolynomial.coeff_zero]
      | succ d ih =>
        constructor
        · intro b _ _; simp [MvPolynomial.coeff_zero]
        · intro s _; simp only [map_zero]
          exact ⟨by simp [MvPolynomial.coeff_zero], ih⟩
    · intro s _; simp [map_zero, MvPolynomial.coeff_zero]
  goodAllDepthsR_C (c : ℚ) (m : Fin n →₀ ℕ) (V : Finset (Fin n)) :
      GoodAllDepthsR (MvPolynomial.C c : MvPolynomial (Fin n) ℚ) m V := by
    constructor
    · intro d
      induction d with
      | zero => intro b hb _; rw [MvPolynomial.coeff_C, if_neg (Ne.symm hb)]
      | succ d ih =>
        constructor
        · intro b hb _; rw [MvPolynomial.coeff_C, if_neg (Ne.symm hb)]
        · intro s _
          rw [MvPolynomial.pderiv_C]
          exact ⟨by simp [MvPolynomial.coeff_zero], (goodAllDepthsR_zero m V).1 d⟩
    · intro s _; rw [MvPolynomial.pderiv_C]; simp [MvPolynomial.coeff_zero]

/-- GoodAllDepthsR for the zero polynomial. -/
theorem goodAllDepthsR_zero {n : ℕ} (m : Fin n →₀ ℕ) (V : Finset (Fin n)) :
    GoodAllDepthsR (0 : MvPolynomial (Fin n) ℚ) m V := by
  constructor
  · intro d
    induction d with
    | zero => intro b _ _; simp [MvPolynomial.coeff_zero]
    | succ d ih =>
      constructor
      · intro b _ _; simp [MvPolynomial.coeff_zero]
      · intro s _; simp only [map_zero]
        exact ⟨by simp [MvPolynomial.coeff_zero], ih⟩
  · intro s _; simp [map_zero, MvPolynomial.coeff_zero]

/-! ## Step 9: GoodAllDepthsR for individual rest factors

Each rest factor has the form 1 - c * X_i * X_{i+1}. For the first-of-block
variable set V = {v | 3 ∣ v.val} and tag T ⊆ V:
- NoSubmonomials holds (already proved)
- For s ∈ V: pderiv s gives either 0 or -c * X_w where w ∉ V (the "partner"
  variable w is i+1 or i, never a multiple of 3)
- Second restricted derivative is always 0 (since w ∉ V) -/

/-- GoodAllDepthsR for C(c') * X_w when w ∉ T and w ∉ V. -/
private theorem goodAllDepthsR_C_mul_X_not_in_V {n : ℕ} (c' : ℚ) (w : Fin n)
    (T : Finset (Fin n)) (V : Finset (Fin n)) (hw_T : w ∉ T) (hw_V : w ∉ V) :
    GoodAllDepthsR (MvPolynomial.C c' * MvPolynomial.X w : MvPolynomial (Fin n) ℚ)
      (tagMonomial T) V := by
  have hnosubmono : NoSubmonomials (MvPolynomial.C c' * MvPolynomial.X w : MvPolynomial (Fin n) ℚ)
      (tagMonomial T) := by
    intro b hb hle
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X']
    split_ifs with heq
    · subst heq
      have := hle w
      rw [Finsupp.single_apply, if_pos rfl, tagMonomial_apply, if_neg hw_T] at this
      omega
    · ring
  have hderiv_zero : ∀ s ∈ V,
      MvPolynomial.pderiv s (MvPolynomial.C c' * MvPolynomial.X w : MvPolynomial (Fin n) ℚ) = 0 := by
    intro s hs
    have hsw : s ≠ w := fun h => hw_V (h ▸ hs)
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, zero_mul, zero_add]
    simp only [MvPolynomial.pderiv_X, Pi.single_apply, if_neg (Ne.symm hsw), mul_zero]
  constructor
  · intro d
    induction d with
    | zero => exact hnosubmono
    | succ d _ =>
      constructor
      · exact hnosubmono
      · intro s hs
        rw [hderiv_zero s hs]
        exact ⟨by simp [MvPolynomial.coeff_zero], (goodAllDepthsR_zero (tagMonomial T) V).1 d⟩
  · intro s hs
    rw [hderiv_zero s hs, MvPolynomial.coeff_zero]

/-- The adjacency/transition factor 1 - c * X_i * X_{i+1} has GoodAllDepthsR
    w.r.t. any first-of-block tag T and variable set V, where V consists of
    multiples of 3 and T ⊆ V. -/
-- Helper: pderiv s of C c * (X i * X j) using Leibniz
private theorem pderiv_C_mul_XX {n : ℕ} (c : ℚ) (i j s : Fin n) :
    MvPolynomial.pderiv s (MvPolynomial.C c * (MvPolynomial.X i * MvPolynomial.X j) :
      MvPolynomial (Fin n) ℚ) =
    MvPolynomial.C c * ((if s = i then (1 : MvPolynomial (Fin n) ℚ) else 0) * MvPolynomial.X j +
      MvPolynomial.X i * (if s = j then 1 else 0)) := by
  rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, zero_mul, zero_add,
    MvPolynomial.pderiv_mul]
  simp only [MvPolynomial.pderiv_X, Pi.single_apply, @eq_comm _ s]

theorem goodAllDepthsR_cadj_factor {n : ℕ} (c : ℚ) (i : Fin n) (hi : i.val + 1 < n)
    (T : Finset (Fin n)) (V : Finset (Fin n))
    (hT : ∀ v ∈ T, 3 ∣ v.val)
    (hV : ∀ v ∈ V, 3 ∣ v.val) :
    GoodAllDepthsR
      ((1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.C c * (MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩))
      (tagMonomial T) V := by
  set j : Fin n := ⟨i.val + 1, hi⟩ with hj_def
  have hij : i ≠ j := by intro h; simp [hj_def, Fin.ext_iff] at h
  have hji : j ≠ i := Ne.symm hij
  -- For any s ∈ V (3 | s.val), the derivative is:
  --   s = i (3|i): -(c * X_j), and 3∤(i+1) so j∉V,j∉T
  --   s = j (3|(i+1)): -(c * X_i), and i≡2 mod 3 so i∉V,i∉T
  --   s ∉ {i,j}: 0
  -- In all cases, the derivative has GoodAllDepthsR
  -- (because the partner variable is not in V, so second restricted derivative = 0)
  -- The factor is 1 - Q where Q = C c * (X i * X j)
  -- pderiv s (1 - Q) = pderiv s 1 - pderiv s Q = -pderiv s Q
  -- We compute pderiv s Q and then handle the subtraction.
  -- Rewrite factor as 1 + C(-c) * (X i * X j) for derivative computation
  have hfactor_eq : (1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.C c *
      (MvPolynomial.X i * MvPolynomial.X j) =
      1 + MvPolynomial.C (-c) * (MvPolynomial.X i * MvPolynomial.X j) := by
    simp [neg_mul, sub_eq_add_neg]
  -- For s = i: pderiv gives C(-c) * X j
  have hderiv_i : MvPolynomial.pderiv i ((1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.C c *
      (MvPolynomial.X i * MvPolynomial.X j)) = MvPolynomial.C (-c) * MvPolynomial.X j := by
    rw [hfactor_eq, map_add (MvPolynomial.pderiv i), MvPolynomial.pderiv_one, zero_add,
      pderiv_C_mul_XX]
    rw [if_pos rfl, if_neg hij, one_mul, mul_zero, add_zero]
  -- For s = j: pderiv gives C(-c) * X i
  have hderiv_j : MvPolynomial.pderiv j ((1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.C c *
      (MvPolynomial.X i * MvPolynomial.X j)) = MvPolynomial.C (-c) * MvPolynomial.X i := by
    rw [hfactor_eq, map_add (MvPolynomial.pderiv j), MvPolynomial.pderiv_one, zero_add,
      pderiv_C_mul_XX]
    rw [if_neg hji, if_pos rfl, zero_mul, mul_one, zero_add]
  -- For s ∉ {i,j}: pderiv is 0
  have hderiv_other : ∀ s : Fin n, s ≠ i → s ≠ j →
      MvPolynomial.pderiv s ((1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.C c *
        (MvPolynomial.X i * MvPolynomial.X j)) = 0 := by
    intro s hsi hsj
    rw [hfactor_eq, map_add (MvPolynomial.pderiv s), MvPolynomial.pderiv_one, zero_add]
    rw [pderiv_C_mul_XX]; simp [if_neg hsi, if_neg hsj]
  -- Key non-membership facts
  have hj_not_V_of_i_in_V : i ∈ V → j ∉ V := by
    intro hi_in hj_in
    have h3i := hV i hi_in; have h3j := hV j hj_in
    simp [hj_def] at h3j; omega
  have hi_not_V_of_j_in_V : j ∈ V → i ∉ V := by
    intro hj_in hi_in
    have h3i := hV i hi_in; have h3j := hV j hj_in
    simp [hj_def] at h3j; omega
  have hj_not_T_of_i_in_V : i ∈ V → j ∉ T := by
    intro hi_in hj_in
    have h3i := hV i hi_in; have h3j := hT j hj_in
    simp [hj_def] at h3j; omega
  have hi_not_T_of_j_in_V : j ∈ V → i ∉ T := by
    intro hj_in hi_in
    have h3i := hT i hi_in; have h3j := hV j hj_in
    simp [hj_def] at h3j; omega
  -- Derivative has GoodAllDepthsR for any s ∈ V
  have hderiv_good : ∀ s ∈ V,
      GoodAllDepthsR (MvPolynomial.pderiv s ((1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.C c *
        (MvPolynomial.X i * MvPolynomial.X j))) (tagMonomial T) V := by
    intro s hs
    by_cases hsi : s = i
    · subst hsi
      rw [hderiv_i]
      exact goodAllDepthsR_C_mul_X_not_in_V (-c) j T V (hj_not_T_of_i_in_V hs) (hj_not_V_of_i_in_V hs)
    · by_cases hsj : s = j
      · subst hsj
        rw [hderiv_j]
        exact goodAllDepthsR_C_mul_X_not_in_V (-c) i T V (hi_not_T_of_j_in_V hs) (hi_not_V_of_j_in_V hs)
      · rw [hderiv_other s hsi hsj]
        exact goodAllDepthsR_zero (tagMonomial T) V
  -- Derivative has constant term 0 for s ∈ V
  have hderiv_const : ∀ s ∈ V,
      MvPolynomial.coeff 0 (MvPolynomial.pderiv s ((1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.C c *
        (MvPolynomial.X i * MvPolynomial.X j))) = 0 := by
    intro s hs
    by_cases hsi : s = i
    · subst hsi; rw [hderiv_i, coeff_zero_mul,
        MvPolynomial.coeff_X', if_neg (Finsupp.single_ne_zero.mpr (by omega : (1 : ℕ) ≠ 0)),
        mul_zero]
    · by_cases hsj : s = j
      · subst hsj; rw [hderiv_j, coeff_zero_mul,
          MvPolynomial.coeff_X', if_neg (Finsupp.single_ne_zero.mpr (by omega : (1 : ℕ) ≠ 0)),
          mul_zero]
      · rw [hderiv_other s hsi hsj, MvPolynomial.coeff_zero]
  -- Build GoodAllDepthsR
  constructor
  · intro d
    induction d with
    | zero => exact noSubmono_cadj_factor c i hi T hT
    | succ d _ =>
      constructor
      · exact noSubmono_cadj_factor c i hi T hT
      · intro s hs
        exact ⟨hderiv_const s hs, (hderiv_good s hs).1 d⟩
  · exact hderiv_const

/-- The adjacency factor 1 - X_i * X_{i+1} (c = 1) has GoodAllDepthsR. -/
theorem goodAllDepthsR_adj_factor {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (T : Finset (Fin n)) (V : Finset (Fin n))
    (hT : ∀ v ∈ T, 3 ∣ v.val)
    (hV : ∀ v ∈ V, 3 ∣ v.val) :
    GoodAllDepthsR
      ((1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩)
      (tagMonomial T) V := by
  have h1c : (1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩ =
      (1 : MvPolynomial (Fin n) ℚ) - MvPolynomial.C 1 * (MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩) := by
    simp
  rw [h1c]
  exact goodAllDepthsR_cadj_factor 1 i hi T V hT hV

/-! ## Step 10: restFactorProd' has GoodAllDepthsR, and the coefficient identity

Chain through the list product to show restFactorProd' satisfies GoodAllDepthsR,
then apply coeff_iterDeriv_mul_inertR to get:
  coeff(tagMonomial S, iterDerivList T (boolFactorFullProd * restFactorProd'))
  = coeff(tagMonomial S, iterDerivList T boolFactorFullProd) -/

/-- Each rest factor (1 - lc.poly) for an adjacency or transition constraint
    has GoodAllDepthsR for first-of-block V and T. -/
theorem goodAllDepthsR_rest_factor {n : ℕ}
    (M : TuringMachine.DTM)
    (T : Finset (Fin n)) (V : Finset (Fin n))
    (hT : ∀ v ∈ T, 3 ∣ v.val) (hV : ∀ v ∈ V, 3 ∣ v.val)
    (lc : PaperFaithfulSeparation.LocalConstraint n)
    (hlc : lc ∈ adjConstraintList n ++ transSkelConstraintList M n) :
    GoodAllDepthsR
      ((1 : MvPolynomial (Fin n) ℚ) - lc.poly) (tagMonomial T) V := by
  obtain ⟨c, i, hi, hpoly⟩ := rest_constraint_cadj_form M n lc hlc
  rw [hpoly]
  exact goodAllDepthsR_cadj_factor c i hi T V hT hV

/-- restFactorProd' has GoodAllDepthsR for first-of-block V and T. -/
theorem goodAllDepthsR_restFactorProd' {n : ℕ}
    (M : TuringMachine.DTM)
    (T : Finset (Fin n)) (V : Finset (Fin n))
    (hT : ∀ v ∈ T, 3 ∣ v.val) (hV : ∀ v ∈ V, 3 ∣ v.val) :
    GoodAllDepthsR (restFactorProd' M n) (tagMonomial T) V := by
  unfold restFactorProd'
  apply goodAllDepthsR_list_prod
  intro p hp
  rw [List.mem_map] at hp
  obtain ⟨lc, hlc, rfl⟩ := hp
  exact goodAllDepthsR_rest_factor M T V hT hV lc hlc

/-- The coefficient identity: for first-of-block tag T and derivative list S
    with elements in V (all multiples of 3),
    coeff(tagMonomial T', iterDerivList S compiledPoly)
    = coeff(tagMonomial T', iterDerivList S boolFactorFullProd)
    where compiledPoly = boolFactorFullProd * restFactorProd'. -/
theorem coeff_iterDeriv_compiledPoly_eq_boolFactor {n : ℕ}
    (M : TuringMachine.DTM) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n)) (T' : Finset (Fin n))
    (V : Finset (Fin n))
    (hSV : ∀ s ∈ S, s ∈ V)
    (hT' : ∀ v ∈ T', 3 ∣ v.val)
    (hV : ∀ v ∈ V, 3 ∣ v.val) :
    MvPolynomial.coeff (tagMonomial T')
      (iterDerivList S (compiledPoly (cook_levin_compilation M n hn htb hns))) =
    MvPolynomial.coeff (tagMonomial T')
      (iterDerivList S (boolFactorFullProd n)) := by
  rw [CompiledBoolFactorBridge.compiledPoly_eq_boolFactorFullProd_mul_rest M n hn htb hns]
  apply coeff_iterDeriv_mul_inertR
  · exact hSV
  · exact restFactorProd'_const_one M n
  · exact (goodAllDepthsR_restFactorProd' M T' V hT' hV).1 S.length

/-! ## Step 11: Linear independence of compiled generators for first-of-block subsets -/

/-- Coefficient of tagMonomial S in mlProj(iterDerivList T.toList compiledPoly) equals
    2^|S∩T| when S and T are first-of-block subsets of the same size. -/
theorem coeff_mlProj_compiled_samesize
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S T : Finset (Fin n))
    (hcardST : S.card = T.card)
    (hS_fob : ∀ v ∈ S, 3 ∣ v.val)
    (hT_fob : ∀ v ∈ T, 3 ∣ v.val) :
    MvPolynomial.coeff (tagMonomial S)
      (mlProj (iterDerivList T.toList
        (compiledPoly (cook_levin_compilation M n hn htb hns)))) =
    (2 : ℚ) ^ (S ∩ T).card := by
  -- Step 1: mlProj preserves coefficients at multilinear monomials
  rw [coeff_mlProj_of_isMultilinear_mono _ _ (tagMonomial_isMultilinear S)]
  -- Step 2: coefficient identity (compiled = boolFactor)
  -- V = the set of all multiples of 3 in Fin n; T.toList elements are all in V
  set V := Finset.univ.filter (fun v : Fin n => 3 ∣ v.val) with hV_def
  have hV : ∀ v ∈ V, 3 ∣ v.val := by
    intro v hv; simp [hV_def] at hv; exact hv
  have hTV : ∀ s ∈ T.toList, s ∈ V := by
    intro s hs
    rw [Finset.mem_toList] at hs
    simp [hV_def, hT_fob s hs]
  rw [coeff_iterDeriv_compiledPoly_eq_boolFactor M hn htb hns T.toList S V hTV hS_fob hV]
  -- Step 3: iterDerivList T.toList boolFactorFullProd = boolFactorDerivProd T
  rw [← boolFactorDerivProd_eq_iterDerivList T]
  exact coeff_tagMonomial_boolFactorDerivProd_samesize S T hcardST

/-- Linear independence of mlProj(iterDerivList S.toList compiledPoly) for
    distinct first-of-block κ-subsets. -/
theorem linearIndependent_mlProj_compiled_fob
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (κ : ℕ) (hκ : κ ≥ 1)
    {F : Finset (Finset (Fin n))}
    (hcard : ∀ S ∈ F, S.card = κ)
    (hfob : ∀ S ∈ F, ∀ v ∈ S, 3 ∣ v.val) :
    LinearIndependent ℚ (fun S : F =>
      mlProj (iterDerivList (S : Finset (Fin n)).toList
        (compiledPoly (cook_levin_compilation M n hn htb hns)))) := by
  -- The coefficient matrix equals the boolFactor coefficient matrix 2^|S∩T|
  -- Use the same Gram/sum-of-squares argument as for boolFactorDerivProd
  -- Strategy: show the compiled vectors equal the boolFactor vectors via coefficient identity,
  -- then transfer linear independence.
  -- Actually, we can use the coefficient identity to directly show LI.
  rw [linearIndependent_iff']
  intro s w hw i hi
  -- Reuse the exact same argument as linearIndependent_mlProj_boolFactorDerivProd_general
  -- by showing the same Gram matrix structure
  set c : Finset (Fin n) → ℚ := fun S =>
    if h : S ∈ F then
      if ⟨S, h⟩ ∈ s then w ⟨S, h⟩ else 0
    else 0 with hc_def
  have hzero_F : ∑ S ∈ F, c S • mlProj (iterDerivList S.toList
      (compiledPoly (cook_levin_compilation M n hn htb hns))) = 0 := by
    have : ∑ S ∈ F, c S • mlProj (iterDerivList S.toList
        (compiledPoly (cook_levin_compilation M n hn htb hns))) =
        ∑ S ∈ s, w S • mlProj (iterDerivList (S : Finset (Fin n)).toList
          (compiledPoly (cook_levin_compilation M n hn htb hns))) := by
      conv_lhs => rw [← Finset.sum_attach F (fun S => c S • mlProj (iterDerivList S.toList
          (compiledPoly (cook_levin_compilation M n hn htb hns))))]
      rw [← Finset.sum_filter_add_sum_filter_not F.attach (fun S => S ∈ s)]
      have hzero_part : ∑ S ∈ F.attach.filter (fun S => S ∉ s),
          c (S : Finset (Fin n)) • mlProj (iterDerivList (S : Finset (Fin n)).toList
            (compiledPoly (cook_levin_compilation M n hn htb hns))) = 0 := by
        apply Finset.sum_eq_zero; intro ⟨S, hSF⟩ hmem
        simp only [Finset.mem_filter, Finset.mem_attach, true_and] at hmem
        rw [show c S = 0 from by simp [hc_def, dif_pos hSF, if_neg hmem], zero_smul]
      rw [hzero_part, add_zero]
      apply Finset.sum_nbij (fun S => S)
      · intro ⟨S, hSF⟩ hmem; simp only [Finset.mem_filter, Finset.mem_attach, true_and] at hmem; exact hmem
      · intro ⟨S₁, _⟩ _ ⟨S₂, _⟩ _ heq; exact heq
      · intro ⟨S, hSF⟩ hmem; exact ⟨⟨S, hSF⟩, by simp [hmem], rfl⟩
      · intro ⟨S, hSF⟩ hmem; simp only [Finset.mem_filter, Finset.mem_attach, true_and] at hmem
        simp only [hc_def, dif_pos hSF, if_pos hmem]
    rw [this, hw]
  -- Extract coefficients: for each T ∈ F, sum_S c_S * 2^|T∩S| = 0
  have hextract : ∀ T ∈ F, ∑ S ∈ F, c S * (2 : ℚ) ^ (T ∩ S).card = 0 := by
    intro T hTF
    have hcoeff_T : MvPolynomial.coeff (tagMonomial T)
        (∑ S ∈ F, c S • mlProj (iterDerivList S.toList
          (compiledPoly (cook_levin_compilation M n hn htb hns)))) = 0 := by
      rw [hzero_F]; simp [MvPolynomial.coeff_zero]
    simp only [coeff_sum, coeff_smul, smul_eq_mul] at hcoeff_T
    convert hcoeff_T using 1
    apply Finset.sum_congr rfl
    intro S hS
    rw [coeff_mlProj_compiled_samesize M n hn htb hns T S
      (by rw [hcard T hTF, hcard S hS]) (hfob T hTF) (hfob S hS)]
  -- From here, the argument is identical to linearIndependent_mlProj_boolFactorDerivProd_general
  -- (SoS Gram matrix argument)
  set g : Finset (Fin n) → ℚ := fun U => ∑ S ∈ F, c S * BlockedBoolRank.zetaIndicator S U with hg_def
  set allSubsets := (Finset.univ : Finset (Fin n)).powerset with hall_def
  have hg_sq_eq : ∑ U ∈ allSubsets, g U ^ 2 =
      ∑ T ∈ F, ∑ S ∈ F, c T * c S * (2 : ℚ) ^ (T ∩ S).card := by
    simp only [hg_def, sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm (s := allSubsets) (t := F)]
    congr 1; funext T
    rw [Finset.sum_comm (s := allSubsets) (t := F)]
    congr 1; funext S
    rw [show ∑ U ∈ allSubsets,
        (c T * BlockedBoolRank.zetaIndicator T U) * (c S * BlockedBoolRank.zetaIndicator S U) =
        c T * c S * ∑ U ∈ allSubsets, BlockedBoolRank.zetaIndicator T U * BlockedBoolRank.zetaIndicator S U from by
      rw [Finset.mul_sum]; congr 1; funext U; ring]
    rw [BlockedBoolRank.zetaIndicator_inner_product]
  have hquad_zero : ∑ T ∈ F, ∑ S ∈ F, c T * c S * (2 : ℚ) ^ (T ∩ S).card = 0 := by
    apply Finset.sum_eq_zero; intro T hT
    rw [show ∑ S ∈ F, c T * c S * (2 : ℚ) ^ (T ∩ S).card =
        c T * ∑ S ∈ F, c S * (2 : ℚ) ^ (T ∩ S).card from by
      rw [Finset.mul_sum]; congr 1; ext S; ring]
    rw [hextract T hT, mul_zero]
  have hg_sq_zero : ∑ U ∈ allSubsets, g U ^ 2 = 0 := by rw [hg_sq_eq, hquad_zero]
  have hg_zero : ∀ U ∈ allSubsets, g U = 0 := BlockedBoolRank.sum_sq_eq_zero_imp hg_sq_zero
  have hg_eval : ∀ T ∈ F, g T = c T := by
    intro T hTF
    show ∑ S ∈ F, c S * BlockedBoolRank.zetaIndicator S T = c T
    rw [show ∑ S ∈ F, c S * BlockedBoolRank.zetaIndicator S T =
        c T * BlockedBoolRank.zetaIndicator T T + ∑ S ∈ F.erase T, c S * BlockedBoolRank.zetaIndicator S T from by
      rw [← Finset.add_sum_erase F _ hTF]]
    rw [show BlockedBoolRank.zetaIndicator T T = 1 from by simp [BlockedBoolRank.zetaIndicator], mul_one]
    suffices h : ∑ S ∈ F.erase T, c S * BlockedBoolRank.zetaIndicator S T = 0 by linarith
    apply Finset.sum_eq_zero; intro S hS
    have hSF := Finset.mem_of_mem_erase hS; have hne := Finset.ne_of_mem_erase hS
    rw [show BlockedBoolRank.zetaIndicator S T = 0 from by
      simp only [BlockedBoolRank.zetaIndicator]; rw [if_neg]; intro hsub
      exact hne (BlockedBoolRank.Finset.eq_of_subset_of_card_eq hsub (by rw [hcard T hTF, hcard S hSF])).symm]
    exact mul_zero _
  have hci : c (i : Finset (Fin n)) = 0 := by
    have hT_mem : (i : Finset (Fin n)) ∈ allSubsets := by
      simp [hall_def, Finset.mem_powerset, Finset.subset_univ]
    rw [← hg_eval _ i.2]; exact hg_zero _ hT_mem
  simp only [hc_def, dif_pos i.2, if_pos hi] at hci
  exact hci

end CrossTermVanishing
