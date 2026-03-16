/-
  MultilinearRestrict.lean — The restricted multilinear interpolation is multilinear.
  PROVED: support_ne_topMon_has_zero (was axiom, now theorem with 0 custom axioms)
-/
import PallLean.Restriction
import PallLean.Depth4Simulation
import PallLean.PneqNP_Defs
import PallLean.MobiusTopCoeff
import PallLean.RestrictIndicator
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.CommRing

open MvPolynomial Finset Restriction BoolEval Depth4Simulation PneqNP_Defs MobiusTopCoeff RestrictIndicator

namespace MultilinearRestrict

variable {n : ℕ}

def IsML (p : MvPolynomial (Fin n) ℚ) (V : Finset (Fin n)) : Prop :=
  ∀ s ∈ p.support, (∀ i ∈ V, s i ≤ 1) ∧ (∀ i, i ∉ V → s i = 0)

private lemma support_one_zero (s : Fin n →₀ ℕ)
    (hs : s ∈ (1 : MvPolynomial (Fin n) ℚ).support) : s = 0 := by
  rw [mem_support_iff] at hs; by_contra h
  exact hs (by rw [MvPolynomial.coeff_one, if_neg (Ne.symm h)])

private lemma mlFactor_support (i : Fin n) (b : Bool) (s : Fin n →₀ ℕ)
    (hs : s ∈ (mlFactor i b).support) : s = 0 ∨ s = Finsupp.single i 1 := by
  unfold mlFactor at hs; cases b <;> simp only [ite_true, ite_false, Bool.false_eq_true] at hs
  · have := MvPolynomial.support_sub (Fin n) (1 : MvPolynomial _ ℚ) (X i) hs
    simp only [mem_union] at this; rcases this with h | h
    · exact Or.inl (support_one_zero s h)
    · exact Or.inr (by rwa [MvPolynomial.support_X, mem_singleton] at h)
  · exact Or.inr (by rwa [MvPolynomial.support_X, mem_singleton] at hs)

private lemma isML_mlFactor (i : Fin n) (b : Bool) : IsML (mlFactor i b) {i} := by
  intro s hs; obtain rfl | rfl := mlFactor_support i b s hs
  · exact ⟨fun _ _ => Nat.zero_le _, fun _ _ => rfl⟩
  · exact ⟨fun j hj => by rw [mem_singleton] at hj; subst hj; simp [Finsupp.single_apply],
          fun j hj => by rw [mem_singleton] at hj; rw [Finsupp.single_apply, if_neg (Ne.symm hj)]⟩

private lemma isML_mul {p q : MvPolynomial (Fin n) ℚ} {V W : Finset (Fin n)}
    (hp : IsML p V) (hq : IsML q W) (hdisj : Disjoint V W) :
    IsML (p * q) (V ∪ W) := by
  intro s hs
  obtain ⟨sp, hsp, sq, hsq, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hs)
  obtain ⟨hpV, hpout⟩ := hp sp hsp
  obtain ⟨hqW, hqout⟩ := hq sq hsq
  constructor
  · intro i hi
    rw [Finsupp.add_apply]
    rcases mem_union.mp hi with h | h
    · linarith [hpV i h, hqout i (disjoint_left.mp hdisj h)]
    · linarith [hqW i h, hpout i (disjoint_right.mp hdisj h)]
  · intro i hi
    rw [Finsupp.add_apply,
      hpout i (fun h => hi (mem_union_left W h)),
      hqout i (fun h => hi (mem_union_right V h))]

private lemma isML_prod (V : Finset (Fin n)) (a : Fin n → Bool) :
    IsML (∏ i ∈ V, mlFactor i (a i)) V := by
  induction V using Finset.induction with
  | empty =>
    simp only [prod_empty]; intro s hs
    obtain rfl := support_one_zero s hs
    exact ⟨fun _ h => absurd h (by simp), fun _ _ => rfl⟩
  | @insert j V hj ih =>
    rw [prod_insert hj]
    have h := isML_mul (isML_mlFactor j (a j)) ih (disjoint_singleton_left.mpr hj)
    rwa [singleton_union] at h

private lemma isML_add {p q : MvPolynomial (Fin n) ℚ} {V : Finset (Fin n)}
    (hp : IsML p V) (hq : IsML q V) : IsML (p + q) V := by
  intro s hs; have := MvPolynomial.support_add hs
  rw [Finset.mem_union] at this; rcases this with h | h <;> [exact hp s h; exact hq s h]

private lemma isML_zero (V : Finset (Fin n)) : IsML (0 : MvPolynomial (Fin n) ℚ) V := by
  intro s hs; simp [MvPolynomial.support_zero] at hs

private lemma isML_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℚ)
    (V : Finset (Fin n)) (hf : ∀ i ∈ s, IsML (f i) V) : IsML (∑ i ∈ s, f i) V := by
  induction s using Finset.cons_induction with
  | empty => simp; exact isML_zero V
  | cons a s ha ih =>
    rw [sum_cons]; exact isML_add (hf a (mem_cons_self a s))
      (ih (fun i hi => hf i (mem_cons_of_mem hi)))

private lemma isML_restrictPoly_boolIndicator (ρ : Restriction n) (a : Fin n → Bool) :
    IsML (restrictPoly ρ (boolIndicator a)) (liveVars ρ) := by
  by_cases hc : ∀ i b, ρ i = some b → a i = b
  · rw [restrictPoly_boolIndicator_consistent' ρ a hc]; exact isML_prod _ a
  · push_neg at hc; obtain ⟨i, b, hρ, hab⟩ := hc
    rw [restrictPoly_boolIndicator_inconsistent' ρ a ⟨i, b, hρ, hab⟩]; exact isML_zero _

/-- The restricted multilinear interpolation is multilinear on liveVars. PROVED. -/
theorem restricted_isML (f : BoolFun n) (ρ : Restriction n) :
    IsML (restrictPoly ρ (multilinearInterp f)) (liveVars ρ) := by
  unfold multilinearInterp restrictPoly; rw [map_sum]
  apply isML_sum; intro a _
  change IsML (restrictPoly ρ (boolIndicator a)) (liveVars ρ)
  exact isML_restrictPoly_boolIndicator ρ a

/-- Key consequence: s ≠ topMon → ∃ live var with 0 exponent. PROVED. -/
theorem support_ne_topMon_has_zero (f : BoolFun n) (ρ : Restriction n)
    (s : Fin n →₀ ℕ) (hs : s ∈ (restrictPoly ρ (multilinearInterp f)).support)
    (hne : s ≠ ∑ j ∈ liveVars ρ, Finsupp.single j 1) :
    ∃ j ∈ liveVars ρ, s j = 0 := by
  obtain ⟨hexp, hvars⟩ := restricted_isML f ρ s hs
  by_contra h; push_neg at h; apply hne; ext i
  simp only [Finsupp.finset_sum_apply, Finsupp.single_apply]
  by_cases hi : i ∈ liveVars ρ
  · have h1 : s i ≥ 1 := Nat.pos_of_ne_zero (h i hi)
    have h2 : s i ≤ 1 := hexp i hi
    rw [← sum_filter, filter_eq']; simp [hi]; omega
  · rw [hvars i hi, ← sum_filter, filter_eq']; simp [hi]

end MultilinearRestrict
