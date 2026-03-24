/-
  SupportedDimLight.lean — Diamond-safe proof components for finrank bound.
  MINIMAL imports: no StrongRankCondition, no RingTheory.MvPolynomial.Basic.
-/
import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.Tactic

namespace SupportedDimLight

def boundedSupp {σ : Type*} [DecidableEq σ] (s : Finset σ) (d : ℕ) : Set (σ →₀ ℕ) :=
  {n : σ →₀ ℕ | n.sum (fun _ a => a) ≤ d ∧ ↑n.support ⊆ ↑s}

noncomputable def restrictSupportDeg (R : Type*) [CommSemiring R] {σ : Type*} [DecidableEq σ]
    (s : Finset σ) (d : ℕ) : Submodule R (MvPolynomial σ R) :=
  MvPolynomial.restrictSupport R (boundedSupp s d)

private theorem val_le_sum {σ : Type*} [DecidableEq σ] (n : σ →₀ ℕ) (x : σ) :
    n x ≤ n.sum (fun _ a => a) := by
  by_cases hx : n x = 0
  · omega
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finsupp.mem_support_iff.mpr (by omega))

-- Fintype instance for boundedSupp via injection into (↥s → Fin(d+1))
noncomputable instance instFintype {σ : Type*} [DecidableEq σ] [Fintype σ]
    (s : Finset σ) (d : ℕ) : Fintype (boundedSupp s d) := by
  let encode : boundedSupp s d → (↥s → Fin (d + 1)) :=
    fun ⟨n, hsum, hsupp⟩ i => ⟨n ↑i, Nat.lt_succ_of_le (le_trans (val_le_sum n ↑i) hsum)⟩
  have h_inj : Function.Injective encode := by
    intro ⟨a, ha_sum, ha_supp⟩ ⟨b, hb_sum, hb_supp⟩ h
    simp only [encode, Subtype.mk.injEq] at h ⊢
    ext x
    by_cases hx : x ∈ s
    · have := congr_fun h ⟨x, hx⟩; exact Fin.ext_iff.mp this
    · have ha0 : a x = 0 := by
        by_contra hne
        have := ha_supp (Finsupp.mem_support_iff.mpr (by omega))
        simp only [Finset.mem_coe] at this; exact hx this
      have hb0 : b x = 0 := by
        by_contra hne
        have := hb_supp (Finsupp.mem_support_iff.mpr (by omega))
        simp only [Finset.mem_coe] at this; exact hx this
      simp [ha0, hb0]
  exact Fintype.ofInjective encode h_inj

-- Card bound
theorem card_le {σ : Type*} [DecidableEq σ] [Fintype σ] (s : Finset σ) (d : ℕ) :
    Fintype.card (boundedSupp s d) ≤ (s.card + d) ^ s.card := by
  let encode : boundedSupp s d → (↥s → Fin (d + 1)) :=
    fun ⟨n, hsum, hsupp⟩ i => ⟨n ↑i, Nat.lt_succ_of_le (le_trans (val_le_sum n ↑i) hsum)⟩
  have h_inj : Function.Injective encode := by
    intro ⟨a, ha_sum, ha_supp⟩ ⟨b, hb_sum, hb_supp⟩ h
    simp only [encode, Subtype.mk.injEq] at h ⊢
    ext x
    by_cases hx : x ∈ s
    · have := congr_fun h ⟨x, hx⟩; exact Fin.ext_iff.mp this
    · have ha0 : a x = 0 := by
        by_contra hne; have := ha_supp (Finsupp.mem_support_iff.mpr (by omega))
        simp only [Finset.mem_coe] at this; exact hx this
      have hb0 : b x = 0 := by
        by_contra hne; have := hb_supp (Finsupp.mem_support_iff.mpr (by omega))
        simp only [Finset.mem_coe] at this; exact hx this
      simp [ha0, hb0]
  calc Fintype.card (boundedSupp s d)
      ≤ Fintype.card (↥s → Fin (d + 1)) := Fintype.card_le_of_injective encode h_inj
    _ = (d + 1) ^ s.card := by simp [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    _ ≤ (s.card + d) ^ s.card := by
        cases s.card with | zero => simp | succ k => exact Nat.pow_le_pow_left (by omega) _

-- The spanning Finset (pre-computed, so bridge file doesn't elaborate it)
noncomputable def spanFinset {σ : Type*} [DecidableEq σ] [Fintype σ]
    (s : Finset σ) (d : ℕ) : Finset (MvPolynomial σ ℚ) :=
  ((Finset.univ : Finset (boundedSupp s d)).image Subtype.val).image
    (fun m => Finsupp.single m (1 : ℚ))

-- restrictSupportDeg ≤ span of spanFinset
theorem span_le {σ : Type*} [DecidableEq σ] [Fintype σ] (s : Finset σ) (d : ℕ) :
    restrictSupportDeg ℚ s d ≤ Submodule.span ℚ (↑(spanFinset s d) : Set (MvPolynomial σ ℚ)) := by
  unfold restrictSupportDeg MvPolynomial.restrictSupport
  rw [Finsupp.supported_eq_span_single]
  apply Submodule.span_mono
  intro x hx
  obtain ⟨m, hm, rfl⟩ := hx
  -- Need: Finsupp.single m 1 ∈ ↑(spanFinset s d)
  -- spanFinset = (univ.image val).image (single · 1)
  -- m ∈ boundedSupp → ⟨m,hm⟩ ∈ univ → m ∈ univ.image val → single m 1 ∈ spanFinset
  have h1 : m ∈ (Finset.univ : Finset (boundedSupp s d)).image Subtype.val :=
    Finset.mem_image.mpr ⟨⟨m, hm⟩, Finset.mem_univ _, rfl⟩
  have h2 : Finsupp.single m (1 : ℚ) ∈ spanFinset s d :=
    Finset.mem_image.mpr ⟨m, h1, rfl⟩
  exact Finset.mem_coe.mpr h2

-- spanFinset.card ≤ (s.card + d)^s.card
theorem spanFinset_card_le {σ : Type*} [DecidableEq σ] [Fintype σ] (s : Finset σ) (d : ℕ) :
    (spanFinset s d).card ≤ (s.card + d) ^ s.card := by
  unfold spanFinset
  calc (Finset.image _ (Finset.image _ Finset.univ)).card
      ≤ (Finset.image Subtype.val Finset.univ).card := Finset.card_image_le
    _ = Fintype.card (boundedSupp s d) := by
        rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ]
    _ ≤ (s.card + d) ^ s.card := card_le s d

end SupportedDimLight
