/-
  Profile.lean — Interface-anonymous profiles (histograms of derivative types)

  A profile is a histogram h : Fin m → ℕ counting how many derivatives
  of each type appear in a block-admissible derivative sequence.

  Paper: Definitions 20-21, Lemma 29.
-/
import PallLean.SPDPDefs
import Mathlib.Tactic

namespace Profile

open SPDP MvPolynomial

/-! ## Profile type -/

/-- A profile (interface-anonymous histogram) with m derivative types.
    h τ = number of derivatives of type τ. -/
abbrev Profile (m : ℕ) := Fin m → ℕ

/-- Total mass of a profile: Σ_τ h(τ) -/
def totalMass {m : ℕ} (h : Profile m) : ℕ := Finset.univ.sum h

-- Profile count bound: the number of weak compositions of ≤ R into m bins
-- is ≤ C(R+m, m). This is used via the Finset of profiles passed to the cover theorem.
-- The bound follows from choose_le_pow (already proved in ProfileCompression.lean).

/-! ## Profile subspace -/

/-- Profile subspace V_h: the span of SPDP generators whose derivative
    sequence has profile h. This is parameterized by:
    - B: block partition
    - κ, ℓ: SPDP parameters
    - p: the polynomial
    - h: the profile
    - profileFn: function mapping derivative sequences to profiles -/
noncomputable def profileSubspace {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) F)
    (profileFn : List (Fin n) → Profile m)
    (h : Profile m) :
    Submodule F (MvPolynomial (Fin n) F) :=
  Submodule.span F
    { q | ∃ (S : List (Fin n)) (m_poly : MvPolynomial (Fin n) F),
        S.length = κ ∧ m_poly.totalDegree ≤ ℓ ∧
        isBlockAdmissible B S ∧
        profileFn S = h ∧
        q = m_poly * iterDerivList S p }

/-- Every SPDP generator belongs to some profile subspace -/
theorem generator_mem_profileSubspace {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) F)
    (profileFn : List (Fin n) → Profile m)
    (S : List (Fin n)) (m_poly : MvPolynomial (Fin n) F)
    (hlen : S.length = κ) (hdeg : m_poly.totalDegree ≤ ℓ)
    (hadm : isBlockAdmissible B S) :
    m_poly * iterDerivList S p ∈
      profileSubspace B κ ℓ p profileFn (profileFn S) := by
  apply Submodule.subset_span
  exact ⟨S, m_poly, hlen, hdeg, hadm, rfl, rfl⟩

/-- Cover theorem: blocked SPDP subspace ≤ ⨆ over profiles.
    Every generator has some profile, so the SPDP subspace is
    contained in the supremum of profile subspaces. -/
theorem spdp_le_iSup_profileSubspace {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) F)
    (profileFn : List (Fin n) → Profile m)
    (profiles : Finset (Profile m))
    (hcomplete : ∀ S : List (Fin n), S.length = κ →
      isBlockAdmissible B S → profileFn S ∈ profiles) :
    blockedSpdpSubspace B κ ℓ p ≤
    ⨆ (h : profiles), profileSubspace B κ ℓ p profileFn h.val := by
  apply Submodule.span_le.mpr
  intro q ⟨S, m_poly, hlen, hdeg, hadm, _, _, hq⟩
  rw [hq]
  have hmem := hcomplete S hlen hadm
  -- q ∈ profileSubspace for profile (profileFn S)
  have hgen := generator_mem_profileSubspace B κ ℓ p profileFn S m_poly hlen hdeg hadm
  -- profileSubspace ≤ iSup
  have hle : profileSubspace B κ ℓ p profileFn (profileFn S) ≤
      ⨆ (h : profiles), profileSubspace B κ ℓ p profileFn h.val :=
    le_iSup_of_le ⟨profileFn S, hmem⟩ (le_refl _)
  exact hle hgen

end Profile
