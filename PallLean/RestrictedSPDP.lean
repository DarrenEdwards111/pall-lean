/-
  RestrictedSPDP.lean — SPDP rank after restriction (paper §6)

  The paper's SPDP rank is measured on the RESTRICTED polynomial C|ρ.
  We use `spdpRank` from SPDPDefs (wide: no block partition, no shift
  locality constraint), matching the paper's Definition 12.
-/
import PallLean.SPDPDefs
import PallLean.Restriction

namespace RestrictedSPDP

open MvPolynomial SPDP Restriction

/-- SPDP rank of a polynomial after restriction (paper §6, Definition 12).
    Derivative sets S and multiplier variables m are restricted to LIVE
    variables only, matching the paper: after restriction, the polynomial
    is treated as living in the space of live variables.

    Derivatives w.r.t. fixed variables are 0 (the restricted polynomial
    doesn't involve them), so restricting S to live vars doesn't change
    the generators. But restricting m to live vars IS essential — otherwise
    multipliers like x_fixed · (derivative) would inflate the rank beyond
    the paper's bounds. -/
noncomputable def restrictedSpdpRank {n : ℕ} {F : Type*} [CommRing F] [Nontrivial F]
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) (ρ : Restriction.Restriction n) : ℕ :=
  Module.finrank F (Submodule.span F
    { q | ∃ (S : List (Fin n)) (m : MvPolynomial (Fin n) F),
        S.length = κ ∧ m.totalDegree ≤ ℓ ∧
        (∀ i ∈ S, i ∈ Restriction.liveVars ρ) ∧
        (∀ v ∈ m.vars, v ∈ Restriction.liveVars ρ) ∧
        q = m * iterDerivList S (Restriction.restrictPoly ρ p) })

/-- SPDP rank without restriction = SPDP rank with identity restriction.
    With identity restriction, all variables are live, so the live-var
    constraints on S and m are trivially satisfied. -/
theorem restrictedSpdpRank_id {n : ℕ} {F : Type*} [CommRing F] [Nontrivial F]
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    restrictedSpdpRank κ ℓ p (Restriction.idRestriction n) = spdpRank κ ℓ p := by
  simp only [restrictedSpdpRank, spdpRank, spdpSubspace]
  have h_eq : { q | ∃ (S : List (Fin n)) (m : MvPolynomial (Fin n) F),
        S.length = κ ∧ m.totalDegree ≤ ℓ ∧
        (∀ i ∈ S, i ∈ Restriction.liveVars (Restriction.idRestriction n)) ∧
        (∀ v ∈ m.vars, v ∈ Restriction.liveVars (Restriction.idRestriction n)) ∧
        q = m * iterDerivList S (Restriction.restrictPoly (Restriction.idRestriction n) p) } =
    { q | ∃ (S : List (Fin n)) (m : MvPolynomial (Fin n) F),
        S.length = κ ∧ m.totalDegree ≤ ℓ ∧
        q = m * iterDerivList S p } := by
    ext q; simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨S, m, hlen, hdeg, _, _, hq⟩
      exact ⟨S, m, hlen, hdeg, by rwa [Restriction.restrictPoly_id] at hq⟩
    · rintro ⟨S, m, hlen, hdeg, hq⟩
      exact ⟨S, m, hlen, hdeg,
        fun i _ => by simp [Restriction.liveVars, Restriction.idRestriction],
        fun v _ => by simp [Restriction.liveVars, Restriction.idRestriction],
        by rwa [Restriction.restrictPoly_id]⟩
  rw [h_eq]

/-- The collapse threshold from the paper.
    d*_n = (k+1) · w where w = numLive(ρ) and k = ⌈log n⌉. -/
def collapseThreshold (n : ℕ) (numLive : ℕ) : ℕ :=
  (Nat.log 2 n + 1) * numLive

end RestrictedSPDP
