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

/-- SPDP rank of a polynomial after restriction.
    Uses the unblocked definition (paper's Definition 12): shifts x^α
    with |α| ≤ ℓ, NO locality constraint, NO block partition. -/
noncomputable def restrictedSpdpRank {n : ℕ} {F : Type*} [CommRing F] [Nontrivial F]
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) (ρ : Restriction.Restriction n) : ℕ :=
  spdpRank κ ℓ (Restriction.restrictPoly ρ p)

/-- SPDP rank without restriction = SPDP rank with identity restriction. -/
theorem restrictedSpdpRank_id {n : ℕ} {F : Type*} [CommRing F] [Nontrivial F]
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    restrictedSpdpRank κ ℓ p (Restriction.idRestriction n) = spdpRank κ ℓ p := by
  unfold restrictedSpdpRank
  congr 1
  exact Restriction.restrictPoly_id p

/-- The collapse threshold from the paper.
    d*_n = (k+1) · w where w = numLive(ρ) and k = ⌈log n⌉. -/
def collapseThreshold (n : ℕ) (numLive : ℕ) : ℕ :=
  (Nat.log 2 n + 1) * numLive

end RestrictedSPDP
