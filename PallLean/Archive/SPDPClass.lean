/-
  SPDPClass.lean — The SPDP-collapsible class C*_SPDP (paper §7)
-/
import PallLean.RestrictedSPDP
import PallLean.CircuitModel

namespace SPDPClass

open RestrictedSPDP Restriction CircuitModel

/-- A polynomial has low SPDP rank under restriction ρ. -/
def SPDPCollapsible {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) (ρ : Restriction.Restriction n)
    (threshold : ℕ) : Prop :=
  restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n) p ρ ≤ threshold

end SPDPClass
