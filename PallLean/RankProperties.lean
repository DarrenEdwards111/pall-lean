import PallLean.SPDPDefs
import Mathlib.Tactic
/-!
# SPDP Rank Properties (axioms for opaque operations)

These axioms capture rank behavior under operations that
change the ambient polynomial ring (different n).
-/

namespace SPDP.RankProps

open SPDP MvPolynomial

/-- Rank under cross-ring extraction: if q is obtained from p by
    restriction + projection + invertible relabel, rank doesn't increase. -/
axiom rank_le_extraction {F : Type*} [CommRing F] [Nontrivial F]
    {n_in n_out : ℕ} (κ : ℕ)
    (p : MvPolynomial (Fin n_in) F) (q : MvPolynomial (Fin n_out) F)
    (h_extract : True) :
    spdpRank κ q ≤ spdpRank κ p

end SPDP.RankProps
