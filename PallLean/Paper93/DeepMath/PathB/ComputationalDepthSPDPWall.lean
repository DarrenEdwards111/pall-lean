import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSPDPProductUB
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBlockPermRankExp

/-!
# The SPDP wall made concrete: `C(k,κ)²` lower vs `s·(#J)·(#monomials)` upper

This file meets the two halves of the SPDP wall at an explicit numerical inequality, giving a genuine restricted lower
bound for the permanent.

  `permanent_depth4_bound` — if `Permₖ` (flattened by an injective `ψ`) equals a depth-`4` circuit `∑_{i<s} ∏_{j} Q_{ij}`
        with `s` products of `≤ mm` factors each of degree `≤ t`, then
        `C(k,κ)² ≤ s · (#{J⊆[mm] : |J|≤κ}) · (#monomials of degree ≤ κt)`.
        (Lower bound `spdpRank ≥ C(k,κ)²` from `ComputationalDepthBlockPermRankExp`, upper bound
        `spdpRank ≤ s·(#J)·(#monomials)` from `ComputationalDepthSPDPProductUB`.)
  `permanent_no_small_depth4` — the contrapositive: if that RHS is `< C(k,κ)²`, the permanent has **no** such circuit.

Choosing `κ = k/2` makes `C(k,κ)² ≈ 4ᵏ/k` exponential, while the RHS is polynomial in `s`, `#J ≤ 2^{mm}`, and
`#monomials ≤ binom(N+κt, N)` — so a *shallow* circuit (`mm`, `t`, `κ` small relative to `k`) provably cannot compute
the permanent.  This is the GKKS-style restricted separation, fully quantitative.

**Honest scope.** This is a *restricted* lower bound (depth-`4`, bounded bottom fan-in `t`), **not** `P ≠ NP` or
`NEXP ⊄ ACC⁰`.  The general wall — "every poly-size circuit ⟹ small SPDP rank" — is false / `P`-vs-`NP`-strength.
The inequality here is the honest, provable meeting point of the two halves.
-/

namespace PallLean.Paper93.DeepMath.PathB.SPDPWall

open MvPolynomial Finset SPDPLowerBound SPDPUpperBound

variable {k : ℕ} {F : Type*} [Field F]

/-- **The concrete SPDP separation inequality (proved)**: a depth-`4` circuit computing the permanent forces
`C(k,κ)² ≤ s · (#{J:|J|≤κ}) · (#degree-≤κt monomials)`. -/
theorem permanent_depth4_bound {N s mm t κ : ℕ} (ψ : Fin k × Fin k → Fin N)
    (hψ : Function.Injective ψ) (Q : Fin s → Fin mm → MvPolynomial (Fin N) F)
    (ht : ∀ i j, (Q i j).totalDegree ≤ t)
    (hcirc : rename ψ (permPoly k F) = ∑ i, ∏ j, Q i j) :
    (k.choose κ) ^ 2 ≤ s * ((Finset.univ.filter (fun J : Finset (Fin mm) => J.card ≤ κ)).card
        * Module.finrank F ↥(MvPolynomial.restrictTotalDegree (Fin N) F (κ * t))) := by
  calc (k.choose κ) ^ 2
      ≤ SPDP.spdpRank κ 0 (rename ψ (permPoly k F)) := spdpRank_renamePerm_choose_ge ψ hψ
    _ = SPDP.spdpRank κ 0 (∑ i, ∏ j, Q i j) := by rw [hcirc]
    _ ≤ ∑ i, SPDP.spdpRank κ 0 (∏ j, Q i j) := spdpRank_sum_le κ 0 Finset.univ _
    _ ≤ ∑ _i : Fin s, ((Finset.univ.filter (fun J : Finset (Fin mm) => J.card ≤ κ)).card
          * Module.finrank F ↥(MvPolynomial.restrictTotalDegree (Fin N) F (κ * t))) :=
        Finset.sum_le_sum (fun i _ => SPDPUpperBound.spdpRank_prod_le_card (Q i) (ht i) κ)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **No small depth-`4` circuit for the permanent (proved)**: if the depth-`4` size budget is below `C(k,κ)²`, the
permanent is not computed by such a circuit.  With `κ = k/2` the threshold `C(k,κ)²` is exponential. -/
theorem permanent_no_small_depth4 {N s mm t κ : ℕ} (ψ : Fin k × Fin k → Fin N)
    (hψ : Function.Injective ψ) (Q : Fin s → Fin mm → MvPolynomial (Fin N) F)
    (ht : ∀ i j, (Q i j).totalDegree ≤ t)
    (hsmall : s * ((Finset.univ.filter (fun J : Finset (Fin mm) => J.card ≤ κ)).card
        * Module.finrank F ↥(MvPolynomial.restrictTotalDegree (Fin N) F (κ * t))) < (k.choose κ) ^ 2) :
    rename ψ (permPoly k F) ≠ ∑ i, ∏ j, Q i j :=
  fun hcirc => absurd (permanent_depth4_bound ψ hψ Q ht hcirc) (not_le.mpr hsmall)

end PallLean.Paper93.DeepMath.PathB.SPDPWall

#print axioms PallLean.Paper93.DeepMath.PathB.SPDPWall.permanent_depth4_bound
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPWall.permanent_no_small_depth4
