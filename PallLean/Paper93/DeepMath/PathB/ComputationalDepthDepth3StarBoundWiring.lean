import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FalsifyDeepestRefutation
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingBridge

/-!
# Star-bound wiring (falsify-deepest): pinning `stars ρ = K` for the good restriction

`tseitin_circuit_validSearch_shallow` needs `stars ρ ≤ budget` to bound the residual refutation's
depth.  The switching count gives a good restriction in the **`K`-star family** `{ρ : stars ρ = K}`,
which pins `stars ρ = K` exactly — the star bound the depth needs.

* `exists_good_star_K` — for a bad set `Bad ⊆ {stars = K}` with `|Bad| < C(n,K)·2^(n-K)` (the binomial
  regime), the family-relative pigeonhole (`exists_good_restriction_in`, `card_stars_eq`) yields a
  good restriction with `stars ρ = K`.
* `tseitin_circuit_good_shallow` — hence, for the explicit Tseitin circuit, a good restriction
  (`stars ρ = K`, `ρ ∉ Bad`) yields a residual `ValidSearch` refutation of depth `≤ K`.

This closes the star-bound sub-gap: the good restriction now has its depth budget pinned to `K`.  What
remains for the falsify-deepest end-to-end is the `falseSet ρ` → `∅` step — subsumed by the size route
(`tseitin_no_small_refutation`, BSW-internal), so the size route only needs the small **`∅`**-refutation
over the full Tseitin CNF (the switching depth bound, fenced Obligation 1).  AC⁰/depth-3;
`Depth3CollapseModel.collapse` and P vs NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **A good restriction in the `K`-star family.**  If `Bad ⊆ {stars = K}` and
`|Bad| < C(n,K)·2^(n-K) = |{stars = K}|`, the pigeonhole gives `ρ ∉ Bad` with `stars ρ = K`. -/
theorem exists_good_star_K {Bad : Finset (Restriction n)} {K : ℕ}
    (hsub : Bad ⊆ Finset.univ.filter (fun ρ : Restriction n => stars ρ = K))
    (hlt : Bad.card < n.choose K * 2 ^ (n - K)) :
    ∃ ρ : Restriction n, stars ρ = K ∧ ρ ∉ Bad := by
  have hF : (Finset.univ.filter (fun ρ : Restriction n => stars ρ = K)).card
      = n.choose K * 2 ^ (n - K) := card_stars_eq K
  obtain ⟨ρ, hρF, hρBad⟩ := exists_good_restriction_in hsub (by rw [hF]; exact hlt)
  exact ⟨ρ, (Finset.mem_filter.mp hρF).2, hρBad⟩

end SwitchingCounting

namespace SearchDischarge

open Depth3 SwitchingCounting

variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- **Good restriction ⟹ shallow residual refutation (star-bound pinned).**  For the explicit Tseitin
circuit, a good restriction in the `K`-star family (`Bad ⊆ {stars = K}`, `|Bad| < C(n,K)·2^(n-K)`)
yields `ρ ∉ Bad` whose canonical tree is a `ValidSearch` refutation from `falseSet ρ` of depth
`≤ K`. -/
theorem tseitin_circuit_good_shallow (G : TseitinGraph V (Fin n)) (charge : V → ZMod 2)
    (hodd : ∑ v : V, charge v = 1) {K : ℕ}
    {Bad : Finset (Restriction n)}
    (hsub : Bad ⊆ Finset.univ.filter (fun ρ : Restriction n => stars ρ = K))
    (hlt : Bad.card < n.choose K * 2 ^ (n - K)) :
    ∃ ρ : Restriction n, ρ ∉ Bad ∧
      ValidSearch rpos rcompl (labSearch (dualDNF (tseitinAxList G charge)))
        (AxiomOf (dualDNF (tseitinAxList G charge))) (falseSet ρ)
        (Depth3.canonicalDT (dualDNF (tseitinAxList G charge)) (stars ρ) ρ) ∧
      (Depth3.canonicalDT (dualDNF (tseitinAxList G charge)) (stars ρ) ρ).depth ≤ K := by
  obtain ⟨ρ, hstars, hBad⟩ := exists_good_star_K hsub hlt
  obtain ⟨hvalid, hdepth⟩ :=
    tseitin_circuit_validSearch_shallow G charge hodd ρ (le_of_eq hstars)
  exact ⟨ρ, hBad, hvalid, hdepth⟩

end SearchDischarge

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.exists_good_star_K
#print axioms PallLean.Paper93.DeepMath.PathB.SearchDischarge.tseitin_circuit_good_shallow
