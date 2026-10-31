import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSPDPProductUB

/-!
# An ACC-normal-form SPDP upper bound, stable under admissible boundaries

This is the *honest reachable* step toward ACC (not "all ACC⁰"): a compression theorem for a specific ACC-like normal
form — a small **sum of products of low-degree factors** — that is preserved by admissible restriction boundaries.

  `spdpRank_sumProd_le` — for `f = ∑_{i<s} ∏_{j<m} Q_{ij}` with each `deg Q_{ij} ≤ t`,
        `spdpRank κ 0 f ≤ s · (#{J⊆[m]:|J|≤κ}) · finrank(restrictTotalDegree κt)` — the depth-`4` / ACC-inner-layer bound.
  `spdpRank_aevalBoundary_sumProd_le` — **the functorial compression**: an admissible boundary is a ring endomorphism
        `aeval g` with `deg (g v) ≤ 1` (a restriction: each variable kept or fixed to a constant).  It commutes with
        `∑`/`∏` and does not raise degree, so it maps the normal form to *another normal form with the same budget*:
        `spdpRank κ 0 (aeval g f) ≤ s · (#{J:|J|≤κ}) · finrank(restrictTotalDegree κt)`.
  `restrictBdry` / `spdpRank_restrictBdry_sumProd_le` — the concrete admissible (sub-cube) boundary
        `v ↦ if v ∈ visible then X v else C (assign v)` and its normal-form bound.

The key point (`totalDegree_aeval_le_of_deg_le_one`): a degree-`≤1` substitution is degree-non-increasing, so the
boundary image `aeval g (Q_{ij})` still has degree `≤ t`.  Combined with `aeval`'s ring-hom functoriality
(`map_sum`, `map_prod`), the whole normal form is carried into the product-derivative dimension budget.

## Honest scope — why this is *not* "all ACC⁰"

This covers the **Beigel–Tarui inner layer** (a `∑∏` of low-degree/local factors) and shows admissible boundaries keep
it in the product-derivative space.  It does **not** cover full `ACC⁰`/`ACC⁰[p]`: the symmetric/`MOD` composition `P`
in the BT normal form `f = P(∑∏)` lifts the bottom degree to `t = polylog` and the shift space
`finrank(restrictTotalDegree κt) ≈ binom(n+κt,n)` then overtakes the permanent's `C(k,κ)²` lower bound at the very `κ`
where it bites — the barrier analysed in the C-arc.  Whether known `ACC⁰[p]` machinery (Razborov–Smolensky) yields a
*controlled-blowup* normal form of this shape is the separate, open question.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SPDPUpperBound

open MvPolynomial Finset

variable {F : Type*} [Field F]

/-- A degree-`≤1` substitution is degree-non-increasing (an admissible boundary keeps each variable or fixes it to a
constant, so it never raises degree). -/
theorem totalDegree_aeval_le_of_deg_le_one {σ : Type*} [DecidableEq σ]
    (g : σ → MvPolynomial σ F) (hg : ∀ v, (g v).totalDegree ≤ 1) (p : MvPolynomial σ F) :
    (aeval g p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum, map_sum]
  refine le_trans (totalDegree_finset_sum _ _) (Finset.sup_le (fun d hd => ?_))
  rw [aeval_monomial, MvPolynomial.algebraMap_eq]
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine le_trans ?_ (MvPolynomial.le_totalDegree hd)
  rw [Finsupp.prod]
  refine le_trans (MvPolynomial.totalDegree_finset_prod _ _) ?_
  rw [Finsupp.sum]
  refine Finset.sum_le_sum (fun v _ => ?_)
  refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
  calc d v * (g v).totalDegree ≤ d v * 1 := Nat.mul_le_mul (le_refl (d v)) (hg v)
    _ = d v := Nat.mul_one _

/-- **The ACC-normal-form SPDP bound (proved)**: a sum of `s` products of `m` factors of degree `≤ t` has SPDP rank
`≤ s · (#{J:|J|≤κ}) · (#monomials of degree ≤ κt)`. -/
theorem spdpRank_sumProd_le {n s m t : ℕ} (Q : Fin s → Fin m → MvPolynomial (Fin n) F)
    (ht : ∀ i j, (Q i j).totalDegree ≤ t) (κ : ℕ) :
    SPDP.spdpRank κ 0 (∑ i, ∏ j, Q i j)
      ≤ s * ((Finset.univ.filter (fun J : Finset (Fin m) => J.card ≤ κ)).card
          * Module.finrank F ↥(MvPolynomial.restrictTotalDegree (Fin n) F (κ * t))) := by
  calc SPDP.spdpRank κ 0 (∑ i, ∏ j, Q i j)
      ≤ ∑ i, SPDP.spdpRank κ 0 (∏ j, Q i j) := spdpRank_sum_le κ 0 Finset.univ _
    _ ≤ ∑ _i : Fin s, ((Finset.univ.filter (fun J : Finset (Fin m) => J.card ≤ κ)).card
          * Module.finrank F ↥(MvPolynomial.restrictTotalDegree (Fin n) F (κ * t))) :=
        Finset.sum_le_sum (fun i _ => spdpRank_prod_le_card (Q i) (ht i) κ)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **Functorial compression under an admissible boundary (proved)**: an admissible boundary `aeval g` (each `deg g v ≤ 1`)
maps an ACC normal form to another normal form with the same degree budget, so the same dimension bound holds. -/
theorem spdpRank_aevalBoundary_sumProd_le {n s m t : ℕ} (g : Fin n → MvPolynomial (Fin n) F)
    (hg : ∀ v, (g v).totalDegree ≤ 1) (Q : Fin s → Fin m → MvPolynomial (Fin n) F)
    (ht : ∀ i j, (Q i j).totalDegree ≤ t) (κ : ℕ) :
    SPDP.spdpRank κ 0 (aeval g (∑ i, ∏ j, Q i j))
      ≤ s * ((Finset.univ.filter (fun J : Finset (Fin m) => J.card ≤ κ)).card
          * Module.finrank F ↥(MvPolynomial.restrictTotalDegree (Fin n) F (κ * t))) := by
  rw [map_sum]
  simp only [map_prod]
  exact spdpRank_sumProd_le (fun i j => aeval g (Q i j))
    (fun i j => le_trans (totalDegree_aeval_le_of_deg_le_one g hg (Q i j)) (ht i j)) κ

/-- A concrete admissible (sub-cube) boundary: keep the visible variables, fix the rest to constants. -/
noncomputable def restrictBdry {n : ℕ} (visible : Finset (Fin n)) (assign : Fin n → F) :
    Fin n → MvPolynomial (Fin n) F :=
  fun v => if v ∈ visible then X v else C (assign v)

theorem restrictBdry_deg {n : ℕ} (visible : Finset (Fin n)) (assign : Fin n → F) (v : Fin n) :
    (restrictBdry visible assign v).totalDegree ≤ 1 := by
  unfold restrictBdry
  split
  · rw [MvPolynomial.totalDegree_X]
  · rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le 1

/-- **The ACC-normal-form bound under a concrete admissible boundary (proved)**: restricting to a sub-cube (keeping some
variables, fixing the rest) keeps the SPDP rank of a normal form within the product-derivative dimension budget. -/
theorem spdpRank_restrictBdry_sumProd_le {n s m t : ℕ} (visible : Finset (Fin n)) (assign : Fin n → F)
    (Q : Fin s → Fin m → MvPolynomial (Fin n) F) (ht : ∀ i j, (Q i j).totalDegree ≤ t) (κ : ℕ) :
    SPDP.spdpRank κ 0 (aeval (restrictBdry visible assign) (∑ i, ∏ j, Q i j))
      ≤ s * ((Finset.univ.filter (fun J : Finset (Fin m) => J.card ≤ κ)).card
          * Module.finrank F ↥(MvPolynomial.restrictTotalDegree (Fin n) F (κ * t))) :=
  spdpRank_aevalBoundary_sumProd_le (restrictBdry visible assign) (restrictBdry_deg visible assign) Q ht κ

end PallLean.Paper93.DeepMath.PathB.SPDPUpperBound

#print axioms PallLean.Paper93.DeepMath.PathB.SPDPUpperBound.spdpRank_sumProd_le
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPUpperBound.spdpRank_aevalBoundary_sumProd_le
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPUpperBound.spdpRank_restrictBdry_sumProd_le
