import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Cross-block vanishing of the additive clause-sheet (audit artifact)

This formalizes the structural fact behind the SPDP-rank collapse of the **additive** clause-sheet
`Q⁺_Φ = 1 - ∑_C V_C²` (cf. `p-vs-np1.pdf`, Remark 54): a second-order partial derivative `∂_u ∂_w`
**across two distinct clause blocks** annihilates every summand, hence `∂_u ∂_w Q⁺ = 0`.

This is the precise reason the additive sheet has *no cross-block mixed partials* — and so cannot
support the identity-minor / high-rank construction the lower bound needs.  The companion numerical
audit (`~/spdp_rank_audit.py`) shows `Γ_{κ,ℓ}(Q⁺)` collapses (`= 1`, or `0` for `κ = 3`) while the
**coupled** sheet `Q^× = ∏_C(1 - z_C V_C²)` has strictly higher rank — so no rank-monotone map can take
one to the other.

* `vars_pderiv_le` — `pderiv` does not introduce variables (`(pderiv i f).vars ⊆ f.vars`); not in
  Mathlib, proved here.
* `pderiv_pderiv_block_eq_zero` — `∂_u ∂_w V = 0` when `V` is supported on a block missing `u` or `w`.
* `cross_block_pderiv_sum_eq_zero` — `∂_u ∂_w (∑_i V_i) = 0` when each block misses `u` or `w`.
* `additive_sheet_cross_block_vanish` — `∂_u ∂_w (1 - ∑_i V_i²) = 0` for cross-block `(u,w)`.

Clean, no `sorry`.  This is an audit artifact about the paper, independent of the depth-3 Lean arc.
-/

namespace PallLean.Paper93.DeepMath.PathB.AdditiveSheetAudit

open MvPolynomial

variable {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]

/-- **`pderiv` introduces no new variables.**  `(pderiv i f).vars ⊆ f.vars`. -/
theorem vars_pderiv_le (i : σ) (f : MvPolynomial σ R) :
    (pderiv i f).vars ⊆ f.vars := by
  intro v hv
  rw [mem_vars] at hv ⊢
  obtain ⟨d, hd, hvd⟩ := hv
  rw [← support_sum_monomial_coeff f, map_sum] at hd
  simp only [pderiv_monomial] at hd
  obtain ⟨s, hs, hds⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  have hd_eq : d = s - Finsupp.single i 1 := Finset.mem_singleton.mp (support_monomial_subset hds)
  refine ⟨s, ?_, ?_⟩
  · simpa using hs
  · have hvs : v ∈ (s - Finsupp.single i 1).support := hd_eq ▸ hvd
    rw [Finsupp.mem_support_iff] at hvs ⊢
    intro h0
    apply hvs
    rw [Finsupp.tsub_apply, h0]
    simp

/-- **Cross-block second derivative of a block-supported polynomial vanishes.**  If `V`'s variables lie
in `block` and `block` misses `u` or `w`, then `∂_u ∂_w V = 0`. -/
theorem pderiv_pderiv_block_eq_zero {u w : σ} {block : Finset σ} {V : MvPolynomial σ R}
    (hV : V.vars ⊆ block) (h : u ∉ block ∨ w ∉ block) :
    pderiv u (pderiv w V) = 0 := by
  rcases h with hu | hw
  · apply pderiv_eq_zero_of_notMem_vars
    exact fun hmem => hu (hV (vars_pderiv_le w V hmem))
  · rw [pderiv_eq_zero_of_notMem_vars (fun hmem => hw (hV hmem)), map_zero]

/-- **Cross-block second derivative of a sum of block-supported polynomials vanishes.** -/
theorem cross_block_pderiv_sum_eq_zero {ι : Type*} (s : Finset ι) {u w : σ}
    {block : ι → Finset σ} {V : ι → MvPolynomial σ R}
    (hV : ∀ i ∈ s, (V i).vars ⊆ block i)
    (hcross : ∀ i ∈ s, u ∉ block i ∨ w ∉ block i) :
    pderiv u (pderiv w (∑ i ∈ s, V i)) = 0 := by
  simp only [map_sum]
  exact Finset.sum_eq_zero (fun i hi => pderiv_pderiv_block_eq_zero (hV i hi) (hcross i hi))

/-- **The additive clause-sheet has vanishing cross-block mixed partials.**  For the additive sheet
`Q⁺ = 1 - ∑_i V_i²` with each `V_i` supported on `block i`, and `(u,w)` spanning two blocks,
`∂_u ∂_w Q⁺ = 0`.  (This is exactly why `Q⁺` cannot carry the high-rank identity minor.) -/
theorem additive_sheet_cross_block_vanish {ι : Type*} (s : Finset ι) {u w : σ}
    {block : ι → Finset σ} {V : ι → MvPolynomial σ R}
    (hV : ∀ i ∈ s, (V i).vars ⊆ block i)
    (hcross : ∀ i ∈ s, u ∉ block i ∨ w ∉ block i) :
    pderiv u (pderiv w ((1 : MvPolynomial σ R) - ∑ i ∈ s, (V i) ^ 2)) = 0 := by
  have hV2 : ∀ i ∈ s, ((V i) ^ 2).vars ⊆ block i := by
    intro i hi
    refine subset_trans ?_ (hV i hi)
    rw [pow_two]
    exact (vars_mul (V i) (V i)).trans (by rw [Finset.union_self])
  rw [map_sub, map_sub, pderiv_one, map_zero, zero_sub, neg_eq_zero]
  exact cross_block_pderiv_sum_eq_zero s hV2 hcross

end PallLean.Paper93.DeepMath.PathB.AdditiveSheetAudit

#print axioms PallLean.Paper93.DeepMath.PathB.AdditiveSheetAudit.vars_pderiv_le
#print axioms PallLean.Paper93.DeepMath.PathB.AdditiveSheetAudit.additive_sheet_cross_block_vanish
