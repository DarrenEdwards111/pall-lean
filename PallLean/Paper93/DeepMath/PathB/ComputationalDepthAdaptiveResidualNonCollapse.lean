import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderResidualSurjective

/-!
# `AdaptiveResidualNonCollapse`: the God-Move target, with the linear/affine class proved

The whole programme now reduces to **one** property (the final open jump):

> **`AdaptiveResidualNonCollapse`** — every *cheap* adaptive decomposition of expander Tseitin / SAT preserves
> `2^{Ω(n)}` residual outcomes.

Proving it for **every** decomposition is `P ≠ NP`.  Following the staged plan, this file proves it for the
**linear/affine class** over `F₂` — the natural first restricted class, because expander-Tseitin residuals are
already linear and the row-independence machinery is in hand.

## The linear non-collapse theorem (HAL's step 4 target)

> *Any low-dimensional `F₂`-linear observation of the residual map leaves exponentially many residual outcomes
> unless the observation dimension is large.*

Precisely: if `res` has rank `r` and the observer reads a linear map `L` of dimension `k`, the residual
restricted to `ker L` (the continuations the observation cannot tell apart) still has rank `≥ r − k`.  So a
dimension-`k` linear quotient cannot collapse the residual below `2^{r−k}` outcomes.

## Proved (clean axioms, no `sorry`)

* `finrank_map_ker_ge` — abstract `F₂` (any field) linear algebra: for `res : E →ₗ R`, `L : E →ₗ M`,
  `finrank (range res) − finrank (range L) ≤ finrank ((ker L).map res)`.  (Rank-nullity for `res|ker L`, with
  `ker(res|ker L) ≅ ker L ⊓ ker res ≤ ker res`.)
* `LinearResidualNonCollapse` — the named property for the linear class.
* `expander_linear_decomposition_noncollapse` — **the discharged instance**: for expander Tseitin's residual
  (rank `= |ι| = Ω(n)`) and *any* `F₂`-linear observation `L : (Edge → ZMod 2) →ₗ Fin k → ZMod 2`, the residual
  on `ker L` has rank `≥ |ι| − k`.  Expansion ⇒ the residual is non-collapsing under every linear observation.

## Honest scope — the final jump

This proves non-collapse for the **linear/affine** decomposition class: no `F₂`-linear change of coordinates
followed by a `k`-dimensional read can collapse the expander-Tseitin residual below `2^{|ι|−k}` outcomes.  It is
**not** `P ≠ NP`: a SAT decider may use a **non-linear** decomposition (branching, low-degree, arbitrary), and
`AdaptiveResidualNonCollapse` for *every* such decomposition is the open min-over-decompositions quantifier.
The staged ladder is now: read-set ✅, linear/affine ✅ (this file); bounded-locality / branching-program next;
then the common invariant that would close the general case — the genuine remaining mathematics, named not
faked.
-/

namespace PallLean.Paper93.DeepMath.PathB

open Module LinearMap Submodule Finset

/-- **Abstract `F₂` (any-field) rank bound (proved).**  Restricting `res` to `ker L` loses at most
`finrank (range L)` of its rank: `finrank (range res) − finrank (range L) ≤ finrank ((ker L).map res)`.  This
is the linear-algebra heart of "a low-dimensional observation cannot collapse a high-rank residual." -/
theorem finrank_map_ker_ge {K E R M : Type*} [Field K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [AddCommGroup R] [Module K R] [AddCommGroup M] [Module K M]
    (res : E →ₗ[K] R) (L : E →ₗ[K] M) :
    finrank K (LinearMap.range res) - finrank K (LinearMap.range L)
      ≤ finrank K ((LinearMap.ker L).map res) := by
  -- rank-nullity for `res` restricted to `ker L`
  have hrn := LinearMap.finrank_range_add_finrank_ker (res.domRestrict (LinearMap.ker L))
  rw [LinearMap.range_domRestrict] at hrn
  -- the restricted kernel injects into `ker res`
  have hker : finrank K (LinearMap.ker (res.domRestrict (LinearMap.ker L)))
      ≤ finrank K (LinearMap.ker res) := by
    rw [ker_domRestrict (LinearMap.ker L) res,
        ← finrank_map_subtype_eq (LinearMap.ker L) ((LinearMap.ker res).comap (LinearMap.ker L).subtype),
        map_comap_subtype]
    exact Submodule.finrank_mono inf_le_right
  have hL := LinearMap.finrank_range_add_finrank_ker L
  have hres := LinearMap.finrank_range_add_finrank_ker res
  omega

/-- **The named property for the linear class.**  `res` is *linearly non-collapsing with rank `r`* if every
`F₂`-linear observation `L` of dimension `k` leaves residual rank `≥ r − k` on the continuations it cannot
distinguish (`ker L`). -/
def LinearResidualNonCollapse {C : Type*} [AddCommGroup C] [Module (ZMod 2) C] [FiniteDimensional (ZMod 2) C]
    {R : Type*} [AddCommGroup R] [Module (ZMod 2) R] (res : C →ₗ[ZMod 2] R) (r : ℕ) : Prop :=
  ∀ {k : ℕ} (L : C →ₗ[ZMod 2] (Fin k → ZMod 2)),
    r - k ≤ finrank (ZMod 2) ((LinearMap.ker L).map res)

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]

/-- **Linear/affine non-collapse for expander Tseitin (proved).**  For a Tseitin graph with expansion `c ≥ 1`
and read-set `w : ι → V` (injective, `2·|ι| ≤ |V|`), the residual map `M.mulVecLin` (vertex parities) has rank
`|ι|`, and *any* `F₂`-linear observation `L` of dimension `k` leaves residual rank `≥ |ι| − k` on `ker L`.  No
linear coordinate change collapses the expander residual below `2^{|ι|−k}` outcomes. -/
theorem expander_linear_decomposition_noncollapse (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → V) (hw : Function.Injective w) (hmed : 2 * Fintype.card ι ≤ Fintype.card V)
    {k : ℕ} (L : (Edge → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) :
    Fintype.card ι - k
      ≤ finrank (ZMod 2) ((LinearMap.ker L).map
          (Matrix.mulVecLin (fun i e => G.constraint (w i) e : Matrix ι Edge (ZMod 2)))) := by
  set M : Matrix ι Edge (ZMod 2) := fun i e => G.constraint (w i) e with hM
  have hsurj : Function.Surjective M.mulVecLin :=
    mulVecLin_surjective_of_row_indep M (constraints_linearIndependent G hc hexp w hw hmed)
  -- rank of the residual map is `|ι|`
  have hrank_res : finrank (ZMod 2) (LinearMap.range M.mulVecLin) = Fintype.card ι := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fintype_fun_eq_card]
  -- rank of the observation is at most `k`
  have hrank_L : finrank (ZMod 2) (LinearMap.range L) ≤ k := by
    refine le_trans (Submodule.finrank_le _) ?_
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have h := finrank_map_ker_ge M.mulVecLin L
  rw [hrank_res] at h
  omega

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.finrank_map_ker_ge
#print axioms PallLean.Paper93.DeepMath.PathB.expander_linear_decomposition_noncollapse
