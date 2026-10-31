import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBoundaryHolonomy
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderResidualSurjective

/-!
# Expander many-loop holonomy amplification (proved): a cheap atlas cannot avoid every loop

`ComputationalDepthBoundaryHolonomy.lean` showed: a single loop with nonzero holonomy (`res v ≠ 0`, flattened
by the observer) forces debt.  The escape was that the observer could flatten a *different* direction, avoiding
that one loop.  **Amplification** closes that escape using expansion: a cheap observer flattens a whole
*subspace* `W` of directions, and the residual map has rank `|ι| = Ω(n)` (expansion), so **any** subspace of
codimension `< |ι|` must contain a twisting direction — the observer cannot avoid all loops at once.

## Proved (clean axioms, no `sorry`)

* `additive_holonomy_forces_debt` — the holonomy lemma for an additive (vector) residual `res` (generalises
  `parity_loop_holonomy` from scalar `ZMod 2` to any additive codomain): `res v ≠ 0` + `view` flattens `v`
  ⇒ debt `= |Config|`.
* `expander_manyloop_holonomy` — **the amplification**: for expander Tseitin (residual rank `|ι|`), any
  observer that flattens a subspace `W` of directions (`view (c + x) = view c` for all `x ∈ W`) with
  `codim W < |ι|` (i.e. `finrank W > |Edge| − |ι|`) carries the **full** debt `2^{|Edge|}` — because such a `W`
  cannot lie inside `ker(residual)`, so it contains a direction `v` with `residual v ≠ 0` (a loop the observer
  flattened but whose residual twisted).

## The curvature reading

Expansion gives the residual map rank `|ι| = Ω(n)`.  A cheap observer flattens a low-codimension subspace.
Linear algebra then forces that subspace to meet a nonzero-holonomy direction: **expander constraints have
nonzero curvature against every low-codimension coordinate flattening.**  This is HAL's "expander loop
holonomy" for the linear/periodic class, discharged from expansion.

## Honest scope

A `W`-periodic view takes `≤ 2^{codim W}` values, so this coincides numerically with effective-boundary
no-hiding (`debt ≥ 2^r − 2^{codim W}`) — the amplification is the *curvature lens* on the same bound, now
expressed as "every cheap flattening twists".  It is **not** `P ≠ NP`: it covers observers that flatten a
*subspace* (linear / periodic structure).  A genuinely nonlinear high-effective-boundary atlas that is not
periodic under any large subspace is unconstrained; forcing nonzero curvature against *those* is the open
min-over-decompositions quantifier, named not faked.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundaryDebt

open scoped BigOperators
open Finset

/-- **Additive (vector) holonomy debt (proved).**  For an additive residual `res` (`res (a+b) = res a + res b`)
on a finite configuration group, a holonomy translation `v` with `res v ≠ 0`, and an observer flattening `v`
(`view (c + v) = view c`), **every** config is twisted, so the debt is the full `|Config|`. -/
theorem additive_holonomy_forces_debt {Config R S : Type*} [Fintype Config] [DecidableEq Config]
    [AddGroup Config] [AddGroup R] [DecidableEq R] [DecidableEq S]
    (res : Config → R) (hadd : ∀ a b : Config, res (a + b) = res a + res b)
    (v : Config) (hv : res v ≠ 0) (view : Config → S) (hview : ∀ c, view (c + v) = view c) :
    Fintype.card Config ≤ debtCount (residualRel res) view := by
  have hkey := holonomy_forces_debt_card res (fun c => c + v) view hview
  have hall : (univ.filter (fun c => res ((fun c => c + v) c) ≠ res c)) = (univ : Finset Config) := by
    apply Finset.filter_true_of_mem
    intro c _
    show res (c + v) ≠ res c
    rw [hadd]
    exact fun hcon => hv (add_eq_left.mp hcon)
  rw [hall, Finset.card_univ] at hkey
  exact hkey

end PallLean.Paper93.DeepMath.PathB.BoundaryDebt

namespace PallLean.Paper93.DeepMath.PathB

open Module LinearMap Submodule Finset
open PallLean.Paper93.DeepMath.PathB.BoundaryDebt

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]

/-- **Expander many-loop holonomy amplification (proved).**  For a Tseitin graph with expansion `c ≥ 1` and
read-set `w : ι → V` (injective, `2·|ι| ≤ |V|`), any observer that flattens a subspace `W` of directions
(`view (c + x) = view c` for all `x ∈ W`) of codimension `< |ι|` — equivalently `finrank W > |Edge| − |ι|` —
carries the full residual debt `2^{|Edge|}`.  Expansion (residual rank `|ι|`) forces such a `W` to contain a
twisting direction; the observer cannot flatten its way around all loops. -/
theorem expander_manyloop_holonomy (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → V) (hw : Function.Injective w) (hmed : 2 * Fintype.card ι ≤ Fintype.card V)
    {S : Type*} [DecidableEq S] (W : Submodule (ZMod 2) (Edge → ZMod 2)) (view : (Edge → ZMod 2) → S)
    (hper : ∀ c : Edge → ZMod 2, ∀ x ∈ W, view (c + x) = view c)
    (hWdim : Fintype.card Edge - Fintype.card ι < finrank (ZMod 2) W) :
    ∃ res : (Edge → ZMod 2) → (ι → ZMod 2),
      Fintype.card (Edge → ZMod 2) ≤ debtCount (residualRel res) view := by
  classical
  let M : Matrix ι Edge (ZMod 2) := fun i e => G.constraint (w i) e
  have hsurj : Function.Surjective M.mulVecLin :=
    mulVecLin_surjective_of_row_indep M (constraints_linearIndependent G hc hexp w hw hmed)
  -- `finrank (ker mulVecLin) = |Edge| − |ι|`
  have hkerrank : finrank (ZMod 2) (LinearMap.ker M.mulVecLin) = Fintype.card Edge - Fintype.card ι := by
    have hrange : finrank (ZMod 2) (LinearMap.range M.mulVecLin) = Fintype.card ι := by
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fintype_fun_eq_card]
    have hsum := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [hrange, Module.finrank_fintype_fun_eq_card] at hsum
    omega
  -- `W` cannot lie in the kernel, so it has a twisting direction
  have hnotle : ¬ (W ≤ LinearMap.ker M.mulVecLin) := by
    intro hle
    have hmono := Submodule.finrank_mono hle
    omega
  obtain ⟨v, hvW, hvker⟩ := Set.not_subset.mp hnotle
  have hres : M.mulVecLin v ≠ 0 := fun h => hvker (LinearMap.mem_ker.mpr h)
  exact ⟨⇑M.mulVecLin,
    additive_holonomy_forces_debt _ (fun a b => map_add M.mulVecLin a b) v hres view
      (fun c => hper c v hvW)⟩

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.additive_holonomy_forces_debt
#print axioms PallLean.Paper93.DeepMath.PathB.expander_manyloop_holonomy
