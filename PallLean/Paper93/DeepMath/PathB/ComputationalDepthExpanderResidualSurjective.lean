import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinWidthKernel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderNoHiding

/-!
# Discharging `hsurj`: expander Tseitin makes the residual surjective (proved)

`ComputationalDepthExpanderNoHiding.lean` reduced the open core to one clean property — *residual
non-collapse* (surjectivity of the residual map onto a large outcome set) — and proved that non-collapse
forces super-log debt.  This file **discharges that property from the expander kernel** for the natural
variable-subset (read-a-set-of-vertices) decomposition of Tseitin, fully proved, no new assumption beyond the
genuine expansion hypothesis `HasExpansion` already used in the width kernel.

The chain is:

```
expansion (HasExpansion c, c ≥ 1)
  ⇒ the vertex constraints over a medium read-set W are LINEARLY INDEPENDENT   (constraints_linearIndependent)
  ⇒ the residual map  x ↦ (parity at v)_{v∈W}  is SURJECTIVE onto 2^{|W|} outcomes   (mulVecLin)
  ⇒ every low-boundary observer carries residual debt 2^{|W|} − 2^B   (surjective_residual_forces_debt)
```

with `|W|` up to `⌊|V|/2⌋ = Ω(n)`.

## Proved (clean axioms, no `sorry`)

* `mulVecLin_surjective_of_row_indep` — general F₂ linear-algebra bridge: a matrix with linearly independent
  rows has surjective `mulVecLin` (full row rank ⇒ surjective).
* `constraints_linearIndependent` — **the expander content**: on a graph with expansion `c ≥ 1`, the vertex
  constraints `{constraint (w i)}` over an injective read-set `w : ι → V` with `2·|ι| ≤ |V|` are linearly
  independent.  (A vanishing F₂ combination is `combination S = 0` for the support set `S`; expansion's
  `exists_combination_ne_zero_of_expansion` forbids that unless `S` is empty.)
* `expander_residual_forces_debt` — **the discharged no-hiding bound**: for expander Tseitin and the read-set
  decomposition, every boundary-`B` observer carries residual debt `2^{|ι|} − 2^B`.  For `|ι| = Ω(n)`,
  `B = O(log n)` this is super-logarithmic — *with no surjectivity hypothesis left to assume*.

## Honest scope — what this closes and what stays open

This discharges `hsurj` for **one explicit family of decompositions**: the "read a medium set of vertices,
residual = the induced vertex-parities" decomposition.  For *that* decomposition class, expansion provably
forces super-log continuation debt — a genuine, fully-proved instance of "small boundary + expander
constraints ⇒ large unresolved debt", the dynamic-Nečiporuk bridge.  It is **not** `P ≠ NP`: a SAT decider is
free to choose a *different* decomposition (not a vertex-parity read), and proving residual non-collapse under
**every** cheap adaptive decomposition is the min-over-decompositions quantifier, still open.  What this file
removes is the "is the residual actually large for a real hard instance?" doubt — for the expander read-set
decomposition the answer is provably yes, via the same expansion that powers the width kernel.
-/

namespace PallLean.Paper93.DeepMath.PathB

open Finset Matrix Module
open PallLean.Paper93.DeepMath.PathB.BoundaryDebt

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]

/-- **F₂ linear-algebra bridge (proved).**  A matrix over `ZMod 2` whose rows are linearly independent has a
surjective `mulVecLin` — full row rank forces the column map onto the whole row-indexed space. -/
theorem mulVecLin_surjective_of_row_indep {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι Edge (ZMod 2)) (h : LinearIndependent (ZMod 2) M.row) :
    Function.Surjective M.mulVecLin := by
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fintype_fun_eq_card]
  exact h.rank_matrix

/-- **The expander content (proved).**  On a Tseitin graph with expansion `c ≥ 1`, the vertex constraints over
an injective read-set `w : ι → V` of at most half the vertices are linearly independent over `F₂`. -/
theorem constraints_linearIndependent (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → V) (hw : Function.Injective w) (hmed : 2 * Fintype.card ι ≤ Fintype.card V) :
    LinearIndependent (ZMod 2) (fun i : ι => (fun e => G.constraint (w i) e : Edge → ZMod 2)) := by
  classical
  have ne_zero_eq_one : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  have ne_one_eq_zero : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- support set of `g`, pushed into `V`
  have hcomb0 : G.combination ((univ.filter (fun i => g i = 1)).image w) = 0 := by
    funext e
    have happ : ∑ i, g i * G.constraint (w i) e = 0 := by
      have hge := congrFun hg e
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hge
      exact hge
    show (∑ v ∈ (univ.filter (fun i => g i = 1)).image w, G.constraint v e) = 0
    rw [Finset.sum_image (fun a _ b _ hab => hw hab), ← happ, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : g i = 1
    · rw [if_pos h, h, one_mul]
    · rw [if_neg h, ne_one_eq_zero _ h, zero_mul]
  -- conclude `g` is zero
  intro i
  by_contra hgi
  have hgi1 : g i = 1 := ne_zero_eq_one _ hgi
  have hiT : i ∈ univ.filter (fun j => g j = 1) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgi1⟩
  have hne : ((univ.filter (fun j => g j = 1)).image w).Nonempty :=
    ⟨w i, Finset.mem_image.mpr ⟨i, hiT, rfl⟩⟩
  have hScard : 1 ≤ ((univ.filter (fun j => g j = 1)).image w).card := Finset.card_pos.mpr hne
  have hSle : ((univ.filter (fun j => g j = 1)).image w).card ≤ Fintype.card ι :=
    le_trans (Finset.card_image_le) (le_trans (Finset.card_filter_le _ _) (le_of_eq Finset.card_univ))
  have hSmed : 2 * ((univ.filter (fun j => g j = 1)).image w).card ≤ Fintype.card V := by omega
  obtain ⟨e, he⟩ :=
    G.exists_combination_ne_zero_of_expansion hc hexp _ hScard hSmed
  exact he (congrFun hcomb0 e)

/-- **No-hiding, discharged for expander Tseitin (proved).**  For a Tseitin graph with expansion `c ≥ 1` and
the read-set decomposition `w : ι → V` (injective, `2·|ι| ≤ |V|`), the residual map (edge-assignment ↦ vertex
parities over `w`) is surjective onto `2^{|ι|}` outcomes, so **every** boundary-`B` observer carries residual
debt `2^{|ι|} − 2^B`.  No surjectivity hypothesis is assumed — expansion supplies it. -/
theorem expander_residual_forces_debt (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → V) (hw : Function.Injective w) (hmed : 2 * Fintype.card ι ≤ Fintype.card V)
    {B : ℕ} (view : (Edge → ZMod 2) → Fin (2 ^ B)) :
    ∃ residual : (Edge → ZMod 2) → Fin (2 ^ Fintype.card ι),
      2 ^ Fintype.card ι - 2 ^ B ≤ debtCount (residualFooling residual) view := by
  classical
  -- the constraint matrix; its rows are the read-set vertex constraints
  let M : Matrix ι Edge (ZMod 2) := fun i e => G.constraint (w i) e
  have hindep : LinearIndependent (ZMod 2) M.row :=
    constraints_linearIndependent G hc hexp w hw hmed
  have hsurj_lin : Function.Surjective M.mulVecLin := mulVecLin_surjective_of_row_indep M hindep
  -- transport the codomain `(ι → ZMod 2)` to `Fin (2 ^ |ι|)`
  have hcardpi : Fintype.card (ι → ZMod 2) = 2 ^ Fintype.card ι := by
    rw [Fintype.card_fun, ZMod.card]
  let e2 := Fintype.equivFinOfCardEq hcardpi
  refine ⟨fun x => e2 (M.mulVecLin x), ?_⟩
  exact surjective_residual_forces_debt _ (e2.surjective.comp hsurj_lin) view

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.mulVecLin_surjective_of_row_indep
#print axioms PallLean.Paper93.DeepMath.PathB.constraints_linearIndependent
#print axioms PallLean.Paper93.DeepMath.PathB.expander_residual_forces_debt
