import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderResidualSurjective

/-!
# Bounded-locality / branching-program non-collapse (proved): the next rung

Staged ladder so far: read-set ✅, `F₂`-linear/affine ✅.  This file proves the **bounded-locality** rung:
a view that depends on only a bounded set of variables — a junta / small-support observation, the semantic
content of decision trees, read-few branching programs, and local feature maps — cannot collapse the
expander-Tseitin residual, **regardless of how complex its output is**.

This is genuinely new content, not subsumed by output-boundary no-hiding: a bounded-support view may have a
huge (even exponential) output alphabet, so its output boundary is unbounded — yet because it reads only `|W|`
variables it factors through the coordinate projection `π_W` and can distinguish at most `2^{|W|}` residual
outcomes.  Locality (variables read), not output size, is what bounds its power.

## Proved (clean axioms, no `sorry`)

* `debtCount_mono` — debt is monotone under coarsening: if `v₁` refines `v₂` (`v₁ x = v₁ y ⇒ v₂ x = v₂ y`)
  then `debtCount F v₁ ≤ debtCount F v₂`.  A coarser observation merges at least as much, so carries at least
  as much debt.
* `bounded_support_forces_debt` — for a surjective residual onto `Fin (2^r)`, **any** view depending only on a
  variable set `W` (`DependsOn`), with arbitrary output, has residual debt `≥ 2^r − 2^{|W|}`.  (It is coarser
  than the linear projection `π_W : C → Fin (2^{|W|})`; apply no-hiding to `π_W` and monotonicity.)
* `expander_bounded_locality_noncollapse` — the discharged instance: for expander Tseitin, any view depending
  on `≤ |W|` edge-variables has residual debt `≥ 2^{|ι|} − 2^{|W|}`.  For `|W| < |ι| = Ω(n)` this is super-log
  — bounded-locality observations cannot collapse the residual.

## Honest scope

This handles the bounded-locality / small-support / read-few-variables decomposition class (juntas, shallow
decision trees, read-bounded branching programs all factor through a bounded variable set).  Combined with the
linear/affine rung, the cheap *structured* decompositions are now covered.  It is **not** `P ≠ NP`: a
decomposition reading *many* variables with a globally clever nonlinear structure (high support, low effective
action) is unconstrained by this; `AdaptiveResidualNonCollapse` for *every* decomposition remains the open
min-over-decompositions quantifier.  The common invariant unifying read-set / linear / bounded-locality into
"every cheap decomposition" is the remaining mathematics, named not faked.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundaryDebt

open scoped BigOperators

/-- **Debt is monotone under coarsening (proved).**  If `v₁` refines `v₂` — every pair `v₁` separates `v₂`
also separates (contrapositive: `v₁ x = v₁ y ⇒ v₂ x = v₂ y`) — then `v₂`, being coarser, merges at least as
many must-separate pairs: `debtCount F v₁ ≤ debtCount F v₂`. -/
theorem debtCount_mono {X S T : Type*} [DecidableEq S] [DecidableEq T] (F : Finset (X × X))
    (v1 : X → S) (v2 : X → T) (h : ∀ x y : X, v1 x = v1 y → v2 x = v2 y) :
    debtCount F v1 ≤ debtCount F v2 := by
  rw [debtCount, debtCount]
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, h p.1 p.2 hp.2⟩

/-- **Bounded-support non-collapse (proved).**  For a surjective residual `residual : (Edge → ZMod 2) →
Fin (2^r)`, any view `view` that depends only on the variable set `W` (`DependsOn`: assignments agreeing on
`W` get equal views) — with *arbitrary* output type `S` — carries residual debt `≥ 2^r − 2^{|W|}`.  Output
complexity is irrelevant; only the number of variables read bounds the view's power. -/
theorem bounded_support_forces_debt {Edge : Type*} [Fintype Edge] [DecidableEq Edge] {r : ℕ}
    (residual : (Edge → ZMod 2) → Fin (2 ^ r)) (hsurj : Function.Surjective residual)
    {S : Type*} [DecidableEq S] (view : (Edge → ZMod 2) → S) (W : Finset Edge)
    (hdep : ∀ x y : Edge → ZMod 2, (∀ e ∈ W, x e = y e) → view x = view y) :
    2 ^ r - 2 ^ W.card ≤ debtCount (residualFooling residual) view := by
  classical
  have hcard : Fintype.card (↥W → ZMod 2) = 2 ^ W.card := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_coe]
  -- the linear coordinate projection onto the read variables, as a `Fin (2^{|W|})`-valued view
  let e2 := Fintype.equivFinOfCardEq hcard
  let piW : (Edge → ZMod 2) → Fin (2 ^ W.card) := fun x => e2 (fun e => x e.val)
  -- `view` is coarser than `piW`
  have hmono : debtCount (residualFooling residual) piW ≤ debtCount (residualFooling residual) view := by
    apply debtCount_mono
    intro x y hxy
    apply hdep
    intro e he
    have hr : (fun e : ↥W => x e.val) = (fun e => y e.val) := e2.injective hxy
    exact congrFun hr ⟨e, he⟩
  have hpi := surjective_residual_forces_debt residual hsurj piW
  omega

end PallLean.Paper93.DeepMath.PathB.BoundaryDebt

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.BoundaryDebt

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]

/-- **Bounded-locality non-collapse for expander Tseitin (proved).**  For a Tseitin graph with expansion
`c ≥ 1` and read-set `w : ι → V` (injective, `2·|ι| ≤ |V|`), any view depending on a bounded set `W` of edge
variables (a junta / shallow decision tree / read-bounded branching program) has residual debt
`≥ 2^{|ι|} − 2^{|W|}`.  For `|W| < |ι| = Ω(n)` this is super-logarithmic: bounded-locality observations cannot
collapse the residual, no matter how complex their output. -/
theorem expander_bounded_locality_noncollapse (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → V) (hw : Function.Injective w) (hmed : 2 * Fintype.card ι ≤ Fintype.card V)
    {S : Type*} [DecidableEq S] (view : (Edge → ZMod 2) → S) (W : Finset Edge)
    (hdep : ∀ x y : Edge → ZMod 2, (∀ e ∈ W, x e = y e) → view x = view y) :
    ∃ residual : (Edge → ZMod 2) → Fin (2 ^ Fintype.card ι),
      2 ^ Fintype.card ι - 2 ^ W.card ≤ debtCount (residualFooling residual) view := by
  classical
  let M : Matrix ι Edge (ZMod 2) := fun i e => G.constraint (w i) e
  have hsurj_lin : Function.Surjective M.mulVecLin :=
    mulVecLin_surjective_of_row_indep M (constraints_linearIndependent G hc hexp w hw hmed)
  have hcardpi : Fintype.card (ι → ZMod 2) = 2 ^ Fintype.card ι := by
    rw [Fintype.card_fun, ZMod.card]
  let e2 := Fintype.equivFinOfCardEq hcardpi
  exact ⟨fun x => e2 (M.mulVecLin x),
    bounded_support_forces_debt _ (e2.surjective.comp hsurj_lin) view W hdep⟩

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.debtCount_mono
#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.bounded_support_forces_debt
#print axioms PallLean.Paper93.DeepMath.PathB.expander_bounded_locality_noncollapse
