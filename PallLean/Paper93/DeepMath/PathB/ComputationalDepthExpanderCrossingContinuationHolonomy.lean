import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingSequenceContinuationHolonomy
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderResidualSurjective
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingBottleneckNoGo

/-!
# Expander residuals inside crossing-sequence continuation holonomy

The crossing/continuation theorem requires a surjective residual map onto
`2^r` future-distinguishable outcomes.  This file removes the abstract
surjectivity input for the natural Tseitin read-set residual: graph expansion
makes the selected vertex constraints linearly independent, hence their parity
map is onto all `2^|ι|` outcome vectors.

Composing that concrete residual with continuation-complete trace semantics gives

```text
2^|ι| <= q^w
```

for every width-`w`, `q`-state crossing representation that preserves those
residuals under future suffixes.

The two remaining obligations stay explicit and cannot be obtained from
polynomial time alone:

1. the solver's physical trace must actually factor through the claimed bounded
   crossing representation;
2. distinct Tseitin residual vectors must be separated by genuine future SAT
   continuations of that run.

The imported crossing-bottleneck no-go explains why (1) cannot be postulated for
all cheap computations: storage access already forces exponential crossing-state
capacity.  Nothing here assumes such a universal normal form or proves `P != NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ExpanderCrossingContinuationHolonomy

open Finset Matrix Module
open PvsNPRunIndexedFaithfulTPhi
open CrossingSequenceContinuationHolonomy
open CrossingSequenceContinuationHolonomy.CrossingSequenceTraceFactorization

variable {V Edge ι Suf State : Type*}
variable [Fintype V] [DecidableEq V]
variable [Fintype Edge] [DecidableEq Edge]
variable [Fintype ι] [DecidableEq ι]

/-- The natural read-set Tseitin residual: an edge assignment is sent to the
vector of vertex parities on `w`, encoded as `Fin (2^|ι|)`. -/
noncomputable def expanderResidual
    (G : TseitinGraph V Edge) (w : ι → V) :
    (Edge → ZMod 2) → Fin (2 ^ Fintype.card ι) := by
  let M : Matrix ι Edge (ZMod 2) := fun i e => G.constraint (w i) e
  have hcard : Fintype.card (ι → ZMod 2) = 2 ^ Fintype.card ι := by
    rw [Fintype.card_fun, ZMod.card]
  let e := Fintype.equivFinOfCardEq hcard
  exact fun x => e (M.mulVecLin x)

/-- Expansion discharges residual non-collapse: the natural Tseitin residual
realises every one of its `2^|ι|` outcome vectors. -/
theorem expanderResidual_surjective
    (G : TseitinGraph V Edge) {c : Nat} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (w : ι → V) (hw : Function.Injective w)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V) :
    Function.Surjective (expanderResidual G w) := by
  classical
  let M : Matrix ι Edge (ZMod 2) := fun i e => G.constraint (w i) e
  have hindep : LinearIndependent (ZMod 2) M.row :=
    constraints_linearIndependent G hc hexp w hw hmed
  have hsurj : Function.Surjective M.mulVecLin :=
    mulVecLin_surjective_of_row_indep M hindep
  have hcard : Fintype.card (ι → ZMod 2) = 2 ^ Fintype.card ι := by
    rw [Fintype.card_fun, ZMod.card]
  let e := Fintype.equivFinOfCardEq hcard
  change Function.Surjective (fun x => e (M.mulVecLin x))
  exact e.surjective.comp hsurj

/-- **Concrete expander/crossing capacity.**  Once the actual trace semantics
separates distinct natural Tseitin residuals by future suffixes, every crossing
representation of the continuation-complete trace has enough capacity for all
`2^|ι|` residual outcomes. -/
theorem expander_residual_capacity_le_crossing_capacity
    [Inhabited Suf]
    (G : TseitinGraph V Edge) {c : Nat} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V)
    {R : ActualDecisionRun ((Edge → ZMod 2) × Suf) State}
    {g crossingWidth q : Nat}
    (F : CrossingSequenceTraceFactorization R g crossingWidth q)
    (hsemantic : ∀ x y,
      expanderResidual G readSet x ≠ expanderResidual G readSet y →
        ∃ s, R.finalAnswer (x, s) ≠ R.finalAnswer (y, s)) :
    2 ^ Fintype.card ι ≤ q ^ crossingWidth := by
  exact F.residual_capacity_le_crossing_capacity
    (expanderResidual G readSet)
    (expanderResidual_surjective G hc hexp readSet hread hmed)
    hsemantic

/-- Gap form: below the expander residual capacity, no continuation-complete
crossing representation with the stated physical/semantic factorisation exists. -/
theorem no_expander_factorization_below_capacity
    [Inhabited Suf]
    (G : TseitinGraph V Edge) {c : Nat} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V)
    {R : ActualDecisionRun ((Edge → ZMod 2) × Suf) State}
    {g crossingWidth q : Nat}
    (hsemantic : ∀ x y,
      expanderResidual G readSet x ≠ expanderResidual G readSet y →
        ∃ s, R.finalAnswer (x, s) ≠ R.finalAnswer (y, s))
    (hgap : q ^ crossingWidth < 2 ^ Fintype.card ι) :
    ¬ Nonempty (CrossingSequenceTraceFactorization R g crossingWidth q) := by
  rintro ⟨F⟩
  exact (Nat.not_le_of_lt hgap)
    (expander_residual_capacity_le_crossing_capacity
      G hc hexp readSet hread hmed F hsemantic)

end PallLean.Paper93.DeepMath.PathB.ExpanderCrossingContinuationHolonomy

#print axioms PallLean.Paper93.DeepMath.PathB.ExpanderCrossingContinuationHolonomy.expanderResidual_surjective
#print axioms PallLean.Paper93.DeepMath.PathB.ExpanderCrossingContinuationHolonomy.expander_residual_capacity_le_crossing_capacity
#print axioms PallLean.Paper93.DeepMath.PathB.ExpanderCrossingContinuationHolonomy.no_expander_factorization_below_capacity
