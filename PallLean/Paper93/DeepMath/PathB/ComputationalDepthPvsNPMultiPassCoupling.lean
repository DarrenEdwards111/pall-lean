import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPCouplingTheorem

/-!
# Multi-pass coupling: from one cut to bounded-width, bounded-pass

The one-cut coupling theorem bounds the boundary state of a decider whose decision factors through **one**
crossing of the prefix/suffix cut.  A bounded-width machine that makes several passes over the input crosses
the cut several times, so the decision factors through the **crossing transcript** — the tuple of states the
machine is in at each crossing — which lives in `Fin passes → State` and has at most `width ^ passes` values.

The coupling generalises with no new idea: the crossing transcript is a sufficient statistic
(`crossing_sufficient`), so `sufficient_card_ge_fooling` gives the standard multi-pass tradeoff

```text
width ^ passes  ≥  |fooling set|      (equivalently  passes · log₂ width ≥ log₂ |fooling|).
```

For the concrete `equalityCNF` SAT family this is `width ^ passes ≥ 2^n`, i.e. a `passes`-pass width-`width`
decider needs `passes · log₂ width ≥ n`.  The one-cut theorem is the `passes = 1` case (`ofOneCut`).

## Honest scope

A genuine bounded-width **multi-pass** communication / streaming lower bound for the equality-CNF SAT family.
It still does **not** reach `P`: the bound only bites while `passes · log width < n` (total crossing
information below `n` bits).  A `P`-time machine has *both* polynomially many passes/steps *and* polynomial
workspace (`width` up to `2^poly`), so `width ^ passes ≥ 2^n` is satisfied trivially — no contradiction.
The obstruction is the same as before: `crossing_sufficient` needs the decision to factor through a *bounded*
transcript with no side channel, which fails once workspace and pass count both grow with `n`.
Not `SAT ∉ P`, not `P ≠ NP`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPMultiPassCoupling

open PallLean.Paper93.DeepMath.PathB.PvsNPBoundaryFoolingWidthLB
open PallLean.Paper93.DeepMath.PathB.PvsNPSATBoundaryFoolingWidthLB
open PallLean.Paper93.DeepMath.PathB.PvsNPCouplingTheorem
open SATDepthMachine

/-- A bounded-width decider making `passes` crossings of the prefix/suffix cut.  The decision factors through
the **crossing transcript** `crossing a : Fin passes → State` (one width-`|State|` state per crossing). -/
structure MultiPassDecider (p q passes : Nat) where
  State : Type
  fintype : Fintype State
  crossing : (Fin p → Bool) → (Fin passes → State)
  decide : (Fin passes → State) → (Fin q → Bool) → Bool

namespace MultiPassDecider

/-- The decided value: cross the cut `passes` times, then answer the suffix from the transcript. -/
def eval {p q passes : Nat} (D : MultiPassDecider p q passes)
    (a : Fin p → Bool) (b : Fin q → Bool) : Bool :=
  D.decide (D.crossing a) b

/-- **The multi-pass coupling.**  The crossing transcript is a sufficient statistic for the decision: the
decision factors through it, so nothing decision-relevant escapes the `passes` crossings. -/
theorem crossing_sufficient {p q passes : Nat} (D : MultiPassDecider p q passes) :
    SufficientStatistic D.crossing D.eval := by
  intro a₁ a₂ h b
  simp only [MultiPassDecider.eval, h]

end MultiPassDecider

/-- **Multi-pass coupling lower bound.**  A bounded-width `passes`-pass decider computing `f` has
`width ^ passes ≥ |fooling set|`. -/
theorem width_pow_passes_ge_fooling {p q passes : Nat} (D : MultiPassDecider p q passes)
    {f : (Fin p → Bool) → (Fin q → Bool) → Bool} (hf : ∀ a b, D.eval a b = f a b)
    {Sset : Finset (Fin p → Bool)} (hfool : Fooling f Sset) :
    Sset.card ≤ (@Fintype.card D.State D.fintype) ^ passes := by
  letI := D.fintype
  have hsuff : SufficientStatistic D.crossing f := by
    intro a₁ a₂ h b
    rw [← hf a₁ b, ← hf a₂ b]
    exact D.crossing_sufficient a₁ a₂ h b
  have h := sufficient_card_ge_fooling hsuff hfool
  rwa [Fintype.card_fun, Fintype.card_fin] at h

/-- `EQ`-decision from a SAT-satisfiability equivalence (works for any decision function). -/
theorem eval_eq_EQ_of_satIff {n : Nat} (g : (Fin n → Bool) → (Fin n → Bool) → Bool)
    (h : ∀ a b, g a b = true ↔ Satisfiable (equalityCNF a b)) :
    ∀ a b, g a b = EQ n a b := by
  intro a b
  apply Bool.eq_iff_iff.mpr
  rw [h a b, equalityCNF_satisfiable_iff]
  simp [EQ]

/-- **Multi-pass SAT tradeoff.**  Any bounded-width `passes`-pass decider correct on the `equalityCNF` family
satisfies `width ^ passes ≥ 2^n`. -/
theorem equalitySAT_multipass_lower_bound (n passes : Nat) (D : MultiPassDecider n n passes)
    (hSAT : ∀ a b, D.eval a b = true ↔ Satisfiable (equalityCNF a b)) :
    2 ^ n ≤ (@Fintype.card D.State D.fintype) ^ passes := by
  have hf : ∀ a b, D.eval a b = EQ n a b := eval_eq_EQ_of_satIff D.eval hSAT
  have h := width_pow_passes_ge_fooling D hf (fooling_EQ n)
  rwa [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h

/-! ## The one-cut theorem is the `passes = 1` case -/

/-- Embed a one-cut decider as a single-pass multi-pass decider. -/
def ofOneCut {p q : Nat} (D : LayeredBoundaryDecider p q) : MultiPassDecider p q 1 where
  State := D.State
  fintype := D.fintype
  crossing := fun a _ => D.mid a
  decide := fun t b => D.finish (t 0) b

theorem ofOneCut_eval {p q : Nat} (D : LayeredBoundaryDecider p q) (a : Fin p → Bool)
    (b : Fin q → Bool) : (ofOneCut D).eval a b = D.eval a b := rfl

/-- With `passes = 1`, the multi-pass bound is exactly the one-cut bound `width ≥ |fooling|`. -/
theorem oneCut_special_case {p q : Nat} (D : LayeredBoundaryDecider p q)
    {f : (Fin p → Bool) → (Fin q → Bool) → Bool} (hf : ∀ a b, D.eval a b = f a b)
    {Sset : Finset (Fin p → Bool)} (hfool : Fooling f Sset) :
    Sset.card ≤ @Fintype.card D.State D.fintype := by
  have h := width_pow_passes_ge_fooling (ofOneCut D)
    (f := f) (fun a b => (ofOneCut_eval D a b).trans (hf a b)) hfool
  simpa using h

end PallLean.Paper93.DeepMath.PathB.PvsNPMultiPassCoupling

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPMultiPassCoupling.width_pow_passes_ge_fooling
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPMultiPassCoupling.equalitySAT_multipass_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPMultiPassCoupling.oneCut_special_case
