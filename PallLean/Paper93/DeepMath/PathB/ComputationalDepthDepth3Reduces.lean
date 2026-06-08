import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LayerCollapseWF

/-!
# AC⁰ reduction, foundation 20: the multi-round reduction spine (branch only)

The combinator that chains the per-round layer collapses into a full depth reduction.  Each round
(bricks 17/19) replaces a tower by a shallower one on *its* subcube, producing its own restriction `ρ`.
The eval-chain only needs the evaluation point `x` to lie in **every** round's subcube simultaneously — it
does *not* need the restrictions to be composed/disjoint (`composeR`) at the equivalence level.  So we
model a `d`-round reduction as the reflexive-transitive closure of one subcube-equivalence step, all valid
at a fixed `x`:

* `Reduces x C C'` — `C` reduces to `C'` through a sequence of subcube-equivalences, each holding at `x`.
* `Reduces.eval_eq` — hence `C` and `C'` compute the same value at `x`.
* `Reduces.trans` / `Reduces.head` — compose chains / prepend one collapse step.

A caller iterates a fixed number of `collapse_*_layer_wf` rounds (each preserving the switching hypotheses
by bricks 15/18/19), `obtain`s each round's `ρ`, and assembles the chain via `Reduces.head`; `eval_eq`
then transports any property of the depth-2 endpoint back to the original tower at every `x` in the
intersection subcube.

## Honest scope

This is the *equivalence* spine: it transports values across the rounds on the common subcube.  It does
**not** by itself reach `parity ∉ AC⁰`.  Two genuine pieces remain: a uniform tower datatype to feed the
chain across rounds, and — for the final contradiction — a *coordinate budget* guaranteeing the common
subcube still has a free variable after `d` rounds.  The latter needs **subcube-relative** switching (each
round applied only to the previous round's free coordinates), which `exists_shallow_all` (a full-domain
restriction) does not yet provide.  We do not paper over that gap.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

namespace Layered

variable {n : ℕ}

/-- `C` reduces to `C'` at `x` through a sequence of subcube-equivalence steps, each valid at `x`. -/
inductive Reduces (x : Fin n → Bool) : Layered n → Layered n → Prop where
  | refl (C : Layered n) : Reduces x C C
  | step (C C' C'' : Layered n) (ρ : Fin n → Option Bool) :
      EquivOn ρ C C' → DTree.agreeRestriction ρ x → Reduces x C' C'' → Reduces x C C''

/-- **The reduction transports values.**  A reduction at `x` equates the endpoints' values at `x`. -/
theorem Reduces.eval_eq {x : Fin n → Bool} {C C' : Layered n} (h : Reduces x C C') :
    eval C x = eval C' x := by
  induction h with
  | refl C => rfl
  | step C C' C'' ρ heq hag _ ih => rw [heq x hag]; exact ih

/-- A single collapse step (an `EquivOn` valid at `x`) is a one-step reduction. -/
theorem Reduces.head {x : Fin n → Bool} {C C' : Layered n} {ρ : Fin n → Option Bool}
    (heq : EquivOn ρ C C') (hag : DTree.agreeRestriction ρ x) : Reduces x C C' :=
  Reduces.step C C' C' ρ heq hag (Reduces.refl C')

/-- Reductions compose. -/
theorem Reduces.trans {x : Fin n → Bool} {C C' C'' : Layered n}
    (h1 : Reduces x C C') (h2 : Reduces x C' C'') : Reduces x C C'' := by
  induction h1 with
  | refl C => exact h2
  | step C C' C'' ρ heq hag _ ih => exact Reduces.step C C' _ ρ heq hag (ih h2)

/-- Prepend one collapse step to a reduction. -/
theorem Reduces.cons {x : Fin n → Bool} {C C' C'' : Layered n} {ρ : Fin n → Option Bool}
    (heq : EquivOn ρ C C') (hag : DTree.agreeRestriction ρ x) (h : Reduces x C' C'') :
    Reduces x C C'' :=
  Reduces.step C C' C'' ρ heq hag h

end Layered

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.Reduces.eval_eq
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.Reduces.trans
