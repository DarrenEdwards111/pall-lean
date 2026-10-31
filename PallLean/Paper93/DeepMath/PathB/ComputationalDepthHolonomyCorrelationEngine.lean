import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCWilliamsCorrelationTarget

/-!
# The holonomy‑correlation engine — measure bias, not classes

A new engine for ACC⁰, beyond rank‑counting: **high holonomy rank should force low correlation** against
predictors whose outputs factor through few classes (low‑dimensional statistics).  We measure *agreement*, not
class counts.

A predictor is `g ∘ π` — a value `g c` constant on each class `c` of a class map `π` (a low‑rank predictor has
few classes).  Its agreement with a target `f` is `#{x : g(π x) = f x}`.

## What is proved (clean axioms, no `sorry`) — the seed

* `agreement_le_sum_majority` — **the correlation bridge**: a class‑constant predictor agrees with `f` on at most
  the sum, over its classes, of the per‑class **majority** of `f`.  (Within each class the predictor's single
  value matches at most the majority; sum over the fibre partition.)
* `low_rank_predictor_low_correlation_with_full_holonomy` — **the seed**: if `f` is **balanced on every predictor
  class** (each class has equally many `f = true` and `f = false`), then `2 · agreement ≤ #inputs` — the predictor
  correlates at `≈ ½`, i.e. has **no advantage**.  This is correlation forced by the predictor's coarseness, not
  by counting functions.

## The holonomy connection

The hard side (`…HolonomyHardEffectiveRank`) gives a target realizing `2^m` holonomy signatures.  A predictor of
rank `r < m` has `≤ 2^r` classes — *coarser* than the target — so (the open step) the target stays **balanced in
each predictor class**, and `low_rank_predictor_low_correlation_with_full_holonomy` forces correlation `≈ ½`.  The
proved engine is the bridge + the balanced payoff; the open piece is **balance‑per‑class from the rank gap**
(`m > r ⇒ f balanced in the predictor's `2^r` classes`) — and, for ACC⁰, that ACC⁰ predictors are low‑rank /
low‑dimensional after approximation.  Both are `NP ⊄ ACC⁰`‑strength
(`ACC0CorrelationAgainstTseitin`, `…ACCWilliamsCorrelationTarget`), under the naturalness ceiling.

## Honest scope

The engine itself — *coarse predictor + balanced target ⇒ no correlation advantage* — is proved.  It runs on any
predictor and target with the balance property; instantiating it needs the rank‑gap‑forces‑balance step (open) and
the ACC⁰‑predictors‑are‑low‑rank step (open).  This is the right engine to try on fragments next (log‑gate,
read‑once), where balance‑per‑class may be establishable; it is the seed, not the theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB.HolonomyCorrelationEngine

open PallLean.Paper93.DeepMath.PathB.ACCWilliamsCorrelationTarget

variable {ι C : Type*}

/-- A class's `f = true` and `f = false` counts partition it. -/
theorem filter_true_add_false (S : Finset ι) (f : ι → Bool) :
    (S.filter (fun x => f x = true)).card + (S.filter (fun x => f x = false)).card = S.card := by
  have h : (S.filter (fun x => f x = false)) = (S.filter (fun x => ¬ f x = true)) :=
    Finset.filter_congr (fun x _ => by cases f x <;> simp)
  rw [h, Finset.card_filter_add_card_filter_not]

/-- **The correlation bridge (proved): a class‑constant predictor agrees with `f` on ≤ the sum of per‑class
majorities.** -/
theorem agreement_le_sum_majority [DecidableEq C] (Inputs : Finset ι) (π : ι → C) (g : C → Bool) (f : ι → Bool) :
    (Inputs.filter (fun x => g (π x) = f x)).card
      ≤ ∑ c ∈ Inputs.image π,
          max ((Inputs.filter (fun x => π x = c)).filter (fun x => f x = true)).card
              ((Inputs.filter (fun x => π x = c)).filter (fun x => f x = false)).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
      (f := π) (t := Inputs.image π)
      (fun x hx => Finset.mem_image_of_mem π (Finset.mem_filter.mp hx).1)]
  apply Finset.sum_le_sum
  intro c _
  refine le_trans (Finset.card_le_card ?_)
    (class_agreement_le_majority (Inputs.filter (fun x => π x = c)) f (g c))
  intro x hx
  rw [Finset.mem_filter, Finset.mem_filter] at hx ⊢
  obtain ⟨⟨hxI, hgf⟩, hπc⟩ := hx
  refine ⟨⟨hxI, hπc⟩, ?_⟩
  rw [← hπc]
  exact hgf

/-- **The seed (proved): a coarse predictor has no correlation advantage on a per‑class‑balanced target.**  If the
target `f` is balanced on each predictor class (equal `f = true` and `f = false` counts), then
`2 · agreement ≤ #inputs`: the predictor agrees `≈ ½` — no advantage.  Correlation forced by the predictor's
coarseness via `agreement_le_sum_majority`. -/
theorem low_rank_predictor_low_correlation_with_full_holonomy [DecidableEq C]
    (Inputs : Finset ι) (π : ι → C) (g : C → Bool) (f : ι → Bool)
    (hbal : ∀ c ∈ Inputs.image π,
      ((Inputs.filter (fun x => π x = c)).filter (fun x => f x = true)).card
        = ((Inputs.filter (fun x => π x = c)).filter (fun x => f x = false)).card) :
    2 * (Inputs.filter (fun x => g (π x) = f x)).card ≤ Inputs.card := by
  classical
  have hagr := agreement_le_sum_majority Inputs π g f
  have hfib : Inputs.card = ∑ c ∈ Inputs.image π, (Inputs.filter (fun x => π x = c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image_of_mem π hx)
  calc 2 * (Inputs.filter (fun x => g (π x) = f x)).card
      ≤ 2 * ∑ c ∈ Inputs.image π,
          max ((Inputs.filter (fun x => π x = c)).filter (fun x => f x = true)).card
              ((Inputs.filter (fun x => π x = c)).filter (fun x => f x = false)).card :=
        Nat.mul_le_mul (le_refl 2) hagr
    _ = ∑ c ∈ Inputs.image π,
          2 * max ((Inputs.filter (fun x => π x = c)).filter (fun x => f x = true)).card
                  ((Inputs.filter (fun x => π x = c)).filter (fun x => f x = false)).card := by
        rw [Finset.mul_sum]
    _ = ∑ c ∈ Inputs.image π, (Inputs.filter (fun x => π x = c)).card := by
        apply Finset.sum_congr rfl
        intro c hc
        have hb := hbal c hc
        have hpart := filter_true_add_false (Inputs.filter (fun x => π x = c)) f
        rw [hb, max_self]
        omega
    _ = Inputs.card := hfib.symm

end PallLean.Paper93.DeepMath.PathB.HolonomyCorrelationEngine

#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyCorrelationEngine.agreement_le_sum_majority
#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyCorrelationEngine.low_rank_predictor_low_correlation_with_full_holonomy
