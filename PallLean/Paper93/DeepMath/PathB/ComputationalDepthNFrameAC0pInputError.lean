import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameFpAmplify

/-!
# The input-level per-gate error bound (RS repair, step 3 — the analytic core)

`NFrameAC0pApproximator` assembled `ErrAdditive` from per-gate local-error *hypotheses* `localErr ≤ B`.  This
file proves the analytic content that turns the OR hypothesis into a **theorem**: for an OR gate applied to any
family of children values `v x : Fin k → Bool` (as a function of the input `x`), there is a *fixed* seed of `t`
weight vectors whose amplified OR detector errs on at most `2^n / p^t` inputs.

The clean formulation: the amplified OR detector's Boolean readout

```text
  orReadout W b  :=  decide (∃ j, linForm (W j) b ≠ 0)
```

errs against `ORb` exactly on `{ b | ORb b ∧ ∀ j, linForm (W j) b = 0 }` (`orReadout_err`) — the input is a `1`
of the OR but every one of the `t` linear forms vanishes.  Applying the abstract averaging `amplify` over the
**inputs** (`I = Fin n → Bool`), with the per-input `1/p` fiber bound `linForm_fiber_bound` supplying
`hbound`, gives a seed `W` with

```text
  p^t · #{ x | orReadout W (v x) ≠ ORb (v x) }  ≤  2^n     (or_input_error_bound).
```

This is the input-level per-gate error bound: for a good seed the OR gate errs on `≤ 2^n·p^{-t}` inputs.  It is
what discharges the OR local-error hypothesis of `approx_ErrAdditive` (via a per-gate seed chosen from this `∃`).

## Honest scope

The **OR** gate's input-level error bound, proved end to end via `amplify` + `linForm_fiber_bound`.  The AND and
MOD gates are dual (the "some input is `0`" form, resp. the `MOD_p` Fermat detector) and are not done here; nor
is the `List`↔`Fin` wiring that plugs `or_input_error_bound` into the `List`-based approximator's `loc` to make
`hAnd/hOr/hMod` literal theorems.  Those are the remaining (mechanical) glue.  No ACC⁰ lower bound.  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameAC0pInputError

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameFpDegree
open PallLean.Paper93.DeepMath.PathB.NFrameFpANDOR
open PallLean.Paper93.DeepMath.PathB.NFrameFpAmplify

section
variable (p : Nat) [Fact p.Prime]

/-- The Boolean readout of the amplified OR detector: fires iff some of the `t` linear forms is nonzero. -/
def orReadout {k t : Nat} (W : Fin t → (Fin k → ZMod p)) (b : Fin k → Bool) : Bool :=
  decide (∃ j, linForm p (W j) b ≠ 0)

/-- The linear form vanishes on the all-`false` vector. -/
theorem linForm_zero_of_ORb_false {k : Nat} (w : Fin k → ZMod p) (b : Fin k → Bool)
    (hb : ORb b = false) : linForm p w b = 0 := by
  simp only [linForm]
  apply Finset.sum_eq_zero
  intro i _
  rw [forall_false_of_ORb_false b hb i]
  simp [boolToZMod]

/-- **The readout's error set.**  `orReadout W b` disagrees with `ORb b` exactly when `b` is a `1` of OR but all
`t` linear forms vanish on it. -/
theorem orReadout_err {k t : Nat} (W : Fin t → (Fin k → ZMod p)) (b : Fin k → Bool) :
    (orReadout p W b ≠ ORb b) ↔ (ORb b = true ∧ ∀ j, linForm p (W j) b = 0) := by
  by_cases hor : ORb b = true
  · simp [orReadout, hor]
  · have hbf : ORb b = false := by
      cases h : ORb b
      · rfl
      · exact absurd h hor
    have hro : orReadout p W b = false := by
      simp only [orReadout, decide_eq_false_iff_not, not_exists, not_not]
      exact fun j => linForm_zero_of_ORb_false p (W j) b hbf
    rw [hbf, hro]; simp

/-- **The input-level per-gate error bound for OR.**  For any children-value family `v`, there is a fixed seed
`W` of `t` weight vectors whose amplified OR readout errs on at most `2^n / p^t` inputs. -/
theorem or_input_error_bound {n k t : Nat} (ht : 0 < t) (v : (Fin n → Bool) → (Fin k → Bool)) :
    ∃ W : Fin t → (Fin k → ZMod p),
      p ^ t * (univ.filter (fun x : Fin n → Bool => orReadout p W (v x) ≠ ORb (v x))).card ≤ 2 ^ n := by
  classical
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have hΩ : 0 < Fintype.card (Fin k → ZMod p) := Fintype.card_pos
  obtain ⟨W, hW⟩ := amplify (I := Fin n → Bool) (Ω := Fin k → ZMod p) p t
    (fun w x => ORb (v x) = true ∧ linForm p w (v x) = 0) hΩ (by
      intro x
      show p * (univ.filter (fun w : Fin k → ZMod p => ORb (v x) = true ∧ linForm p w (v x) = 0)).card
        ≤ Fintype.card (Fin k → ZMod p)
      rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
      by_cases hz : ORb (v x) = true
      · obtain ⟨j, hj⟩ : ∃ j, (v x) j = true := by
          simpa only [ORb, decide_eq_true_eq] using hz
        have hfe : (univ.filter (fun w : Fin k → ZMod p => ORb (v x) = true ∧ linForm p w (v x) = 0))
            = (univ.filter (fun w : Fin k → ZMod p => linForm p w (v x) = 0)) := by
          apply Finset.filter_congr; intro w _; simp [hz]
        rw [hfe]
        exact linForm_fiber_bound p (v x) j hj
      · have hfe : (univ.filter (fun w : Fin k → ZMod p => ORb (v x) = true ∧ linForm p w (v x) = 0)) = ∅ := by
          apply Finset.filter_false_of_mem; intro w _; simp [hz]
        rw [hfe]; simp)
  refine ⟨W, ?_⟩
  have hset : (univ.filter (fun x : Fin n → Bool => orReadout p W (v x) ≠ ORb (v x)))
      = (univ.filter (fun x : Fin n → Bool => ∀ j, ORb (v x) = true ∧ linForm p (W j) (v x) = 0)) := by
    apply Finset.filter_congr
    intro x _
    rw [orReadout_err]
    obtain ⟨j0⟩ := Fin.pos_iff_nonempty.mp ht
    constructor
    · rintro ⟨h1, h2⟩ j; exact ⟨h1, h2 j⟩
    · intro h; exact ⟨(h j0).1, fun j => (h j).2⟩
  rw [hset]
  rwa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hW

end

end PallLean.Paper93.DeepMath.PathB.NFrameAC0pInputError

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameAC0pInputError.orReadout_err
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameAC0pInputError.or_input_error_bound
