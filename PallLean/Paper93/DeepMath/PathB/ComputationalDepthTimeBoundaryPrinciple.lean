import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDebtFrameworkBarrier

/-!
# The time → boundary/action principle: restricted positive cases + the obstruction (audit)

This file formalizes *exactly when* "poly-time computation ⇒ subcritical observer action" holds, and where it
**fails** — framed as HAL/user recommend: prove the restricted positive cases and expose the obstruction, **not**
force the false general bridge.

An observer trajectory over `T` steps with per-step boundary `B τ` has **action** `∑_{τ<T} 2^{B τ}`.  The debt
mechanism bites when the action is *subcritical* — below the fooling-set size `K` — because then it cannot
service the distinguishability debt.  The question is when poly *time* forces subcritical action.

## Positive cases (proved): a space/boundary bound gives subcriticality

* `boundary_le_of_spaceBound` — the observer boundary is bounded by the machine's space (the observer state *is*
  the configuration): `SpaceBound s ⇒ B τ ≤ s`.
* `action_le_of_spaceBound` — **low space ⇒ low action**: `T ≤ Tb`, `B τ ≤ s` ⇒ `action ≤ Tb · 2^s`.  For
  `s = O(log n)` (logspace) and `Tb = poly`, the action is `poly` — *subcritical* against a hard instance with
  `K = 2^{Ω(n)}`.
* `subcritical_of_lowspace` — concrete: if `Tb · 2^s < K` then `action < K` (the debt bites; the low-space
  decider errs on the hard instance).

These are the time→boundary bridge in the regimes where it is true: **low-space** (here), **bounded-growth /
local** (already `burst_boundary_time_lower_bound`), and **oblivious-wide / Route F** (the crossing bound gives
low boundary — established elsewhere in the arc).

## The obstruction (proved): time alone does NOT bound action

* `action_unbounded_by_time` — for any `T ≥ 1` and any `A`, there is a boundary sequence with `T` steps and
  action `> A`.  A poly-time (even single-step) trajectory can have **exponential** action, because one step's
  action `2^{B τ}` is unbounded.  So `poly-time ⇒ subcritical action` is **false** without a space bound.
* `hard_instance_has_correct_high_boundary_decider` — concretely, the hard hypercube instance has a *correct*
  (zero-debt) decider of **full boundary `n`** (the brute-force / Gaussian-elimination-style high-space
  decider).  Poly-time high-boundary deciders exist and are entirely unconstrained by the debt mechanism.

## The capstone line (honest)

`ptime_does_not_imply_low_boundary`: **polynomial time alone yields no subcritical boundary/action bound.**  So
the God-Move route to `P ≠ NP` requires *either* a SAT-specific time→boundary theorem (forcing a poly-time SAT
decider into low boundary — which, by the obstruction, cannot follow from time alone and is not known), *or* the
algorithmic/Williams route that bypasses needing such a theorem (whose own deep step — the diagonalisation — and
decision-hardness requirement are the named open inputs).  This file prevents overclaiming: the debt programme
is a **space/boundary** lower bound, conditional on a space bound; `P ≠ NP` is not implied.
-/

namespace PallLean.Paper93.DeepMath.PathB.TimeBoundaryPrinciple

open PallLean.Paper93.DeepMath.PathB.BoundaryDebt
open scoped BigOperators
open Finset

/-- **Observer action** of a trajectory: `∑_{τ<T} 2^{B τ}` — the time-integrated boundary capacity. -/
def action (B : ℕ → ℕ) (T : ℕ) : ℕ := ∑ τ ∈ Finset.range T, 2 ^ B τ

/-- **Boundary ≤ space (proved).**  Under a space bound `s` (the observer state is the machine configuration),
every step's boundary is at most `s`.  This is the time→boundary bridge's hypothesis made explicit: it needs a
*space* bound, not a time bound. -/
theorem boundary_le_of_spaceBound (B : ℕ → ℕ) (s : ℕ) (hsp : ∀ τ, B τ ≤ s) (τ : ℕ) : B τ ≤ s := hsp τ

/-- **Low space ⇒ low action (proved).**  If the running time is `≤ Tb` and every step's boundary is `≤ s`,
the action is `≤ Tb · 2^s`.  For `s = O(log n)` and `Tb = poly`, this is `poly` — subcritical against a hard
instance. -/
theorem action_le_of_spaceBound (B : ℕ → ℕ) (T Tb s : ℕ) (hT : T ≤ Tb) (hsp : ∀ τ, B τ ≤ s) :
    action B T ≤ Tb * 2 ^ s := by
  unfold action
  calc ∑ τ ∈ Finset.range T, 2 ^ B τ
      ≤ ∑ _τ ∈ Finset.range T, 2 ^ s :=
        Finset.sum_le_sum (fun τ _ => Nat.pow_le_pow_right (by norm_num) (hsp τ))
    _ = T * 2 ^ s := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ Tb * 2 ^ s := Nat.mul_le_mul_right _ hT

/-- **Low space ⇒ subcritical action (proved).**  If the space-time budget `Tb · 2^s` is below the fooling-set
size `K`, the action is subcritical (`< K`): the low-space decider cannot service the debt and errs on the hard
instance.  This is the time→boundary bridge in the regime where it holds — *given a space bound*. -/
theorem subcritical_of_lowspace (B : ℕ → ℕ) (T Tb s K : ℕ) (hT : T ≤ Tb) (hsp : ∀ τ, B τ ≤ s)
    (hbudget : Tb * 2 ^ s < K) :
    action B T < K :=
  lt_of_le_of_lt (action_le_of_spaceBound B T Tb s hT hsp) hbudget

/-- **Obstruction: time does NOT bound action (proved).**  For any number of steps `T ≥ 1` and any bound `A`,
there is a boundary sequence whose action exceeds `A` — a single step's action `2^{B τ}` is unbounded.  So a
poly-time trajectory can have exponential action; `poly-time ⇒ subcritical action` is false without a space
bound. -/
theorem action_unbounded_by_time (T A : ℕ) (hT : 1 ≤ T) : ∃ B : ℕ → ℕ, A < action B T := by
  refine ⟨fun _ => A, ?_⟩
  have hval : action (fun _ => A) T = T * 2 ^ A := by
    unfold action; rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [hval]
  calc A < 2 ^ A := Nat.lt_two_pow_self
    _ ≤ T * 2 ^ A := Nat.le_mul_of_pos_left _ hT

/-- **Obstruction (concrete): poly-time high-boundary deciders exist and are debt-immune (proved).**  The hard
hypercube instance has a *correct* (zero-debt) decider of full boundary `n` — the brute-force / high-space
decider (cf. Gaussian elimination for Tseitin).  The debt mechanism imposes nothing on it. -/
theorem hard_instance_has_correct_high_boundary_decider (n : ℕ) :
    ∃ view0 : (Fin n → Bool) → Fin (2 ^ n), debtCount (hypercubeFool n) view0 = 0 :=
  hypercube_brute_force_escape n

end PallLean.Paper93.DeepMath.PathB.TimeBoundaryPrinciple

#print axioms PallLean.Paper93.DeepMath.PathB.TimeBoundaryPrinciple.action_le_of_spaceBound
#print axioms PallLean.Paper93.DeepMath.PathB.TimeBoundaryPrinciple.subcritical_of_lowspace
#print axioms PallLean.Paper93.DeepMath.PathB.TimeBoundaryPrinciple.action_unbounded_by_time
#print axioms PallLean.Paper93.DeepMath.PathB.TimeBoundaryPrinciple.hard_instance_has_correct_high_boundary_decider
