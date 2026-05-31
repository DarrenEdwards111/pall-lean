import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRestrictionStarCount
import Mathlib.Tactic.Ring

/-!
# The binomial layer-ratio (analytic core of the switching count)

**STATUS: REAL COMBINATORIAL CORE.  AN HONEST CAVEAT ON THE LABEL FACTOR.**

The switching count compares the `t`-star layer `C(N,t)·2^(N-t)` to the
`(t-s)`-star layer `C(N,t-s)·2^(N-t+s)`.  Dividing, the decisive ratio is
`C(N,t-s)/C(N,t)`, bounded here:

  `C(N, t-s) · (N-t+1)^s ≤ C(N, t) · t^s`   (for `s ≤ t ≤ N`),

i.e. `C(N,t-s)/C(N,t) ≤ (t/(N-t+1))^s`.  With `t ≈ pN` this is `≈ p^s` — the
multiplicative gain per restricted star.  Proof: iterate the Pascal recurrence
`C(N,k+1)·(k+1) = C(N,k)·(N-k)` `s` times.

**Honest caveat (a real finding, not a socket).**  This ratio is the genuine
combinatorial core, but it does **not** close the switching gate against the
*loose* label bound `((2^w)^m)^numTerms` proved earlier: that bound is exponential
in the whole circuit size, whereas `(t/(N-t+1))^{-s}` only gains `≈ (1/p)^s`.  The
gate needs the *tight* Håstad label `(2w)^s` (a label per path step, `≈ w` choices
each, over a path of length `≤ s`) — re-deriving that tighter `circuitLabelSpace`
is the actual remaining quantitative work.  This file supplies the ratio it will
be combined with; it does not claim the gate is discharged.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

/-- **Binomial layer-ratio.**  Iterating the Pascal recurrence: for `s ≤ t ≤ N`,
`C(N, t-s) · (N-t+1)^s ≤ C(N, t) · t^s`. -/
theorem binom_layer_ratio {N : ℕ} : ∀ (s t : ℕ), s ≤ t → t ≤ N →
    Nat.choose N (t - s) * (N - t + 1) ^ s ≤ Nat.choose N t * t ^ s := by
  intro s
  induction s with
  | zero => intro t _ _; simp
  | succ s ih =>
    intro t hst ht
    have hstep : Nat.choose N (t - (s + 1)) * (N - t + 1) ≤ Nat.choose N (t - s) * t := by
      have hrec := Nat.choose_succ_right_eq N (t - (s + 1))
      have he1 : (t - (s + 1)) + 1 = t - s := by omega
      have he2 : N - (t - (s + 1)) = N - t + s + 1 := by omega
      rw [he1, he2] at hrec
      calc Nat.choose N (t - (s + 1)) * (N - t + 1)
          ≤ Nat.choose N (t - (s + 1)) * (N - t + s + 1) := mul_le_mul_left' (by omega) _
        _ = Nat.choose N (t - s) * (t - s) := hrec.symm
        _ ≤ Nat.choose N (t - s) * t := mul_le_mul_left' (by omega) _
    have ihs : Nat.choose N (t - s) * (N - t + 1) ^ s ≤ Nat.choose N t * t ^ s :=
      ih t (by omega) ht
    calc Nat.choose N (t - (s + 1)) * (N - t + 1) ^ (s + 1)
        = (Nat.choose N (t - (s + 1)) * (N - t + 1)) * (N - t + 1) ^ s := by ring
      _ ≤ (Nat.choose N (t - s) * t) * (N - t + 1) ^ s := mul_le_mul_right' hstep _
      _ = t * (Nat.choose N (t - s) * (N - t + 1) ^ s) := by ring
      _ ≤ t * (Nat.choose N t * t ^ s) := mul_le_mul_left' ihs _
      _ = Nat.choose N t * t ^ (s + 1) := by ring

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.binom_layer_ratio
