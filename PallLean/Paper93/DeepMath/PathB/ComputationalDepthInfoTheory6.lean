import PallLean.Paper93.DeepMath.PathB.ComputationalDepthInfoTheory5

/-!
# Information-theory foundations 6: transcript information cost (IC ≤ CC)

The first step of the protocol/transcript model.  A deterministic protocol on
inputs `γ` with transcript type `τ` is a function `f : γ → τ`; the transcript is
the random variable `f(X)`, whose distribution is the pushforward of the input
distribution.  For a deterministic transcript the information cost `I(X; f(X))`
equals `H(f(X))`, and the fundamental bound is `IC ≤ CC` (`H(f(X)) ≤ log #τ`).

* **`pushforward f p`** — the distribution of `f(X)`; **`pushforward_isProbDist`
  (proved)** — it is a distribution;
* **`infoCost f p := entropy (pushforward f p)`** — the information cost of the
  transcript (`= I(X; f(X))` for deterministic `f`);
* **`infoCost_nonneg` (proved)** — `IC ≥ 0`;
* **`infoCost_le_log_card` (proved)** — `IC ≤ log #τ`: **information cost is at
  most communication** (with `#τ ≤ 2^{CC}` this is `IC ≤ CC·log 2`).

Real analysis / finite sums, not `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.InfoTheory

open Real Finset

variable {γ τ : Type*} [Fintype γ] [Fintype τ]

/-- The pushforward of `p` along `f`: the distribution of `f(X)`. -/
noncomputable def pushforward [DecidableEq τ] (f : γ → τ) (p : γ → ℝ) : τ → ℝ :=
  fun t => ∑ x, if f x = t then p x else 0

theorem pushforward_isProbDist [DecidableEq τ] {f : γ → τ} {p : γ → ℝ}
    (hp : IsProbDist p) : IsProbDist (pushforward f p) := by
  refine ⟨fun t => Finset.sum_nonneg (fun x _ => ?_), ?_⟩
  · by_cases h : f x = t <;> simp [h, hp.1 x]
  · simp only [pushforward]
    rw [Finset.sum_comm]
    have hx : ∀ x, ∑ t, (if f x = t then p x else 0) = p x := by
      intro x; simp
    simp only [hx]
    exact hp.2

/-- The information cost of a deterministic transcript `f`: `H(f(X)) = I(X; f(X))`. -/
noncomputable def infoCost [DecidableEq τ] (f : γ → τ) (p : γ → ℝ) : ℝ :=
  entropy (pushforward f p)

theorem infoCost_nonneg [DecidableEq τ] {f : γ → τ} {p : γ → ℝ} (hp : IsProbDist p) :
    0 ≤ infoCost f p :=
  entropy_nonneg (pushforward_isProbDist hp)

/-- **Information cost is at most communication (proved)**: `IC ≤ log #τ`. -/
theorem infoCost_le_log_card [DecidableEq τ] [Nonempty τ] {f : γ → τ} {p : γ → ℝ}
    (hp : IsProbDist p) : infoCost f p ≤ Real.log (Fintype.card τ) :=
  entropy_le_log_card (pushforward_isProbDist hp)

end PallLean.Paper93.DeepMath.PathB.InfoTheory

#print axioms PallLean.Paper93.DeepMath.PathB.InfoTheory.pushforward_isProbDist
#print axioms PallLean.Paper93.DeepMath.PathB.InfoTheory.infoCost_le_log_card
