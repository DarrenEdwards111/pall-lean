import PallLean.Paper93.DeepMath.PathB.ComputationalDepthInfoTheory6

/-!
# Information-theory foundations 7: the data-processing inequality

Post-processing cannot increase entropy: `H(f(X)) ≤ H(X)`.  This rests on the
subadditivity of `negMulLog` (equivalently, superadditivity of `x ↦ x log x`),
applied fiberwise to the pushforward.

* **`negMulLog_add_le` (proved)** — `negMulLog(a+b) ≤ negMulLog a + negMulLog b`;
* **`negMulLog_sum_le` (proved)** — the finite version over a `Finset`;
* **`entropy_pushforward_le_entropy` (proved)** — `H(f(X)) ≤ H(X)`;
* **`infoCost_le_entropy` (proved)** — the transcript information cost is at most
  the input entropy.

Real analysis / finite sums, not `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.InfoTheory

open Real Finset

/-- **`negMulLog` is subadditive (proved)**: `negMulLog(a+b) ≤ negMulLog a + negMulLog b`. -/
theorem negMulLog_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.negMulLog (a + b) ≤ Real.negMulLog a + Real.negMulLog b := by
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · rw [← ha0]; simp
  · rcases eq_or_lt_of_le hb with hb0 | hbpos
    · rw [← hb0]; simp
    · have hab : 0 < a + b := by linarith
      rw [Real.negMulLog, Real.negMulLog, Real.negMulLog]
      have h1 : a * Real.log a ≤ a * Real.log (a + b) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log hapos (by linarith)) (le_of_lt hapos)
      have h2 : b * Real.log b ≤ b * Real.log (a + b) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log hbpos (by linarith)) (le_of_lt hbpos)
      nlinarith [h1, h2]

/-- **Finite subadditivity of `negMulLog` (proved)**. -/
theorem negMulLog_sum_le {ι : Type*} [DecidableEq ι] (p : ι → ℝ) :
    ∀ (s : Finset ι), (∀ i ∈ s, 0 ≤ p i) →
      Real.negMulLog (∑ i ∈ s, p i) ≤ ∑ i ∈ s, Real.negMulLog (p i) := by
  intro s
  induction s using Finset.induction with
  | empty => intro _; simp
  | @insert a s ha ih =>
    intro hp
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hpa : 0 ≤ p a := hp a (Finset.mem_insert_self a s)
    have hps : ∀ i ∈ s, 0 ≤ p i := fun i hi => hp i (Finset.mem_insert_of_mem hi)
    have h1 := negMulLog_add_le (p a) (∑ i ∈ s, p i) hpa (Finset.sum_nonneg hps)
    have h2 := ih hps
    linarith

variable {γ τ : Type*} [Fintype γ] [Fintype τ]

/-- **The data-processing inequality (proved)**: `H(f(X)) ≤ H(X)`. -/
theorem entropy_pushforward_le_entropy [DecidableEq τ] [DecidableEq γ]
    {f : γ → τ} {p : γ → ℝ} (hp : ∀ i, 0 ≤ p i) :
    entropy (pushforward f p) ≤ entropy p := by
  rw [entropy, entropy]
  rw [← Finset.sum_fiberwise_of_maps_to (fun (x : γ) _ => Finset.mem_univ (f x))
      (fun x => Real.negMulLog (p x))]
  refine Finset.sum_le_sum (fun t _ => ?_)
  have hpf : pushforward f p t = ∑ x ∈ Finset.univ.filter (fun x => f x = t), p x := by
    rw [pushforward, Finset.sum_filter]
  rw [hpf]
  exact negMulLog_sum_le p _ (fun i _ => hp i)

/-- **Transcript info cost is at most input entropy (proved)**: `IC ≤ H(X)`. -/
theorem infoCost_le_entropy [DecidableEq τ] [DecidableEq γ]
    {f : γ → τ} {p : γ → ℝ} (hp : ∀ i, 0 ≤ p i) :
    infoCost f p ≤ entropy p :=
  entropy_pushforward_le_entropy hp

end PallLean.Paper93.DeepMath.PathB.InfoTheory

#print axioms PallLean.Paper93.DeepMath.PathB.InfoTheory.entropy_pushforward_le_entropy
#print axioms PallLean.Paper93.DeepMath.PathB.InfoTheory.infoCost_le_entropy
