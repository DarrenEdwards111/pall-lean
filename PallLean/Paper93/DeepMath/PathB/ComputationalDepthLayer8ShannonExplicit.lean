import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer8ShannonCount

/-!
# Layer 8 (general circuits) — Shannon's theorem, explicit-threshold form

A clean, recognizable form of the classical Shannon counting lower bound: instantiating
`shannon_counting_bound` at the explicit size threshold `s = 2ⁿ/(n+6) − 1 ≈ 2ⁿ/n`.

* `mul_div_pred_lt` — `(n+6)·(2ⁿ/(n+6) − 1) < 2ⁿ` (the strictness that makes the threshold work).
* `threshold_pow` — `(n+6)^{2ⁿ/(n+6) − 1} < 2^{2ⁿ}` (so the counting bound fires): `(n+6) ≤ 2^{n+6}`
  gives `(n+6)^s ≤ 2^{(n+6)·s} < 2^{2ⁿ}`.
* **`exists_function_needing_exp_size`** — for every `n`, some Boolean function on `n` inputs requires
  general-circuit size `> 2ⁿ/(n+6) − 1`.

**Honest status (unchanged).**  This is the classical Shannon theorem: a hard function **exists** and
needs near-`2ⁿ/n` size.  It is **nonconstructive** — it names no explicit function.  The *explicit*
super-polynomial frontier (an explicit `f` requiring super-poly size, → `NP ⊄ P/poly`) remains open and
barrier-blocked; see `SCOPE_LAYER8_GENERAL_CIRCUITS.md` and the explicit-frontier scope doc.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer8

/-- `(n+6)·(2ⁿ/(n+6) − 1) < 2ⁿ`. -/
theorem mul_div_pred_lt (n : ℕ) : (n + 6) * (2 ^ n / (n + 6) - 1) < 2 ^ n := by
  have hmul : (n + 6) * (2 ^ n / (n + 6)) ≤ 2 ^ n := by
    rw [mul_comm]; exact Nat.div_mul_le_self _ _
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  rcases Nat.eq_zero_or_pos (2 ^ n / (n + 6)) with h0 | h1
  · rw [h0, Nat.zero_sub, Nat.mul_zero]; exact hpos
  · obtain ⟨q', hq'⟩ := Nat.exists_eq_succ_of_ne_zero h1.ne'
    rw [hq', Nat.succ_sub_one]
    rw [hq', Nat.mul_succ] at hmul
    omega

/-- The Shannon threshold inequality: `(n+6)^{2ⁿ/(n+6) − 1} < 2^{2ⁿ}`. -/
theorem threshold_pow (n : ℕ) : (n + 6) ^ (2 ^ n / (n + 6) - 1) < 2 ^ (2 ^ n) := by
  calc (n + 6) ^ (2 ^ n / (n + 6) - 1)
      ≤ (2 ^ (n + 6)) ^ (2 ^ n / (n + 6) - 1) :=
        Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ = 2 ^ ((n + 6) * (2 ^ n / (n + 6) - 1)) := by rw [← pow_mul]
    _ < 2 ^ (2 ^ n) := Nat.pow_lt_pow_right (by decide) (mul_div_pred_lt n)

/-- **Shannon's theorem (explicit threshold form).**  For every `n`, some Boolean function on `n` inputs
requires general-circuit size strictly greater than `2ⁿ/(n+6) − 1` (≈ `2ⁿ/n`): every circuit computing it
has size `> 2ⁿ/(n+6) − 1`.  **Nonconstructive** — exhibits no explicit such function. -/
theorem exists_function_needing_exp_size (n : ℕ) :
    ∃ f : (Fin n → Bool) → Bool, ∀ c : Circuit n, Computes c f → 2 ^ n / (n + 6) - 1 < c.size := by
  obtain ⟨f, hf⟩ := shannon_counting_bound (threshold_pow n)
  refine ⟨f, fun c hcomp => ?_⟩
  by_contra h
  push_neg at h
  exact hf ⟨c, h, hcomp⟩

end PallLean.Paper93.DeepMath.PathB.Layer8

#print axioms PallLean.Paper93.DeepMath.PathB.Layer8.exists_function_needing_exp_size
