import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3OneRoundConcrete

/-!
# AC⁰ reduction, foundation 36: discharging the survivor Chernoff bound (branch only)

The analytic input of brick 35 (`one_round_exists_p_fifth`'s `hsurv`) discharged to a purely combinatorial
dimension condition.  At `p = 1/5`, `t = 1/2` the survivor tail is `(9/10)^(stars τ)`, which must beat
`(1/2)^(k+1)`.  The elementary fact `(10/9)^7 > 2` means every `7` surviving coordinates buy a factor `> 2`,
so once `stars τ ≥ 7(k+1)` the tail is below `(1/2)^(k+1)`.

* `survivor_chernoff` — `7·(k+1) ≤ m  ⟹  (9/10)^m < (1/2)^(k+1)`.
* `one_round_exists_p_fifth_dim` — one switching round at `p=1/5, t=1/2` from the size condition and the
  **dimension condition** `7·(k+1) ≤ stars τ` (no analytic hypothesis left).

So one round is now driven entirely by combinatorial conditions: gates small enough (`size`) and enough
survivors at the base (`dimension`).  This is the per-round step the `d`-fold loop iterates.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The survivor Chernoff bound.**  If `7·(k+1) ≤ m`, the survivor tail `(9/10)^m` is below
`(1/2)^(k+1)` — because `(10/9)^7 > 2`. -/
theorem survivor_chernoff (k m : ℕ) (hm : 7 * (k + 1) ≤ m) :
    ((9 : ℚ) / 10) ^ m < (1 / 2) ^ (k + 1) := by
  have h9 : (0 : ℚ) < (9 : ℚ) ^ m := by positivity
  have h10 : (0 : ℚ) < (10 : ℚ) ^ m := by positivity
  have h2 : (0 : ℚ) < (2 : ℚ) ^ (k + 1) := by positivity
  have hb1 : (1 : ℚ) ≤ 10 / 9 := by norm_num
  have h79 : (2 : ℚ) < (10 / 9) ^ 7 := by norm_num
  have key2 : (2 : ℚ) ^ (k + 1) < (10 / 9) ^ m := by
    calc (2 : ℚ) ^ (k + 1) < ((10 / 9) ^ 7) ^ (k + 1) :=
          pow_lt_pow_left₀ h79 (by norm_num) (Nat.succ_ne_zero k)
      _ = (10 / 9) ^ (7 * (k + 1)) := by rw [← pow_mul]
      _ ≤ (10 / 9) ^ m := pow_le_pow_right₀ hb1 hm
  rw [div_pow, lt_div_iff₀ h9] at key2
  rw [div_pow, div_pow, one_pow, div_lt_div_iff₀ h10 h2, one_mul, mul_comm]
  exact key2

/-- **One concrete round from combinatorial conditions.**  At `p=1/5, t=1/2`, given the size condition and
the dimension condition `7·(k+1) ≤ stars τ`, some restriction extending `τ` makes every gate shallow and
keeps more than `k` survivors. -/
theorem one_round_exists_p_fifth_dim (w F s k : ℕ)
    (τ : Fin n → Option Bool) (G : Finset (List (Clause n)))
    (hcons : ∀ g ∈ G, ∀ T ∈ g, Consistent T)
    (hnd : ∀ g ∈ G, ∀ T ∈ g, (T.lits.map litVarOf).Nodup)
    (hw : ∀ g ∈ G, ∀ T ∈ g, T.lits.length ≤ w)
    (hdeep : 2 * (G.card * Fintype.card (Fin F → Option (Fin w → Option (Option Bool)))) < 2 ^ s)
    (hdim : 7 * (k + 1) ≤ stars τ) :
    ∃ ρ : Fin n → Option Bool,
      Extends τ ρ ∧ (∀ g ∈ G, (canonicalDTree g w F ρ).depth < s) ∧ k < stars ρ :=
  one_round_exists_p_fifth w F s k τ G hcons hnd hw hdeep (survivor_chernoff k (stars τ) hdim)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.survivor_chernoff
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.one_round_exists_p_fifth_dim
