import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ShallowSurvivorUnif

/-!
# AC⁰ reduction, foundation 35: concrete one-round instantiation (branch only)

The first numeric instantiation: fixing `p = 1/5` (so `2p/(1-p) = 1/2`) and `t = 1/2`, the uniform
conditional switching primitive (brick 34) fires under two clean, separated conditions —

* a **size** condition `2 · (#gates · |Labels|) < 2^s` (purely natural-number; the binding constraint,
  fully discharged here), and
* a **survivor** condition `(9/10)^(stars τ) < (1/2)^(k+1)` (the Chernoff tail at the chosen `p, t`; the
  analytic input that the `d`-round chaining must propagate).

* `one_round_exists_p_fifth` — one switching round at `p=1/5, t=1/2`, from those two conditions, produces a
  restriction extending `τ` that makes every gate shallow and keeps `k < stars ρ` survivors.

This pins down the parameters and reduces a round to elementary inequalities; the survivor condition is the
honest remaining analytic content (a Chernoff bound on `Binomial(stars τ, 1/5)`), not hidden.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Concrete one-round switching at `p = 1/5`, `t = 1/2`.**  Under the size condition
`2·(#gates·|Labels|) < 2^s` and the survivor condition `(9/10)^(stars τ) < (1/2)^(k+1)`, some restriction
extending `τ` makes every gate shallow and keeps more than `k` survivors. -/
theorem one_round_exists_p_fifth (w F s k : ℕ)
    (τ : Fin n → Option Bool) (G : Finset (List (Clause n)))
    (hcons : ∀ g ∈ G, ∀ T ∈ g, Consistent T)
    (hnd : ∀ g ∈ G, ∀ T ∈ g, (T.lits.map litVarOf).Nodup)
    (hw : ∀ g ∈ G, ∀ T ∈ g, T.lits.length ≤ w)
    (hdeep : 2 * (G.card * Fintype.card (Fin F → Option (Fin w → Option (Option Bool)))) < 2 ^ s)
    (hsurv : ((9 : ℚ) / 10) ^ (stars τ) < (1 / 2) ^ (k + 1)) :
    ∃ ρ : Fin n → Option Bool,
      Extends τ ρ ∧ (∀ g ∈ G, (canonicalDTree g w F ρ).depth < s) ∧ k < stars ρ := by
  refine exists_shallow_survivor_extends_unif (p := 1/5) (t := 1/2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) w F s k τ G hcons hnd hw ?_
  set L : ℚ := (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ) with hLdef
  rw [show (2 * (1/5) / (1 - 1/5) : ℚ) = 1/2 by norm_num,
      show ((1/2) * (1/5) + (1 - 1/5) : ℚ) = 9/10 by norm_num]
  have hkpos : (0 : ℚ) < (1/2) ^ k := by positivity
  have h2s : (0 : ℚ) < (2 : ℚ) ^ s := by positivity
  have hT1 : (G.card : ℚ) * ((1/2) ^ s * L) * (1/2) ^ k ≤ (1/2) ^ (k + 1) := by
    rw [pow_succ, show (G.card : ℚ) * ((1/2) ^ s * L) * (1/2) ^ k
        = ((G.card : ℚ) * L * (1/2) ^ s) * (1/2) ^ k by ring, mul_comm ((1/2 : ℚ) ^ k) (1/2)]
    apply mul_le_mul_of_nonneg_right _ (le_of_lt hkpos)
    have e : (G.card : ℚ) * L * (1/2) ^ s = ((G.card : ℚ) * L) / 2 ^ s := by
      rw [div_pow, one_pow]; ring
    rw [e, div_le_iff₀ h2s]
    have hc : 2 * ((G.card : ℚ) * L) ≤ (2 : ℚ) ^ s := by
      rw [hLdef]; exact_mod_cast Nat.le_of_lt hdeep
    linarith
  calc (G.card : ℚ) * ((1/2) ^ s * L) * (1/2) ^ k + (9/10) ^ (stars τ)
      < (1/2) ^ (k + 1) + (1/2) ^ (k + 1) := by linarith [hT1, hsurv]
    _ = (1/2) ^ k := by rw [pow_succ]; ring

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.one_round_exists_p_fifth
