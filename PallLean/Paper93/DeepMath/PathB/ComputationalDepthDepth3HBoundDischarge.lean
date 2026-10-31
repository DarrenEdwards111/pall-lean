import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockCircuitCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CumulShell
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CompactRatio

/-!
# Block-DT model, hbound-discharge lemmas 3–5: the parameter inequality + unconditional collapse (branch `razborov-recoverRho-wip`)

The final pieces discharging `circuit_collapse_exists`'s union bound, yielding the **unconditional**
block-shallow-all collapse over the `K`-star shell.

* `gate_absorb` (lemma 3) — gate-count absorption: `G·(m+1) < 2^s ⟹ G·(m+1)·(2·2^w)^s < (4·2^w)^s`.
* `collapse_param_ineq` (lemma 4) — the assembled union bound `G·|{stars≤K-s}|·(2^w)^s < C(n,K)·2^{n-K}`,
  combining the cumulative short-shell bound (lemma 1, `cumul_stars_le`), `card_stars_eq`, the compact binomial
  ratio (lemma 2, `compact_binom_ratio`), and `gate_absorb`.
* `circuit_collapse_uncond` (lemma 5) — feeding the discharged bound to `circuit_collapse_exists`: under the
  explicit regime there is one restriction in the `K`-star shell collapsing **every** gate's block-DT to depth
  `< s`.

Regime: `s ≤ K ≤ n`, `3(K-s) ≤ n+1` (shell domination), `(4·2^w)·K + K ≤ n+1` (binomial ratio),
`G·(K-s+1) < 2^s` (gate absorption — `s ≳ log₂(G·(K-s+1))`).  For constant width `w` this is satisfiable with
`K, s = Θ(n/2^w)` and `G = poly`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Gate-count absorption (lemma 3).**  When `G·(m+1) < 2^s`, the gate count and the cumulative-shell factor
`(m+1)` are absorbed into one factor of `2^s`, turning the in-flight base `(2·2^w)^s` into `(4·2^w)^s`. -/
theorem gate_absorb (w G m s : ℕ) (hgs : G * (m + 1) < 2 ^ s) :
    G * (m + 1) * (2 * 2 ^ w) ^ s < (4 * 2 ^ w) ^ s := by
  have hpow : (4 * 2 ^ w) ^ s = 2 ^ s * (2 * 2 ^ w) ^ s := by
    rw [show (4 : ℕ) * 2 ^ w = 2 * (2 * 2 ^ w) by ring, mul_pow]
  rw [hpow]
  exact mul_lt_mul_of_pos_right hgs (by positivity)

/-- **The assembled union bound (lemma 4).**  Under the regime, the gate-union switching count is strictly
below the `K`-star shell size — exactly the hypothesis `circuit_collapse_exists` needs. -/
theorem collapse_param_ineq (G w K s : ℕ)
    (hsK : s ≤ K) (hKn : K ≤ n) (h3 : 3 * (K - s) ≤ n + 1)
    (hr : (4 * 2 ^ w) * K + K ≤ n + 1) (hgs : G * (K - s + 1) < 2 ^ s) :
    G * ((Finset.univ.filter (fun σ : Restriction n => stars σ ≤ K - s)).card * (2 ^ w) ^ s)
      < n.choose K * 2 ^ (n - K) := by
  -- the core: `G·(K-s+1)·(2·2^w)^s · C(n,K-s) < C(n,K)`.
  have hA : G * (K - s + 1) * (2 * 2 ^ w) ^ s * n.choose (K - s) < n.choose K := by
    rcases Nat.eq_zero_or_pos (n.choose (K - s)) with hc0 | hcpos
    · rw [hc0, Nat.mul_zero]; exact Nat.choose_pos hKn
    · calc G * (K - s + 1) * (2 * 2 ^ w) ^ s * n.choose (K - s)
          < (4 * 2 ^ w) ^ s * n.choose (K - s) := by
            have hga := gate_absorb w G (K - s) s hgs
            exact mul_lt_mul_of_pos_right hga hcpos
        _ ≤ n.choose K := compact_binom_ratio hsK hr
  calc G * ((Finset.univ.filter (fun σ : Restriction n => stars σ ≤ K - s)).card * (2 ^ w) ^ s)
      ≤ G * ((K - s + 1) * (Finset.univ.filter (fun σ : Restriction n => stars σ = K - s)).card
              * (2 ^ w) ^ s) := by
        gcongr
        exact cumul_stars_le K s h3
    _ = 2 ^ (n - K) * (G * (K - s + 1) * (2 * 2 ^ w) ^ s * n.choose (K - s)) := by
        rw [card_stars_eq, show n - (K - s) = (n - K) + s by omega, pow_add, mul_pow]
        ring
    _ < 2 ^ (n - K) * n.choose K := mul_lt_mul_of_pos_left hA (by positivity)
    _ = n.choose K * 2 ^ (n - K) := by ring

/-- **The unconditional circuit collapse (lemma 5).**  Under the explicit regime, there is a single
restriction in the `K`-star shell under which every gate's block decision tree is shallow (depth `< s`). -/
theorem circuit_collapse_uncond (G : ℕ) (gates : Fin G → List (Clause n)) (w K s : ℕ)
    (hcons : ∀ g, ∀ T ∈ gates g, Consistent T) (hw : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ w)
    (hsK : s ≤ K) (hKn : K ≤ n) (h3 : 3 * (K - s) ≤ n + 1)
    (hr : (4 * 2 ^ w) * K + K ≤ n + 1) (hgs : G * (K - s + 1) < 2 ^ s) :
    ∃ ρ : Restriction n,
      SwitchingCounting.stars ρ = K ∧ ∀ g, (blockStream (gates g) s ρ).length < s :=
  circuit_collapse_exists G gates w K s hcons hw (collapse_param_ineq G w K s hsK hKn h3 hr hgs)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.circuit_collapse_uncond
