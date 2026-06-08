import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockCircuitCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockSwitchingProb

/-!
# Block-DT model, foundation 19: the quantitative restriction budget (branch only)

The probabilistic-method existence of a depth-reducing restriction, in **closed Håstad form**: a single
clean ℚ condition on the parameters that *guarantees* a good restriction exists.

> If `G · (2^w · 2K/(n-K+1))^s / (1 - 2K/(n-K+1)) < 1` (the union bound over `G` gates in closed Håstad
> form), then there is one restriction in the `K`-star shell under which **every** gate's canonical
> block-DT is shallow (depth `< s`).

This is the per-round budget: it combines the union bound (`circuit_collapse_exists`) with the closed
Håstad tail (`sum_term_le`), so the messy cumulative shell sum never appears — only the clean geometric
bound the user supplies a parameter regime for.

* `circuit_collapse_budget` — the closed-form sufficient condition for a depth-reducing restriction.

## Honest scope

This discharges **one round's** existence from a clean checkable inequality.  A full `parity ∉ AC⁰`
theorem chains `d-2` such rounds, re-choosing the star probability each round so survivors stay `≥ s`
while the tree depth stays `< #survivors`; that cross-round composition (restriction-of-restriction,
survivor accounting) is the remaining bookkeeping.  The per-round budget itself is complete here.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The per-round restriction budget (closed Håstad form).**  If the union bound over the `G` gates
holds in closed Håstad form, a single restriction in the `K`-star shell makes every gate's block-DT
shallow (depth `< s`). -/
theorem circuit_collapse_budget (G : ℕ) (gates : Fin G → List (Clause n)) (w K s : ℕ)
    (hcons : ∀ g, ∀ T ∈ gates g, Consistent T)
    (hw : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ w)
    (hsK : s ≤ K) (hKn : K ≤ n) (hr : 2 * K < n - K + 1)
    (hbudget :
      (G : ℚ) * (((2 : ℚ) ^ w * (((2 * K : ℕ) : ℚ) / ((n - K + 1 : ℕ) : ℚ))) ^ s
          / (1 - ((2 * K : ℕ) : ℚ) / ((n - K + 1 : ℕ) : ℚ))) < 1) :
    ∃ ρ : Restriction n,
      SwitchingCounting.stars ρ = K ∧ ∀ g, (blockStream (gates g) s ρ).length < s := by
  classical
  refine circuit_collapse_exists G gates w K s hcons hw ?_
  -- It remains to prove the ℕ union-bound inequality from the ℚ Håstad budget.
  set SC := (Finset.univ.filter (fun σ : Restriction n => SwitchingCounting.stars σ ≤ K - s)).card
    with hSCdef
  have hDc : 0 < n.choose K := Nat.choose_pos hKn
  have hD : (0 : ℚ) < ↑(n.choose K) * 2 ^ (n - K) := by
    have : (0 : ℚ) < ↑(n.choose K) := by exact_mod_cast hDc
    positivity
  -- cast the goal to ℚ
  rw [← Nat.cast_lt (α := ℚ)]
  push_cast
  -- `↑SC` equals the cumulative shell sum
  have hSC : (↑SC : ℚ) = ∑ j ∈ Finset.range (K - s + 1), (↑(n.choose j) * 2 ^ (n - j) : ℚ) := by
    rw [hSCdef, card_stars_le]; push_cast; rfl
  -- closed Håstad bound on the shell sum
  have hsum := sum_term_le K s hsK hKn hr
  rw [← hSC] at hsum
  -- chain: G·SC·(2^w)^s ≤ |Ω|·(G·Håstad) < |Ω|
  calc (↑G : ℚ) * (↑SC * (2 ^ w) ^ s)
      ≤ (↑G : ℚ) * ((↑(n.choose K) * 2 ^ (n - K)
            * ((((2 * K : ℕ) : ℚ) / ((n - K + 1 : ℕ) : ℚ)) ^ s
              / (1 - ((2 * K : ℕ) : ℚ) / ((n - K + 1 : ℕ) : ℚ)))) * (2 ^ w) ^ s) := by
        gcongr
    _ = (↑(n.choose K) * 2 ^ (n - K))
          * ((↑G : ℚ) * (((2 : ℚ) ^ w * (((2 * K : ℕ) : ℚ) / ((n - K + 1 : ℕ) : ℚ))) ^ s
              / (1 - ((2 * K : ℕ) : ℚ) / ((n - K + 1 : ℕ) : ℚ)))) := by
        rw [mul_pow]; ring
    _ < (↑(n.choose K) * 2 ^ (n - K)) * 1 := by exact mul_lt_mul_of_pos_left hbudget hD
    _ = ↑(n.choose K) * 2 ^ (n - K) := mul_one _

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.circuit_collapse_budget
