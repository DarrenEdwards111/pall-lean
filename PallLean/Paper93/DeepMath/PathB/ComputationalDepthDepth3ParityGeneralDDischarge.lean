import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityGeneralD
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SurvivorExtendsUncond

/-!
# Tight switching, step 52: discharging the general-`d` oracles at concrete numerics (branch `razborov-recoverRho-wip`)

The two abstract inputs of the general-`d` capstone (`parity_not_altO`, step 51) are discharged from the
unconditional survivor machinery:

* **`survivor_round_trivial`** discharges `hround` *unconditionally* — every restriction has `stars ρ ≤ n ≤ F`,
  so the identity `ρ = τ` already extends `τ`, keeps `s ≤ stars ρ`, and stays `≤ F`.  No budget needed: the
  per-round survivor existence is free (`stars` is monotone and capped by `n`).
* **`terminal_shallow_of_survivor`** discharges `hterm` for a single bottom `DNF` via
  `exists_survivor_shallow_extends_uncond` (step 36) at `G = {cs}` — the genuine switching-budget content
  (per-gate width `≤ w`, clause-count `≤ m`, the tight rate `hr1`, and the subcube-relative union bound
  `hsmall` below the box mass).  The `(canonicalDT cs F σ').depth < s ≤ stars σ'` chain gives `< stars σ'`.
* **`tight_rate_recip_8wm`** discharges the rate hypotheses `0 ≤ p`, `3p ≤ 1`, `hr1` at the concrete tight
  choice `p = 1/(8wm)` (the Håstad rate): `(2p/(1-p))·2wm = 4wm/(8wm-1) < 1`.
* **`parity_not_altO_hround_discharged`** is the capstone with `hround` eliminated — only the terminal
  switching budget `hterm` remains, exactly as the depth-4 proof carries `hsmall₁`.

So at the concrete rate `p = 1/(8wm)`, the per-round oracle is free and the terminal oracle is the standard
unconditional Håstad/Razborov switching bound on the final `DNF` — no `hnf`/`hleaf`/`hpos`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **`hround` discharged unconditionally.**  The identity `ρ = τ` is a survivor round: `Extends` is
reflexive, and `stars ρ ≤ n ≤ F` for every `ρ`, so no budget is needed. -/
theorem survivor_round_trivial {F : ℕ} (hF : n ≤ F) (s : ℕ) :
    ∀ τ : Fin n → Option Bool, s ≤ SwitchingCounting.stars τ →
      ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ s ≤ SwitchingCounting.stars ρ ∧
        SwitchingCounting.stars ρ ≤ F :=
  fun τ hτ => ⟨τ, fun _ _ h => h, hτ,
    le_trans (by rw [SwitchingCounting.stars]; exact le_trans (Finset.card_le_univ _) (by simp)) hF⟩

/-- **`hterm` discharged from the unconditional survivor budget.**  For a single bottom `DNF` `cs`, the
subcube-relative survivor budget (`exists_survivor_shallow_extends_uncond`, `G = {cs}`) yields a restriction
`σ'` extending `σ` that makes `cs` shallow: `(canonicalDT cs F σ').depth < s ≤ stars σ'`. -/
theorem terminal_shallow_of_survivor {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s m : ℕ} [NeZero w] [NeZero m] (hF : n ≤ F)
    (cs : List (Clause n)) (σ : Fin n → Option Bool)
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) (hm : cs.length ≤ m)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) < 1)
    (hsmall :
        (∑ σ' ∈ (extBox σ).filter (fun σ' => SwitchingCounting.stars σ' < s), pweight p σ')
          + (((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
              / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))))
        < ((1 - p) / 2) ^ (n - SwitchingCounting.stars σ)) :
    ∃ σ' : Fin n → Option Bool, Extends σ σ' ∧ SwitchingCounting.stars σ' ≤ F ∧
      (canonicalDT cs F σ').depth < SwitchingCounting.stars σ' := by
  obtain ⟨ρ, hext, hge, hle, hsh⟩ :=
    exists_survivor_shallow_extends_uncond hp0 hp3 hF σ {cs}
      (by intro g hg; rw [Finset.mem_singleton] at hg; subst hg; exact hw)
      (by intro g hg; rw [Finset.mem_singleton] at hg; subst hg; exact hm)
      hr1
      (by simpa using hsmall)
  exact ⟨ρ, hext, hle, lt_of_lt_of_le (hsh cs (Finset.mem_singleton_self cs)) hge⟩

/-- **The concrete tight rate `p = 1/(8wm)`.**  At the Håstad rate the three rate hypotheses hold:
`0 ≤ p`, `3p ≤ 1`, and `(2p/(1-p))·2wm = 4wm/(8wm-1) < 1`. -/
theorem tight_rate_recip_8wm (w m : ℕ) [NeZero w] [NeZero m] :
    (0 : ℚ) ≤ 1 / (8 * (w : ℚ) * (m : ℚ)) ∧
    3 * (1 / (8 * (w : ℚ) * (m : ℚ))) ≤ 1 ∧
    (2 * (1 / (8 * (w : ℚ) * (m : ℚ))) / (1 - 1 / (8 * (w : ℚ) * (m : ℚ))))
        * (2 * (w : ℚ) * (m : ℚ)) < 1 := by
  have hw1 : (1 : ℚ) ≤ (w : ℚ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne w)
  have hm1 : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hwm : (1 : ℚ) ≤ (w : ℚ) * (m : ℚ) := one_le_mul_of_one_le_of_one_le hw1 hm1
  have h8 : (0 : ℚ) < 8 * (w : ℚ) * (m : ℚ) := by nlinarith [hwm]
  have hp_lt : 1 / (8 * (w : ℚ) * (m : ℚ)) < 1 := by rw [div_lt_one h8]; nlinarith [hwm]
  have h1p : (0 : ℚ) < 1 - 1 / (8 * (w : ℚ) * (m : ℚ)) := by linarith
  refine ⟨by positivity, ?_, ?_⟩
  · rw [mul_one_div, div_le_one h8]; nlinarith [hwm]
  · rw [div_mul_eq_mul_div, div_lt_one h1p]
    have hexp : 2 * (1 / (8 * (w : ℚ) * (m : ℚ))) * (2 * (w : ℚ) * (m : ℚ)) = 1 / 2 := by
      field_simp; ring
    have h18 : 1 / (8 * (w : ℚ) * (m : ℚ)) ≤ 1 / 8 :=
      one_div_le_one_div_of_le (by norm_num) (by nlinarith [hwm])
    rw [hexp]; linarith [h18]

/-- **The general-`d` capstone with `hround` discharged.**  Only the terminal switching budget `hterm`
remains (dischargeable per `DNF` by `terminal_shallow_of_survivor`), exactly as the depth-4 proof carries
`hsmall₁`. -/
theorem parity_not_altO_hround_discharged (s F d : ℕ) (C₀ : Layered n)
    (τ₀ : Fin n → Option Bool) (hF : n ≤ F) (hC₀ : AltO (d + 2) C₀)
    (hτ₀ : s ≤ SwitchingCounting.stars τ₀)
    (hterm : ∀ (cs : List (Clause n)) (σ : Fin n → Option Bool), s ≤ SwitchingCounting.stars σ →
      ∃ σ' : Fin n → Option Bool, Extends σ σ' ∧ SwitchingCounting.stars σ' ≤ F ∧
        (canonicalDT cs F σ').depth < SwitchingCounting.stars σ') :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x :=
  parity_not_altO s F d C₀ τ₀ hC₀ hτ₀ (survivor_round_trivial hF s) hterm

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.survivor_round_trivial
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.terminal_shallow_of_survivor
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_altO_hround_discharged
