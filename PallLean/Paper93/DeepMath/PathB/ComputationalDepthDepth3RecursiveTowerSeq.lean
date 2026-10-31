import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RecursiveTowerSurv

/-!
# Tight switching, step 64: the recursive tower with a per-round survivor threshold (branch `razborov-recoverRho-wip`)

The survivor-threading engine (step 43) maintains a *single* threshold `s` at every round — but the Håstad
regime needs the survivor count to *decrease* round by round (`stars ≈ p^i · n`), so the threshold must be a
**sequence** `s : ℕ → ℕ`.  Here the engine is generalised: round `i` assumes `s i ≤ stars τ` and guarantees
`s (i+1) ≤ stars ρ`, and the chain carries `s i ≤ stars σ` to level `i`.  The scalar engine (step 43) is the
constant-sequence special case.

* `recursive_tower_chain_surv_seq` — the per-round-threshold `Nat.rec` chain.
* `recursive_tower_not_parity_surv_seq` — the per-round-threshold general-`d` parity lower bound.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The per-round-threshold survivor chain.**  With a threshold sequence `s : ℕ → ℕ`, the oracle assuming
`s i ≤ stars τ` and keeping `s (i+1) ≤ stars ρ`, folding `d` rounds yields a common finest `σ` with
`s d ≤ stars σ` and `Reduces x C₀ Cd`. -/
theorem recursive_tower_chain_surv_seq (Valid : ℕ → Layered n → Prop) (s : ℕ → ℕ)
    (C₀ : Layered n) (τ₀ : Fin n → Option Bool) (hC₀ : Valid 0 C₀)
    (hτ₀ : s 0 ≤ SwitchingCounting.stars τ₀)
    (oracle : ∀ (i : ℕ) (C : Layered n) (τ : Fin n → Option Bool), Valid i C →
      s i ≤ SwitchingCounting.stars τ →
      ∃ (C' : Layered n) (ρ : Fin n → Option Bool),
        Extends τ ρ ∧ s (i + 1) ≤ SwitchingCounting.stars ρ ∧ EquivOn ρ C C' ∧ Valid (i + 1) C') :
    ∀ d, ∃ (Cd : Layered n) (σ : Fin n → Option Bool), Valid d Cd ∧ Extends τ₀ σ ∧
      s d ≤ SwitchingCounting.stars σ ∧ ∀ x, DTree.agreeRestriction σ x → Reduces x C₀ Cd := by
  intro d
  induction d with
  | zero => exact ⟨C₀, τ₀, hC₀, fun _ _ h => h, hτ₀, fun x _ => Reduces.refl _⟩
  | succ d ih =>
    obtain ⟨Cd, σd, hVd, hextd, hsurvd, hredd⟩ := ih
    obtain ⟨C', ρ, hextρ, hsurvρ, heqρ, hV'⟩ := oracle d Cd σd hVd hsurvd
    refine ⟨C', ρ, hV', fun v b h => hextρ v b (hextd v b h), hsurvρ, fun x hx => ?_⟩
    have hagd : DTree.agreeRestriction σd x := agreeRestriction_of_extends hextρ hx
    exact (hredd x hagd).trans (Reduces.head heqρ hx)

/-- **The per-round-threshold general-`d` parity lower bound.**  Survivor-threading oracle with a decreasing
threshold sequence + a terminal shallow `DNF` ⟹ `C₀` does not compute parity. -/
theorem recursive_tower_not_parity_surv_seq (Valid : ℕ → Layered n → Prop) (s : ℕ → ℕ)
    (C₀ : Layered n) (τ₀ : Fin n → Option Bool) (hC₀ : Valid 0 C₀)
    (hτ₀ : s 0 ≤ SwitchingCounting.stars τ₀)
    (oracle : ∀ (i : ℕ) (C : Layered n) (τ : Fin n → Option Bool), Valid i C →
      s i ≤ SwitchingCounting.stars τ →
      ∃ (C' : Layered n) (ρ : Fin n → Option Bool),
        Extends τ ρ ∧ s (i + 1) ≤ SwitchingCounting.stars ρ ∧ EquivOn ρ C C' ∧ Valid (i + 1) C')
    (d F : ℕ)
    (hterm : ∀ (Cd : Layered n) (σ : Fin n → Option Bool), Valid d Cd → Extends τ₀ σ →
      s d ≤ SwitchingCounting.stars σ →
      ∃ (σ' : Fin n → Option Bool) (D : List (Clause n)),
        Extends σ σ' ∧ Cd = dnf D ∧ SwitchingCounting.stars σ' ≤ F ∧
        (canonicalDT D F σ').depth < SwitchingCounting.stars σ') :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x := by
  obtain ⟨Cd, σ, hVd, hextd, hsurv, hredd⟩ :=
    recursive_tower_chain_surv_seq Valid s C₀ τ₀ hC₀ hτ₀ oracle d
  obtain ⟨σ', D, hextσ', hCdD, hle, hsh⟩ := hterm Cd σ hVd hextd hsurv
  have hred : ∀ x, DTree.agreeRestriction σ' x → Reduces x C₀ (dnf D) :=
    fun x hx => hCdD ▸ hredd x (agreeRestriction_of_extends hextσ' hx)
  have hnp := tower_not_parity_tight C₀ D F σ' hle hsh hred
  push_neg at hnp
  obtain ⟨x, _, hx⟩ := hnp
  exact ⟨x, hx⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.recursive_tower_chain_surv_seq
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.recursive_tower_not_parity_surv_seq
