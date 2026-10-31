import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightIterated

/-!
# Tight switching, step 43: the survivor-threading recursive tower (branch `razborov-recoverRho-wip`)

The dischargeable form of the recursive tower (step 40).  `recursive_tower_chain`'s oracle was stated `∀ τ`
unconditionally — but the real per-round collapse only produces an extending restriction when the current
subcube still has enough survivors (`s ≤ stars τ`); the conditional budget fails on low-survivor subcubes.
So the engine must **thread the survivor condition**: the oracle assumes `s ≤ stars τ` and guarantees
`s ≤ stars ρ`, and the recursion maintains `s ≤ stars` at every level (starting from `s ≤ stars τ₀`).  This is
exactly the subcube-relative survivor budget (`exists_survivor_shallow_extends_uncond`, step 36) that
discharges the oracle.

* `recursive_tower_chain_surv` — the survivor-threading `Nat.rec` chain (axiom-free).
* `recursive_tower_not_parity_surv` — the dischargeable general-`d` parity lower bound.

This makes the recursion-engine oracle genuinely dischargeable by the unconditional collapse rounds (steps
37/38) on the conditional measure — the survivor precondition is precisely what those rounds need and what
their survivor budget supplies, level by level.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The survivor-threading recursive tower chain.**  With the oracle assuming `s ≤ stars τ` and keeping
`s ≤ stars ρ`, folding `d` rounds yields a common finest `σ` with `s ≤ stars σ` and `Reduces x C₀ Cd`. -/
theorem recursive_tower_chain_surv (Valid : ℕ → Layered n → Prop) (s : ℕ)
    (C₀ : Layered n) (τ₀ : Fin n → Option Bool) (hC₀ : Valid 0 C₀)
    (hτ₀ : s ≤ SwitchingCounting.stars τ₀)
    (oracle : ∀ (i : ℕ) (C : Layered n) (τ : Fin n → Option Bool), Valid i C →
      s ≤ SwitchingCounting.stars τ →
      ∃ (C' : Layered n) (ρ : Fin n → Option Bool),
        Extends τ ρ ∧ s ≤ SwitchingCounting.stars ρ ∧ EquivOn ρ C C' ∧ Valid (i + 1) C') :
    ∀ d, ∃ (Cd : Layered n) (σ : Fin n → Option Bool), Valid d Cd ∧ Extends τ₀ σ ∧
      s ≤ SwitchingCounting.stars σ ∧ ∀ x, DTree.agreeRestriction σ x → Reduces x C₀ Cd := by
  intro d
  induction d with
  | zero => exact ⟨C₀, τ₀, hC₀, fun _ _ h => h, hτ₀, fun x _ => Reduces.refl _⟩
  | succ d ih =>
    obtain ⟨Cd, σd, hVd, hextd, hsurvd, hredd⟩ := ih
    obtain ⟨C', ρ, hextρ, hsurvρ, heqρ, hV'⟩ := oracle d Cd σd hVd hsurvd
    refine ⟨C', ρ, hV', fun v b h => hextρ v b (hextd v b h), hsurvρ, fun x hx => ?_⟩
    have hagd : DTree.agreeRestriction σd x := agreeRestriction_of_extends hextρ hx
    exact (hredd x hagd).trans (Reduces.head heqρ hx)

/-- **The dischargeable general-`d` recursive-tower parity lower bound.**  Survivor-threading oracle + a
terminal shallow `DNF` ⟹ `C₀` does not compute parity. -/
theorem recursive_tower_not_parity_surv (Valid : ℕ → Layered n → Prop) (s : ℕ)
    (C₀ : Layered n) (τ₀ : Fin n → Option Bool) (hC₀ : Valid 0 C₀)
    (hτ₀ : s ≤ SwitchingCounting.stars τ₀)
    (oracle : ∀ (i : ℕ) (C : Layered n) (τ : Fin n → Option Bool), Valid i C →
      s ≤ SwitchingCounting.stars τ →
      ∃ (C' : Layered n) (ρ : Fin n → Option Bool),
        Extends τ ρ ∧ s ≤ SwitchingCounting.stars ρ ∧ EquivOn ρ C C' ∧ Valid (i + 1) C')
    (d F : ℕ)
    (hterm : ∀ (Cd : Layered n) (σ : Fin n → Option Bool), Valid d Cd → Extends τ₀ σ →
      s ≤ SwitchingCounting.stars σ →
      ∃ (σ' : Fin n → Option Bool) (D : List (Clause n)),
        Extends σ σ' ∧ Cd = dnf D ∧ SwitchingCounting.stars σ' ≤ F ∧
        (canonicalDT D F σ').depth < SwitchingCounting.stars σ') :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x := by
  obtain ⟨Cd, σ, hVd, hextd, hsurv, hredd⟩ :=
    recursive_tower_chain_surv Valid s C₀ τ₀ hC₀ hτ₀ oracle d
  obtain ⟨σ', D, hextσ', hCdD, hle, hsh⟩ := hterm Cd σ hVd hextd hsurv
  have hred : ∀ x, DTree.agreeRestriction σ' x → Reduces x C₀ (dnf D) :=
    fun x hx => hCdD ▸ hredd x (agreeRestriction_of_extends hextσ' hx)
  have hnp := tower_not_parity_tight C₀ D F σ' hle hsh hred
  push_neg at hnp
  obtain ⟨x, _, hx⟩ := hnp
  exact ⟨x, hx⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.recursive_tower_chain_surv
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.recursive_tower_not_parity_surv
