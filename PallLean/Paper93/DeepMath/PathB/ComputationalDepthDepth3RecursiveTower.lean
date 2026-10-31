import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightIterated

/-!
# Tight switching, step 40: the recursive tower — general-`d` (branch `razborov-recoverRho-wip`)

The general-`d` capstone, generalizing the depth-4 dependent threading (step 39).  The obstruction to a fixed
tower (`exists_nested_reduction`, step 22) was that each round's next tower **depends on the chosen
restriction**.  Here the per-round **oracle** produces that next tower: given the *actual* current tower `C`
(of shape `Valid i`) and subcube `τ`, it returns an extending `ρ`, the next tower `C'` (of shape
`Valid (i+1)`), and `EquivOn ρ C C'`.  A `Nat.rec` then folds `d` such rounds into a single `Reduces` chain at
a common finest `σ`, and the terminal (`hterm`) supplies the shallow bottom `DNF`.

This is exactly the restriction-dependent recursion depth-4 (step 39) instantiates at `d = 2`: there `Valid`
is the depth-`(4-i)` alternating-tower shape, the oracle is `collapse_or_layer_tight_extends_uncond`
(round 1) / `collapse_to_dnf_layer_tight_extends_uncond` (round 2) — for depth `≥ 5` the oracle additionally
re-merges (`merge_*_EquivOn`) to restore the alternation after each peel.  The recursion engine here is shape-
and round-agnostic; the caller supplies `Valid`/`oracle`/`hterm` for their circuit family.

* `recursive_tower_chain` — the `Nat.rec` building the nested `Reduces` chain (axiom-free).
* `recursive_tower_not_parity` — the general-`d` parity lower bound.

## Honest scope

`oracle`/`Valid`/`hterm` are the per-instance interface, discharged by the unconditional collapse rounds
(steps 37/38) + the survivor budget (step 36) + the merge lemmas — concretely demonstrated for `d = 2` by
`parity_not_depth4_uncond` (step 39).  No `hnf`/`hleaf`/`hpos`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The recursive tower chain.**  Folding `d` restriction-dependent rounds (each producing the next
tower via the `oracle`) into a single `Reduces` at a common finest `σ` extending `τ₀`, with the final tower
of shape `Valid d`. -/
theorem recursive_tower_chain (Valid : ℕ → Layered n → Prop)
    (C₀ : Layered n) (τ₀ : Fin n → Option Bool) (hC₀ : Valid 0 C₀)
    (oracle : ∀ (i : ℕ) (C : Layered n) (τ : Fin n → Option Bool), Valid i C →
      ∃ (C' : Layered n) (ρ : Fin n → Option Bool),
        Extends τ ρ ∧ EquivOn ρ C C' ∧ Valid (i + 1) C') :
    ∀ d, ∃ (Cd : Layered n) (σ : Fin n → Option Bool), Valid d Cd ∧ Extends τ₀ σ ∧
      ∀ x, DTree.agreeRestriction σ x → Reduces x C₀ Cd := by
  intro d
  induction d with
  | zero => exact ⟨C₀, τ₀, hC₀, fun _ _ h => h, fun x _ => Reduces.refl _⟩
  | succ d ih =>
    obtain ⟨Cd, σd, hVd, hextd, hredd⟩ := ih
    obtain ⟨C', ρ, hextρ, heqρ, hV'⟩ := oracle d Cd σd hVd
    refine ⟨C', ρ, hV', fun v b h => hextρ v b (hextd v b h), fun x hx => ?_⟩
    have hagd : DTree.agreeRestriction σd x := agreeRestriction_of_extends hextρ hx
    exact (hredd x hagd).trans (Reduces.head heqρ hx)

/-- **The general-`d` recursive-tower parity lower bound.**  A tower whose layers each collapse (the
`oracle`, restriction-dependent) down to a bottom `DNF` `D` that a terminal survivor-shallow restriction
makes shallow (`hterm`) does not compute parity. -/
theorem recursive_tower_not_parity (Valid : ℕ → Layered n → Prop)
    (C₀ : Layered n) (τ₀ : Fin n → Option Bool) (hC₀ : Valid 0 C₀)
    (oracle : ∀ (i : ℕ) (C : Layered n) (τ : Fin n → Option Bool), Valid i C →
      ∃ (C' : Layered n) (ρ : Fin n → Option Bool),
        Extends τ ρ ∧ EquivOn ρ C C' ∧ Valid (i + 1) C')
    (d F : ℕ)
    (hterm : ∀ (Cd : Layered n) (σ : Fin n → Option Bool), Valid d Cd → Extends τ₀ σ →
      ∃ (σ' : Fin n → Option Bool) (D : List (Clause n)),
        Extends σ σ' ∧ Cd = dnf D ∧ SwitchingCounting.stars σ' ≤ F ∧
        (canonicalDT D F σ').depth < SwitchingCounting.stars σ') :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x := by
  obtain ⟨Cd, σ, hVd, hextd, hredd⟩ := recursive_tower_chain Valid C₀ τ₀ hC₀ oracle d
  obtain ⟨σ', D, hextσ', hCdD, hle, hsh⟩ := hterm Cd σ hVd hextd
  have hred : ∀ x, DTree.agreeRestriction σ' x → Reduces x C₀ (dnf D) :=
    fun x hx => hCdD ▸ hredd x (agreeRestriction_of_extends hextσ' hx)
  have hnp := tower_not_parity_tight C₀ D F σ' hle hsh hred
  push_neg at hnp
  obtain ⟨x, _, hx⟩ := hnp
  exact ⟨x, hx⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.recursive_tower_chain
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.recursive_tower_not_parity
