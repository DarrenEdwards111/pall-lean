import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LayerCollapseUncond
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseOrExtendsUncond
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightIterated

/-!
# Tight switching, step 39: the unconditional depth-4 parity lower bound (branch `razborov-recoverRho-wip`)

The manual two-round (`d = 2`) assembly — the safe test case for the dependent tower construction before
the general recursion.  An `OR`-of-`AND`-of-`DNF` circuit (depth 4) does not compute parity:

1. **round 1** (`collapse_or_layer_tight_extends_uncond`, step 37) collapses the depth-4 tower `C₀` to a
   depth-3 `OR`-of-`CNF` `C₁` on a restriction `ρ₁` — `C₁` **depends on the chosen `ρ₁`**;
2. **round 2 + terminal** (`hrest`, discharged by `collapse_to_dnf_layer_tight_extends_uncond` (step 38) on
   the *actual* `C₁ ρ₁`, then `exists_survivor_shallow_extends_uncond`) consumes that `C₁ ρ₁`, producing
   `ρ₃ ⊇ ρ₁` and a bottom `DNF` `D₂` with `EquivOn ρ₃ (C₁ ρ₁) (dnf D₂)` and `canonicalDT D₂` shallow;
3. **capstone** `iterated_not_parity_tight` (step 17, `d = 2`) folds `C₀ ⟶ C₁ ⟶ dnf D₂` and refutes parity.

This exercises exactly the restriction-dependent threading (`ρ₁` chosen → `C₁ ρ₁` formed → round 2 consumes
it → `ρ₁ ⊆ ρ₃`) that the general recursive tower must generalise.  No `hnf`/`hleaf`/`hpos`.

* `parity_not_depth4_uncond` — the unconditional depth-4 parity lower bound.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The unconditional depth-4 parity lower bound.**  Round 1 collapses `OR`-of-`AND`-of-`DNF` to a
restriction-dependent `OR`-of-`CNF` `C₁`; `hrest` (round 2 + terminal, discharged by the dual-extends round
and the survivor budget on the *actual* `C₁`) yields a shallow bottom `DNF`; the capstone refutes parity. -/
theorem parity_not_depth4_uncond {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s₁ m : ℕ} [NeZero w] [NeZero m] (hF : n ≤ F)
    (gates : List (Finset (List (Clause n)))) (Gtot : Finset (List (Clause n)))
    (hsub : ∀ G ∈ gates, G ⊆ Gtot)
    (hw : ∀ g ∈ Gtot, ∀ T ∈ g, T.lits.length ≤ w) (hm : ∀ g ∈ Gtot, g.length ≤ m)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) < 1)
    (hsmall₁ :
        (∑ σ ∈ (extBox (fun _ : Fin n => (none : Option Bool))).filter (fun σ => SwitchingCounting.stars σ < s₁),
            pweight p σ)
          + (Gtot.card : ℚ)
              * (((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s₁
                  / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))))
        < ((1 - p) / 2) ^ (n - SwitchingCounting.stars (fun _ : Fin n => (none : Option Bool))))
    (hrest : ∀ ρ₁ : Restriction n, Extends (fun _ : Fin n => (none : Option Bool)) ρ₁ →
        (∀ G ∈ gates, ∀ C ∈ G.toList.flatMap
            (fun g => dtreeToCNF (toDTree (canonicalDT g F ρ₁))), C.lits.length < s₁) →
        ∃ (ρ₃ : Restriction n) (D₂ : List (Clause n)),
          Extends ρ₁ ρ₃ ∧ SwitchingCounting.stars ρ₃ ≤ F ∧
          (canonicalDT D₂ F ρ₃).depth < SwitchingCounting.stars ρ₃ ∧
          EquivOn ρ₃ (gOr (gates.map (fun G => cnf (G.toList.flatMap
            (fun g => dtreeToCNF (toDTree (canonicalDT g F ρ₁))))))) (dnf D₂)) :
    ∃ x : Fin n → Bool,
      eval (gOr (gates.map (fun G => gAnd (G.toList.map dnf)))) x ≠ DTree.parity x := by
  classical
  -- round 1: collapse the depth-4 tower to a restriction-dependent OR-of-CNF C₁
  obtain ⟨ρ₁, _hext₁, _hge₁, heq₁, hwid₁⟩ :=
    collapse_or_layer_tight_extends_uncond hp0 hp3 hF (fun _ : Fin n => (none : Option Bool)) gates Gtot hsub hw hm hr1 hsmall₁
  -- round 2 + terminal on the actual C₁ ρ₁
  obtain ⟨ρ₃, D₂, hext₃, hle₃, hshallow₃, heq₂⟩ := hrest ρ₁ _hext₁ hwid₁
  -- assemble the d = 2 tower
  let C : ℕ → Layered n := fun i => match i with
    | 0 => gOr (gates.map (fun G => gAnd (G.toList.map dnf)))
    | 1 => gOr (gates.map (fun G => cnf (G.toList.flatMap
        (fun g => dtreeToCNF (toDTree (canonicalDT g F ρ₁))))))
    | _ => dnf D₂
  let ρ : ℕ → Restriction n := fun i => match i with | 0 => ρ₁ | _ => ρ₃
  have hext : ∀ i, Extends (ρ i) ρ₃ := by
    intro i; cases i with
    | zero => exact hext₃
    | succ j => exact fun v b hb => hb
  have heq : ∀ i, EquivOn (ρ i) (C i) (C (i + 1)) := by
    intro i; cases i with
    | zero => exact heq₁
    | succ j => cases j with
      | zero => exact heq₂
      | succ k => exact fun x _ => rfl
  have hfinal := iterated_not_parity_tight C ρ ρ₃ 2 D₂ F hext heq rfl hle₃ hshallow₃
  push_neg at hfinal
  obtain ⟨x, _, hx⟩ := hfinal
  exact ⟨x, hx⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_depth4_uncond
