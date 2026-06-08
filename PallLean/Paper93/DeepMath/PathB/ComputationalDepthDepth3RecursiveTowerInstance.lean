import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RecursiveTowerSurv
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseOrExtendsUncond

/-!
# Tight switching, step 44: discharging the recursive-tower oracle (a real instance) (branch `razborov-recoverRho-wip`)

The validation that the survivor-threading recursive tower (step 43) is **genuinely dischargeable** — its
oracle is satisfied by the real collapse round, not a vacuous socket.  We instantiate
`recursive_tower_not_parity_surv` for the `OR`-of-`CNF` family (`d = 1`): the shape predicate `Valid` is
"`= gOr (G.toList.map cnf)` at level 0, a bottom `dnf` afterwards", and the oracle is discharged by
`collapse_to_dnf_layer_tight_extends_uncond` (step 38) at level 0 and the identity afterwards.  The survivor
precondition `s ≤ stars τ` is exactly the dual-extends round's input; its survivor output `s ≤ stars ρ`
threads forward.

So `recursive_tower_chain_surv`'s oracle is concretely dischargeable by the unconditional collapse rounds —
the engine is non-socket.  (The general-`d` instance additionally needs the leaf-recursive collapse over
`Layered`-valued gates; this `d = 1` case validates the engine itself.)

* `parity_orcnf_via_recursive_tower` — an `OR`-of-`CNF` does not compute parity, routed through the recursive
  tower engine (oracle discharged by the real collapse round).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered Classical

variable {n : ℕ}

/-- **`OR`-of-`CNF` parity refutation, via the recursive-tower engine.**  The engine's oracle is discharged
by the dual-extends collapse round (level 0) and the identity (afterwards), validating that
`recursive_tower_not_parity_surv` is genuinely dischargeable. -/
theorem parity_orcnf_via_recursive_tower {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s m : ℕ} [NeZero w] [NeZero m] (hF : n ≤ F) (G : Finset (List (Clause n)))
    (hw : ∀ g ∈ G.image negDNF, ∀ T ∈ g, T.lits.length ≤ w)
    (hm : ∀ g ∈ G.image negDNF, g.length ≤ m)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) < 1)
    (τ₀ : Fin n → Option Bool) (hτ₀ : s ≤ SwitchingCounting.stars τ₀)
    (hbudget : ∀ τ : Fin n → Option Bool, s ≤ SwitchingCounting.stars τ →
        (∑ σ ∈ (extBox τ).filter (fun σ => SwitchingCounting.stars σ < s), pweight p σ)
          + ((G.image negDNF).card : ℚ)
              * (((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
                  / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))))
        < ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ))
    (hterm : ∀ (Cd : Layered n) (σ : Fin n → Option Bool),
        (if (1 : ℕ) = 0 then Cd = gOr (G.toList.map cnf) else ∃ D : List (Clause n), Cd = dnf D) →
        Extends τ₀ σ → s ≤ SwitchingCounting.stars σ →
        ∃ (σ' : Fin n → Option Bool) (D : List (Clause n)),
          Extends σ σ' ∧ Cd = dnf D ∧ SwitchingCounting.stars σ' ≤ F ∧
          (canonicalDT D F σ').depth < SwitchingCounting.stars σ') :
    ∃ x : Fin n → Bool, eval (gOr (G.toList.map cnf)) x ≠ DTree.parity x := by
  classical
  refine recursive_tower_not_parity_surv
    (fun i C => if i = 0 then C = gOr (G.toList.map cnf) else ∃ D : List (Clause n), C = dnf D)
    s (gOr (G.toList.map cnf)) τ₀ (by simp) hτ₀ ?_ 1 F hterm
  -- discharge the oracle
  intro i C τ hV hsurv
  by_cases hi : i = 0
  · subst hi
    change C = gOr (G.toList.map cnf) at hV
    obtain ⟨ρ, hext, hge, _hshallow, heq, _hwid⟩ :=
      collapse_to_dnf_layer_tight_extends_uncond hp0 hp3 hF τ G hw hm hr1 (hbudget τ hsurv)
    refine ⟨dnf (G.toList.flatMap (fun g =>
        dtreeToDNF (DTree.negTree (toDTree (canonicalDT (negDNF g) F ρ))))), ρ, hext, hge, ?_, ?_⟩
    · rw [hV]; exact heq
    · show ∃ D : List (Clause n),
        dnf (G.toList.flatMap (fun g =>
          dtreeToDNF (DTree.negTree (toDTree (canonicalDT (negDNF g) F ρ))))) = dnf D
      exact ⟨_, rfl⟩
  · simp only [if_neg hi] at hV
    refine ⟨C, τ, fun _ _ h => h, hsurv, fun x _ => rfl, ?_⟩
    show ∃ D : List (Clause n), C = dnf D
    exact hV

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_orcnf_via_recursive_tower
