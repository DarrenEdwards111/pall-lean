import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightIterated

/-!
# Tight switching, step 22: the general depth-`d` assembly over the tight tree (branch `razborov-recoverRho-wip`)

The depth-`d` generalisation of `parity_not_depth3_tight` (step 21).  Given a tower sequence `C 0, C 1, …`
where each layer collapses to the next under a restriction extending the running subcube (`hround`, supplied
per layer by `collapse_or_layer_tight_extends`, step 19), and the final tower is a bottom `DNF` `D` that a
terminal survivor-shallow restriction makes shallow (`hterm`, supplied by `exists_survivor_shallow_extends`,
step 18), the original tower `C 0` does not compute parity.

The construction nests the per-round restrictions automatically: `exists_nested_reduction` folds the rounds
into a single `Reduces` chain at a common finest `σ`, then the terminal restriction extends `σ` once more and
lifts the chain (every earlier round's `EquivOn` survives passing to a finer subcube,
`agreeRestriction_of_extends`).  The parity contradiction is then `tower_not_parity_tight` (step 17) over the
single-literal tree.

* `exists_nested_reduction` — `d` nested `EquivOn` rounds fold to `Reduces x (C 0) (C d)` at a common `σ`.
* `nested_not_parity` — the depth-`d` parity lower bound: `∃ x, eval (C 0) x ≠ parity x`.

## Honest scope

Both per-instance inputs are stated openly: `hround` (each layer's tight collapse round, discharged by
step 19) and `hterm` (the terminal shallowing of the bottom `DNF`, discharged by step 18).  Each carries the
empty-skip wall (brick 49) on its gates — the irreducible switching-lemma content — and all budgets are
`F`-independent (so satisfiable, step 13).  This is the complete tight depth-`d` reduction; instantiating
`C`/`hround`/`hterm` for a concrete circuit family is bookkeeping over this skeleton.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **Nested rounds fold to a single reduction.**  If each layer `C i` collapses to `C (i+1)` under some
restriction extending the running subcube, then `d` rounds reduce `C 0` to `C d` on a common finest `σ`
extending the base `τ₀`. -/
theorem exists_nested_reduction (C : ℕ → Layered n) (τ₀ : Fin n → Option Bool)
    (hround : ∀ i, ∀ τ : Fin n → Option Bool, ∃ ρ : Fin n → Option Bool,
      Extends τ ρ ∧ EquivOn ρ (C i) (C (i + 1))) :
    ∀ d, ∃ σ : Fin n → Option Bool, Extends τ₀ σ ∧
      ∀ x, DTree.agreeRestriction σ x → Reduces x (C 0) (C d) := by
  intro d
  induction d with
  | zero => exact ⟨τ₀, fun _ _ h => h, fun x _ => Reduces.refl _⟩
  | succ d ih =>
    obtain ⟨σd, hextd, hredd⟩ := ih
    obtain ⟨ρ, hextρ, heqρ⟩ := hround d σd
    refine ⟨ρ, fun v b h => hextρ v b (hextd v b h), fun x hx => ?_⟩
    have hagd : DTree.agreeRestriction σd x := agreeRestriction_of_extends hextρ hx
    exact (hredd x hagd).trans (Reduces.head heqρ hx)

/-- **The general depth-`d` tight parity lower bound.**  A tower whose layers each collapse (`hround`) down
to a bottom `DNF` `D` (`hCd`) that a terminal survivor-shallow restriction makes shallow (`hterm`) does not
compute parity. -/
theorem nested_not_parity (C : ℕ → Layered n) (d F : ℕ) (D : List (Clause n))
    (τ₀ : Fin n → Option Bool)
    (hround : ∀ i, ∀ τ : Fin n → Option Bool, ∃ ρ : Fin n → Option Bool,
      Extends τ ρ ∧ EquivOn ρ (C i) (C (i + 1)))
    (hCd : C d = dnf D)
    (hterm : ∀ τ : Fin n → Option Bool, ∃ σ : Fin n → Option Bool, Extends τ σ ∧
      SwitchingCounting.stars σ ≤ F ∧ (canonicalDT D F σ).depth < SwitchingCounting.stars σ) :
    ∃ x : Fin n → Bool, eval (C 0) x ≠ DTree.parity x := by
  obtain ⟨σd, hextd, hredd⟩ := exists_nested_reduction C τ₀ hround d
  obtain ⟨σ, hextσ, hle, hsh⟩ := hterm σd
  have hred : ∀ x, DTree.agreeRestriction σ x → Reduces x (C 0) (dnf D) :=
    fun x hx => hCd ▸ hredd x (agreeRestriction_of_extends hextσ hx)
  have hnp := tower_not_parity_tight (C 0) D F σ hle hsh hred
  push_neg at hnp
  obtain ⟨x, _, hx⟩ := hnp
  exact ⟨x, hx⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.exists_nested_reduction
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.nested_not_parity
