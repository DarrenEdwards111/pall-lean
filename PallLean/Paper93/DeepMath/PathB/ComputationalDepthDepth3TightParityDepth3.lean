import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightCollapseOr
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightIterated

/-!
# Tight switching, step 21: the depth-3 assembly over the tight tree (branch `razborov-recoverRho-wip`)

The tight, `F`-independent, **non-vacuous** replacement for `parity_not_depth3` (foundation 39, whose
budgets were jointly *unsatisfiable* under the crude `(4^w+1)^F` count, `depth3_budgets_unsatisfiable`).  An
`OR` of `CNF` gates does not compute parity — assembled end-to-end over the single-literal canonical tree:

1. **round 1 (dual collapse)** — `collapse_to_dnf_layer_tight` (step 20) collapses the `OR`-of-`CNF`s to a
   single bottom `DNF` `D₁` on a restriction `ρ₁` (an `EquivOn` round), `F`-independent;
2. **terminal round** — a survivor-shallow restriction `ρ₂ ⊇ ρ₁` makes `D₁`'s single-literal canonical tree
   shallow relative to the survivors (`hterm`, discharged by `exists_survivor_shallow_extends`, step 18);
3. **chaining** — `iterated_not_parity_tight` (step 17, `d = 1`) folds the reduction `C₀ ⟶ dnf D₁` and the
   shallow terminal tree into: `OR`-of-`CNF` does not compute parity on `ρ₂`'s subcube.

* `parity_not_depth3_tight` — `∃ x, eval (gOr (G.toList.map cnf)) x ≠ parity x`, under the round-1 dual
  budget and the terminal `hterm`.

Unlike `depth3_budgets_unsatisfiable`, *these* budgets are satisfiable: the round-1 cap
`#gates·r^s₁/(1-r)` and the terminal survivor budget are both `F`-independent (`tight_round_budget_-`
`satisfiable`, step 13, exhibits a point with `s ≤ k < n`).  So this is a genuine, non-vacuous bound.

## Honest scope

The terminal round is packaged as `hterm` — *for any* round-1 restriction `ρ₁` achieving the round-1
shallowness, a survivor-shallow `ρ₂` extending it exists for the produced `D₁`.  This is exactly the
conclusion of `exists_survivor_shallow_extends` (step 18) applied to the single gate `{D₁}`; supplying it
requires `D₁`'s alive/leaf/position conditions — the empty-skip wall (brick 49) on the *intermediate*
collapsed DNF, which propagates through the round.  We carry it openly as a hypothesis rather than hide it.
Generalising from depth 3 to depth `d` is the same iteration with nested `τ`'s (`collapse_or_layer_-`
`tight_extends`, step 19).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered Classical

variable {n : ℕ}

/-- **The tight depth-3 parity lower bound.**  An `OR` of `CNF` gates does not compute parity: round-1 dual
collapse to a bottom `DNF` `D₁` (`F`-independent), then a survivor-shallow terminal restriction (`hterm`)
makes `D₁` shallow, refuting parity via the tight reduction spine.  Non-vacuous (the budgets are satisfiable,
step 13). -/
theorem parity_not_depth3_tight {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s₁ s₂ : ℕ} [NeZero w] (hF : n ≤ F) (G : Finset (List (Clause n)))
    (hnf₁ : ∀ g ∈ G.image negDNF, ∀ ρ : Restriction n, ∀ U ∈ g,
      SwitchingCounting.termFalsified ρ U = false)
    (hleaf₁ : ∀ g ∈ G.image negDNF, ∀ ρ : Restriction n,
      SwitchingCounting.anyTermSat g (deepestEnd g F ρ) = false)
    (hpos₁ : ∀ g ∈ G.image negDNF, ∀ ρ : Restriction n, ∀ q ∈ deepestFullSeq g F ρ, q.1 < w)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ)) < 1)
    (hsmall₁ : ((G.image negDNF).card : ℚ)
        * (((2 * p / (1 - p)) * (2 * (w : ℚ))) ^ s₁
            / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ)))) < 1)
    (hterm : ∀ ρ₁ : Restriction n,
        (∀ g ∈ G, (canonicalDT (negDNF g) F ρ₁).depth < s₁) →
        ∃ ρ₂ : Restriction n, Extends ρ₁ ρ₂ ∧ s₂ ≤ SwitchingCounting.stars ρ₂ ∧
          SwitchingCounting.stars ρ₂ ≤ F ∧
          (canonicalDT (G.toList.flatMap (fun g =>
            dtreeToDNF (DTree.negTree (toDTree (canonicalDT (negDNF g) F ρ₁))))) F ρ₂).depth < s₂) :
    ∃ x : Fin n → Bool, eval (gOr (G.toList.map cnf)) x ≠ DTree.parity x := by
  classical
  -- round 1: dual collapse to a single bottom DNF `D₁`
  obtain ⟨ρ₁, hsh₁, heq₁, _hwid₁⟩ :=
    collapse_to_dnf_layer_tight hp0 hp3 hF G hnf₁ hleaf₁ hpos₁ hr1 hsmall₁
  set D₁ : List (Clause n) :=
    G.toList.flatMap (fun g =>
      dtreeToDNF (DTree.negTree (toDTree (canonicalDT (negDNF g) F ρ₁)))) with hD₁
  -- terminal: survivor-shallow restriction for `D₁`
  obtain ⟨ρ₂, hext₂, hge₂, hle₂, hshD₁⟩ := hterm ρ₁ hsh₁
  have hshallow : (canonicalDT D₁ F ρ₂).depth < SwitchingCounting.stars ρ₂ :=
    lt_of_lt_of_le hshD₁ hge₂
  -- assemble the (d = 1) round sequence
  let C : ℕ → Layered n := fun i => match i with | 0 => gOr (G.toList.map cnf) | _ + 1 => dnf D₁
  let ρ : ℕ → Restriction n := fun i => match i with | 0 => ρ₁ | _ + 1 => ρ₂
  have hext : ∀ i, Extends (ρ i) ρ₂ := by
    intro i; cases i with
    | zero => exact hext₂
    | succ j => exact fun v b hb => hb
  have heq : ∀ i, EquivOn (ρ i) (C i) (C (i + 1)) := by
    intro i; cases i with
    | zero => exact heq₁
    | succ j => exact fun x _ => rfl
  have hfinal := iterated_not_parity_tight C ρ ρ₂ 1 D₁ F hext heq rfl hle₂ hshallow
  push_neg at hfinal
  obtain ⟨x, _, hx⟩ := hfinal
  exact ⟨x, hx⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_depth3_tight
