import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SurvivorExtendsUncond
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LeafTowerBounded
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LeafClauses

/-!
# Tight switching, step 60: the per-round survivor `hsurv`, discharged (branch `razborov-recoverRho-wip`)

The sole structural input of the width-aware capstone (step 59) is the per-round survivor `hsurv`.  Here it
is discharged from the unconditional subcube survivor budget (`exists_survivor_shallow_extends_uncond`, step
36) at the gate set `G = bottomGates C ∪ (bottomGates C).map negDNF` — every bottom gate together with its
De Morgan dual (a `dnf` gate switches by `canonicalDT cs`, a `cnf` gate by `canonicalDT (negDNF cs)`, so both
must be shallowed).  `BottomWidth w C` discharges the survivor's width hypothesis `hw` (and `negDNF` preserves
term width), the per-round clause-count bound discharges `hm`, and what remains is exactly the tight rate
`hr1` and the subcube-relative budget `hsmall` — the irreducible Håstad/Razborov probability.

* `bottomGatesG` — the survivor gate set (bottoms ∪ their De Morgan duals).
* `hsurv_of_budget` — `Shallows F ρ s C` plus the survivor data, from the budget at `bottomGatesG C`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- The per-round survivor gate set: every bottom gate of `C`, together with its De Morgan dual. -/
def bottomGatesG (C : Layered n) : Finset (List (Clause n)) :=
  (bottomGates C ++ (bottomGates C).map negDNF).toFinset

theorem mem_bottomGatesG {C : Layered n} {g : List (Clause n)} :
    g ∈ bottomGatesG C ↔ g ∈ bottomGates C ∨ ∃ cs ∈ bottomGates C, g = negDNF cs := by
  rw [bottomGatesG, List.mem_toFinset, List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨cs, hcs, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨cs, hcs, rfl⟩
  · rintro (h | ⟨cs, hcs, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨cs, hcs, rfl⟩

/-- **The per-round survivor `hsurv`, discharged from the budget.**  Given the bottom width `BottomWidth w C`,
a clause-count bound `m` on the bottoms, the tight rate `hr1`, and the subcube budget `hsmall` at the gate set
`bottomGatesG C`, there is a survivor `ρ` extending `τ` that keeps `s ≤ stars ρ ≤ F` and shallows every bottom
gate of `C` below `s` in both polarities (`Shallows F ρ s C`). -/
theorem hsurv_of_budget {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s m : ℕ} [NeZero w] [NeZero m] (hF : n ≤ F)
    (C : Layered n) (τ : Fin n → Option Bool)
    (hbw : BottomWidth w C) (_hτ : s ≤ SwitchingCounting.stars τ)
    (hm : ∀ cs ∈ bottomGates C, cs.length ≤ m)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) < 1)
    (hsmall :
        (∑ σ ∈ (extBox τ).filter (fun σ => SwitchingCounting.stars σ < s), pweight p σ)
          + ((bottomGatesG C).card : ℚ)
              * (((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
                  / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))))
        < ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ)) :
    ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ s ≤ SwitchingCounting.stars ρ ∧
      SwitchingCounting.stars ρ ≤ F ∧ Shallows F ρ s C := by
  obtain ⟨ρ, hext, hge, hle, hsh⟩ :=
    exists_survivor_shallow_extends_uncond hp0 hp3 hF τ (bottomGatesG C)
      (by -- hw: width ≤ w on every gate of bottomGatesG C
        intro g hg T hT
        rcases mem_bottomGatesG.mp hg with h | ⟨cs, hcs, rfl⟩
        · exact hbw g h T hT
        · rw [negDNF, List.mem_map] at hT
          obtain ⟨S, hS, rfl⟩ := hT
          simpa using hbw cs hcs S hS)
      (by -- hm: clause-count ≤ m on every gate
        intro g hg
        rcases mem_bottomGatesG.mp hg with h | ⟨cs, hcs, rfl⟩
        · exact hm g h
        · rw [negDNF, List.length_map]; exact hm cs hcs)
      hr1 hsmall
  refine ⟨ρ, hext, hge, hle, ?_⟩
  intro cs hcs
  exact ⟨hsh cs (mem_bottomGatesG.mpr (Or.inl hcs)),
    hsh (negDNF cs) (mem_bottomGatesG.mpr (Or.inr ⟨cs, hcs, rfl⟩))⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.hsurv_of_budget
