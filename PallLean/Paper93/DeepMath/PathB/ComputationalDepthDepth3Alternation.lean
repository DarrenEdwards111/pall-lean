import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Reduces

/-!
# Tight switching, step 49: the alternation invariant (branch `razborov-recoverRho-wip`)

The shape predicate the recursive-tower `Valid` tracks: a proper alternating `AC⁰` tower, depth-indexed and
polarity-typed, with **non-empty** gates (the degeneracy `gAnd []` is excluded — it would grow depth under the
merge).  `AltO k` (top `OR`) and `AltA k` (top `AND`) are mutually inductive:

* `AltO 2 = dnf`, `AltA 2 = cnf` (the bottom gates);
* `AltO (k+3) = gOr` of a non-empty list of `AltA (k+2)`s;
* `AltA (k+3) = gAnd` of a non-empty list of `AltO (k+2)`s.

So `AltO 3 = gOr`-of-`cnf`, `AltA 3 = gAnd`-of-`dnf`, etc. — exactly the bottom-two-levels the collapse round
switches and merges.  The per-round collapse (step 47) reduces `AltO (k+3) → AltO (k+2)` (and `AltA` dually),
one level per round, so `depth₀ - 2` rounds reach `AltO 2 = dnf` — the bottom `DNF` the parity capstone needs.

* `AltO` / `AltA` — the mutual alternation predicates.
* `AltO_two_dnf` / `AltA_two_cnf` — the base levels are bottom gates (for the engine's `hterm`).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

-- Mutually inductive alternation predicates: AltO k = depth-k alternating tower top OR, AltA k = top AND; non-empty gates.
mutual
inductive AltO : ℕ → Layered n → Prop where
  | dnf (cs : List (Clause n)) : AltO 2 (Layered.dnf cs)
  | gOr (k : ℕ) (gs : List (Layered n)) (hne : gs ≠ [])
      (h : ∀ g ∈ gs, AltA (k + 2) g) : AltO (k + 3) (Layered.gOr gs)
inductive AltA : ℕ → Layered n → Prop where
  | cnf (cs : List (Clause n)) : AltA 2 (Layered.cnf cs)
  | gAnd (k : ℕ) (gs : List (Layered n)) (hne : gs ≠ [])
      (h : ∀ g ∈ gs, AltO (k + 2) g) : AltA (k + 3) (Layered.gAnd gs)
end

/-- A depth-2 top-`OR` alternating tower is a bottom `DNF`. -/
theorem AltO_two_dnf {C : Layered n} (h : AltO 2 C) : ∃ cs, C = Layered.dnf cs := by
  cases h with
  | dnf cs => exact ⟨cs, rfl⟩

/-- A depth-2 top-`AND` alternating tower is a bottom `CNF`. -/
theorem AltA_two_cnf {C : Layered n} (h : AltA 2 C) : ∃ cs, C = Layered.cnf cs := by
  cases h with
  | cnf cs => exact ⟨cs, rfl⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.AltO_two_dnf
