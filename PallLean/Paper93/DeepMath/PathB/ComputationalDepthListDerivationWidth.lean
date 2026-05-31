import PallLean.Paper93.DeepMath.PathB.ComputationalDepthListDerivation

/-!
# The width lower bound in the list-derivation model

The medium-clause / semantic-measure argument that gives the width **lower** bound
works verbatim for the list model: any weakening derivation whose target has
measure `≥ t` contains a clause of measure in `[t, 2t)` — a *medium* clause, hence
wide.  This puts the lower bound in the same model as the fat-clause downward
recursion (`exists_small_width_refutation`), so the two can be combined without a
`Fin ↔ List` bridge.

The proof is a clean structural induction on the derivation: scan to the earliest
clause of measure `≥ t`; its justifiers all have measure `< t`, so it can be
neither an axiom (`μ ≤ a < t`) nor a weakening (`μ ≤` an earlier `μ < t`), hence a
resolvent of two `<t` clauses — medium by subadditivity.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace LDeriv

variable {Lit : Type*} [DecidableEq Lit] {compl : Lit → Lit}
  {Axiom : ResolutionClause Lit → Prop}

/-- **Abstract width lower bound for list derivations.**  For any measure `μ` that
is subadditive on resolvents, monotone under weakening, and bounded on axioms by
`a < t`, with `medium ⇒ wide`: any derivation containing a clause of measure `≥ t`
contains a clause of width `≥ W`. -/
theorem exists_wide_clause {a t W : ℕ} {L : List (ResolutionClause Lit)}
    (h : LDeriv compl Axiom L) (μ : ResolutionClause Lit → ℕ)
    (hsub : ∀ {C E : ResolutionClause Lit} (p : Lit),
        μ (ResolutionClause.resolvent compl C E p) ≤ μ C + μ E)
    (hmono : ∀ {C C' : ResolutionClause Lit}, C ⊆ C' → μ C' ≤ μ C)
    (hax : ∀ {C : ResolutionClause Lit}, Axiom C → μ C ≤ a)
    (ht : a < t)
    (hwide : ∀ {C : ResolutionClause Lit}, t ≤ μ C → μ C < 2 * t →
        W ≤ ResolutionClause.width C)
    (hroot : ∃ C ∈ L, t ≤ μ C) :
    ∃ C ∈ L, W ≤ ResolutionClause.width C := by
  classical
  revert hroot
  induction h with
  | nil => intro hroot; obtain ⟨C, hC, _⟩ := hroot; exact absurd hC (by simp)
  | @cons C L just h ih =>
    intro hroot
    by_cases hL : ∃ C' ∈ L, t ≤ μ C'
    · obtain ⟨C', hC', hW'⟩ := ih hL
      exact ⟨C', List.mem_cons.mpr (Or.inr hC'), hW'⟩
    · push_neg at hL
      have hμC : t ≤ μ C := by
        obtain ⟨C', hC', htC'⟩ := hroot
        rcases List.mem_cons.mp hC' with h1 | h1
        · exact h1 ▸ htC'
        · exact absurd htC' (not_le.mpr (hL C' h1))
      rcases just with hax' | ⟨D, E, p, hD, hE, heq⟩ | ⟨D, hD, hsub'⟩
      · exact absurd hμC (not_le.mpr (lt_of_le_of_lt (hax hax') ht))
      · refine ⟨C, List.mem_cons.mpr (Or.inl rfl), hwide hμC ?_⟩
        rw [heq]
        calc μ (ResolutionClause.resolvent compl D E p)
            ≤ μ D + μ E := hsub p
          _ < t + t := Nat.add_lt_add (hL D hD) (hL E hE)
          _ = 2 * t := (two_mul t).symm
      · exact absurd hμC (not_le.mpr (lt_of_le_of_lt (hmono hsub') (hL D hD)))

end LDeriv

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.exists_wide_clause
