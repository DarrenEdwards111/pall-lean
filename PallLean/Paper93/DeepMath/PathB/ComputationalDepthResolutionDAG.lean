import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinRootBound

/-!
# DAG-resolution width lower bound (general resolution, not just tree-like)

The earlier width/size results are for the tree-like inductive `ResolutionDerivation`.
Here we model **general (DAG) resolution** — a sequence of clauses where each is an
axiom or the resolvent of two *earlier* ones (so clauses are reused, not re-derived)
— and prove the Ben-Sasson–Wigderson **width** lower bound for it: every DAG
refutation of expander-Tseitin contains a clause of width `≥ c·t`.

The argument is the medium-clause principle on the derivation order: the empty
clause has measure `≥ t`; take the *earliest* clause of measure `≥ t`.  It cannot be
an axiom (`μ ≤ 1 < t`), so it is a resolvent of two earlier clauses, both of measure
`< t` by minimality; subadditivity then pins its measure in `[t, 2t)` — a medium
clause, which expansion forces to be wide.
-/

namespace PallLean.Paper93.DeepMath.PathB

variable {Lit : Type*} [DecidableEq Lit]

/-- A **general (DAG) resolution derivation**: `n` clauses, each either an axiom or
the resolvent of two strictly earlier clauses. -/
structure ResolutionDAG (compl : Lit → Lit) (Axiom : ResolutionClause Lit → Prop)
    (n : ℕ) where
  clause : Fin n → ResolutionClause Lit
  valid : ∀ i : Fin n, Axiom (clause i) ∨
    ∃ (j k : Fin n) (p : Lit), j < i ∧ k < i ∧
      clause i = ResolutionClause.resolvent compl (clause j) (clause k) p

namespace ResolutionDAG

variable {compl : Lit → Lit} {Axiom : ResolutionClause Lit → Prop} {n : ℕ}

/-- **Abstract DAG width lower bound.**  If `μ` is subadditive on resolvents,
axioms have `μ ≤ a < t`, some clause `i₀` has `μ ≥ t`, and every medium-`μ` clause
(`t ≤ μ < 2t`) is wide (`width ≥ W`), then some clause of the DAG has width `≥ W`. -/
theorem exists_wide_clause {a t W : ℕ} (D : ResolutionDAG compl Axiom n)
    (μ : ResolutionClause Lit → ℕ)
    (hsub : ∀ {C E : ResolutionClause Lit} (p : Lit),
        μ (ResolutionClause.resolvent compl C E p) ≤ μ C + μ E)
    (hax : ∀ {C : ResolutionClause Lit}, Axiom C → μ C ≤ a)
    (ht : a < t)
    (hwide : ∀ {C : ResolutionClause Lit}, t ≤ μ C → μ C < 2 * t →
        W ≤ ResolutionClause.width C)
    (i₀ : Fin n) (hroot : t ≤ μ (D.clause i₀)) :
    ∃ i : Fin n, W ≤ ResolutionClause.width (D.clause i) := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun i => t ≤ μ (D.clause i))
  have hS : S.Nonempty := ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hroot⟩⟩
  set m := S.min' hS with hm_def
  have hm : t ≤ μ (D.clause m) := (Finset.mem_filter.mp (S.min'_mem hS)).2
  have hmin : ∀ j : Fin n, j < m → μ (D.clause j) < t := by
    intro j hj
    by_contra hc
    push_neg at hc
    exact absurd (S.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)) (not_le.mpr hj)
  rcases D.valid m with hax' | ⟨j, k, p, hjm, hkm, heq⟩
  · exact absurd hm (not_le.mpr (lt_of_le_of_lt (hax hax') ht))
  · refine ⟨m, hwide hm ?_⟩
    rw [heq]
    calc μ (ResolutionClause.resolvent compl (D.clause j) (D.clause k) p)
        ≤ μ (D.clause j) + μ (D.clause k) := hsub p
      _ < t + t := Nat.add_lt_add (hmin j hjm) (hmin k hkm)
      _ = 2 * t := (two_mul t).symm

end ResolutionDAG

open TseitinResolution

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]

/-- **DAG-resolution width lower bound for expander-Tseitin.**  Every general
(DAG) resolution refutation of the Tseitin axioms on an expander contains a clause
of width `≥ c·t` (`2 ≤ t`, `4t ≤ |V|`).  This extends the tree-like width bound to
unrestricted resolution. -/
theorem dag_resolution_width_lower_bound (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TConstr G charge v a)
    (Axiom : ResolutionClause (TLit Edge) → Prop)
    (haxiom : ∀ C, Axiom C → ∃ v : V, SemanticMeasure.Implies TSat (TConstr G charge) {v} C)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht2 : 2 ≤ t)
    (hcard : 4 * t ≤ Fintype.card V) {n : ℕ}
    (D : ResolutionDAG tcompl Axiom n) (i₀ : Fin n)
    (hi₀ : D.clause i₀ = (∅ : ResolutionClause (TLit Edge))) :
    ∃ i : Fin n, c * t ≤ ResolutionClause.width (D.clause i) := by
  refine D.exists_wide_clause (SemanticMeasure.measure TSat (TConstr G charge)) (a := 1)
    (t := t) (W := c * t)
    (fun {C E} p => SemanticMeasure.measure_resolvent_le TSat (TConstr G charge) tcompl
      tsat_tcompl hunsat C E p)
    (fun {C} hC => ?_)
    (by omega)
    (fun {C} hlo hhi => width_ge_of_medium G charge hunsat hexp (by omega) hcard hlo hhi)
    i₀ ?_
  · obtain ⟨v, hv⟩ := haxiom C hC
    calc SemanticMeasure.measure TSat (TConstr G charge) C
        ≤ ({v} : Finset V).card :=
          SemanticMeasure.measure_le_of_implies TSat (TConstr G charge) hv
      _ = 1 := Finset.card_singleton v
  · rw [hi₀]
    exact TseitinRootBound.root_bound G charge hunsat hc hexp hcard

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.ResolutionDAG.exists_wide_clause
#print axioms PallLean.Paper93.DeepMath.PathB.dag_resolution_width_lower_bound
