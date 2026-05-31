import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResolutionDAG

/-!
# The weakening-DAG model and its width lower bound

Toward the *general* (DAG) size–width bound via the fat-clause method, the
restriction of a DAG refutation produces **weakening** steps (a satisfied clause
disappears and the surviving parent's restricted clause is weakened up to the
restricted resolvent).  So the target model is general resolution **with
weakening**: a sequence of clauses, each an axiom, a resolvent of two earlier
clauses, or a *superclause* of an earlier clause.

The width lower bound transfers to this model unchanged: the medium-clause
principle still picks the earliest clause of measure `≥ t`, which can be neither an
axiom (`μ ≤ a < t`) **nor a weakening** (a superclause has `μ ≤` the earlier
clause's `μ < t`, by monotonicity `hmono`), hence is a resolvent of two `<t`
clauses — medium, so wide.
-/

namespace PallLean.Paper93.DeepMath.PathB

variable {Lit : Type*} [DecidableEq Lit]

/-- General resolution **with weakening**: each clause is an axiom, the resolvent of
two strictly earlier clauses, or a superclause of a strictly earlier clause. -/
structure WeakeningDAG (compl : Lit → Lit) (Axiom : ResolutionClause Lit → Prop)
    (n : ℕ) where
  clause : Fin n → ResolutionClause Lit
  valid : ∀ i : Fin n, Axiom (clause i) ∨
    (∃ (j k : Fin n) (p : Lit), j < i ∧ k < i ∧
      clause i = ResolutionClause.resolvent compl (clause j) (clause k) p) ∨
    (∃ j : Fin n, j < i ∧ clause j ⊆ clause i)

namespace WeakeningDAG

variable {compl : Lit → Lit} {Axiom : ResolutionClause Lit → Prop} {n : ℕ}

/-- **Abstract width lower bound for weakening-DAGs.**  As for plain DAGs, but the
monotonicity input `hmono` additionally rules out the earliest `≥t` clause being a
weakening. -/
theorem exists_wide_clause {a t W : ℕ} (D : WeakeningDAG compl Axiom n)
    (μ : ResolutionClause Lit → ℕ)
    (hsub : ∀ {C E : ResolutionClause Lit} (p : Lit),
        μ (ResolutionClause.resolvent compl C E p) ≤ μ C + μ E)
    (hmono : ∀ {C C' : ResolutionClause Lit}, C ⊆ C' → μ C' ≤ μ C)
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
  rcases D.valid m with hax' | ⟨j, k, p, hjm, hkm, heq⟩ | ⟨j, hjm, hsub'⟩
  · exact absurd hm (not_le.mpr (lt_of_le_of_lt (hax hax') ht))
  · refine ⟨m, hwide hm ?_⟩
    rw [heq]
    calc μ (ResolutionClause.resolvent compl (D.clause j) (D.clause k) p)
        ≤ μ (D.clause j) + μ (D.clause k) := hsub p
      _ < t + t := Nat.add_lt_add (hmin j hjm) (hmin k hkm)
      _ = 2 * t := (two_mul t).symm
  · exact absurd hm (not_le.mpr (lt_of_le_of_lt (hmono hsub') (hmin j hjm)))

end WeakeningDAG

open TseitinResolution

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]

/-- **Weakening-DAG width lower bound for expander-Tseitin.**  Every general
resolution-with-weakening refutation of the Tseitin axioms on an expander contains a
clause of width `≥ c·t`.  This is the model the fat-clause restriction recursion
targets. -/
theorem weakening_dag_width_lower_bound (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TConstr G charge v a)
    (Axiom : ResolutionClause (TLit Edge) → Prop)
    (haxiom : ∀ C, Axiom C → ∃ v : V, SemanticMeasure.Implies TSat (TConstr G charge) {v} C)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht2 : 2 ≤ t)
    (hcard : 4 * t ≤ Fintype.card V) {n : ℕ}
    (D : WeakeningDAG tcompl Axiom n) (i₀ : Fin n)
    (hi₀ : D.clause i₀ = (∅ : ResolutionClause (TLit Edge))) :
    ∃ i : Fin n, c * t ≤ ResolutionClause.width (D.clause i) := by
  refine D.exists_wide_clause (SemanticMeasure.measure TSat (TConstr G charge)) (a := 1)
    (t := t) (W := c * t)
    (fun {C E} p => SemanticMeasure.measure_resolvent_le TSat (TConstr G charge) tcompl
      tsat_tcompl hunsat C E p)
    (fun {C C'} h => SemanticMeasure.measure_mono TSat (TConstr G charge) hunsat h)
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

#print axioms PallLean.Paper93.DeepMath.PathB.WeakeningDAG.exists_wide_clause
#print axioms PallLean.Paper93.DeepMath.PathB.weakening_dag_width_lower_bound
