import PallLean.SemanticEntanglementBridge

/-!
# Dynamic graph entanglement

This file models an infinite-state graph through its legal finite trajectories.
The state type is unrestricted and may therefore contain polynomial,
restriction, derivative, partition, and compiler states.  `pathCost` is the
dynamic/minimax cost of a trajectory (for example the maximum SPDP cost seen
along it).

The first audit is deliberately adversarial.  If a trajectory may start at an
arbitrary representation, every representation supplies a singleton path.
Under the natural condition that a path costs at least its final state, the
resulting graph minimum is exactly ordinary semantic entanglement.  Thus an
infinite graph only creates a new lower-bound route when its admissible
sources or transitions rule out those free singleton paths.
-/

namespace DynamicGraphEntanglement

open SemanticEntanglementBridge

variable {Input : Nat → Type}

/--
A dynamic representation graph, presented by its legal finite trajectories.
`Trajectory n` may range over paths in an infinite graph.  The endpoint is a
representation in the underlying semantic model.
-/
structure GraphModel (Input : Nat → Type) extends Model Input where
  Trajectory : Nat → Type
  finish : {n : Nat} → Trajectory n → Rep n
  pathCost : {n : Nat} → Trajectory n → Nat
  singleton : {n : Nat} → Rep n → Trajectory n
  finish_singleton : ∀ {n : Nat} (r : Rep n), finish (singleton r) = r
  pathCost_singleton : ∀ {n : Nat} (r : Rep n), pathCost (singleton r) = cost r
  finish_cost_le_pathCost : ∀ {n : Nat} (p : Trajectory n), cost (finish p) ≤ pathCost p

/-- Dynamic costs of all free-source trajectories ending in a realization of `f`. -/
def graphRealizationCosts
    (G : GraphModel Input) (f : BoolFamily Input) (n : Nat) : Set Nat :=
  {k | ∃ p : G.Trajectory n,
    G.computes (G.finish p) (f n) ∧ G.pathCost p = k}

/-- Free-source minimax graph entanglement. -/
noncomputable def graphEntanglement
    (G : GraphModel Input) (f : BoolFamily Input) (n : Nat) : Nat :=
  sInf (graphRealizationCosts G f n)

/-- A concrete dynamic trajectory upper-bounds free-source graph entanglement. -/
theorem graphEntanglement_le_pathCost
    (G : GraphModel Input) (f : BoolFamily Input) {n : Nat}
    (p : G.Trajectory n) (hp : G.computes (G.finish p) (f n)) :
    graphEntanglement G f n ≤ G.pathCost p := by
  apply Nat.sInf_le
  exact ⟨p, hp, rfl⟩

/--
Free-source collapse theorem.  Allowing a singleton trajectory at every
representation makes the infinite graph minimum identical to the semantic
minimum over representations.
-/
theorem graphEntanglement_eq_semanticEntanglement
    (G : GraphModel Input) (f : BoolFamily Input)
    (hTotal : IsTotalFor G.toModel f) (n : Nat) :
    graphEntanglement G f n = semanticEntanglement G.toModel f n := by
  apply Nat.le_antisymm
  · obtain ⟨r, hr, hcost⟩ :=
      semanticEntanglement_attained G.toModel f hTotal n
    refine (graphEntanglement_le_pathCost G f (G.singleton r) ?_).trans_eq ?_
    · simpa [G.finish_singleton r] using hr
    · simpa [G.pathCost_singleton r] using hcost
  · have hGraphCosts : (graphRealizationCosts G f n).Nonempty := by
      obtain ⟨r, hr⟩ := hTotal n
      refine ⟨G.pathCost (G.singleton r), G.singleton r, ?_, rfl⟩
      simpa [G.finish_singleton r] using hr
    obtain ⟨p, hp, hcost⟩ := Nat.sInf_mem hGraphCosts
    change semanticEntanglement G.toModel f n ≤
      sInf (graphRealizationCosts G f n)
    rw [← hcost]
    exact (semanticEntanglement_le_cost G.toModel f (G.finish p) hp).trans
      (G.finish_cost_le_pathCost p)

/-- The free-source graph quantity escapes every polynomial. -/
def HasSuperpolynomialGraphEntanglement
    (G : GraphModel Input) (f : BoolFamily Input) : Prop :=
  ∀ c : Nat, ∃ n : Nat, (n + 1) ^ c < graphEntanglement G f n

/--
The graph lower bound is exactly the semantic lower bound when all
representations are admitted as free singleton sources.
-/
theorem superpolynomial_graph_iff_semantic
    (G : GraphModel Input) (f : BoolFamily Input)
    (hTotal : IsTotalFor G.toModel f) :
    HasSuperpolynomialGraphEntanglement G f ↔
      HasSuperpolynomialSemanticEntanglement G.toModel f := by
  simp only [HasSuperpolynomialGraphEntanglement,
    HasSuperpolynomialSemanticEntanglement,
    graphEntanglement_eq_semanticEntanglement G f hTotal]

#print axioms graphEntanglement_eq_semanticEntanglement
#print axioms superpolynomial_graph_iff_semantic

end DynamicGraphEntanglement
