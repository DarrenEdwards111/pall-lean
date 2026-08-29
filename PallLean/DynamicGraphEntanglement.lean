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
  start : {n : Nat} → Trajectory n → Rep n
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

/-! ## Source-constrained graph entanglement -/

/-- A permitted source set at every input length. -/
abbrev SourceSet (G : GraphModel Input) :=
  (n : Nat) → G.Rep n → Prop

/-- Costs of legal trajectories from `source` to an endpoint computing `f`. -/
def sourcedGraphCosts
    (G : GraphModel Input) (source : SourceSet G)
    (f : BoolFamily Input) (n : Nat) : Set Nat :=
  {k | ∃ p : G.Trajectory n,
    source n (G.start p) ∧
    G.computes (G.finish p) (f n) ∧
    G.pathCost p = k}

/--
Source-constrained bottleneck complexity.  Unlike `graphEntanglement`, an
arbitrary easy endpoint is not automatically an admissible singleton path.
-/
noncomputable def sourcedGraphEntanglement
    (G : GraphModel Input) (source : SourceSet G)
    (f : BoolFamily Input) (n : Nat) : Nat :=
  sInf (sourcedGraphCosts G source f n)

/-- The target is reachable from the permitted source at every length. -/
def SourceReachable
    (G : GraphModel Input) (source : SourceSet G)
    (f : BoolFamily Input) : Prop :=
  ∀ n : Nat, ∃ p : G.Trajectory n,
    source n (G.start p) ∧ G.computes (G.finish p) (f n)

/-- Polynomial-bottleneck legal trajectories from the permitted source. -/
def HasPolynomialSourcedTrajectories
    (G : GraphModel Input) (source : SourceSet G)
    (f : BoolFamily Input) : Prop :=
  ∃ c : Nat, ∀ n : Nat, ∃ p : G.Trajectory n,
    source n (G.start p) ∧
    G.computes (G.finish p) (f n) ∧
    G.pathCost p ≤ (n + 1) ^ c

/-- Source-constrained graph entanglement escapes every polynomial. -/
def HasSuperpolynomialSourcedGraphEntanglement
    (G : GraphModel Input) (source : SourceSet G)
    (f : BoolFamily Input) : Prop :=
  ∀ c : Nat, ∃ n : Nat,
    (n + 1) ^ c < sourcedGraphEntanglement G source f n

/-- Direct minimax statement: every legal sourced path crosses the barrier. -/
def HasSuperpolynomialPathBarrier
    (G : GraphModel Input) (source : SourceSet G)
    (f : BoolFamily Input) : Prop :=
  ∀ c : Nat, ∃ n : Nat, ∀ p : G.Trajectory n,
    source n (G.start p) →
    G.computes (G.finish p) (f n) →
    (n + 1) ^ c < G.pathCost p

/-- Every concrete sourced trajectory upper-bounds the sourced minimum. -/
theorem sourcedGraphEntanglement_le_pathCost
    (G : GraphModel Input) (source : SourceSet G)
    (f : BoolFamily Input) {n : Nat} (p : G.Trajectory n)
    (hsource : source n (G.start p))
    (hfinish : G.computes (G.finish p) (f n)) :
    sourcedGraphEntanglement G source f n ≤ G.pathCost p := by
  apply Nat.sInf_le
  exact ⟨p, hsource, hfinish, rfl⟩

/--
For a reachable target, the infimum formulation is exactly the statement that
every admissible source-to-target trajectory crosses a superpolynomial
bottleneck.
-/
theorem superpolynomial_sourced_iff_pathBarrier
    (G : GraphModel Input) (source : SourceSet G)
    (f : BoolFamily Input) (hReach : SourceReachable G source f) :
    HasSuperpolynomialSourcedGraphEntanglement G source f ↔
      HasSuperpolynomialPathBarrier G source f := by
  constructor
  · intro hHard c
    obtain ⟨n, hn⟩ := hHard c
    refine ⟨n, ?_⟩
    intro p hs hf
    exact hn.trans_le (sourcedGraphEntanglement_le_pathCost G source f p hs hf)
  · intro hBarrier c
    obtain ⟨n, hn⟩ := hBarrier c
    refine ⟨n, ?_⟩
    have hCosts : (sourcedGraphCosts G source f n).Nonempty := by
      obtain ⟨p, hs, hf⟩ := hReach n
      exact ⟨G.pathCost p, p, hs, hf, rfl⟩
    obtain ⟨p, hs, hf, hp⟩ := Nat.sInf_mem hCosts
    change (n + 1) ^ c < sInf (sourcedGraphCosts G source f n)
    rw [← hp]
    exact hn p hs hf

/-- Polynomial sourced trajectories give a polynomial sourced minimum. -/
theorem polynomial_sourced_trajectories_bound_entanglement
    (G : GraphModel Input) (source : SourceSet G)
    (f : BoolFamily Input)
    (hPoly : HasPolynomialSourcedTrajectories G source f) :
    ∃ c : Nat, ∀ n : Nat,
      sourcedGraphEntanglement G source f n ≤ (n + 1) ^ c := by
  obtain ⟨c, hc⟩ := hPoly
  refine ⟨c, ?_⟩
  intro n
  obtain ⟨p, hs, hf, hp⟩ := hc n
  exact (sourcedGraphEntanglement_le_pathCost G source f p hs hf).trans hp

/-- A sourced energy barrier rules out every polynomial-bottleneck path family. -/
theorem superpolynomial_sourced_not_polynomial
    (G : GraphModel Input) (source : SourceSet G)
    (f : BoolFamily Input)
    (hHard : HasSuperpolynomialSourcedGraphEntanglement G source f) :
    ¬ HasPolynomialSourcedTrajectories G source f := by
  intro hPoly
  obtain ⟨c, hc⟩ :=
    polynomial_sourced_trajectories_bound_entanglement G source f hPoly
  obtain ⟨n, hn⟩ := hHard c
  exact (Nat.not_lt_of_ge (hc n)) hn

/--
Abstract graph separation theorem.  `p_has_paths` is the universal simulation
theorem for polynomial time; `hSATBarrier` is the source-to-SAT dynamic-SPDP
energy barrier.  These are the two non-circular obligations of the graph
route.
-/
theorem separation_of_sourced_graph_barrier
    (G : GraphModel Input) (source : SourceSet G)
    (InP InNP : BoolFamily Input → Prop)
    (SAT : BoolFamily Input)
    (p_has_paths : ∀ f, InP f →
      HasPolynomialSourcedTrajectories G source f)
    (hSATNP : InNP SAT)
    (hSATBarrier :
      HasSuperpolynomialSourcedGraphEntanglement G source SAT) :
    InP ≠ InNP := by
  intro hEq
  have hSATP : InP SAT := by simpa [hEq] using hSATNP
  exact superpolynomial_sourced_not_polynomial G source SAT hSATBarrier
    (p_has_paths SAT hSATP)

#print axioms graphEntanglement_eq_semanticEntanglement
#print axioms superpolynomial_graph_iff_semantic
#print axioms polynomial_sourced_trajectories_bound_entanglement
#print axioms superpolynomial_sourced_iff_pathBarrier
#print axioms superpolynomial_sourced_not_polynomial
#print axioms separation_of_sourced_graph_barrier

end DynamicGraphEntanglement
