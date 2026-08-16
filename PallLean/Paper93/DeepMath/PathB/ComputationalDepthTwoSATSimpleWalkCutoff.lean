import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTwoSATBoundedReachability

/-!
# Simple implication walks and the `2n-1` cutoff

This file isolates the finite pigeonhole half of the fixed-fuel theorem.  Explicit directed walks are converted to the
bounded executable reachability predicate.  If the walk has no repeated vertices, its length is at most `2n-1`, since
the literal type has exactly `2n` vertices.

The one remaining graph-theoretic bridge is cycle erasure: every implication walk has a simple walk with the same
endpoints.  Keeping that obligation separate prevents the cutoff from being smuggled in as an assumption.
-/

namespace PallLean.Paper93.DeepMath.PathB.TwoSATSimpleWalkCutoff

open PallLean.Paper93.DeepMath.PathB.TwoSATFastSAT
open PallLean.Paper93.DeepMath.PathB.TwoSATSCCLinearBudget
open PallLean.Paper93.DeepMath.PathB.TwoSATBoundedReachability

variable {n : ℕ}

/-- A typed directed walk through an explicit edge list. -/
inductive EdgeWalk (edges : List (Lit n × Lit n)) : Lit n → Lit n → Type
  | nil (a : Lit n) : EdgeWalk edges a a
  | snoc {a b c : Lit n} (walk : EdgeWalk edges a b) (edge : (b, c) ∈ edges) : EdgeWalk edges a c

namespace EdgeWalk

def length {edges : List (Lit n × Lit n)} : {a b : Lit n} → EdgeWalk edges a b → ℕ
  | _, _, .nil _ => 0
  | _, _, .snoc walk _ => length walk + 1

def vertices {edges : List (Lit n × Lit n)} : {a b : Lit n} → EdgeWalk edges a b → List (Lit n)
  | _, _, .nil a => [a]
  | _, c, .snoc walk _ => vertices walk ++ [c]

@[simp] theorem vertices_nil {edges : List (Lit n × Lit n)} (a : Lit n) :
    vertices (EdgeWalk.nil (edges := edges) a) = [a] := by simp [vertices]

@[simp] theorem vertices_snoc
    {edges : List (Lit n × Lit n)} {a b c : Lit n}
    (walk : EdgeWalk edges a b) (edge : (b, c) ∈ edges) :
    vertices (walk.snoc edge) = vertices walk ++ [c] := by simp [vertices]

theorem vertices_length {edges : List (Lit n × Lit n)} {a b : Lit n}
    (walk : EdgeWalk edges a b) : (vertices walk).length = length walk + 1 := by
  induction walk with
  | nil => simp [vertices, length]
  | snoc walk edge ih => simp [vertices, length, ih, Nat.add_assoc]

/-- Every explicit walk is recognized at fuel equal to its edge length. -/
theorem to_reachWithin {edges : List (Lit n × Lit n)} {a b : Lit n}
    (walk : EdgeWalk edges a b) : ReachWithin edges (length walk) a b := by
  induction walk with
  | nil => simp [length, ReachWithin]
  | snoc walk edge ih =>
      simp only [length, ReachWithin]
      exact Or.inr ⟨(_, _), edge, ih, rfl⟩

/-- Every semantic implication reachability proof has an explicit edge-list walk. -/
theorem nonempty_of_reach (cls : List (Clause n)) {a b : Lit n} (h : Reach cls a b) :
    Nonempty (EdgeWalk (implicationEdges cls) a b) := by
  induction h with
  | refl => exact ⟨.nil _⟩
  | @tail b c _ hbc ih =>
      obtain ⟨walk⟩ := ih
      exact ⟨walk.snoc ((mem_implicationEdges_iff cls b c).mpr hbc)⟩

/-- Any vertex occurring on a walk is the endpoint of a prefix walk. -/
theorem exists_prefix_to
    {edges : List (Lit n × Lit n)} {a b c : Lit n}
    (walk : EdgeWalk edges a b) (hc : c ∈ vertices walk) :
    ∃ pre : EdgeWalk edges a c, List.IsPrefix (vertices pre) (vertices walk) := by
  induction walk with
  | nil =>
      simp only [vertices_nil, List.mem_singleton] at hc
      subst c
      refine ⟨.nil _, ?_⟩
      exact List.prefix_refl _
  | @snoc b d walk edge ih =>
      rw [vertices_snoc, List.mem_append] at hc
      rcases hc with hc | hc
      · obtain ⟨pre, hprefix⟩ := ih hc
        have hp : vertices walk <+: vertices walk ++ [d] := List.prefix_append _ _
        rw [← vertices_snoc walk edge] at hp
        exact ⟨pre, hprefix.trans hp⟩
      · simp only [List.mem_singleton] at hc
        subst c
        refine ⟨walk.snoc edge, ?_⟩
        exact List.prefix_refl _

/-- **Cycle erasure (proved): every directed walk has a simple walk with the same endpoints.** -/
theorem exists_simple
    {edges : List (Lit n × Lit n)} {a b : Lit n} (walk : EdgeWalk edges a b) :
    ∃ simple : EdgeWalk edges a b, (vertices simple).Nodup := by
  induction walk with
  | nil => exact ⟨.nil _, by simp [vertices]⟩
  | @snoc b c walk edge ih =>
      obtain ⟨simple, hsimple⟩ := ih
      by_cases hc : c ∈ vertices simple
      · obtain ⟨pre, hprefix⟩ := exists_prefix_to simple hc
        exact ⟨pre, hsimple.sublist hprefix.sublist⟩
      · refine ⟨simple.snoc edge, ?_⟩
        rw [vertices_snoc]
        simpa using hsimple.append (by simp) (by simp [hc])

/-- A simple walk never uses more vertices than the finite literal universe. -/
theorem length_lt_card_of_nodup {edges : List (Lit n × Lit n)} {a b : Lit n}
    (walk : EdgeWalk edges a b) (hsimple : (vertices walk).Nodup) :
    length walk < Fintype.card (Lit n) := by
  have hcard := hsimple.length_le_card
  rw [vertices_length] at hcard
  omega

theorem reachWithin_mono_le
    {edges : List (Lit n × Lit n)} {a b : Lit n} {fuel fuel' : ℕ}
    (h : ReachWithin edges fuel a b) (hle : fuel ≤ fuel') :
    ReachWithin edges fuel' a b := by
  induction hle with
  | refl => exact h
  | @step fuel' hle ih => exact reachWithin_mono ih

/-- **Finite cutoff for simple walks (proved).** -/
theorem simpleWalk_reachWithin_cutoff
    {edges : List (Lit n × Lit n)} {a b : Lit n}
    (walk : EdgeWalk edges a b) (hsimple : (vertices walk).Nodup) :
    ReachWithin edges (2 * n - 1) a b := by
  apply reachWithin_mono_le (to_reachWithin walk)
  have hlt := length_lt_card_of_nodup walk hsimple
  rw [card_literals] at hlt
  omega

/-- **Uniform finite cutoff (proved): every semantic implication path is found by fuel `2n-1`.** -/
theorem reachWithin_cutoff (cls : List (Clause n)) {a b : Lit n} (h : Reach cls a b) :
    ReachWithin (implicationEdges cls) (2 * n - 1) a b := by
  obtain ⟨walk⟩ := nonempty_of_reach cls h
  obtain ⟨simple, hsimple⟩ := exists_simple walk
  exact simpleWalk_reachWithin_cutoff simple hsimple

/-- The fixed-fuel Boolean kernel decides semantic implication reachability exactly. -/
theorem boundedReach_cutoff_iff (cls : List (Clause n)) (a b : Lit n) :
    boundedReach (implicationEdges cls) (2 * n - 1) a b = true ↔ Reach cls a b := by
  rw [boundedReach_eq_true_iff]
  exact ⟨reachWithin_sound cls, reachWithin_cutoff cls⟩

end EdgeWalk

end PallLean.Paper93.DeepMath.PathB.TwoSATSimpleWalkCutoff

#print axioms PallLean.Paper93.DeepMath.PathB.TwoSATSimpleWalkCutoff.EdgeWalk.nonempty_of_reach
#print axioms PallLean.Paper93.DeepMath.PathB.TwoSATSimpleWalkCutoff.EdgeWalk.exists_simple
#print axioms PallLean.Paper93.DeepMath.PathB.TwoSATSimpleWalkCutoff.EdgeWalk.length_lt_card_of_nodup
#print axioms PallLean.Paper93.DeepMath.PathB.TwoSATSimpleWalkCutoff.EdgeWalk.simpleWalk_reachWithin_cutoff
#print axioms PallLean.Paper93.DeepMath.PathB.TwoSATSimpleWalkCutoff.EdgeWalk.reachWithin_cutoff
#print axioms PallLean.Paper93.DeepMath.PathB.TwoSATSimpleWalkCutoff.EdgeWalk.boundedReach_cutoff_iff
