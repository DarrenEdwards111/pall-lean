import Mathlib.Combinatorics.Pigeonhole
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniformContextualReconstructionDepth
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTseitinSpaceObserver

/-!
# UCRD on interacting Tseitin contexts with bounded reuse

The first UCRD theorem used the easy equality-CNF family and obtained the
linear tradeoff `n <= passes * bits`.  This file moves to a genuinely
interacting family: odd-charge Tseitin contradictions on complete graphs.

The observer is still restricted, but the restriction is now the one suggested
by No Fixed-Structure Amortization.  There are `contexts` proof/reconstruction
tasks and a pool of `resources` reusable observer actions.  Every context has
`required` mandatory boundary units, and one physical resource may discharge
units in at most `readK` contexts/positions.  A strong pigeonhole argument gives

```text
contexts * required <= resources * readK.
```

For complete-graph Tseitin, the existing kernel-checked resolution-space
theorem supplies `required = t` whenever `4*t <= n`.  Thus `q` interacting
Tseitin contexts force `q*t <= resources*readK`; for constant reuse this is a
direct-sum/non-amortization law, and with `q=t` it is quadratic in the selected
Tseitin scale.

## Honest scope

This is an unconditional theorem for bounded-reuse **resolution
proof/reconstruction observers**.  It is not a SAT decision lower bound.  The
Tseitin instances here are unsatisfiable and the task is faithful refutation,
not recognizing a promised family by syntax.  Unrestricted machines may reuse
one resource arbitrarily often; proving that every polynomial-time SAT decider
admits a bounded-`readK` normalization would again be the missing general
lower-bound bridge.
-/

namespace PallLean.Paper93.DeepMath.PathB.UCRDTseitinBoundedReuse

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TseitinResolution
open PallLean.Paper93.DeepMath.PathB.TseitinSpaceObserver
open scoped BigOperators

/-! ## Abstract bounded-reuse reconstruction accounting -/

/-- A finite resource pool serving mandatory reconstruction units across many
contexts.  `readK` bounds the total number of context/unit pairs served by any
one physical resource. -/
structure BoundedReuseReconstruction
    (contexts required resources readK : ℕ) where
  resourceOf : Fin contexts × Fin required → Fin resources
  fiber_le : ∀ r : Fin resources,
    Fintype.card {x : Fin contexts × Fin required // resourceOf x = r} ≤ readK

/-- **Bounded-reuse direct sum.**  If one resource serves at most `readK`
mandatory units, then the total resource capacity must cover all
`contexts*required` units. -/
theorem direct_sum_le_resource_reuse
    {contexts required resources readK : ℕ}
    (R : BoundedReuseReconstruction contexts required resources readK) :
    contexts * required ≤ resources * readK := by
  by_contra h
  have hgap : resources * readK < contexts * required := by omega
  obtain ⟨r, hr⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card
      (f := R.resourceOf) (n := readK) (by simpa using hgap)
  have hr' : readK <
      Fintype.card {x : Fin contexts × Fin required // R.resourceOf x = r} := by
    simpa only [Fintype.card_subtype] using hr
  exact (Nat.not_lt_of_ge (R.fiber_le r)) hr'

/-- If the available reuse-weighted capacity is smaller than the mandatory
direct sum, no bounded-reuse reconstruction exists. -/
theorem no_boundedReuseReconstruction_of_gap
    (contexts required resources readK : ℕ)
    (hgap : resources * readK < contexts * required) :
    ¬ Nonempty (BoundedReuseReconstruction contexts required resources readK) := by
  rintro ⟨R⟩
  exact (Nat.not_lt_of_ge (direct_sum_le_resource_reuse R)) hgap

/-! ## Genuine complete-graph Tseitin reconstruction contexts -/

variable {n contexts t resources readK : ℕ}

/-- A family of actual odd-charge complete-graph Tseitin refutations together
with bounded-reuse accounting for the `t` boundary units forced in every
context.

The formulas are context-dependent through their charge functions and axiom
sets.  Each context is internally interacting: every Tseitin edge is shared by
two vertex constraints of the complete graph. -/
structure CompleteGraphTseitinReconstructionSchedule
    (n contexts t resources readK : ℕ) where
  charge : Fin contexts → Fin n → ZMod 2
  oddCharge : ∀ i, ∑ v, charge i v = 1
  Axiom : Fin contexts →
    ResolutionClause (TLit {s : Finset (Fin n) // s.card = 2}) → Prop
  axiom_sound : ∀ i C, Axiom i C →
    ∃ v : Fin n,
      SemanticMeasure.Implies TSat
        (TConstr (completeGraph n) (charge i)) {v} C
  final : Fin contexts →
    Configuration (TLit {s : Finset (Fin n) // s.card = 2})
  refutation : ∀ i, Blackboard tcompl (Axiom i) (final i)
  derives_empty : ∀ i,
    (∅ : ResolutionClause (TLit {s : Finset (Fin n) // s.card = 2})) ∈ final i
  resourceOf : (i : Fin contexts) →
    Fin (observerBoundary (refutation i)) → Fin resources
  fiber_le : ∀ r : Fin resources,
    Fintype.card
      {x : Σ i : Fin contexts, Fin (observerBoundary (refutation i)) //
        resourceOf x.1 x.2 = r} ≤ readK

namespace CompleteGraphTseitinReconstructionSchedule

/-- Every context in the schedule genuinely needs at least `t` units of
resolution observer boundary.  This is inherited from expansion and odd-charge
Tseitin unsatisfiability, not stipulated by the accounting object. -/
theorem each_context_requires_boundary
    (S : CompleteGraphTseitinReconstructionSchedule
      n contexts t resources readK)
    (ht : 1 < t) (hcard : 4 * t ≤ n) (i : Fin contexts) :
    t ≤ observerBoundary (S.refutation i) := by
  exact completeGraph_tseitin_space_lower_bound n
    (S.charge i) (S.oddCharge i) (S.Axiom i) (S.axiom_sound i)
    ht hcard (S.refutation i) (S.derives_empty i)

/-- **Tseitin UCRD direct-sum law.**  Across `contexts` genuine interacting
Tseitin refutations, bounded reuse forces
`contexts*t <= resources*readK`.

The size hypotheses certify independently that `t` is a real proof-space
boundary requirement in every context; the inequality then says those required
units cannot be amortized beyond the declared read bound. -/
theorem reconstruction_direct_sum
    (S : CompleteGraphTseitinReconstructionSchedule
      n contexts t resources readK)
    (ht : 1 < t) (hcard : 4 * t ≤ n) :
    contexts * t ≤ resources * readK := by
  have hreal : ∀ i, t ≤ observerBoundary (S.refutation i) :=
    fun i ↦ S.each_context_requires_boundary ht hcard i
  let embed : Fin contexts × Fin t →
      Σ i : Fin contexts, Fin (observerBoundary (S.refutation i)) :=
    fun x ↦ ⟨x.1, Fin.castLE (hreal x.1) x.2⟩
  have hembed : Function.Injective embed := by
    intro x y hxy
    let recover :
        (Σ i : Fin contexts, Fin (observerBoundary (S.refutation i))) → ℕ × ℕ :=
      fun z ↦ (z.1.val, z.2.val)
    have hrecover : recover (embed x) = recover (embed y) :=
      congrArg recover hxy
    apply Prod.ext
    · apply Fin.ext
      exact congrArg Prod.fst hrecover
    · apply Fin.ext
      exact congrArg Prod.snd hrecover
  let requiredResource : Fin contexts × Fin t → Fin resources :=
    fun x ↦ S.resourceOf (embed x).1 (embed x).2
  have hfiber : ∀ r : Fin resources,
      Fintype.card
        {x : Fin contexts × Fin t // requiredResource x = r} ≤ readK := by
    intro r
    let fiberEmbed :
        {x : Fin contexts × Fin t // requiredResource x = r} →
          {y : Σ i : Fin contexts, Fin (observerBoundary (S.refutation i)) //
            S.resourceOf y.1 y.2 = r} :=
      fun x ↦ ⟨embed x.1, x.2⟩
    have hfiberEmbed : Function.Injective fiberEmbed := by
      intro x y hxy
      apply Subtype.ext
      exact hembed (congrArg (fun z ↦ z.1) hxy)
    exact (Fintype.card_le_of_injective fiberEmbed hfiberEmbed).trans (S.fiber_le r)
  exact direct_sum_le_resource_reuse
    { resourceOf := requiredResource, fiber_le := hfiber }

/-- No bounded-reuse Tseitin schedule exists below the direct-sum capacity. -/
theorem no_schedule_below_direct_sum
    (ht : 1 < t) (hcard : 4 * t ≤ n)
    (hgap : resources * readK < contexts * t) :
    ¬ Nonempty (CompleteGraphTseitinReconstructionSchedule
      n contexts t resources readK) := by
  rintro ⟨S⟩
  exact (Nat.not_lt_of_ge (S.reconstruction_direct_sum ht hcard)) hgap

/-- With one-use resources, `q` contexts require at least `q*t` resources: an
exact direct sum with no cross-context amortization. -/
theorem readOnce_requires_full_direct_sum
    (S : CompleteGraphTseitinReconstructionSchedule n contexts t resources 1)
    (ht : 1 < t) (hcard : 4 * t ≤ n) :
    contexts * t ≤ resources := by
  simpa using S.reconstruction_direct_sum ht hcard

/-- At `contexts = t`, constant-`k` reuse forces quadratic selected-scale
action: `t^2 <= resources*k`.  This is quadratic in the proof-space scale, not
superpolynomial in the aggregate encoding size. -/
theorem square_contexts_force_quadratic_action
    (S : CompleteGraphTseitinReconstructionSchedule n t t resources readK)
    (ht : 1 < t) (hcard : 4 * t ≤ n) :
    t ^ 2 ≤ resources * readK := by
  simpa [pow_two] using S.reconstruction_direct_sum ht hcard

end CompleteGraphTseitinReconstructionSchedule

end PallLean.Paper93.DeepMath.PathB.UCRDTseitinBoundedReuse

#print axioms PallLean.Paper93.DeepMath.PathB.UCRDTseitinBoundedReuse.direct_sum_le_resource_reuse
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDTseitinBoundedReuse.no_boundedReuseReconstruction_of_gap
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDTseitinBoundedReuse.CompleteGraphTseitinReconstructionSchedule.each_context_requires_boundary
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDTseitinBoundedReuse.CompleteGraphTseitinReconstructionSchedule.reconstruction_direct_sum
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDTseitinBoundedReuse.CompleteGraphTseitinReconstructionSchedule.no_schedule_below_direct_sum
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDTseitinBoundedReuse.CompleteGraphTseitinReconstructionSchedule.readOnce_requires_full_direct_sum
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDTseitinBoundedReuse.CompleteGraphTseitinReconstructionSchedule.square_contexts_force_quadratic_action
