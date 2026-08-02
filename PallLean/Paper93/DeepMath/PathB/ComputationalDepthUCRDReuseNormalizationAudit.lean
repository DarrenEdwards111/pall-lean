import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUCRDTseitinBoundedReuse

/-!
# UCRD reuse-normalization audit

`ComputationalDepthUCRDTseitinBoundedReuse` proved a genuine direct sum for
Tseitin proof/reconstruction observers once every physical resource has reuse
multiplicity at most `readK`.  This file tests whether merely normalizing an
arbitrary finite trace to *some* bounded-reuse presentation supplies leverage.

The answer is exact:

* every finite resource assignment automatically has reuse at most its total
  number of uses;
* a single resource can serve every use and attain that upper bound;
* at the selected Tseitin scale `contexts = required = t`, this full
  amortization uses one resource with `readK = t^2` and exactly saturates the
  direct-sum inequality;
* `t |-> t^2` is a polynomial budget;
* moreover, the Tseitin direct sum `contexts*t` is at most the aggregate vertex
  scale `contexts*n` whenever `4*t <= n`.

Thus a generic finite or polynomial reuse normalization is not the missing
bridge.  The necessary theorem would have to force reuse *strictly below the
total-use scale* in a way that creates a superpolynomial gap.  Polynomial time
alone only bounds the total number of uses polynomially and permits a universal
subcomputation to be reused at every one of them (the Uhlig escape).

## Honest scope

This is a no-go calibration, not `P != NP`.  It proves why the previous
bounded-reuse theorem does not lift merely by observing that a polynomial-time
trace has finite/polynomial multiplicity.  A useful low-reuse normalization for
general SAT machines remains new lower-bound mathematics.
-/

namespace PallLean.Paper93.DeepMath.PathB.UCRDReuseNormalizationAudit

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.UCRDTseitinBoundedReuse

/-! ## Every finite trace has a tautological total-use normalization -/

/-- Any assignment of `contexts*required` uses to resources is automatically a
bounded-reuse reconstruction when the reuse allowance equals the total number
of uses. -/
def normalizeAtTotalUse
    {contexts required resources : ℕ}
    (resourceOf : Fin contexts × Fin required → Fin resources) :
    BoundedReuseReconstruction
      contexts required resources (contexts * required) where
  resourceOf := resourceOf
  fiber_le := by
    intro r
    calc
      Fintype.card
          {x : Fin contexts × Fin required // resourceOf x = r}
          ≤ Fintype.card (Fin contexts × Fin required) :=
        Fintype.card_subtype_le _
      _ = contexts * required := by simp

/-- The tautological normalization recovers only the identity
`totalUses <= resources*totalUses` (when a resource map exists).  It does not
create a separating gap. -/
theorem totalUse_normalization_capacity
    {contexts required resources : ℕ}
    (resourceOf : Fin contexts × Fin required → Fin resources) :
    contexts * required ≤ resources * (contexts * required) :=
  direct_sum_le_resource_reuse (normalizeAtTotalUse resourceOf)

/-! ## Full amortization attains the total-use multiplicity -/

/-- A single universal resource can serve every context/unit pair.  Its allowed
reuse is exactly the total number of uses. -/
def fullAmortization (contexts required : ℕ) :
    BoundedReuseReconstruction contexts required 1 (contexts * required) :=
  normalizeAtTotalUse (fun _ ↦ (0 : Fin 1))

/-- Full amortization exactly saturates the capacity expression: one resource
times total reuse is the total-use count. -/
theorem fullAmortization_capacity_exact (contexts required : ℕ) :
    1 * (contexts * required) = contexts * required := by
  simp

/-- At the quadratic selected scale, a single resource with multiplicity
`t^2` is a valid reconstruction accounting. -/
def selectedScaleFullAmortization (t : ℕ) :
    BoundedReuseReconstruction t t 1 (t ^ 2) := by
  simpa [pow_two] using fullAmortization t t

/-- The selected-scale full-amortization profile saturates rather than
contradicts the Tseitin direct sum. -/
theorem selectedScale_capacity_exact (t : ℕ) :
    t ^ 2 = 1 * (t ^ 2) := by simp

/-! ## Polynomial and aggregate-size calibration -/

/-- Quadratic reuse is a polynomial budget in the repository's concrete
machine-budget sense. -/
theorem squareReuse_isPolynomialBudget :
    IsPolynomialBudget (fun n ↦ n ^ 2) := by
  refine ⟨2, 1, ?_⟩
  intro n
  simp only [one_mul]
  exact Nat.pow_le_pow_left (Nat.le_succ n) 2

/-- The per-context Tseitin requirement is no larger than the vertex count at
the scale where the proof-space theorem applies. -/
theorem required_le_vertices {t n : ℕ} (hcard : 4 * t ≤ n) : t ≤ n := by
  omega

/-- Consequently, even the full read-once direct sum is only linear in the
aggregate vertex scale of all contexts. -/
theorem directSum_le_aggregateVertexScale
    (contexts t n : ℕ) (hcard : 4 * t ≤ n) :
    contexts * t ≤ contexts * n :=
  Nat.mul_le_mul_left contexts (required_le_vertices hcard)

/-- With `contexts=t` and the canonical `n=4t` choice, the apparently
quadratic selected-scale action is bounded by the aggregate input scale
`t*(4t)`. -/
theorem selectedSquare_le_aggregateVertexScale (t : ℕ) :
    t ^ 2 ≤ t * (4 * t) := by
  rw [pow_two]
  exact directSum_le_aggregateVertexScale t t (4 * t) (by omega)

/-! ## Exact surviving target -/

/-- A genuinely useful normalization must beat the tautological total-use
multiplicity.  This definition records that quantitative requirement without
claiming it follows from polynomial time. -/
def BeatsTotalUseMultiplicity
    {contexts required resources readK : ℕ}
    (_R : BoundedReuseReconstruction contexts required resources readK) : Prop :=
  readK < contexts * required

/-- Full amortization does not beat total-use multiplicity. -/
theorem fullAmortization_not_beatsTotalUse (contexts required : ℕ) :
    ¬ BeatsTotalUseMultiplicity (fullAmortization contexts required) := by
  simp [BeatsTotalUseMultiplicity]

end PallLean.Paper93.DeepMath.PathB.UCRDReuseNormalizationAudit

#print axioms PallLean.Paper93.DeepMath.PathB.UCRDReuseNormalizationAudit.normalizeAtTotalUse
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDReuseNormalizationAudit.totalUse_normalization_capacity
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDReuseNormalizationAudit.fullAmortization
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDReuseNormalizationAudit.selectedScaleFullAmortization
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDReuseNormalizationAudit.squareReuse_isPolynomialBudget
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDReuseNormalizationAudit.directSum_le_aggregateVertexScale
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDReuseNormalizationAudit.selectedSquare_le_aggregateVertexScale
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDReuseNormalizationAudit.fullAmortization_not_beatsTotalUse
