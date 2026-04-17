/-
  AmplituhedronGaugeScaffold.lean — roadmap for constructing Π⋆
  --------------------------------------------------------------

  This archived file provides a **scaffold / roadmap** toward the paper-deep
  construction of the amplituhedron gauge Π⋆ from paper §28.3
  (Euler-Lagrange / N-Frame-Lagrangian construction).

  Strategy: factor `exists_amplituhedron_gauge` (the on-path axiom in
  `GlobalGodMoveGauge.lean`) into three named sub-claims, each smaller
  and more directly aligned with paper §28.3 content:

    (A) PositionCollapseMap: a ℚ-linear collapse of block-position
        multiplicity that bounds the projected rank by n^200.
    (B) IdentityMinorPreservation: the same map, on SAT-decider
        compiled polynomials, preserves the C(n/3, log n) identity-minor
        lower bound.
    (C) RankMonotonicity: projected rank ≤ unprojected rank
        (structural — would follow from general SPDP rank behavior
        under ℚ-linear maps).

  At present, `IsAmplituhedronGauge` in `GlobalGodMoveGauge.lean` already
  bundles these three. This file formalizes the reduction and identifies
  which pieces are paper-deep vs. structural.

  This is an archived scaffold — not on the critical path. Its goal is
  to provide a cleaner decomposition of the single load-bearing axiom
  for future work.
-/

import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

namespace AmplituhedronGaugeScaffold

/-! ## Abstract gauge witness

Factored form of the three properties `IsAmplituhedronGauge` bundles.
We state the structural (projection-like) content separately from the
two paper-deep properties. -/

/-- A **structurally valid** gauge candidate: a ℚ-linear endomorphism
on a finite-dimensional vector space that is idempotent (a projection).

Projections are the natural class of "gauge" maps: they pick a
subspace (the image) and map any vector to its canonical representative
there. Idempotency `π ∘ π = π` expresses "projection". -/
structure IsProjection {V : Type*} [AddCommGroup V] [Module ℚ V]
    (π : V →ₗ[ℚ] V) : Prop where
  idempotent : π ∘ₗ π = π

/-- Every idempotent ℚ-linear map has the decomposition
`V = im π ⊕ ker π`. -/
theorem IsProjection.decompose {V : Type*} [AddCommGroup V] [Module ℚ V]
    {π : V →ₗ[ℚ] V} (_hπ : IsProjection π) :
    ∀ v : V, v = π v + (v - π v) := by
  intro v
  abel

/-- For a projection, `π(v - π v) = 0` — the non-image part is in the kernel. -/
theorem IsProjection.ker_complement {V : Type*} [AddCommGroup V] [Module ℚ V]
    {π : V →ₗ[ℚ] V} (hπ : IsProjection π) (v : V) :
    π (v - π v) = 0 := by
  have hidem : π (π v) = π v := by
    have := congrArg (· v) hπ.idempotent
    simpa using this
  simp [map_sub, hidem]

/-- Idempotent: `π (π v) = π v` — this is the defining property of an
idempotent linear map (a projection). -/
theorem IsProjection.apply_apply {V : Type*} [AddCommGroup V] [Module ℚ V]
    {π : V →ₗ[ℚ] V} (hπ : IsProjection π) (v : V) :
    π (π v) = π v := by
  have := congrArg (· v) hπ.idempotent
  simpa using this

/-- The range of a projection equals the fixed-point set. -/
theorem IsProjection.mem_range_iff_fixed {V : Type*} [AddCommGroup V] [Module ℚ V]
    {π : V →ₗ[ℚ] V} (hπ : IsProjection π) (v : V) :
    v ∈ LinearMap.range π ↔ π v = v := by
  constructor
  · rintro ⟨w, hw⟩
    rw [← hw, hπ.apply_apply]
  · intro h
    exact ⟨v, h⟩

/-- For a projection, `range π ⊕ ker π = ⊤` (internal direct sum in
finite-dimensional settings; here we just show the algebraic facts
that underlie it: every `v` is `π v + (v - π v)`, the first is in the
range, the second in the kernel). -/
theorem IsProjection.range_add_ker_decomp {V : Type*} [AddCommGroup V] [Module ℚ V]
    {π : V →ₗ[ℚ] V} (hπ : IsProjection π) (v : V) :
    π v ∈ LinearMap.range π ∧ (v - π v) ∈ LinearMap.ker π := by
  refine ⟨⟨v, rfl⟩, ?_⟩
  simp [LinearMap.mem_ker, hπ.ker_complement v]

/-! ## Paper-deep content as named claims

The two paper-deep pieces, stated abstractly, are:
  (A) Position-collapse bound: on a *generic* compiled polynomial, the
      projection's image has rank bounded by a polynomial in `n`.
  (B) Identity-minor preservation: on a *SAT-decider* compiled
      polynomial, the projection's image still contains an identity
      minor of exponential rank.

The gap (polynomial vs. exponential rank) is the separation.
The gauge Π⋆ realizes this in paper §28.3 via Euler-Lagrange
extremization over the N-Frame Lagrangian on the amplituhedron.

We name these as abstract predicates below, to be instantiated by a
concrete construction in future work. -/

/-- Abstract **position-collapse** property (paper §28.3 P-side
bound via amplituhedron). Here `VRank` is the abstract rank functional
and `target` is the polynomial bound (e.g. `n^200`). -/
def PositionCollapseMap {V : Type*} [AddCommGroup V] [Module ℚ V]
    (VRank : V → ℕ) (π : V →ₗ[ℚ] V)
    (compiledPoly : V) (target : ℕ) : Prop :=
  VRank (π compiledPoly) ≤ target

/-- Abstract **identity-minor preservation** (paper §28.3 NP-side for
SAT-deciders). The projection preserves a combinatorial lower bound
on a specified compiled polynomial. -/
def IdentityMinorPreservation {V : Type*} [AddCommGroup V] [Module ℚ V]
    (VRank : V → ℕ) (π : V →ₗ[ℚ] V)
    (satCompiledPoly : V) (lower : ℕ) : Prop :=
  lower ≤ VRank (π satCompiledPoly)

/-! ## Sandwich from the two paper-deep claims

If a projection satisfies both (A) and (B) and the same input polynomial
is both `compiledPoly` and `satCompiledPoly` (i.e., the DTM decides SAT),
then the rank `r = VRank(π p)` lies in `[lower, target]`. This is the
rank sandwich the main axiom asserts. -/

theorem rank_sandwich_from_projection
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (VRank : V → ℕ) (π : V →ₗ[ℚ] V) (p : V)
    (target lower : ℕ)
    (hPC : PositionCollapseMap VRank π p target)
    (hIM : IdentityMinorPreservation VRank π p lower) :
    ∃ r : ℕ, lower ≤ r ∧ r ≤ target :=
  ⟨VRank (π p), hIM, hPC⟩

/-- **Arithmetic gap ⇒ impossibility**: if `target < lower`, no such
`r` can exist. The paper's content is precisely this arithmetic gap
at `n = 2^804`: `n^200 < C(n/3, log n)`. -/
theorem rank_sandwich_impossible_of_arith_gap
    (target lower : ℕ) (hgap : target < lower) :
    ¬ ∃ r : ℕ, lower ≤ r ∧ r ≤ target := by
  rintro ⟨r, hr_lo, hr_hi⟩
  omega

/-! ## Summary of what remains paper-deep

Constructing Π⋆ concretely requires:
1. A ℚ-linear projection π realizing position-collapse on generic
   compiled polynomials (paper §28.3 amplituhedron construction).
2. Verification of the P-side bound (property A) — n^200 follows
   from the polynomial complexity of the DTM's transition table under
   position collapse.
3. Verification of the NP-side lower bound (property B) — the
   identity minor structure survives under π on SAT-decider compiled
   polynomials because DecidesSAT pins down the tableau's clause data.

The gauge axiom `exists_amplituhedron_gauge` asserts all three exist.
This file shows how they assemble into a rank sandwich, which by the
arithmetic gap at `n = 2^804` yields the separation. -/

end AmplituhedronGaugeScaffold
