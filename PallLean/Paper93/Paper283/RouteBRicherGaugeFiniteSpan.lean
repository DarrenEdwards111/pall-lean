import PallLean.Paper93.Paper283.RouteBTransportNPIdentityMinor
import PallLean.Paper93.Paper283.RouteBGaugeCandidate
import PallLean.Paper93.NFrame.UnitPreservingAdmissible
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Route B richer finite-span candidate gauges

This file constructs finite-rank NFrame `CandidateGauge`s whose range is a
chosen finite span of Route B/Cook-Levin rows.  It is deliberately not the
constants projection: the constructed projection has finite-dimensional range
by construction, and the fixed-row theorem below is the exact finite-span
projection lemma needed by the fixed-embed NP
identity-minor transport surface.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open TuringMachine
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulCompilation
open PaperFaithfulSeparation

attribute [local instance] Classical.dec

/-- Ambient polynomial row space for an `N`-variable NFrame candidate. -/
private abbrev Ambient (N : Nat) :=
  MvPolynomial (Fin N) ℚ

/-- Route B Cook-Levin ambient polynomial row space. -/
private abbrev RouteBCLSpace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :=
  Ambient (RouteBCookLevinDim M n hn2 htb hns)

/-- Linear projection onto a selected submodule along an explicitly supplied
complement.  This is the designable version of `finiteSubmoduleProjection`:
the existing projection below chooses the complement by `Classical.choose`,
while this interface lets Route B carry a complement selected for SPDP
invariance. -/
noncomputable def finiteSubmoduleProjectionWithComplement {N : Nat}
    (S C : Submodule ℚ (Ambient N)) (hC : IsCompl S C) :
    Ambient N →ₗ[ℚ] Ambient N :=
  Submodule.IsCompl.projection hC

/-- The noncomputable linear projection onto a selected submodule, using an
arbitrary complement over the field `ℚ`. -/
noncomputable def finiteSubmoduleProjection {N : Nat}
    (S : Submodule ℚ (Ambient N)) :
    Ambient N →ₗ[ℚ] Ambient N :=
  let q := Classical.choose S.exists_isCompl
  let hq : IsCompl S q := Classical.choose_spec S.exists_isCompl
  Submodule.IsCompl.projection hq

/-- The arbitrary complement selected by `finiteSubmoduleProjection`.  Exposing
this submodule makes the residual/kernal obstruction concrete: kernel
compatibility is invariance of this chosen complement under the relevant
generator maps. -/
noncomputable def finiteSubmoduleProjectionComplement {N : Nat}
    (S : Submodule ℚ (Ambient N)) :
    Submodule ℚ (Ambient N) :=
  Classical.choose S.exists_isCompl

/-- The selected complement is complementary to `S`. -/
theorem finiteSubmoduleProjection_isCompl {N : Nat}
    (S : Submodule ℚ (Ambient N)) :
    IsCompl S (finiteSubmoduleProjectionComplement S) := by
  unfold finiteSubmoduleProjectionComplement
  exact Classical.choose_spec S.exists_isCompl

/-- The explicit-complement projection has exactly range `S`. -/
theorem finiteSubmoduleProjectionWithComplement_range {N : Nat}
    (S C : Submodule ℚ (Ambient N)) (hC : IsCompl S C) :
    LinearMap.range (finiteSubmoduleProjectionWithComplement S C hC) = S := by
  unfold finiteSubmoduleProjectionWithComplement
  exact Submodule.IsCompl.projection_range hC

/-- The explicit-complement projection fixes every row in `S`. -/
theorem finiteSubmoduleProjectionWithComplement_fixed_of_mem {N : Nat}
    (S C : Submodule ℚ (Ambient N)) (hC : IsCompl S C)
    {p : Ambient N} (hp : p ∈ S) :
    finiteSubmoduleProjectionWithComplement S C hC p = p := by
  unfold finiteSubmoduleProjectionWithComplement
  exact Submodule.IsCompl.projection_apply_left hC ⟨p, hp⟩

/-- The explicit-complement projection is idempotent. -/
theorem finiteSubmoduleProjectionWithComplement_idempotent {N : Nat}
    (S C : Submodule ℚ (Ambient N)) (hC : IsCompl S C) :
    (finiteSubmoduleProjectionWithComplement S C hC).comp
        (finiteSubmoduleProjectionWithComplement S C hC) =
      finiteSubmoduleProjectionWithComplement S C hC := by
  apply LinearMap.ext
  intro p
  rw [LinearMap.comp_apply]
  unfold finiteSubmoduleProjectionWithComplement
  exact Submodule.IsCompl.projection_apply_left hC
    ⟨Submodule.IsCompl.projection hC p,
      Submodule.IsCompl.projection_apply_mem hC p⟩

/-- The kernel of the explicit-complement projection is exactly the supplied
complement. -/
theorem finiteSubmoduleProjectionWithComplement_ker {N : Nat}
    (S C : Submodule ℚ (Ambient N)) (hC : IsCompl S C) :
    LinearMap.ker (finiteSubmoduleProjectionWithComplement S C hC) = C := by
  unfold finiteSubmoduleProjectionWithComplement
  exact Submodule.IsCompl.projection_ker hC

/-- Pointwise zero criterion for the explicit-complement projection. -/
theorem finiteSubmoduleProjectionWithComplement_apply_eq_zero_iff {N : Nat}
    (S C : Submodule ℚ (Ambient N)) (hC : IsCompl S C) (p : Ambient N) :
    finiteSubmoduleProjectionWithComplement S C hC p = 0 ↔ p ∈ C := by
  change p ∈ LinearMap.ker (finiteSubmoduleProjectionWithComplement S C hC) ↔
    p ∈ C
  rw [finiteSubmoduleProjectionWithComplement_ker S C hC]

/-- The projection onto `S` has exactly range `S`. -/
theorem finiteSubmoduleProjection_range {N : Nat}
    (S : Submodule ℚ (Ambient N)) :
    LinearMap.range (finiteSubmoduleProjection S) = S := by
  unfold finiteSubmoduleProjection
  exact Submodule.IsCompl.projection_range
    (Classical.choose_spec S.exists_isCompl)

/-- The projection onto `S` fixes every row in `S`. -/
theorem finiteSubmoduleProjection_fixed_of_mem {N : Nat}
    (S : Submodule ℚ (Ambient N)) {p : Ambient N}
    (hp : p ∈ S) :
    finiteSubmoduleProjection S p = p := by
  unfold finiteSubmoduleProjection
  let q := Classical.choose S.exists_isCompl
  let hq : IsCompl S q := Classical.choose_spec S.exists_isCompl
  exact Submodule.IsCompl.projection_apply_left hq ⟨p, hp⟩

/-- The projection onto `S` is idempotent. -/
theorem finiteSubmoduleProjection_idempotent {N : Nat}
    (S : Submodule ℚ (Ambient N)) :
    (finiteSubmoduleProjection S).comp (finiteSubmoduleProjection S) =
      finiteSubmoduleProjection S := by
  apply LinearMap.ext
  intro p
  rw [LinearMap.comp_apply]
  unfold finiteSubmoduleProjection
  let q := Classical.choose S.exists_isCompl
  let hq : IsCompl S q := Classical.choose_spec S.exists_isCompl
  exact Submodule.IsCompl.projection_apply_left hq
    ⟨Submodule.IsCompl.projection hq p,
      Submodule.IsCompl.projection_apply_mem hq p⟩

/-- The kernel of `finiteSubmoduleProjection S` is exactly the selected
arbitrary complement. -/
theorem finiteSubmoduleProjection_ker {N : Nat}
    (S : Submodule ℚ (Ambient N)) :
    LinearMap.ker (finiteSubmoduleProjection S) =
      finiteSubmoduleProjectionComplement S := by
  unfold finiteSubmoduleProjection finiteSubmoduleProjectionComplement
  exact Submodule.IsCompl.projection_ker
    (Classical.choose_spec S.exists_isCompl)

/-- Pointwise zero criterion for the finite-submodule projection. -/
theorem finiteSubmoduleProjection_apply_eq_zero_iff {N : Nat}
    (S : Submodule ℚ (Ambient N)) (p : Ambient N) :
    finiteSubmoduleProjection S p = 0 ↔
      p ∈ finiteSubmoduleProjectionComplement S := by
  rw [← finiteSubmoduleProjection_ker S]
  rfl

/-- Any finite-dimensional submodule gives a finite-rank `CandidateGauge` whose
range is that submodule. -/
noncomputable def candidateGaugeOfFiniteSubmodule {N : Nat}
    (S : Submodule ℚ (Ambient N)) [Module.Finite ℚ S] :
    PallLean.Paper93.NFrame.CandidateGauge N where
  projection := finiteSubmoduleProjection S
  is_idempotent := finiteSubmoduleProjection_idempotent S
  rank_finite := by
    rw [finiteSubmoduleProjection_range S]
    infer_instance

/-- The candidate built from `S` has range exactly `S`. -/
theorem candidateGaugeOfFiniteSubmodule_range {N : Nat}
    (S : Submodule ℚ (Ambient N)) [Module.Finite ℚ S] :
    LinearMap.range (candidateGaugeOfFiniteSubmodule S).projection = S :=
  finiteSubmoduleProjection_range S

/-- The candidate built from `S` fixes every row in `S`. -/
theorem candidateGaugeOfFiniteSubmodule_fixed_of_mem {N : Nat}
    (S : Submodule ℚ (Ambient N)) [Module.Finite ℚ S]
    {p : Ambient N} (hp : p ∈ S) :
    (candidateGaugeOfFiniteSubmodule S).projection p = p :=
  finiteSubmoduleProjection_fixed_of_mem S hp

/-- Finite-rank `CandidateGauge` whose range is `S` and whose kernel is the
explicit supplied complement `C`. -/
noncomputable def candidateGaugeOfFiniteSubmoduleWithComplement {N : Nat}
    (S C : Submodule ℚ (Ambient N)) [Module.Finite ℚ S]
    (hC : IsCompl S C) :
    PallLean.Paper93.NFrame.CandidateGauge N where
  projection := finiteSubmoduleProjectionWithComplement S C hC
  is_idempotent := finiteSubmoduleProjectionWithComplement_idempotent S C hC
  rank_finite := by
    rw [finiteSubmoduleProjectionWithComplement_range S C hC]
    infer_instance

/-- The explicit-complement candidate built from `S, C` has range exactly
`S`. -/
theorem candidateGaugeOfFiniteSubmoduleWithComplement_range {N : Nat}
    (S C : Submodule ℚ (Ambient N)) [Module.Finite ℚ S]
    (hC : IsCompl S C) :
    LinearMap.range
        (candidateGaugeOfFiniteSubmoduleWithComplement S C hC).projection =
      S :=
  finiteSubmoduleProjectionWithComplement_range S C hC

/-- The explicit-complement candidate built from `S, C` fixes every row in
`S`. -/
theorem candidateGaugeOfFiniteSubmoduleWithComplement_fixed_of_mem {N : Nat}
    (S C : Submodule ℚ (Ambient N)) [Module.Finite ℚ S]
    (hC : IsCompl S C) {p : Ambient N} (hp : p ∈ S) :
    (candidateGaugeOfFiniteSubmoduleWithComplement S C hC).projection p = p :=
  finiteSubmoduleProjectionWithComplement_fixed_of_mem S C hC hp

/-- Pointwise zero criterion for the explicit-complement candidate. -/
theorem candidateGaugeOfFiniteSubmoduleWithComplement_apply_eq_zero_iff {N : Nat}
    (S C : Submodule ℚ (Ambient N)) [Module.Finite ℚ S]
    (hC : IsCompl S C) (p : Ambient N) :
    (candidateGaugeOfFiniteSubmoduleWithComplement S C hC).projection p = 0 ↔
      p ∈ C :=
  finiteSubmoduleProjectionWithComplement_apply_eq_zero_iff S C hC p

/-- The finite span of a specified finite row family. -/
noncomputable def finiteRowsSubmodule {N m : Nat}
    (rows : Fin m → Ambient N) : Submodule ℚ (Ambient N) :=
  Submodule.span ℚ (Set.range rows)

/-- A finite row span is finite-dimensional. -/
theorem finiteRowsSubmodule_finite {N m : Nat}
    (rows : Fin m → Ambient N) :
    Module.Finite ℚ (finiteRowsSubmodule rows) :=
  Module.Finite.span_of_finite ℚ (Set.finite_range rows)

/-- Finite-span candidate gauge for a specified finite row family. -/
noncomputable def finiteRowsCandidateGauge {N m : Nat}
    (rows : Fin m → Ambient N) :
    PallLean.Paper93.NFrame.CandidateGauge N :=
  haveI : Module.Finite ℚ (finiteRowsSubmodule rows) :=
    finiteRowsSubmodule_finite rows
  candidateGaugeOfFiniteSubmodule (finiteRowsSubmodule rows)

/-- Finite-span candidate gauge for a specified finite row family and an
explicit complement to that row span. -/
noncomputable def finiteRowsCandidateGaugeWithComplement {N m : Nat}
    (rows : Fin m → Ambient N) (C : Submodule ℚ (Ambient N))
    (hC : IsCompl (finiteRowsSubmodule rows) C) :
    PallLean.Paper93.NFrame.CandidateGauge N :=
  haveI : Module.Finite ℚ (finiteRowsSubmodule rows) :=
    finiteRowsSubmodule_finite rows
  candidateGaugeOfFiniteSubmoduleWithComplement (finiteRowsSubmodule rows) C hC

/-- The range of the finite-rows candidate is the finite span of the rows. -/
theorem finiteRowsCandidateGauge_range {N m : Nat}
    (rows : Fin m → Ambient N) :
    LinearMap.range (finiteRowsCandidateGauge rows).projection =
      finiteRowsSubmodule rows := by
  haveI : Module.Finite ℚ (finiteRowsSubmodule rows) :=
    finiteRowsSubmodule_finite rows
  unfold finiteRowsCandidateGauge
  exact candidateGaugeOfFiniteSubmodule_range (finiteRowsSubmodule rows)

/-- Every specified row belongs to the range of the finite-rows candidate. -/
theorem finiteRowsCandidateGauge_range_contains_row {N m : Nat}
    (rows : Fin m → Ambient N) (i : Fin m) :
    rows i ∈ LinearMap.range (finiteRowsCandidateGauge rows).projection := by
  rw [finiteRowsCandidateGauge_range rows]
  exact Submodule.subset_span ⟨i, rfl⟩

/-- The range of the explicit-complement finite-rows candidate is the finite
span of the rows. -/
theorem finiteRowsCandidateGaugeWithComplement_range {N m : Nat}
    (rows : Fin m → Ambient N) (C : Submodule ℚ (Ambient N))
    (hC : IsCompl (finiteRowsSubmodule rows) C) :
    LinearMap.range (finiteRowsCandidateGaugeWithComplement rows C hC).projection =
      finiteRowsSubmodule rows := by
  haveI : Module.Finite ℚ (finiteRowsSubmodule rows) :=
    finiteRowsSubmodule_finite rows
  unfold finiteRowsCandidateGaugeWithComplement
  exact
    candidateGaugeOfFiniteSubmoduleWithComplement_range
      (finiteRowsSubmodule rows) C hC

/-- Every specified row is fixed by the finite-rows candidate. -/
theorem finiteRowsCandidateGauge_fixes_row {N m : Nat}
    (rows : Fin m → Ambient N) (i : Fin m) :
    (finiteRowsCandidateGauge rows).projection (rows i) = rows i := by
  haveI : Module.Finite ℚ (finiteRowsSubmodule rows) :=
    finiteRowsSubmodule_finite rows
  exact candidateGaugeOfFiniteSubmodule_fixed_of_mem
    (finiteRowsSubmodule rows)
    (Submodule.subset_span ⟨i, rfl⟩)

/-- Every specified row is fixed by the explicit-complement finite-rows
candidate. -/
theorem finiteRowsCandidateGaugeWithComplement_fixes_row {N m : Nat}
    (rows : Fin m → Ambient N) (C : Submodule ℚ (Ambient N))
    (hC : IsCompl (finiteRowsSubmodule rows) C) (i : Fin m) :
    (finiteRowsCandidateGaugeWithComplement rows C hC).projection (rows i) =
      rows i := by
  haveI : Module.Finite ℚ (finiteRowsSubmodule rows) :=
    finiteRowsSubmodule_finite rows
  exact
    candidateGaugeOfFiniteSubmoduleWithComplement_fixed_of_mem
      (finiteRowsSubmodule rows) C hC
      (Submodule.subset_span ⟨i, rfl⟩)

/-- The kernel of a finite-rows candidate projection is the arbitrary complement
selected for its finite row span. -/
theorem finiteRowsCandidateGauge_projection_apply_eq_zero_iff {N m : Nat}
    (rows : Fin m → Ambient N) (p : Ambient N) :
    (finiteRowsCandidateGauge rows).projection p = 0 ↔
      p ∈ finiteSubmoduleProjectionComplement (finiteRowsSubmodule rows) := by
  haveI : Module.Finite ℚ (finiteRowsSubmodule rows) :=
    finiteRowsSubmodule_finite rows
  unfold finiteRowsCandidateGauge
  simpa [candidateGaugeOfFiniteSubmodule] using
    finiteSubmoduleProjection_apply_eq_zero_iff
      (finiteRowsSubmodule rows) p

/-- Pointwise zero criterion for the explicit-complement finite-row
projection. -/
theorem finiteRowsCandidateGaugeWithComplement_projection_apply_eq_zero_iff
    {N m : Nat}
    (rows : Fin m → Ambient N) (C : Submodule ℚ (Ambient N))
    (hC : IsCompl (finiteRowsSubmodule rows) C) (p : Ambient N) :
    (finiteRowsCandidateGaugeWithComplement rows C hC).projection p = 0 ↔
      p ∈ C := by
  haveI : Module.Finite ℚ (finiteRowsSubmodule rows) :=
    finiteRowsSubmodule_finite rows
  unfold finiteRowsCandidateGaugeWithComplement
  simpa [candidateGaugeOfFiniteSubmoduleWithComplement] using
    finiteSubmoduleProjectionWithComplement_apply_eq_zero_iff
      (finiteRowsSubmodule rows) C hC p

/-- Route B finite-span candidate gauge for specified Cook-Levin witness rows. -/
noncomputable def routeBRicherFiniteRowsCandidateGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {m : Nat} (rows : Fin m → RouteBCLSpace M n hn2 htb hns) :
    PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns) :=
  finiteRowsCandidateGauge rows

/-- Route B finite-span candidate gauge with an explicit complement to the
specified Cook-Levin row span. -/
noncomputable def routeBRicherFiniteRowsCandidateGaugeWithComplement
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {m : Nat} (rows : Fin m → RouteBCLSpace M n hn2 htb hns)
    (C : Submodule ℚ (RouteBCLSpace M n hn2 htb hns))
    (hC : IsCompl (finiteRowsSubmodule rows) C) :
    PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns) :=
  finiteRowsCandidateGaugeWithComplement rows C hC

/-- The Route B finite-span candidate has range equal to the span of the
specified Cook-Levin witness rows. -/
theorem routeBRicherFiniteRowsCandidateGauge_range
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {m : Nat} (rows : Fin m → RouteBCLSpace M n hn2 htb hns) :
    LinearMap.range
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows).projection =
      finiteRowsSubmodule rows := by
  unfold routeBRicherFiniteRowsCandidateGauge
  exact finiteRowsCandidateGauge_range rows

/-- The explicit-complement Route B finite-span candidate has range equal to
the span of the specified Cook-Levin witness rows. -/
theorem routeBRicherFiniteRowsCandidateGaugeWithComplement_range
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {m : Nat} (rows : Fin m → RouteBCLSpace M n hn2 htb hns)
    (C : Submodule ℚ (RouteBCLSpace M n hn2 htb hns))
    (hC : IsCompl (finiteRowsSubmodule rows) C) :
    LinearMap.range
        (routeBRicherFiniteRowsCandidateGaugeWithComplement
          M n hn2 htb hns rows C hC).projection =
      finiteRowsSubmodule rows := by
  unfold routeBRicherFiniteRowsCandidateGaugeWithComplement
  exact finiteRowsCandidateGaugeWithComplement_range rows C hC

/-- The Route B finite-span candidate range contains each specified
Cook-Levin witness row. -/
theorem routeBRicherFiniteRowsCandidateGauge_range_contains_row
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {m : Nat} (rows : Fin m → RouteBCLSpace M n hn2 htb hns) (i : Fin m) :
    rows i ∈ LinearMap.range
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows).projection := by
  unfold routeBRicherFiniteRowsCandidateGauge
  exact finiteRowsCandidateGauge_range_contains_row rows i

/-- The Route B finite-span candidate fixes each specified Cook-Levin witness
row.  This is the local constructor lemma needed for fixed-embed NP transport. -/
theorem routeBRicherFiniteRowsCandidateGauge_fixes_row
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {m : Nat} (rows : Fin m → RouteBCLSpace M n hn2 htb hns) (i : Fin m) :
    (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows).projection
        (rows i) =
      rows i := by
  unfold routeBRicherFiniteRowsCandidateGauge
  exact finiteRowsCandidateGauge_fixes_row rows i

/-- The explicit-complement Route B finite-span candidate fixes each specified
Cook-Levin witness row. -/
theorem routeBRicherFiniteRowsCandidateGaugeWithComplement_fixes_row
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {m : Nat} (rows : Fin m → RouteBCLSpace M n hn2 htb hns)
    (C : Submodule ℚ (RouteBCLSpace M n hn2 htb hns))
    (hC : IsCompl (finiteRowsSubmodule rows) C) (i : Fin m) :
    (routeBRicherFiniteRowsCandidateGaugeWithComplement
        M n hn2 htb hns rows C hC).projection (rows i) =
      rows i := by
  unfold routeBRicherFiniteRowsCandidateGaugeWithComplement
  exact finiteRowsCandidateGaugeWithComplement_fixes_row rows C hC i

/-- Pointwise zero criterion for the Route B finite-row projection. -/
theorem routeBRicherFiniteRowsCandidateGauge_projection_apply_eq_zero_iff
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {m : Nat} (rows : Fin m → RouteBCLSpace M n hn2 htb hns)
    (p : RouteBCLSpace M n hn2 htb hns) :
    (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows).projection p = 0 ↔
      p ∈ finiteSubmoduleProjectionComplement (finiteRowsSubmodule rows) := by
  unfold routeBRicherFiniteRowsCandidateGauge
  exact finiteRowsCandidateGauge_projection_apply_eq_zero_iff rows p

/-- Pointwise zero criterion for the explicit-complement Route B finite-row
projection. -/
theorem routeBRicherFiniteRowsCandidateGaugeWithComplement_projection_apply_eq_zero_iff
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {m : Nat} (rows : Fin m → RouteBCLSpace M n hn2 htb hns)
    (C : Submodule ℚ (RouteBCLSpace M n hn2 htb hns))
    (hC : IsCompl (finiteRowsSubmodule rows) C)
    (p : RouteBCLSpace M n hn2 htb hns) :
    (routeBRicherFiniteRowsCandidateGaugeWithComplement
        M n hn2 htb hns rows C hC).projection p = 0 ↔
      p ∈ C := by
  unfold routeBRicherFiniteRowsCandidateGaugeWithComplement
  exact
    finiteRowsCandidateGaugeWithComplement_projection_apply_eq_zero_iff
      rows C hC p

/-- A finite-span candidate fixing an embedded source obstruction yields the
Route B fixed-embed NP certificate once extraction and the source lower bound
are supplied.

This theorem is the precise reduction from "construct a richer finite-rank
gauge containing the witness row" to the already-existing projected
identity-minor transport lemma. -/
noncomputable def routeBRicherFiniteRowsCandidateGauge_npIdentityMinorFixedEmbedCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {m : Nat} (rows : Fin m → RouteBCLSpace M n hn2 htb hns)
    (i : Fin m)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (hrow :
      rows i =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q) :
    RouteBNPIdentityMinorFixedEmbedCertificate M n hn2 htb hns
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows) where
  Q := Q
  fixed_embed := by
    rw [← hrow]
    exact routeBRicherFiniteRowsCandidateGauge_fixes_row
      M n hn2 htb hns rows i
  extracts_compiled := hextract
  source_lower_bound := hsource

/-- Criterion showing a finite-span candidate is genuinely not the constants
candidate: it suffices that it fixes one row not fixed by the constants
projection. -/
theorem routeBRicherFiniteRowsCandidateGauge_ne_constantsCandidateGauge_of_row
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {m : Nat} (rows : Fin m → RouteBCLSpace M n hn2 htb hns) (i : Fin m)
    (hnotConstFixed :
      (routeBConstantsCandidateGauge M n hn2 htb hns).projection (rows i) ≠
        rows i) :
    routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows ≠
      routeBConstantsCandidateGauge M n hn2 htb hns := by
  intro hEq
  have hfix :
      (routeBConstantsCandidateGauge M n hn2 htb hns).projection (rows i) =
        rows i := by
    rw [← hEq]
    exact routeBRicherFiniteRowsCandidateGauge_fixes_row
      M n hn2 htb hns rows i
  exact hnotConstFixed hfix

/-! ## Axiom audit anchors -/

#print axioms finiteSubmoduleProjectionWithComplement
#print axioms finiteSubmoduleProjectionWithComplement_range
#print axioms finiteSubmoduleProjectionWithComplement_fixed_of_mem
#print axioms finiteSubmoduleProjectionWithComplement_idempotent
#print axioms finiteSubmoduleProjectionWithComplement_ker
#print axioms finiteSubmoduleProjectionWithComplement_apply_eq_zero_iff
#print axioms finiteSubmoduleProjection_range
#print axioms finiteSubmoduleProjection_fixed_of_mem
#print axioms finiteSubmoduleProjection_idempotent
#print axioms finiteSubmoduleProjectionComplement
#print axioms finiteSubmoduleProjection_isCompl
#print axioms finiteSubmoduleProjection_ker
#print axioms finiteSubmoduleProjection_apply_eq_zero_iff
#print axioms candidateGaugeOfFiniteSubmodule
#print axioms candidateGaugeOfFiniteSubmoduleWithComplement
#print axioms finiteRowsCandidateGauge_fixes_row
#print axioms finiteRowsCandidateGaugeWithComplement_fixes_row
#print axioms finiteRowsCandidateGauge_projection_apply_eq_zero_iff
#print axioms finiteRowsCandidateGaugeWithComplement_projection_apply_eq_zero_iff
#print axioms routeBRicherFiniteRowsCandidateGauge_fixes_row
#print axioms routeBRicherFiniteRowsCandidateGaugeWithComplement_fixes_row
#print axioms routeBRicherFiniteRowsCandidateGauge_projection_apply_eq_zero_iff
#print axioms routeBRicherFiniteRowsCandidateGaugeWithComplement_projection_apply_eq_zero_iff
#print axioms routeBRicherFiniteRowsCandidateGauge_npIdentityMinorFixedEmbedCertificate
#print axioms routeBRicherFiniteRowsCandidateGauge_ne_constantsCandidateGauge_of_row

end PallLean.Paper93.Paper283
