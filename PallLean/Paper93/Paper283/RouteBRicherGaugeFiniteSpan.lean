import PallLean.Paper93.Paper283.RouteBTransportNPIdentityMinor
import PallLean.Paper93.Paper283.RouteBKeepFOBFiniteRankNoGo
import PallLean.Paper93.Paper283.RouteBGaugeCandidate
import PallLean.Paper93.NFrame.UnitPreservingAdmissible
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Route B richer finite-span candidate gauges

This file constructs finite-rank NFrame `CandidateGauge`s whose range is a
chosen finite span of Route B/Cook-Levin rows.  It is deliberately not the
constants projection and not the full `keepFOB` map: the constructed projection
has finite-dimensional range by construction, and the fixed-row theorem below
is the exact finite-span projection lemma needed by the fixed-embed NP
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

/-- The noncomputable linear projection onto a selected submodule, using an
arbitrary complement over the field `ℚ`. -/
noncomputable def finiteSubmoduleProjection {N : Nat}
    (S : Submodule ℚ (Ambient N)) :
    Ambient N →ₗ[ℚ] Ambient N :=
  let q := Classical.choose S.exists_isCompl
  let hq : IsCompl S q := Classical.choose_spec S.exists_isCompl
  Submodule.IsCompl.projection hq

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

/-- Every specified row is fixed by the finite-rows candidate. -/
theorem finiteRowsCandidateGauge_fixes_row {N m : Nat}
    (rows : Fin m → Ambient N) (i : Fin m) :
    (finiteRowsCandidateGauge rows).projection (rows i) = rows i := by
  haveI : Module.Finite ℚ (finiteRowsSubmodule rows) :=
    finiteRowsSubmodule_finite rows
  exact candidateGaugeOfFiniteSubmodule_fixed_of_mem
    (finiteRowsSubmodule rows)
    (Submodule.subset_span ⟨i, rfl⟩)

/-- Route B finite-span candidate gauge for specified Cook-Levin witness rows. -/
noncomputable def routeBRicherFiniteRowsCandidateGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {m : Nat} (rows : Fin m → RouteBCLSpace M n hn2 htb hns) :
    PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns) :=
  finiteRowsCandidateGauge rows

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

/-- Any Route B finite-span candidate is not the full `keepFOB` projection as a
SAT-side map.  This follows from the general finite-rank no-go theorem. -/
theorem routeBRicherFiniteRowsCandidateGauge_ne_keepFOB
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {m : Nat} (rows : Fin m → RouteBCLSpace M n hn2 htb hns) :
    routeBNFrameCandidateAsSATGauge M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows) ≠
      satDeciderGaugeKeepFOBProjection M n hn2 htb hns :=
  candidate_projection_ne_satDeciderGaugeKeepFOBProjection
    M n hn2 htb hns
    (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)

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

#print axioms finiteSubmoduleProjection_range
#print axioms finiteSubmoduleProjection_fixed_of_mem
#print axioms finiteSubmoduleProjection_idempotent
#print axioms candidateGaugeOfFiniteSubmodule
#print axioms finiteRowsCandidateGauge_fixes_row
#print axioms routeBRicherFiniteRowsCandidateGauge_fixes_row
#print axioms routeBRicherFiniteRowsCandidateGauge_npIdentityMinorFixedEmbedCertificate
#print axioms routeBRicherFiniteRowsCandidateGauge_ne_keepFOB
#print axioms routeBRicherFiniteRowsCandidateGauge_ne_constantsCandidateGauge_of_row

end PallLean.Paper93.Paper283
