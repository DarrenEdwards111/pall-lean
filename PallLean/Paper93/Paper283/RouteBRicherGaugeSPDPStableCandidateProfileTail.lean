import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidate
import PallLean.Paper93.Paper283.RouteBRicherGaugeConcreteMultilinearTail
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateNoGo

/-!
# Multilinear-coverage abstraction for the smaller SPDP-stable candidate

This file factors the broad multilinear-tail proof of `SelectedRowClosure`
through abstract sufficient conditions.  Three predicates are introduced:

* `RouteBRicherSPDPStableCandidateMlCovering tail` — every `mlProj` output
  already lies in the prepended row span.  This is what the broad
  multilinear tail satisfies vacuously.

* `RouteBRicherSPDPStableCandidateOrbitMlCovering tail` — only the `mlProj`
  outputs that arise as Route B SPDP generator rows of the head row or of
  some `tail i` need be in the prepended row span, weaker than `MlCovering`.

* `RouteBRicherSPDPStableCandidateAdmissibleOrbitMlCovering tail` — the same
  coverage restricted to the admissible `(S, shift)` side conditions that the
  SPDP row-closure package actually consumes.  This is the sharp finite-tail
  target for a concrete profile-window construction.

The key narrowing observation
(`routeBRicherSPDPStableCandidate_residualInvisible_iff_residualGeneratorZero_of_mlCovering`)
is that any tail satisfying `MlCovering` reduces `ResidualInvisible` to the
strict `ResidualGeneratorZero` condition that the broad multilinear tail
provably cannot meet (cf. `RouteBRicherGaugeConcreteMultilinearNoGo`).
Hence the live design space for `SelectedRowClosure ∧ ResidualInvisible`
consists precisely of tails satisfying `OrbitMlCovering` but **not**
`MlCovering`.

A natural source of such tails (per Lemma 213 of the paper) is the
canonical-window profile alphabet at `R = Θ(log n)`, whose multilinear span
covers the head/tail orbit but not every `mlProj p`.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Every `mlProj` output already lies in the prepended row span.  This is
the broad-tail-style sufficient condition for the row-closure package. -/
def RouteBRicherSPDPStableCandidateMlCovering
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) : Prop :=
  forall q : SATDeciderGaugeSpace M n hn2 htb hns,
    mlProj q ∈ finiteRowsSubmodule
      (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail)

/-- Orbit-restricted multilinear coverage: only generator rows produced from
the concrete NP head row and from each `tail i` need to lie in the
prepended row span.  This is the precise minimal sufficient condition for
the head/tail row-closure package. -/
def RouteBRicherSPDPStableCandidateOrbitMlCovering
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) : Prop :=
  forall (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    routeBSPDPGeneratorRow M n hn2 htb hns
        (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) S shift ∈
        finiteRowsSubmodule
          (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail) ∧
    forall i : Fin m,
      routeBSPDPGeneratorRow M n hn2 htb hns (tail i) S shift ∈
        finiteRowsSubmodule
          (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail)

/-- Admissible orbit-restricted multilinear coverage: the same head/tail
orbit coverage as `RouteBRicherSPDPStableCandidateOrbitMlCovering`, but only
for the admissible shifts that the concrete prepended row-closure package
actually asks for.  This is the sharp target for a concrete profile-window
tail. -/
def RouteBRicherSPDPStableCandidateAdmissibleOrbitMlCovering
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) : Prop :=
  forall (spdpKappa ell : Nat)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    routeBSPDPGeneratorRow M n hn2 htb hns
        (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) S shift ∈
        finiteRowsSubmodule
          (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail) ∧
    forall i : Fin m,
      routeBSPDPGeneratorRow M n hn2 htb hns (tail i) S shift ∈
        finiteRowsSubmodule
          (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail)

/-- Log-window orbit coverage: the profile-window target only asks to cover
admissible head/tail generator rows whose touched-variable list and shift
degree both lie inside the canonical `Nat.log 2 n` window. -/
def RouteBRicherSPDPStableCandidateLogWindowOrbitMlCovering
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) : Prop :=
  forall (spdpKappa ell : Nat)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    S.length <= Nat.log 2 n ->
    shift.totalDegree <= Nat.log 2 n ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    routeBSPDPGeneratorRow M n hn2 htb hns
        (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) S shift ∈
        finiteRowsSubmodule
          (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail) ∧
    forall i : Fin m,
      routeBSPDPGeneratorRow M n hn2 htb hns (tail i) S shift ∈
        finiteRowsSubmodule
          (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail)

/-- Head-only log-window coverage: the currently reachable finite/profile
coverage target asks only that the concrete NP head row's log-window generator
orbit remain in the selected finite row span. -/
def RouteBRicherSPDPStableCandidateLogWindowHeadMlCovering
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) : Prop :=
  forall (spdpKappa ell : Nat)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    S.length <= Nat.log 2 n ->
    shift.totalDegree <= Nat.log 2 n ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    routeBSPDPGeneratorRow M n hn2 htb hns
        (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) S shift ∈
      finiteRowsSubmodule
        (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail)

/-- Subspace-level finite/profile support target for the concrete NP head row:
for every blocked-SPDP profile inside the canonical log window, the compiled
head's blocked subspace is already contained in the selected finite row span.

This is the natural consumer for a finite profile-window tail: once an
existing finite support/profile lemma proves this submodule containment, the
row-level head coverage theorem below follows without re-opening the concrete
generator syntax. -/
def RouteBRicherSPDPStableCandidateLogWindowHeadSPDPSubspaceCovered
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) : Prop :=
  forall (spdpKappa ell : Nat),
    spdpKappa <= Nat.log 2 n ->
    ell <= Nat.log 2 n ->
    mlBlockedSpdpSubspace
        (cook_levin_compilation M n hn2 htb hns).partition
        spdpKappa ell
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) <=
      finiteRowsSubmodule
        (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail)

/-- Tail-row log-window stability: every selected tail row is closed under the
same log-window generator operators.  This is the remaining finite/profile
stability obligation after head coverage is separated out. -/
def RouteBRicherSPDPStableCandidateLogWindowTailRowStable
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) : Prop :=
  forall (spdpKappa ell : Nat)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    S.length <= Nat.log 2 n ->
    shift.totalDegree <= Nat.log 2 n ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    forall i : Fin m,
      routeBSPDPGeneratorRow M n hn2 htb hns (tail i) S shift ∈
        finiteRowsSubmodule
          (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail)

/-- The side-condition needed to use a log-window tail for the existing
admissible SPDP row-closure API: every admissible query consumed by that API
must actually sit inside the canonical profile window. -/
def RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  forall (spdpKappa ell : Nat)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    S.length <= Nat.log 2 n ∧ shift.totalDegree <= Nat.log 2 n

/-- Log-window complement invariance: the profile-window version of the
projection-kernel obstruction only asks for invariance on admissible generator
queries inside the canonical `Nat.log 2 n` window. -/
def RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) : Prop :=
  forall (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    S.length <= Nat.log 2 n ->
    shift.totalDegree <= Nat.log 2 n ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    p ∈ routeBRicherSPDPStableCandidateProjectionComplement
      M n hn2 htb hns tail ->
    routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∈
      routeBRicherSPDPStableCandidateProjectionComplement
        M n hn2 htb hns tail

/-- Route B's current formal interface for the paper's Section 39
"holographic invariance" principle.

This is intentionally a thin naming layer over the stable-tail work.  In the
Route B finite-row setting, the holographic-invariance content is:

* log-window/profile orbit coverage: every log-sized admissible generator row
  seen from the concrete NP head and selected tail rows remains on the finite
  boundary span;
* log-window complement invariance: the chosen projection complement is
  invisible to the same generator operators.

This is not, by itself, a completed full Section 39 theorem for the current
unbounded SPDP row-closure API.  Promotion to
`RouteBRicherSPDPStableCandidateObligations` below still requires the explicit
window side condition `RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed`
or a replacement windowed consumer API. -/
structure RouteBRicherSPDPStableCandidateHolographicInvariance
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    Prop where
  log_window_orbit_coverage :
    RouteBRicherSPDPStableCandidateLogWindowOrbitMlCovering
      M n hn2 htb hns tail
  log_window_complement_invariant :
    RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
      M n hn2 htb hns tail

/-- A single log-window head generator row escaping the selected span refutes
the holographic-invariance interface. -/
theorem routeBRicherSPDPStableCandidate_not_holographicInvariance_of_logWindowHeadOrbit_escape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hbad :
      exists (spdpKappa ell : Nat)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ∧
        shift.totalDegree <= ell ∧
        S.length <= Nat.log 2 n ∧
        shift.totalDegree <= Nat.log 2 n ∧
        shift.vars <= S.toFinset ∧
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ∧
        routeBSPDPGeneratorRow M n hn2 htb hns
          (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) S shift ∉
          finiteRowsSubmodule
            (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail)) :
    ¬ RouteBRicherSPDPStableCandidateHolographicInvariance
        M n hn2 htb hns tail := by
  intro holo
  obtain ⟨spdpKappa, ell, S, shift,
    hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm, hescape⟩ := hbad
  exact hescape
    (holo.log_window_orbit_coverage spdpKappa ell S shift
      hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm).1

/-- A single log-window tail generator row escaping the selected span refutes
the holographic-invariance interface. -/
theorem routeBRicherSPDPStableCandidate_not_holographicInvariance_of_logWindowTailOrbit_escape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hbad :
      exists (spdpKappa ell : Nat)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns)
        (i : Fin m),
        S.length = spdpKappa ∧
        shift.totalDegree <= ell ∧
        S.length <= Nat.log 2 n ∧
        shift.totalDegree <= Nat.log 2 n ∧
        shift.vars <= S.toFinset ∧
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ∧
        routeBSPDPGeneratorRow M n hn2 htb hns (tail i) S shift ∉
          finiteRowsSubmodule
            (routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail)) :
    ¬ RouteBRicherSPDPStableCandidateHolographicInvariance
        M n hn2 htb hns tail := by
  intro holo
  obtain ⟨spdpKappa, ell, S, shift, i,
    hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm, hescape⟩ := hbad
  have htail :=
    (holo.log_window_orbit_coverage spdpKappa ell S shift
      hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm).2 i
  exact hescape
    htail

/-- A single log-window generator row escaping the chosen complement refutes
the holographic-invariance interface.  This is the complement-escape no-go at
the Section 39 naming seam. -/
theorem routeBRicherSPDPStableCandidate_not_holographicInvariance_of_logWindowComplement_escape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hbad :
      exists (spdpKappa ell : Nat)
        (p : SATDeciderGaugeSpace M n hn2 htb hns)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ∧
        shift.totalDegree <= ell ∧
        S.length <= Nat.log 2 n ∧
        shift.totalDegree <= Nat.log 2 n ∧
        shift.vars <= S.toFinset ∧
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ∧
        p ∈ routeBRicherSPDPStableCandidateProjectionComplement
          M n hn2 htb hns tail ∧
        routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∉
          routeBRicherSPDPStableCandidateProjectionComplement
            M n hn2 htb hns tail) :
    ¬ RouteBRicherSPDPStableCandidateHolographicInvariance
        M n hn2 htb hns tail := by
  intro holo
  obtain ⟨spdpKappa, ell, p, S, shift,
    hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm,
    hpComplement, hescape⟩ := hbad
  exact hescape
    (holo.log_window_complement_invariant spdpKappa ell p S shift
      hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm hpComplement)

/-- Full log-window orbit coverage is exactly the packaging of head coverage
and tail-row stability.  The first piece is the reachable profile-window
coverage theorem; the second names the remaining finite-tail stability
obligation. -/
theorem routeBRicherSPDPStableCandidate_logWindowOrbitMlCovering_of_head_tailStable
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hhead :
      RouteBRicherSPDPStableCandidateLogWindowHeadMlCovering
        M n hn2 htb hns tail)
    (htail :
      RouteBRicherSPDPStableCandidateLogWindowTailRowStable
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateLogWindowOrbitMlCovering
      M n hn2 htb hns tail := by
  intro spdpKappa ell S shift
    hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm
  exact
    ⟨hhead spdpKappa ell S shift
        hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm,
      htail spdpKappa ell S shift
        hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm⟩

/-- Full log-window orbit coverage exposes its head-only component. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadMlCovering_of_logWindowOrbitMlCovering
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcov :
      RouteBRicherSPDPStableCandidateLogWindowOrbitMlCovering
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateLogWindowHeadMlCovering
      M n hn2 htb hns tail := by
  intro spdpKappa ell S shift
    hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm
  exact
    (hcov spdpKappa ell S shift
      hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm).1

/-- Full log-window orbit coverage exposes its tail-row stability component. -/
theorem routeBRicherSPDPStableCandidate_logWindowTailRowStable_of_logWindowOrbitMlCovering
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcov :
      RouteBRicherSPDPStableCandidateLogWindowOrbitMlCovering
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateLogWindowTailRowStable
      M n hn2 htb hns tail := by
  intro spdpKappa ell S shift
    hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm i
  exact
    (hcov spdpKappa ell S shift
      hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm).2 i

/-- A finite/profile subspace cover for the concrete NP head row gives the
row-level log-window head coverage obligation.  The proof queries the
subspace cover at the actual shift degree, so it does not require the ambient
`ell` parameter itself to be bounded by the log window. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadMlCovering_of_headSPDPSubspaceCovered
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcover :
      RouteBRicherSPDPStableCandidateLogWindowHeadSPDPSubspaceCovered
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateLogWindowHeadMlCovering
      M n hn2 htb hns tail := by
  intro spdpKappa ell S shift
    hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm
  have hKappaLog : spdpKappa <= Nat.log 2 n := by
    simpa [hSlen] using hSlog
  have hrowRaw :
      mlProj
          (shift * SPDP.iterDerivList S
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)))
        ∈
        mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition
          spdpKappa shift.totalDegree
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) := by
    exact
      Submodule.subset_span
        ⟨S, shift, hSlen, le_rfl, hshiftVars, hadm, rfl⟩
  exact
    (hcover spdpKappa shift.totalDegree hKappaLog hshiftLog)
      (by
        simpa [routeBSPDPGeneratorRow,
          routeBRicherConcreteNPWitnessRows_zero_eq_compiledPoly] using
          hrowRaw)

/-- Head coverage plus tail-row stability gives the concrete prepended-row
log-window package consumed by the finite-row SPDP frontier. -/
theorem routeBRicherSPDPStableCandidate_spdpLogWindowRowClosurePackage_of_head_tailStable
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hhead :
      RouteBRicherSPDPStableCandidateLogWindowHeadMlCovering
        M n hn2 htb hns tail)
    (htail :
      RouteBRicherSPDPStableCandidateLogWindowTailRowStable
        M n hn2 htb hns tail) :
    RouteBRicherConcreteNPPrependedRowsSPDPLogWindowRowClosurePackage
      M n hn2 htb hns tail where
  concrete_row_closure := by
    intro spdpKappa ell S shift
      hSlen hshiftDegree hSlog hellLog hshiftVars hadm
    exact
      hhead spdpKappa ell S shift
        hSlen hshiftDegree
        (by simpa [hSlen] using hSlog)
        (le_trans hshiftDegree hellLog)
        hshiftVars hadm
  tail_row_closure := by
    intro spdpKappa ell S shift
      hSlen hshiftDegree hSlog hellLog hshiftVars hadm i
    exact
      htail spdpKappa ell S shift
        hSlen hshiftDegree
        (by simpa [hSlen] using hSlog)
        (le_trans hshiftDegree hellLog)
        hshiftVars hadm i

/-- Full log-window orbit coverage gives the concrete prepended-row
log-window row-closure package consumed by the finite-row frontier. -/
theorem routeBRicherSPDPStableCandidate_spdpLogWindowRowClosurePackage_of_logWindowOrbitMlCovering
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcov :
      RouteBRicherSPDPStableCandidateLogWindowOrbitMlCovering
        M n hn2 htb hns tail) :
    RouteBRicherConcreteNPPrependedRowsSPDPLogWindowRowClosurePackage
      M n hn2 htb hns tail :=
  routeBRicherSPDPStableCandidate_spdpLogWindowRowClosurePackage_of_head_tailStable
    M n hn2 htb hns tail
    (routeBRicherSPDPStableCandidate_logWindowHeadMlCovering_of_logWindowOrbitMlCovering
      M n hn2 htb hns tail hcov)
    (routeBRicherSPDPStableCandidate_logWindowTailRowStable_of_logWindowOrbitMlCovering
      M n hn2 htb hns tail hcov)

/-- The concrete prepended-row log-window package gives the stable candidate
log-window orbit coverage target.  The package can be queried at the actual
shift degree, so no separate `ell <= Nat.log 2 n` assumption is needed here. -/
theorem routeBRicherSPDPStableCandidate_logWindowOrbitMlCovering_of_spdpLogWindowRowClosurePackage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (pkg :
      RouteBRicherConcreteNPPrependedRowsSPDPLogWindowRowClosurePackage
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateLogWindowOrbitMlCovering
      M n hn2 htb hns tail := by
  intro spdpKappa ell S shift
    hSlen _hshiftDegree hSlog hshiftLog hshiftVars hadm
  exact
    ⟨pkg.concrete_row_closure
        spdpKappa shift.totalDegree S shift
        hSlen le_rfl
        (by simpa [hSlen] using hSlog)
        hshiftLog hshiftVars hadm,
      pkg.tail_row_closure
        spdpKappa shift.totalDegree S shift
        hSlen le_rfl
        (by simpa [hSlen] using hSlog)
        hshiftLog hshiftVars hadm⟩

/-- A long admissible query refutes the global claim that all admissible SPDP
queries are log-windowed. -/
theorem routeBRicherSPDPStableCandidate_not_admissibleQueriesLogWindowed_of_long_admissible
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      exists (spdpKappa ell : Nat)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ∧
        shift.totalDegree <= ell ∧
        shift.vars <= S.toFinset ∧
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ∧
        Nat.log 2 n < S.length) :
    ¬ RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed
        M n hn2 htb hns := by
  intro hwindow
  obtain ⟨spdpKappa, ell, S, shift,
    hSlen, hshiftDegree, hshiftVars, hadm, hlong⟩ := hbad
  have hSlog :
      S.length <= Nat.log 2 n :=
    (hwindow spdpKappa ell S shift
      hSlen hshiftDegree hshiftVars hadm).1
  exact (Nat.not_lt.mpr hSlog) hlong

/-- A high-degree admissible shift refutes the global claim that all
admissible SPDP queries are log-windowed. -/
theorem routeBRicherSPDPStableCandidate_not_admissibleQueriesLogWindowed_of_highDegree_admissible
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      exists (spdpKappa ell : Nat)
        (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (shift : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = spdpKappa ∧
        shift.totalDegree <= ell ∧
        shift.vars <= S.toFinset ∧
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition S ∧
        Nat.log 2 n < shift.totalDegree) :
    ¬ RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed
        M n hn2 htb hns := by
  intro hwindow
  obtain ⟨spdpKappa, ell, S, shift,
    hSlen, hshiftDegree, hshiftVars, hadm, hhigh⟩ := hbad
  have hshiftLog :
      shift.totalDegree <= Nat.log 2 n :=
    (hwindow spdpKappa ell S shift
      hSlen hshiftDegree hshiftVars hadm).2
  exact (Nat.not_lt.mpr hshiftLog) hhigh

/-- Unrestricted orbit coverage implies the sharp admissible-orbit version. -/
theorem routeBRicherSPDPStableCandidate_admissibleOrbitMlCovering_of_orbitMlCovering
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcov :
      RouteBRicherSPDPStableCandidateOrbitMlCovering
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateAdmissibleOrbitMlCovering
      M n hn2 htb hns tail := by
  intro _spdpKappa _ell S shift _hSlen _hshiftDegree _hshiftVars hadm
  exact hcov S shift hadm

/-- A log-window orbit cover gives the existing admissible-orbit target once
the SPDP API's admissible queries are known to be log-windowed. -/
theorem routeBRicherSPDPStableCandidate_admissibleOrbitMlCovering_of_logWindowOrbitMlCovering
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcov :
      RouteBRicherSPDPStableCandidateLogWindowOrbitMlCovering
        M n hn2 htb hns tail)
    (hwindow :
      RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateAdmissibleOrbitMlCovering
      M n hn2 htb hns tail := by
  intro spdpKappa ell S shift hSlen hshiftDegree hshiftVars hadm
  obtain ⟨hSlog, hshiftLog⟩ :=
    hwindow spdpKappa ell S shift
      hSlen hshiftDegree hshiftVars hadm
  exact
    hcov spdpKappa ell S shift
      hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm

/-- A log-window complement-invariance proof gives the full chosen-complement
invariance target exactly when the admissible SPDP API itself is known to be
log-windowed. -/
theorem routeBRicherSPDPStableCandidate_chosenComplementInvariant_of_logWindowChosenComplementInvariant
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hinvariant :
      RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
        M n hn2 htb hns tail)
    (hwindow :
      RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateChosenComplementInvariant
      M n hn2 htb hns tail := by
  intro spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm hpComplement
  obtain ⟨hSlog, hshiftLog⟩ :=
    hwindow spdpKappa ell S shift
      hSlen hshiftDegree hshiftVars hadm
  exact
    hinvariant spdpKappa ell p S shift
      hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm hpComplement

/-- `MlCovering` is strictly stronger than `OrbitMlCovering`: any
multilinear-covering tail orbit-covers via the trivial expansion. -/
theorem routeBRicherSPDPStableCandidate_orbitMlCovering_of_mlCovering
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcov :
      RouteBRicherSPDPStableCandidateMlCovering
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateOrbitMlCovering
      M n hn2 htb hns tail := by
  intro S shift _hadm
  refine ⟨?_, ?_⟩
  · -- routeBSPDPGeneratorRow ... = mlProj (shift * iterDerivList S npRow)
    simpa [routeBSPDPGeneratorRow] using hcov _
  · intro i
    simpa [routeBSPDPGeneratorRow] using hcov _

/-- `MlCovering` also gives the sharp admissible-orbit coverage target. -/
theorem routeBRicherSPDPStableCandidate_admissibleOrbitMlCovering_of_mlCovering
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcov :
      RouteBRicherSPDPStableCandidateMlCovering
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateAdmissibleOrbitMlCovering
      M n hn2 htb hns tail :=
  routeBRicherSPDPStableCandidate_admissibleOrbitMlCovering_of_orbitMlCovering
    M n hn2 htb hns tail
    (routeBRicherSPDPStableCandidate_orbitMlCovering_of_mlCovering
      M n hn2 htb hns tail hcov)

/-- Full multilinear coverage also gives the log-window coverage target.  This
is useful as a sanity bridge, but it is the broad route already known to be too
large for the final finite-profile construction. -/
theorem routeBRicherSPDPStableCandidate_logWindowOrbitMlCovering_of_mlCovering
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcov :
      RouteBRicherSPDPStableCandidateMlCovering
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateLogWindowOrbitMlCovering
      M n hn2 htb hns tail := by
  intro spdpKappa ell S shift
    hSlen hshiftDegree _hSlog _hshiftLog _hshiftVars hadm
  exact
    routeBRicherSPDPStableCandidate_orbitMlCovering_of_mlCovering
      M n hn2 htb hns tail hcov S shift hadm

/-- Sharp admissible-orbit coverage discharges the explicit head/tail SPDP
row-closure package. -/
theorem routeBRicherSPDPStableCandidate_spdpRowClosurePackage_of_admissibleOrbitMlCovering
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcov :
      RouteBRicherSPDPStableCandidateAdmissibleOrbitMlCovering
        M n hn2 htb hns tail) :
    RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
      M n hn2 htb hns tail where
  concrete_row_closure := by
    intro spdpKappa ell S shift hSlen hshiftDegree hshiftVars hadm
    exact
      (hcov spdpKappa ell S shift
        hSlen hshiftDegree hshiftVars hadm).1
  tail_row_closure := by
    intro spdpKappa ell S shift hSlen hshiftDegree hshiftVars hadm i
    exact
      (hcov spdpKappa ell S shift
        hSlen hshiftDegree hshiftVars hadm).2 i

/-- `OrbitMlCovering` discharges the explicit head/tail SPDP row-closure
package.  This is the abstract analog of the broad multilinear-tail proof
in `routeBRicherConcreteNPPrependedMultilinearRows_spdpRowClosurePackage`. -/
theorem routeBRicherSPDPStableCandidate_spdpRowClosurePackage_of_orbitMlCovering
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcov :
      RouteBRicherSPDPStableCandidateOrbitMlCovering
        M n hn2 htb hns tail) :
    RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
      M n hn2 htb hns tail :=
  routeBRicherSPDPStableCandidate_spdpRowClosurePackage_of_admissibleOrbitMlCovering
    M n hn2 htb hns tail
    (routeBRicherSPDPStableCandidate_admissibleOrbitMlCovering_of_orbitMlCovering
      M n hn2 htb hns tail hcov)

/-- Sharp admissible-orbit coverage discharges the smaller-candidate
`SelectedRowClosure` obligation directly. -/
theorem routeBRicherSPDPStableCandidate_selectedRowClosure_of_admissibleOrbitMlCovering
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcov :
      RouteBRicherSPDPStableCandidateAdmissibleOrbitMlCovering
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateSelectedRowClosure
      M n hn2 htb hns tail :=
  routeBRicherSPDPStableCandidate_spdpRowClosurePackage_of_admissibleOrbitMlCovering
    M n hn2 htb hns tail hcov

/-- `OrbitMlCovering` discharges the smaller-candidate `SelectedRowClosure`
obligation directly. -/
theorem routeBRicherSPDPStableCandidate_selectedRowClosure_of_orbitMlCovering
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcov :
      RouteBRicherSPDPStableCandidateOrbitMlCovering
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateSelectedRowClosure
      M n hn2 htb hns tail :=
  routeBRicherSPDPStableCandidate_spdpRowClosurePackage_of_orbitMlCovering
    M n hn2 htb hns tail hcov

/-- The two concrete proof obligations needed for the SPDP-stable candidate:
sharp admissible-orbit coverage for selected-row closure, plus residual
invisibility for the projection kernel. -/
theorem routeBRicherSPDPStableCandidate_obligations_of_admissibleOrbitMlCovering_residualInvisible
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcov :
      RouteBRicherSPDPStableCandidateAdmissibleOrbitMlCovering
        M n hn2 htb hns tail)
    (hinvisible :
      RouteBRicherSPDPStableCandidateResidualInvisible
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateObligations
      M n hn2 htb hns tail where
  selected_row_closure :=
    routeBRicherSPDPStableCandidate_selectedRowClosure_of_admissibleOrbitMlCovering
      M n hn2 htb hns tail hcov
  residual_invisible := hinvisible

/-- Kernel-generator invisibility is the sharper form of residual
invisibility, so admissible orbit coverage plus the kernel form gives the
full smaller-candidate obligation package. -/
theorem routeBRicherSPDPStableCandidate_obligations_of_admissibleOrbitMlCovering_kernelGeneratorInvisible
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcov :
      RouteBRicherSPDPStableCandidateAdmissibleOrbitMlCovering
        M n hn2 htb hns tail)
    (hkernel :
      RouteBRicherSPDPStableCandidateKernelGeneratorInvisible
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateObligations
      M n hn2 htb hns tail :=
  routeBRicherSPDPStableCandidate_obligations_of_admissibleOrbitMlCovering_residualInvisible
    M n hn2 htb hns tail hcov
    ((routeBRicherSPDPStableCandidate_residualInvisible_iff_kernelGeneratorInvisible
      M n hn2 htb hns tail).mpr hkernel)

/-- A zero-before-projection kernel proof is stronger than needed, but it also
packages with admissible orbit coverage into the full smaller-candidate
obligations. -/
theorem routeBRicherSPDPStableCandidate_obligations_of_admissibleOrbitMlCovering_kernelGeneratorZero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcov :
      RouteBRicherSPDPStableCandidateAdmissibleOrbitMlCovering
        M n hn2 htb hns tail)
    (hzero :
      RouteBRicherSPDPStableCandidateKernelGeneratorZero
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateObligations
      M n hn2 htb hns tail :=
  routeBRicherSPDPStableCandidate_obligations_of_admissibleOrbitMlCovering_residualInvisible
    M n hn2 htb hns tail hcov
    (routeBRicherSPDPStableCandidate_residualInvisible_of_kernelGeneratorZero
      M n hn2 htb hns tail hzero)

/-- The practical target for the current finite-row projection: sharp
admissible-orbit coverage plus invariance of the projection's chosen
complement under admissible generator maps. -/
theorem routeBRicherSPDPStableCandidate_obligations_of_admissibleOrbitMlCovering_chosenComplementInvariant
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcov :
      RouteBRicherSPDPStableCandidateAdmissibleOrbitMlCovering
        M n hn2 htb hns tail)
    (hinvariant :
      RouteBRicherSPDPStableCandidateChosenComplementInvariant
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateObligations
      M n hn2 htb hns tail :=
  routeBRicherSPDPStableCandidate_obligations_of_admissibleOrbitMlCovering_residualInvisible
    M n hn2 htb hns tail hcov
    (routeBRicherSPDPStableCandidate_residualInvisible_of_chosenComplementInvariant
      M n hn2 htb hns tail hinvariant)

/-- Fully packaged log-window route.  It exposes the exact additional global
side condition needed to promote genuinely windowed profile proofs to the
current unbounded SPDP-stable candidate API. -/
theorem routeBRicherSPDPStableCandidate_obligations_of_logWindowOrbitMlCovering_logWindowChosenComplementInvariant
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcov :
      RouteBRicherSPDPStableCandidateLogWindowOrbitMlCovering
        M n hn2 htb hns tail)
    (hwindow :
      RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed
        M n hn2 htb hns)
    (hinvariant :
      RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateObligations
      M n hn2 htb hns tail :=
  routeBRicherSPDPStableCandidate_obligations_of_admissibleOrbitMlCovering_chosenComplementInvariant
    M n hn2 htb hns tail
    (routeBRicherSPDPStableCandidate_admissibleOrbitMlCovering_of_logWindowOrbitMlCovering
      M n hn2 htb hns tail hcov hwindow)
    (routeBRicherSPDPStableCandidate_chosenComplementInvariant_of_logWindowChosenComplementInvariant
      M n hn2 htb hns tail hinvariant hwindow)

/-- The holographic-invariance interface exposes the complement half as the
same `KernelGeneratorInvisible` obstruction used by the stable-candidate core,
provided the current unbounded SPDP API is restricted to log-window queries. -/
theorem routeBRicherSPDPStableCandidate_kernelGeneratorInvisible_of_holographicInvariance
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (holo :
      RouteBRicherSPDPStableCandidateHolographicInvariance
        M n hn2 htb hns tail)
    (hwindow :
      RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateKernelGeneratorInvisible
      M n hn2 htb hns tail :=
  (routeBRicherSPDPStableCandidate_kernelGeneratorInvisible_iff_chosenComplementInvariant
    M n hn2 htb hns tail).mpr
    (routeBRicherSPDPStableCandidate_chosenComplementInvariant_of_logWindowChosenComplementInvariant
      M n hn2 htb hns tail holo.log_window_complement_invariant hwindow)

/-- Thin Section 39-facing wrapper: once the missing log-window consumer bridge
is supplied, holographic invariance discharges the stable-tail/complement
obligations. -/
theorem routeBRicherSPDPStableCandidate_obligations_of_holographicInvariance
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (holo :
      RouteBRicherSPDPStableCandidateHolographicInvariance
        M n hn2 htb hns tail)
    (hwindow :
      RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateObligations
      M n hn2 htb hns tail :=
  routeBRicherSPDPStableCandidate_obligations_of_logWindowOrbitMlCovering_logWindowChosenComplementInvariant
    M n hn2 htb hns tail
    holo.log_window_orbit_coverage hwindow
    holo.log_window_complement_invariant

/-- `MlCovering` discharges `SelectedRowClosure` via `OrbitMlCovering`. -/
theorem routeBRicherSPDPStableCandidate_selectedRowClosure_of_mlCovering
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcov :
      RouteBRicherSPDPStableCandidateMlCovering
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateSelectedRowClosure
      M n hn2 htb hns tail :=
  routeBRicherSPDPStableCandidate_selectedRowClosure_of_orbitMlCovering
    M n hn2 htb hns tail
    (routeBRicherSPDPStableCandidate_orbitMlCovering_of_mlCovering
      M n hn2 htb hns tail hcov)

/-- The broad multilinear tail satisfies `MlCovering` — the canonical
witness.  This makes the abstraction unconditional: any narrower
`OrbitMlCovering` tail recovers the same row-closure path the broad tail
already exhibits. -/
theorem routeBRicherSPDPStableCandidate_mlCovering_for_multilinearTail
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateMlCovering
      M n hn2 htb hns
      (routeBRicherMultilinearTailRows M n hn2 htb hns) := by
  intro q
  exact
    routeBRicherConcreteNPPrependedMultilinearRows_mlProj_mem
      M n hn2 htb hns q

/-- The broad multilinear tail also satisfies the log-window orbit target,
again through the over-large `MlCovering` route. -/
theorem routeBRicherSPDPStableCandidate_logWindowOrbitMlCovering_for_multilinearTail
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowOrbitMlCovering
      M n hn2 htb hns
      (routeBRicherMultilinearTailRows M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_logWindowOrbitMlCovering_of_mlCovering
    M n hn2 htb hns
    (routeBRicherMultilinearTailRows M n hn2 htb hns)
    (routeBRicherSPDPStableCandidate_mlCovering_for_multilinearTail
      M n hn2 htb hns)

/-- Strict-form residual condition for the smaller candidate: every Route B
SPDP generator row of the projection residual vanishes (not merely its
projection).  This is the analog of the broad-case
`RouteBRicherConcreteNPPrependedMultilinearResidualGeneratorZero`. -/
def RouteBRicherSPDPStableCandidateResidualGeneratorZero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) : Prop :=
  forall (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    routeBSPDPGeneratorRow M n hn2 htb hns
      (p -
        routeBRicherSPDPStableCandidateProjection
          M n hn2 htb hns tail p)
      S shift = 0

/-- Under `MlCovering`, the smaller-candidate residual-invisibility
condition is *equivalent* to the strict residual-generator-zero condition.
This is the broad-multilinear-tail no-go propagation: any tail that already
covers every `mlProj` inherits the strict obstruction.

Proof: the residual generator is itself a `mlProj` output, hence it lies
in the prepended row span, hence it is fixed by the projection.  Therefore
"projection of the residual generator vanishes" coincides with "the residual
generator vanishes". -/
theorem routeBRicherSPDPStableCandidate_residualInvisible_iff_residualGeneratorZero_of_mlCovering
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcov :
      RouteBRicherSPDPStableCandidateMlCovering
        M n hn2 htb hns tail) :
    RouteBRicherSPDPStableCandidateResidualInvisible
        M n hn2 htb hns tail ↔
      RouteBRicherSPDPStableCandidateResidualGeneratorZero
        M n hn2 htb hns tail := by
  let Pi := routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail
  let rows := routeBRicherSPDPStableCandidateRows M n hn2 htb hns tail
  constructor
  · intro hinv spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm
    let residualRow :=
      routeBSPDPGeneratorRow M n hn2 htb hns (p - Pi p) S shift
    have hmem : residualRow ∈ finiteRowsSubmodule rows := by
      dsimp [residualRow, routeBSPDPGeneratorRow, rows]
      exact hcov _
    have hfixed : Pi residualRow = residualRow := by
      simpa [Pi, rows,
        routeBRicherSPDPStableCandidateProjection,
        routeBRicherSPDPStableCandidateGauge] using
        routeBRicherFiniteRowsCandidateGauge_fixed_of_mem
          M n hn2 htb hns rows hmem
    have hzero : Pi residualRow = 0 :=
      hinv spdpKappa ell p S shift
        hSlen hshiftDegree hshiftVars hadm
    rwa [hfixed] at hzero
  · intro hzero spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm
    have h :=
      hzero spdpKappa ell p S shift
        hSlen hshiftDegree hshiftVars hadm
    show Pi
      (routeBSPDPGeneratorRow M n hn2 htb hns (p - Pi p) S shift) = 0
    rw [h]
    simp

/-- Specialised no-go for `MlCovering` tails: refutability of the strict
residual condition transports to refutability of `ResidualInvisible`.
A direct combination with the broad-case no-go criteria from
`RouteBRicherGaugeConcreteMultilinearResidual`. -/
theorem routeBRicherSPDPStableCandidate_residualInvisible_noGo_of_mlCovering_residualGenerator_ne_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcov :
      RouteBRicherSPDPStableCandidateMlCovering
        M n hn2 htb hns tail)
    (hbad :
      ¬ RouteBRicherSPDPStableCandidateResidualGeneratorZero
          M n hn2 htb hns tail) :
    ¬ RouteBRicherSPDPStableCandidateResidualInvisible
        M n hn2 htb hns tail := by
  intro hinv
  exact hbad
    ((routeBRicherSPDPStableCandidate_residualInvisible_iff_residualGeneratorZero_of_mlCovering
      M n hn2 htb hns tail hcov).mp hinv)

/-! ## Live design space

The above propagation theorem says: **for any tail satisfying `MlCovering`,
the residual-invisibility obligation is no easier than the strict
residual-generator-zero obligation that the broad multilinear tail provably
cannot meet.**  Combined with the no-go criteria in
`RouteBRicherGaugeSPDPStableCandidateNoGo`, this means:

* If a candidate tail satisfies `MlCovering`, it inherits the broad-case
  refutation criteria — any `p` with `Π p = 0 ∧ Π(mlProj p) ≠ 0` rules it
  out.
* The live search is for tails satisfying the sharp
  `AdmissibleOrbitMlCovering` target but **not** `MlCovering`.  These close
  `SelectedRowClosure` by construction (via
  `routeBRicherSPDPStableCandidate_selectedRowClosure_of_admissibleOrbitMlCovering`)
  while leaving `ResidualInvisible` non-trivially satisfiable.

A natural source of `AdmissibleOrbitMlCovering ∧ ¬MlCovering` candidates is
the canonical-window profile alphabet at `R = Θ(log n)`: `nO(1)` distinct
profiles suffice to cover generator rows from the head/tail orbit but do
not span every multilinear monomial in the ambient Cook-Levin variable
set.
-/

/-! ## Axiom audit anchors -/

#print axioms RouteBRicherSPDPStableCandidateMlCovering
#print axioms RouteBRicherSPDPStableCandidateOrbitMlCovering
#print axioms RouteBRicherSPDPStableCandidateAdmissibleOrbitMlCovering
#print axioms RouteBRicherSPDPStableCandidateLogWindowOrbitMlCovering
#print axioms RouteBRicherSPDPStableCandidateLogWindowHeadMlCovering
#print axioms RouteBRicherSPDPStableCandidateLogWindowHeadSPDPSubspaceCovered
#print axioms RouteBRicherSPDPStableCandidateLogWindowTailRowStable
#print axioms RouteBRicherSPDPStableCandidateAdmissibleQueriesLogWindowed
#print axioms RouteBRicherSPDPStableCandidateLogWindowChosenComplementInvariant
#print axioms RouteBRicherSPDPStableCandidateHolographicInvariance
#print axioms RouteBRicherSPDPStableCandidateResidualGeneratorZero
#print axioms routeBRicherSPDPStableCandidate_not_holographicInvariance_of_logWindowHeadOrbit_escape
#print axioms routeBRicherSPDPStableCandidate_not_holographicInvariance_of_logWindowTailOrbit_escape
#print axioms routeBRicherSPDPStableCandidate_not_holographicInvariance_of_logWindowComplement_escape
#print axioms routeBRicherSPDPStableCandidate_logWindowOrbitMlCovering_of_head_tailStable
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadMlCovering_of_logWindowOrbitMlCovering
#print axioms routeBRicherSPDPStableCandidate_logWindowTailRowStable_of_logWindowOrbitMlCovering
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadMlCovering_of_headSPDPSubspaceCovered
#print axioms routeBRicherSPDPStableCandidate_spdpLogWindowRowClosurePackage_of_head_tailStable
#print axioms routeBRicherSPDPStableCandidate_spdpLogWindowRowClosurePackage_of_logWindowOrbitMlCovering
#print axioms routeBRicherSPDPStableCandidate_logWindowOrbitMlCovering_of_spdpLogWindowRowClosurePackage
#print axioms routeBRicherSPDPStableCandidate_not_admissibleQueriesLogWindowed_of_long_admissible
#print axioms routeBRicherSPDPStableCandidate_not_admissibleQueriesLogWindowed_of_highDegree_admissible
#print axioms routeBRicherSPDPStableCandidate_admissibleOrbitMlCovering_of_orbitMlCovering
#print axioms routeBRicherSPDPStableCandidate_admissibleOrbitMlCovering_of_logWindowOrbitMlCovering
#print axioms routeBRicherSPDPStableCandidate_chosenComplementInvariant_of_logWindowChosenComplementInvariant
#print axioms routeBRicherSPDPStableCandidate_orbitMlCovering_of_mlCovering
#print axioms routeBRicherSPDPStableCandidate_admissibleOrbitMlCovering_of_mlCovering
#print axioms routeBRicherSPDPStableCandidate_logWindowOrbitMlCovering_of_mlCovering
#print axioms routeBRicherSPDPStableCandidate_spdpRowClosurePackage_of_admissibleOrbitMlCovering
#print axioms routeBRicherSPDPStableCandidate_spdpRowClosurePackage_of_orbitMlCovering
#print axioms routeBRicherSPDPStableCandidate_selectedRowClosure_of_admissibleOrbitMlCovering
#print axioms routeBRicherSPDPStableCandidate_selectedRowClosure_of_orbitMlCovering
#print axioms routeBRicherSPDPStableCandidate_selectedRowClosure_of_mlCovering
#print axioms routeBRicherSPDPStableCandidate_obligations_of_admissibleOrbitMlCovering_residualInvisible
#print axioms routeBRicherSPDPStableCandidate_obligations_of_admissibleOrbitMlCovering_kernelGeneratorInvisible
#print axioms routeBRicherSPDPStableCandidate_obligations_of_admissibleOrbitMlCovering_kernelGeneratorZero
#print axioms routeBRicherSPDPStableCandidate_obligations_of_admissibleOrbitMlCovering_chosenComplementInvariant
#print axioms routeBRicherSPDPStableCandidate_obligations_of_logWindowOrbitMlCovering_logWindowChosenComplementInvariant
#print axioms routeBRicherSPDPStableCandidate_kernelGeneratorInvisible_of_holographicInvariance
#print axioms routeBRicherSPDPStableCandidate_obligations_of_holographicInvariance
#print axioms routeBRicherSPDPStableCandidate_mlCovering_for_multilinearTail
#print axioms routeBRicherSPDPStableCandidate_logWindowOrbitMlCovering_for_multilinearTail
#print axioms routeBRicherSPDPStableCandidate_residualInvisible_iff_residualGeneratorZero_of_mlCovering
#print axioms routeBRicherSPDPStableCandidate_residualInvisible_noGo_of_mlCovering_residualGenerator_ne_zero

end PallLean.Paper93.Paper283
