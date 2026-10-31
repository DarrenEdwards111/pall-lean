import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRegulatedBlackHoleAudit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPNFrameDynamicMERAHolonomy

/-!
# Black-hole MERA trace dynamics

This file builds the dynamical version of the regulated black-hole proposal.  The black hole is not a
static metadata field attached to a representation.  A computation is a deterministic finite-boundary
MERA trajectory, and a horizon forms at an intermediate time.  The horizon carries a finite regulator
precision and a finite reconstruction cost.

The model cleanly separates three logically different ingredients:

* **kinematics:** local deterministic boundary evolution and a horizon occurring on the trace;
* **regulated divergence:** `b` horizon bits require reconstruction charge at least `2^b`;
* **the two load-bearing dynamical laws:** the target semantics force `b ≥ n`, and no computation can
  finish before paying the reconstruction charge.

The central theorem is real but conditional: those two laws imply decision time at least `2^n`, hence
exclude every polynomial time bound.  This is the exact route by which black-hole dynamics *could*
supply a full lower bound.

The file also applies the necessary adversarial controls.

1. A constant-false function has a one-step, one-state MERA trace with a zero-precision horizon.
2. Therefore no target-independent law can force linear horizon precision for every computation.
3. A semantics-specific admissibility predicate must exclude cheap SAT traces while accepting cheap easy
   traces.  Merely declaring every horizon to be expensive inserts the desired conclusion by definition.

Accordingly, the remaining open construction is precisely named: a representation-invariant SAT
admissibility law deriving linear horizon precision and the no-shortcut inequality from actual MERA
dynamics.  It is not asserted here.  Nothing in this file proves `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BlackHoleMERATraceDynamics

open PallLean.Paper93.DeepMath.PathB.PvsNPNFrameRestrictedMERADecoder
open PallLean.Paper93.DeepMath.PathB.PvsNPNFrameRestrictedMERADecoder.BoundedBondLocalMERADecoderFamily
open PallLean.Paper93.DeepMath.PathB.PvsNPNFrameDynamicMERAHolonomy
open PallLean.Paper93.DeepMath.PathB.RegulatedBlackHoleAudit

abbrev MERAFamily := BoundedBondLocalMERADecoderFamily

/-! ## Deterministic MERA decision trajectories -/

/-- A finite-boundary deterministic MERA trajectory computing one Boolean target.

`boundary_card_le` retains the repository's genuine fixed-bond causal-cone restriction.  `decisionTime`
is the number of dynamical updates, rather than the static number of MERA renormalisation layers. -/
structure MERADecisionTrace (M : MERAFamily) (n : Nat)
    (Input : Type*) (target : Input → Bool) where
  BoundaryState : Type
  [stateFintype : Fintype BoundaryState]
  [stateDecidableEq : DecidableEq BoundaryState]
  encode : Input → BoundaryState
  step : Nat → BoundaryState → BoundaryState
  decode : BoundaryState → Bool
  decisionTime : Nat
  correct : ∀ input,
    decode (runFrom step 0 decisionTime (encode input)) = target input
  boundary_card_le : Fintype.card BoundaryState ≤ M.accessibleRank n

namespace MERADecisionTrace

variable {M : MERAFamily} {n : Nat} {Input : Type*} {target : Input → Bool}

/-- Boundary state reached at a given dynamical time. -/
def stateAt (T : MERADecisionTrace M n Input target)
    (time : Nat) (input : Input) : T.BoundaryState :=
  runFrom T.step 0 time (T.encode input)

@[simp] theorem decode_final (T : MERADecisionTrace M n Input target) (input : Input) :
    T.decode (T.stateAt T.decisionTime input) = target input :=
  T.correct input

end MERADecisionTrace

/-! ## A finite dynamical horizon -/

/-- A regulated black-hole horizon forming on a concrete MERA trajectory.

This structure contains only finite kinematic data and the regulated divergence law.  It deliberately
does not contain the no-shortcut or linear-precision claims; those are the substantive dynamical laws
tested below. -/
structure DynamicalHorizon {M : MERAFamily} {n : Nat}
    {Input : Type*} {target : Input → Bool}
    (T : MERADecisionTrace M n Input target) where
  formationTime : Nat
  formation_le_decision : formationTime ≤ T.decisionTime
  precisionBits : Nat
  reconstructionCost : Nat
  regulatedDivergence : 2 ^ precisionBits ≤ reconstructionCost

/-- The no-shortcut condition: the computation cannot finish before paying the horizon reconstruction
cost.  Naming it separately prevents the lower bound from being hidden inside the horizon definition. -/
def NoHorizonShortcut {M : MERAFamily} {n : Nat}
    {Input : Type*} {target : Input → Bool}
    {T : MERADecisionTrace M n Input target}
    (H : DynamicalHorizon T) : Prop :=
  H.reconstructionCost ≤ T.decisionTime

/-- The semantic forcing condition at size `n`: this horizon requires at least `n` finite resolution
bits. -/
def LinearHorizonPrecision {M : MERAFamily} {n : Nat}
    {Input : Type*} {target : Input → Bool}
    {T : MERADecisionTrace M n Input target}
    (H : DynamicalHorizon T) : Prop :=
  n ≤ H.precisionBits

/-- **Horizon-to-time theorem.**  Forced linear precision plus no-shortcut dynamics yields an actual
exponential decision-time lower bound. -/
theorem two_pow_le_decisionTime_of_horizon
    {M : MERAFamily} {n : Nat} {Input : Type*} {target : Input → Bool}
    {T : MERADecisionTrace M n Input target} (H : DynamicalHorizon T)
    (hprecision : LinearHorizonPrecision H)
    (hshortcut : NoHorizonShortcut H) :
    2 ^ n ≤ T.decisionTime := by
  exact le_trans (Nat.pow_le_pow_right (by omega) hprecision)
    (le_trans H.regulatedDivergence hshortcut)

/-! ## Target-specific admissibility and the complete conditional chain -/

/-- A target-specific predicate deciding which trace/horizon pairs are physically and semantically
admissible.  For a viable route this must be invariant under allowed MERA gauge/layout changes and must
not inspect an alleged solver's answer. -/
abbrev HorizonAdmissibility (M : MERAFamily) (n : Nat)
    (Input : Type*) (target : Input → Bool) :=
  (T : MERADecisionTrace M n Input target) → DynamicalHorizon T → Prop

/-- The two black-hole laws required of every admissible trace for the selected target family.

This package is named rather than constructed for SAT.  Its fields are exactly the new mathematical
content: semantic forcing of precision and the dynamical no-shortcut theorem. -/
structure BlackHoleDynamicsLaws
    (M : MERAFamily)
    (Input : Nat → Type*)
    (target : (n : Nat) → Input n → Bool)
    (Admissible : (n : Nat) → HorizonAdmissibility M n (Input n) (target n)) : Prop where
  forcesLinearPrecision : ∀ n T H, Admissible n T H → LinearHorizonPrecision H
  noShortcut : ∀ n T H, Admissible n T H → NoHorizonShortcut H

/-- A selected admissible black-hole MERA trace at every input size. -/
structure AdmissibleBlackHoleTraceFamily
    (M : MERAFamily)
    (Input : Nat → Type*)
    (target : (n : Nat) → Input n → Bool)
    (Admissible : (n : Nat) → HorizonAdmissibility M n (Input n) (target n)) where
  trace : (n : Nat) → MERADecisionTrace M n (Input n) (target n)
  horizon : (n : Nat) → DynamicalHorizon (trace n)
  admissible : ∀ n, Admissible n (trace n) (horizon n)

namespace AdmissibleBlackHoleTraceFamily

variable {M : MERAFamily}
  {Input : Nat → Type*}
  {target : (n : Nat) → Input n → Bool}
  {Admissible : (n : Nat) → HorizonAdmissibility M n (Input n) (target n)}

/-- Decision-time scale of a selected trace family. -/
def time (F : AdmissibleBlackHoleTraceFamily M Input target Admissible) (n : Nat) : Nat :=
  (F.trace n).decisionTime

/-- The black-hole laws force exponential time pointwise. -/
theorem two_pow_le_time
    (F : AdmissibleBlackHoleTraceFamily M Input target Admissible)
    (L : BlackHoleDynamicsLaws M Input target Admissible) (n : Nat) :
    2 ^ n ≤ F.time n := by
  exact two_pow_le_decisionTime_of_horizon (F.horizon n)
    (L.forcesLinearPrecision n (F.trace n) (F.horizon n) (F.admissible n))
    (L.noShortcut n (F.trace n) (F.horizon n) (F.admissible n))

end AdmissibleBlackHoleTraceFamily

/-- A standard polynomial upper bound, with explicit coefficient, degree, and additive constant. -/
def PolynomiallyBounded (time : Nat → Nat) : Prop :=
  ∃ A C B : Nat, ∀ n, time n ≤ A * n ^ C + B

/-- **Conditional separation engine.**  A target family satisfying the two black-hole dynamics laws has
no polynomially bounded decision-time trace family. -/
theorem not_polynomiallyBounded_of_blackHoleDynamics
    {M : MERAFamily}
    {Input : Nat → Type*}
    {target : (n : Nat) → Input n → Bool}
    {Admissible : (n : Nat) → HorizonAdmissibility M n (Input n) (target n)}
    (F : AdmissibleBlackHoleTraceFamily M Input target Admissible)
    (L : BlackHoleDynamicsLaws M Input target Admissible) :
    ¬ PolynomiallyBounded F.time := by
  rintro ⟨A, C, B, hpoly⟩
  obtain ⟨n, _, hgap⟩ := two_pow_is_superpolynomial A C B
  have hexp := F.two_pow_le_time L n
  exact (not_lt_of_ge (le_trans hexp (hpoly n))) hgap

/-! ## Adversarial easy-function and zero-horizon controls -/

/-- The one-state, zero-cone MERA family used to calibrate easy functions. -/
def trivialMERA : MERAFamily :=
  profileSaturatedFamily 1 0 (by omega)

/-- A one-step one-state MERA trajectory for the constant-false function. -/
def easyFalseTrace (n : Nat) :
    MERADecisionTrace trivialMERA n (Fin n → Bool) (fun _ => false) where
  BoundaryState := Unit
  encode := fun _ => ()
  step := fun _ state => state
  decode := fun _ => false
  decisionTime := 1
  correct := fun _ => rfl
  boundary_card_le := by
    simp [trivialMERA, profileSaturatedFamily]

/-- The easy trace admits a genuine finite zero-precision horizon. -/
def easyZeroHorizon (n : Nat) : DynamicalHorizon (easyFalseTrace n) where
  formationTime := 0
  formation_le_decision := by simp [easyFalseTrace]
  precisionBits := 0
  reconstructionCost := 1
  regulatedDivergence := by norm_num

@[simp] theorem easyFalseTrace_time (n : Nat) :
    (easyFalseTrace n).decisionTime = 1 := rfl

@[simp] theorem easyZeroHorizon_precision (n : Nat) :
    (easyZeroHorizon n).precisionBits = 0 := rfl

theorem easyZeroHorizon_noShortcut (n : Nat) :
    NoHorizonShortcut (easyZeroHorizon n) := by
  simp [NoHorizonShortcut, easyZeroHorizon, easyFalseTrace]

/-- **Easy-function control.**  At every positive size the correct constant-false trajectory refutes
linear horizon precision.  Hence the forcing law cannot be a target-independent consequence of merely
having deterministic MERA dynamics and a regulated horizon. -/
theorem easy_function_refutes_universal_linear_precision
    {n : Nat} (hn : 0 < n) :
    ¬ LinearHorizonPrecision (easyZeroHorizon n) := by
  simp [LinearHorizonPrecision, easyZeroHorizon]
  omega

/-- Any admissibility predicate that accepts the cheap easy-function horizon is incompatible with a
law forcing linear precision for that easy target at positive lengths.  A valid SAT law must therefore
be semantic and target-specific, not a universal black-hole postulate. -/
theorem accepting_easy_control_refutes_forcing_law
    (Admissible : (n : Nat) →
      HorizonAdmissibility trivialMERA n (Fin n → Bool) (fun _ => false))
    (haccept : ∀ n, Admissible n (easyFalseTrace n) (easyZeroHorizon n))
    {n : Nat} (hn : 0 < n) :
    ¬ (∀ T H, Admissible n T H → LinearHorizonPrecision H) := by
  intro hforce
  exact easy_function_refutes_universal_linear_precision hn
    (hforce (easyFalseTrace n) (easyZeroHorizon n) (haccept n))

/-!
## Honest endpoint

The dynamical chain itself is now exact and machine checked:

`forced horizon precision` + `regulated divergence` + `no shortcut`
`⇒ 2^n ≤ decisionTime`
`⇒ no polynomial time bound`.

The constant-false calibration proves that neither linear precision nor no-shortcut hardness follows
from generic MERA evolution alone.  The remaining full-separation target is therefore not another
arithmetic lemma.  It is a representation-invariant, target-specific theorem showing that every exact
SAT trace admissible under concrete local/isometric horizon dynamics satisfies both fields of
`BlackHoleDynamicsLaws`, while easy polynomial-time traces remain admissible with cheap horizons.
-/

end PallLean.Paper93.DeepMath.PathB.BlackHoleMERATraceDynamics

#print axioms PallLean.Paper93.DeepMath.PathB.BlackHoleMERATraceDynamics.two_pow_le_decisionTime_of_horizon
#print axioms PallLean.Paper93.DeepMath.PathB.BlackHoleMERATraceDynamics.AdmissibleBlackHoleTraceFamily.two_pow_le_time
#print axioms PallLean.Paper93.DeepMath.PathB.BlackHoleMERATraceDynamics.not_polynomiallyBounded_of_blackHoleDynamics
#print axioms PallLean.Paper93.DeepMath.PathB.BlackHoleMERATraceDynamics.easy_function_refutes_universal_linear_precision
#print axioms PallLean.Paper93.DeepMath.PathB.BlackHoleMERATraceDynamics.accepting_easy_control_refutes_forcing_law
