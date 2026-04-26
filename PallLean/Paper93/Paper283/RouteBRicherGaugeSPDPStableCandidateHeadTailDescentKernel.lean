import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailComplementProof

/-!
# Kernel criterion for head-tail chosen-projection descent

This file isolates the projection-kernel content behind the Route B
head-span-tail descent obligation.  The chosen complement remains arbitrary;
the exact checkable condition is that each log-window generator sends the
chosen projection kernel into the chosen projection kernel, equivalently that
applying the generator and then projecting gives zero on every kernel vector.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-! ## General projection-kernel descent lemmas -/

/-- For an idempotent projection `Pi`, a linear map `L` descends through `Pi`
exactly when `Pi ∘ L` kills the kernel of `Pi`. -/
theorem linearMap_projection_descent_iff_kernel_invisible
    {E : Type*} [AddCommGroup E] [Module Rat E]
    (Pi L : E →ₗ[Rat] E)
    (hPi : Pi.comp Pi = Pi) :
    Pi.comp L = (Pi.comp L).comp Pi ↔
      ∀ p : E, Pi p = 0 → Pi (L p) = 0 := by
  constructor
  · intro hdesc p hp
    have happ := congrArg (fun F : E →ₗ[Rat] E => F p) hdesc
    simpa [LinearMap.comp_apply, hp] using happ
  · intro hkernel
    apply LinearMap.ext
    intro p
    have hPiPi : Pi (Pi p) = Pi p := by
      have happ := congrArg (fun F : E →ₗ[Rat] E => F p) hPi
      simpa [LinearMap.comp_apply] using happ
    have hresZero : Pi (p - Pi p) = 0 := by
      simp [map_sub, hPiPi]
    have hrowZero : Pi (L (p - Pi p)) = 0 :=
      hkernel (p - Pi p) hresZero
    have hsubZero : Pi (L p) - Pi (L (Pi p)) = 0 := by
      simpa [map_sub] using hrowZero
    have hpoint : Pi (L p) = Pi (L (Pi p)) := sub_eq_zero.mp hsubZero
    simpa [LinearMap.comp_apply] using hpoint

/-- Equivalent obstruction-free form of projection descent. -/
theorem linearMap_projection_descent_iff_no_kernel_obstruction
    {E : Type*} [AddCommGroup E] [Module Rat E]
    (Pi L : E →ₗ[Rat] E)
    (hPi : Pi.comp Pi = Pi) :
    Pi.comp L = (Pi.comp L).comp Pi ↔
      ¬ ∃ p : E, Pi p = 0 ∧ Pi (L p) ≠ 0 := by
  rw [linearMap_projection_descent_iff_kernel_invisible Pi L hPi]
  constructor
  · intro hkernel hbad
    rcases hbad with ⟨p, hp, hvisible⟩
    exact hvisible (hkernel p hp)
  · intro hno p hp
    by_contra hvisible
    exact hno ⟨p, hp, hvisible⟩

/-- Failure of projection descent is exactly a visible kernel vector. -/
theorem linearMap_not_projection_descent_iff_kernel_obstruction
    {E : Type*} [AddCommGroup E] [Module Rat E]
    (Pi L : E →ₗ[Rat] E)
    (hPi : Pi.comp Pi = Pi) :
    Pi.comp L ≠ (Pi.comp L).comp Pi ↔
      ∃ p : E, Pi p = 0 ∧ Pi (L p) ≠ 0 := by
  constructor
  · intro hnot
    by_contra hno
    exact hnot
      ((linearMap_projection_descent_iff_no_kernel_obstruction Pi L hPi).mpr hno)
  · intro hbad hdesc
    exact
      ((linearMap_projection_descent_iff_no_kernel_obstruction Pi L hPi).mp hdesc)
        hbad

/-- Finite-submodule specialization: descent through the noncomputably chosen
finite-submodule projection is exactly the pointwise kernel-zero condition. -/
theorem finiteSubmoduleProjection_descent_iff_kernel_zero
    {N : Nat}
    (S : Submodule Rat (MvPolynomial (Fin N) Rat))
    (L : MvPolynomial (Fin N) Rat →ₗ[Rat] MvPolynomial (Fin N) Rat) :
    (finiteSubmoduleProjection S).comp L =
        ((finiteSubmoduleProjection S).comp L).comp
          (finiteSubmoduleProjection S) ↔
      ∀ p, finiteSubmoduleProjection S p = 0 →
        finiteSubmoduleProjection S (L p) = 0 :=
  linearMap_projection_descent_iff_kernel_invisible
    (finiteSubmoduleProjection S) L
    (finiteSubmoduleProjection_idempotent S)

/-- The same finite-submodule criterion, rewritten through the exposed chosen
complement.  This is the exact place where the arbitrary complement enters. -/
theorem finiteSubmoduleProjection_descent_iff_complement_invariant
    {N : Nat}
    (S : Submodule Rat (MvPolynomial (Fin N) Rat))
    (L : MvPolynomial (Fin N) Rat →ₗ[Rat] MvPolynomial (Fin N) Rat) :
    (finiteSubmoduleProjection S).comp L =
        ((finiteSubmoduleProjection S).comp L).comp
          (finiteSubmoduleProjection S) ↔
      Submodule.map L (finiteSubmoduleProjectionComplement S) ≤
        finiteSubmoduleProjectionComplement S := by
  rw [finiteSubmoduleProjection_descent_iff_kernel_zero S L]
  constructor
  · intro hkernel q hq
    rcases hq with ⟨p, hp, rfl⟩
    exact
      (finiteSubmoduleProjection_apply_eq_zero_iff S (L p)).mp
        (hkernel p
          ((finiteSubmoduleProjection_apply_eq_zero_iff S p).mpr hp))
  · intro hstable p hp
    have hpComplement :
        p ∈ finiteSubmoduleProjectionComplement S :=
      (finiteSubmoduleProjection_apply_eq_zero_iff S p).mp hp
    have hmap :
        L p ∈ Submodule.map L (finiteSubmoduleProjectionComplement S) :=
      ⟨p, hpComplement, rfl⟩
    exact
      (finiteSubmoduleProjection_apply_eq_zero_iff S (L p)).mpr
        (hstable hmap)

/-- Failure of finite-submodule projection descent is exactly a chosen-kernel
vector whose generator image remains visible after projection. -/
theorem finiteSubmoduleProjection_not_descent_iff_kernel_obstruction
    {N : Nat}
    (S : Submodule Rat (MvPolynomial (Fin N) Rat))
    (L : MvPolynomial (Fin N) Rat →ₗ[Rat] MvPolynomial (Fin N) Rat) :
    (finiteSubmoduleProjection S).comp L ≠
        ((finiteSubmoduleProjection S).comp L).comp
          (finiteSubmoduleProjection S) ↔
      ∃ p, finiteSubmoduleProjection S p = 0 ∧
        finiteSubmoduleProjection S (L p) ≠ 0 :=
  linearMap_not_projection_descent_iff_kernel_obstruction
    (finiteSubmoduleProjection S) L
    (finiteSubmoduleProjection_idempotent S)

/-! ## Head-span-tail specialization -/

/-- Checkable kernel criterion for the head-span tail: every log-window
generator is invisible after projecting whenever its input is in the chosen
projection kernel. -/
def RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelCriterion
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
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
    routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
        p = 0 ->
    routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) = 0

/-- A concrete obstruction to head-span-tail chosen-projection descent. -/
def RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelObstruction
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
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
    routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
        p = 0 ∧
    routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
        (routeBSPDPGeneratorRow M n hn2 htb hns p S shift) ≠ 0

/-- Head-span-tail descent is equivalent to the pointwise chosen-kernel
criterion. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_iff_kernelCriterion
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
        M n hn2 htb hns ↔
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelCriterion
        M n hn2 htb hns := by
  constructor
  · intro hdescent spdpKappa ell p S shift hSlen hshiftDegree hSlog
      hshiftLog hshiftVars hadm hp
    let tail :=
      routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns
    let Pi := routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail
    let L := routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift
    have hPi : Pi.comp Pi = Pi := by
      apply LinearMap.ext
      intro q
      simpa [Pi, tail, LinearMap.comp_apply] using
        routeBRicherSPDPStableCandidate_projection_idempotent
          M n hn2 htb hns tail q
    have hdesc : Pi.comp L = (Pi.comp L).comp Pi := by
      simpa [RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent,
        tail, Pi, L] using
        hdescent spdpKappa ell S shift hSlen hshiftDegree hSlog
          hshiftLog hshiftVars hadm
    exact
      (linearMap_projection_descent_iff_kernel_invisible Pi L hPi).mp
        hdesc p hp
  · intro hkernel spdpKappa ell S shift hSlen hshiftDegree hSlog
      hshiftLog hshiftVars hadm
    let tail :=
      routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns
    let Pi := routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail
    let L := routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift
    have hPi : Pi.comp Pi = Pi := by
      apply LinearMap.ext
      intro q
      simpa [Pi, tail, LinearMap.comp_apply] using
        routeBRicherSPDPStableCandidate_projection_idempotent
          M n hn2 htb hns tail q
    exact
      (linearMap_projection_descent_iff_kernel_invisible Pi L hPi).mpr
        (fun p hp => by
          simpa [Pi, L, tail, routeBSPDPGeneratorRowLinearMap_apply] using
            hkernel spdpKappa ell p S shift hSlen hshiftDegree hSlog
              hshiftLog hshiftVars hadm hp)

/-- The kernel criterion proves the chosen-projection descent target. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_of_kernelCriterion
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hkernel :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelCriterion
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
      M n hn2 htb hns :=
  (routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_iff_kernelCriterion
    M n hn2 htb hns).mpr hkernel

/-- The same kernel criterion proves the existing projection-intertwining
surface. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionIntertwines_of_kernelCriterion
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hkernel :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelCriterion
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionIntertwines
      M n hn2 htb hns :=
  (routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionIntertwines_iff_descent
    M n hn2 htb hns).mpr
    (routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_of_kernelCriterion
      M n hn2 htb hns hkernel)

/-- Projection intertwining is equivalent to the pointwise chosen-kernel
criterion. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionIntertwines_iff_kernelCriterion
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionIntertwines
        M n hn2 htb hns ↔
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelCriterion
        M n hn2 htb hns := by
  rw [routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionIntertwines_iff_descent]
  exact
    routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_iff_kernelCriterion
      M n hn2 htb hns

/-- Exact obstruction theorem: descent holds precisely when there is no
log-window generator with a visible chosen-kernel vector. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_iff_no_kernelObstruction
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
        M n hn2 htb hns ↔
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelObstruction
        M n hn2 htb hns := by
  rw [routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_iff_kernelCriterion]
  constructor
  · intro hkernel hbad
    rcases hbad with ⟨spdpKappa, ell, p, S, shift,
      hSlen, hshiftDegree, hSlog, hshiftLog, hshiftVars, hadm,
      hp, hvisible⟩
    exact hvisible
      (hkernel spdpKappa ell p S shift hSlen hshiftDegree hSlog
        hshiftLog hshiftVars hadm hp)
  · intro hno spdpKappa ell p S shift hSlen hshiftDegree hSlog
      hshiftLog hshiftVars hadm hp
    by_contra hvisible
    exact hno ⟨spdpKappa, ell, p, S, shift, hSlen, hshiftDegree,
      hSlog, hshiftLog, hshiftVars, hadm, hp, hvisible⟩

/-- Failure of head-span-tail descent is exactly the displayed kernel
obstruction. -/
theorem routeBRicherSPDPStableCandidate_not_logWindowHeadTailChosenProjectionDescent_iff_kernelObstruction
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    ¬ RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionDescent
        M n hn2 htb hns ↔
      RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelObstruction
        M n hn2 htb hns := by
  constructor
  · intro hnot
    by_contra hno
    exact hnot
      ((routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_iff_no_kernelObstruction
        M n hn2 htb hns).mpr hno)
  · intro hbad hdescent
    exact
      ((routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_iff_no_kernelObstruction
        M n hn2 htb hns).mp hdescent) hbad

/-! ## Axiom audit anchors -/

#print axioms linearMap_projection_descent_iff_kernel_invisible
#print axioms finiteSubmoduleProjection_descent_iff_complement_invariant
#print axioms RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelCriterion
#print axioms RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelObstruction
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_iff_kernelCriterion
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionIntertwines_of_kernelCriterion
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_iff_no_kernelObstruction
#print axioms routeBRicherSPDPStableCandidate_not_logWindowHeadTailChosenProjectionDescent_iff_kernelObstruction

end PallLean.Paper93.Paper283
