import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeRoundTransition

/-!
# Machine-parametric fixed-round certificates

The original scheduled certificate is specialized to `runtimeFixedRoundBody`.
This module exposes the already-generic repetition theorem through a
machine-parametric certificate, allowing a universal translated round body
to replace the legacy continuation controller without rebuilding the
countdown/repetition proof.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeParametricRoundCertificate

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRepeatAdapter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr (unaryD)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice (cntT)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRep

/-- One exact, halting, left-safe transition for an arbitrary fixed body. -/
def RuntimeBodyCertificate (M : Machine) (T T' : List Bool) : Prop :=
  ∃ clock sf pf,
    run M clock (init M T) = ⟨sf, pf, T'⟩ ∧
      M.halt sf = true ∧
      LeftSafeRun M (init M T) clock

/-- Coherently choose clocks, states, and heads from per-index certificates. -/
theorem runtimeBody_family_of_certificates (M : Machine) (B : Nat)
    (tail : Nat → List Bool)
    (hcert : ∀ t, t < B → RuntimeBodyCertificate M (tail t) (tail (t + 1))) :
    ∃ bodyClock : Nat → Nat,
      ∃ sf : Nat → M.State,
      ∃ pf : Nat → Nat,
        (∀ t, t < B →
          run M (bodyClock t) (init M (tail t)) =
            ⟨sf t, pf t, tail (t + 1)⟩) ∧
        (∀ t, t < B → M.halt (sf t) = true) ∧
        (∀ t, t < B →
          LeftSafeRun M (init M (tail t)) (bodyClock t)) := by
  let bodyClock := fun t => if ht : t < B then (hcert t ht).choose else 0
  let sf := fun t => if ht : t < B then
    (hcert t ht).choose_spec.choose else M.start
  let pf := fun t => if ht : t < B then
    (hcert t ht).choose_spec.choose_spec.choose else 0
  refine ⟨bodyClock, sf, pf, ?_, ?_, ?_⟩
  · intro t ht
    simp only [bodyClock, sf, pf, dif_pos ht]
    exact (hcert t ht).choose_spec.choose_spec.choose_spec.1
  · intro t ht
    simp only [sf, dif_pos ht]
    exact (hcert t ht).choose_spec.choose_spec.choose_spec.2.1
  · intro t ht
    simp only [bodyClock, dif_pos ht]
    exact (hcert t ht).choose_spec.choose_spec.choose_spec.2.2

/-- Any single fixed machine with per-round certificates can be iterated by
the verified protected countdown controller. -/
theorem runtimeRep_run_of_body_certificates (M : Machine) (B : Nat)
    (tail : Nat → List Bool)
    (hcert : ∀ t, t < B → RuntimeBodyCertificate M (tail t) (tail (t + 1))) :
    ∃ totalClock,
      run (repMachine (runtimeCountdownBody B M)) totalClock
          (init (repMachine (runtimeCountdownBody B M))
            (cntT B 0 ++ tail 0)) =
        ⟨Sum.inl (4, false), 2 * B + 1, unaryD B ++ tail B⟩ := by
  obtain ⟨bodyClock, sf, pf, hrun, hhalt, hleft⟩ :=
    runtimeBody_family_of_certificates M B tail hcert
  let protectedClock := fun t =>
    runtimeCountdownBodyClock B M (tail t) (bodyClock t)
  refine ⟨repRounds protectedClock B + (4 * B + 4), ?_⟩
  simpa [protectedClock] using
    (runtimeRep_run M B tail bodyClock sf pf hrun hhalt hleft)

/-- The legacy certificate embeds definitionally into the parametric one. -/
theorem runtimeFixedRoundCertificate_to_body
    (T T' : List Bool)
    (h : PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.RuntimeFixedRoundCertificate T T') :
    RuntimeBodyCertificate
      PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundTransition.runtimeFixedRoundBody
      T T' := h

#print axioms runtimeBody_family_of_certificates
#print axioms runtimeRep_run_of_body_certificates

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeParametricRoundCertificate
