import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCbudgetConeBound

/-!
# Collective replacement certificates

The lightweight semantic endpoint shared by the observer/thermodynamic route
and exact finite circuit arguments.  Keeping it below either DAG-surgery stack
avoids importing incompatible alternative implementations together.
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverCentricNFrameActionBridge

open PallLean.Paper93.DeepMath.PathB

/-- A semantic certificate that a circuit can be collectively recomputed with
strictly fewer gates. -/
structure CollectiveReplacementCertificate {n : ℕ}
    (c : List (NFrameBoundaryTransducer.CGate n)) where
  replacement : List (NFrameBoundaryTransducer.CGate n)
  sameOutput : ∀ x, NFrameBoundaryTransducer.output replacement x =
    NFrameBoundaryTransducer.output c x
  shorter : replacement.length < c.length

/-- A `cbudget`-minimal circuit admits no collective replacement certificate. -/
theorem no_collectiveReplacement_of_minimal {n : ℕ}
    (f : (Fin n → Bool) → Bool) (c : List (NFrameBoundaryTransducer.CGate n))
    (hcomp : NFrameBoundaryTransducer.computes c f)
    (hmin : c.length = NFrameBoundaryTransducer.cbudget f) :
    ¬ Nonempty (CollectiveReplacementCertificate c) := by
  rintro ⟨R⟩
  have hRcomp : NFrameBoundaryTransducer.computes R.replacement f := by
    intro x
    rw [R.sameOutput x]
    exact hcomp x
  have hbudget : NFrameBoundaryTransducer.cbudget f ≤ R.replacement.length :=
    Nat.sInf_le ⟨R.replacement, hRcomp, rfl⟩
  have hshort := R.shorter
  omega

end PallLean.Paper93.DeepMath.PathB.ObserverCentricNFrameActionBridge

#print axioms PallLean.Paper93.DeepMath.PathB.ObserverCentricNFrameActionBridge.no_collectiveReplacement_of_minimal
