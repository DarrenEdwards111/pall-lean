import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGodelTowerSpring
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUCRDSATLoopEvaluatorFrontier

/-!
# N-Frame Gödel hierarchy tower / finite-SAT bridge audit

This file returns to the actual construction in N-Frame Book 1, §2.3: an
ascending hierarchy of sound observer theories, with a single uniform Rosser-
style sentence that escapes every level of a computably presented tower.

The loop/holonomy experiments were useful negative calibrations, but a loop is
not the Book 1 tower.  The tower's essential structure is vertical:

* lower-level provability embeds into the next level;
* soundness connects provability to truth;
* one fixed-point sentence is true exactly when it is absent from every level;
* adjoining the escape produces a strict extension, but no old level captures
  the uniform escape;
* consequently there is no final sound and truth-complete level.

We then audit the proposed P-versus-NP bridge.  To turn tower non-escape into a
SAT time lower bound one needs the extra claim that any polynomial SAT decider
forces the tower escape into some finite level.  We prove that this capture
claim is equivalent to `¬ SATDecisionInP`: tower non-escape discharges the
contradiction once capture is supplied, while in the absence of a polynomial
SAT decider capture holds vacuously.

Thus the tower is the correct N-Frame object and its non-escape theorem is
real.  The unresolved step is not another tower lemma; it is the finite-
complexity bridge from an arbitrary polynomial SAT machine to levelwise
provability of the uniform escape.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameGodelTowerSATBridgeAudit

open SATDepthMachine

/-! ## Book-faithful uniform escape tower -/

/-- An abstract uniform Rosser tower.  `fixedpoint` is the strengthened Book 1
non-escape sentence: it is true exactly when no level proves it. -/
structure UniformRosserTower where
  Sentence : Type
  Prov : Nat → Sentence → Prop
  True_ : Sentence → Prop
  /-- Every old proof remains available one level higher. -/
  monotone : ∀ n ψ, Prov n ψ → Prov (n + 1) ψ
  escape : Sentence
  /-- One sentence diagonalizes simultaneously against all finite levels. -/
  fixedpoint : True_ escape ↔ ∀ n, ¬ Prov n escape
  /-- Levelwise semantic soundness is the load-bearing Gödel condition. -/
  sound : ∀ n ψ, Prov n ψ → True_ ψ

/-- The uniform escape is absent from every level. -/
theorem UniformRosserTower.escape_unprovable
    (T : UniformRosserTower) (n : Nat) :
    ¬ T.Prov n T.escape := by
  intro hp
  have ht : T.True_ T.escape := T.sound n T.escape hp
  exact (T.fixedpoint.mp ht n) hp

/-- Nonetheless, the uniform escape is semantically true. -/
theorem UniformRosserTower.escape_true (T : UniformRosserTower) :
    T.True_ T.escape := by
  apply T.fixedpoint.mpr
  exact T.escape_unprovable

/-- Membership in some finite rung of the tower. -/
def UniformRosserTower.InUnion
    (T : UniformRosserTower) (ψ : T.Sentence) : Prop :=
  ∃ n, T.Prov n ψ

/-- The single Rosser sentence escapes the whole finite tower union. -/
theorem UniformRosserTower.escape_not_in_union
    (T : UniformRosserTower) :
    ¬ T.InUnion T.escape := by
  rintro ⟨n, hn⟩
  exact T.escape_unprovable n hn

/-- No finite level is complete for all truths of the tower semantics. -/
theorem UniformRosserTower.no_final_complete_level
    (T : UniformRosserTower) :
    ¬ ∃ n, ∀ ψ, T.True_ ψ → T.Prov n ψ := by
  rintro ⟨n, hcomplete⟩
  exact T.escape_unprovable n (hcomplete T.escape T.escape_true)

/-! ## Strict ascent by adjoining the escape -/

/-- Extend rung `n` by adjoining the uniform escape sentence. -/
def UniformRosserTower.extendedProv
    (T : UniformRosserTower) (n : Nat) (ψ : T.Sentence) : Prop :=
  T.Prov n ψ ∨ ψ = T.escape

theorem UniformRosserTower.old_proofs_embed
    (T : UniformRosserTower) (n : Nat) (ψ : T.Sentence)
    (hψ : T.Prov n ψ) :
    T.extendedProv n ψ :=
  Or.inl hψ

theorem UniformRosserTower.extension_proves_escape
    (T : UniformRosserTower) (n : Nat) :
    T.extendedProv n T.escape :=
  Or.inr rfl

/-- Every rung has a strict escape extension: the old rung omits the escape
while the extension contains it. -/
theorem UniformRosserTower.strict_extension_at_escape
    (T : UniformRosserTower) (n : Nat) :
    ¬ T.Prov n T.escape ∧ T.extendedProv n T.escape :=
  ⟨T.escape_unprovable n, T.extension_proves_escape n⟩

/-! ## Finite SAT interpretation is not yet a time lower bound -/

/-- A solver-independent interpretation of finite CNFs in tower sentences.
This supplies semantic meaning but makes no complexity-capture claim. -/
structure FiniteSATInterpretation (T : UniformRosserTower) where
  encode : CNF → T.Sentence
  escapeCNF : CNF
  escape_encoded : encode escapeCNF = T.escape
  truth_preserving : ∀ φ, T.True_ (encode φ) ↔ Satisfiable φ

/-- If the uniform escape has a finite CNF representative, that representative
is satisfiable.  This is semantic only; it does not place the sentence in any
polynomial observer level. -/
theorem FiniteSATInterpretation.escapeCNF_satisfiable
    {T : UniformRosserTower} (I : FiniteSATInterpretation T) :
    Satisfiable I.escapeCNF := by
  apply (I.truth_preserving I.escapeCNF).mp
  rw [I.escape_encoded]
  exact T.escape_true

/-! ## The exact missing P-versus-NP bridge -/

/-- The load-bearing capture claim: a polynomial SAT decider would force the
uniform tower escape into some finite observer level. -/
def SolverForcesTowerCapture
    (U : MachineModel) (T : UniformRosserTower) : Prop :=
  SATDecisionInP U → T.InUnion T.escape

/-- Tower non-escape converts the capture claim into a SAT lower bound. -/
theorem no_SATDecisionInP_of_solverForcesTowerCapture
    (U : MachineModel) (T : UniformRosserTower)
    (hcapture : SolverForcesTowerCapture U T) :
    ¬ SATDecisionInP U := by
  intro hP
  exact T.escape_not_in_union (hcapture hP)

/-- **Exact bridge audit.**  For a genuine uniform-escape tower, the assertion
that every polynomial SAT solver is captured by a finite rung is equivalent to
the desired SAT lower bound itself. -/
theorem solverForcesTowerCapture_iff_no_SATDecisionInP
    (U : MachineModel) (T : UniformRosserTower) :
    SolverForcesTowerCapture U T ↔ ¬ SATDecisionInP U := by
  constructor
  · exact no_SATDecisionInP_of_solverForcesTowerCapture U T
  · intro hno hP
    exact (hno hP).elim

/-- Consequently, tower capture is also exactly the absence of a polynomial
uniform evaluator for the genuine CNF loops from the preceding calibration. -/
theorem solverForcesTowerCapture_iff_no_uniformSATLoopEvaluator
    (U : MachineModel) (T : UniformRosserTower) :
    SolverForcesTowerCapture U T ↔
      ¬ Nonempty
        (PallLean.Paper93.DeepMath.PathB.UCRDSATLoopEvaluatorFrontier.UniformSATLoopEvaluator U) := by
  rw [solverForcesTowerCapture_iff_no_SATDecisionInP]
  exact
    (PallLean.Paper93.DeepMath.PathB.UCRDSATLoopEvaluatorFrontier.no_uniformSATLoopEvaluator_iff_no_SATDecisionInP U).symm

end PallLean.Paper93.DeepMath.PathB.NFrameGodelTowerSATBridgeAudit

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameGodelTowerSATBridgeAudit.UniformRosserTower.escape_unprovable
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameGodelTowerSATBridgeAudit.UniformRosserTower.escape_true
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameGodelTowerSATBridgeAudit.UniformRosserTower.escape_not_in_union
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameGodelTowerSATBridgeAudit.UniformRosserTower.no_final_complete_level
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameGodelTowerSATBridgeAudit.UniformRosserTower.strict_extension_at_escape
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameGodelTowerSATBridgeAudit.FiniteSATInterpretation.escapeCNF_satisfiable
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameGodelTowerSATBridgeAudit.solverForcesTowerCapture_iff_no_SATDecisionInP
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameGodelTowerSATBridgeAudit.solverForcesTowerCapture_iff_no_uniformSATLoopEvaluator
