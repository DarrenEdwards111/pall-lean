import Mathlib.Computability.Halting
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTowerIndependentDecoderAudit

/-!
# N-Frame tower: unbounded behavioral reflection no-go

The compact-quotation route still has one tempting semantic implementation:
decode a Kleene program name to a finite CNF whose satisfiability says that the
named program eventually halts.  A solver-negating fixed-point program could
then turn this reflection theorem into the desired SAT liar law.

This file closes that implementation route with mathlib's genuine halting
theorem.  The obstruction already appears in the two-formula fragment of SAT.
Map `true` to the empty satisfiable CNF and `false` to the concrete
unsatisfiable `noCNF`.  If a total computable bit selected between those two
formulas and their SAT truth reflected unbounded `Code.eval` termination, the
bit would decide the halting problem.

The result distinguishes two very different decoders:

* truth-coded finite CNFs are easy once the truth bit has already been
  computed;
* a total computable truth bit for unbounded Kleene behavior cannot exist.

Therefore compact quotation cannot evade the Cook--Levin self-size barrier by
silently replacing bounded tableaux with unbounded behavioral semantics.  The
former is finite but faces the proved clock/size obstruction; the latter would
decide halting before producing its tiny CNF.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameTowerHaltingReflectionNoGo

open SATDepthMachine
open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge

/-! ## The two-formula truth codec -/

/-- Encode one already-known truth bit as a finite CNF. -/
def truthCodedCNF : Bool → CNF
  | false => noCNF
  | true => yesCNF

/-- The two-formula codec reflects its input bit exactly. -/
theorem truthCodedCNF_satisfiable_iff (b : Bool) :
    Satisfiable (truthCodedCNF b) ↔ b = true := by
  cases b
  · simp [truthCodedCNF, noCNF_not_satisfiable]
  · simp [truthCodedCNF, yesCNF_satisfiable]

/-- Any total Boolean classifier can be packaged as tiny SAT instances.  This
is answer coding: all semantic work is performed in `bit` before the CNF is
chosen. -/
theorem truthCodedCNF_reflects_bit (bit : Code → Bool) (c : Code) :
    Satisfiable (truthCodedCNF (bit c)) ↔ bit c = true :=
  truthCodedCNF_satisfiable_iff (bit c)

/-! ## Unbounded behavioral reflection would decide halting -/

/-- The proposed compact semantic bridge.  `satBit` is the total effective SAT
classifier obtained by running finite brute-force SAT on the decoder's output.
Keeping it explicit avoids imposing a new global coding instance on the
repository's `CNF` structure. -/
structure ComputableHaltingSATReflection where
  decode : Code → CNF
  satBit : Code → Bool
  satBit_computable : Computable satBit
  satBit_correct : ∀ c : Code,
    satBit c = true ↔ Satisfiable (decode c)
  reflects_halting : ∀ c : Code,
    Satisfiable (decode c) ↔ (Code.eval c 0).Dom

/-- A reflection bridge makes the halting predicate computable. -/
theorem haltingPredicate_computable
    (R : ComputableHaltingSATReflection) :
    ComputablePred (fun c : Code => (Code.eval c 0).Dom) := by
  have hbit : ComputablePred (fun c : Code => R.satBit c = true) := by
    apply Computable.computablePred
    simpa using R.satBit_computable
  apply hbit.of_eq
  intro c
  exact (R.satBit_correct c).trans (R.reflects_halting c)

/-- **Unbounded-reflection no-go.**  No compact decoder with an effective SAT
classifier for its finite outputs can reflect arbitrary Kleene termination. -/
theorem no_computableHaltingSATReflection :
    ¬ Nonempty ComputableHaltingSATReflection := by
  rintro ⟨R⟩
  exact ComputablePred.halting_problem 0 (haltingPredicate_computable R)

/-! ## Exact diagnosis of answer coding -/

/-- If the truth-coded decoder reflects halting, its selected bit itself is
exactly a halting decider. -/
theorem reflects_halting_iff_bit_decides_halting
    (bit : Code → Bool) :
    (∀ c : Code,
      Satisfiable (truthCodedCNF (bit c)) ↔ (Code.eval c 0).Dom) ↔
    (∀ c : Code, bit c = true ↔ (Code.eval c 0).Dom) := by
  constructor <;> intro h c
  · exact (truthCodedCNF_satisfiable_iff (bit c)).symm.trans (h c)
  · exact (truthCodedCNF_satisfiable_iff (bit c)).trans (h c)

/-- Consequently even the direct bit-level specification is incompatible with
computability. -/
theorem no_computable_halting_truth_bit :
    ¬ ∃ bit : Code → Bool,
      Computable bit ∧ ∀ c : Code, bit c = true ↔ (Code.eval c 0).Dom := by
  rintro ⟨bit, hcomp, hcorrect⟩
  have hbit : ComputablePred (fun c : Code => bit c = true) := by
    apply Computable.computablePred
    simpa using hcomp
  exact ComputablePred.halting_problem 0 (hbit.of_eq hcorrect)

end PallLean.Paper93.DeepMath.PathB.NFrameTowerHaltingReflectionNoGo

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerHaltingReflectionNoGo.truthCodedCNF_satisfiable_iff
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerHaltingReflectionNoGo.haltingPredicate_computable
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerHaltingReflectionNoGo.no_computableHaltingSATReflection
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerHaltingReflectionNoGo.reflects_halting_iff_bit_decides_halting
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerHaltingReflectionNoGo.no_computable_halting_truth_bit
