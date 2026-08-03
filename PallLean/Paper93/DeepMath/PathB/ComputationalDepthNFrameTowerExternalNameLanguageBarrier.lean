import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTowerHaltingReflectionNoGo

/-!
# N-Frame tower: external-name language barrier

After literal tableau self-containment and unbounded behavioral reflection are
closed, one apparent escape remains: let a finite CNF carry a compact external
program name and allow its truth definition to consult that name.

This file separates the two resulting languages.

* Under ordinary CNF semantics, the external name is inert.  Changing it while
  retaining the same local clauses cannot change satisfiability.
* Under name-sensitive semantics, even the fixed local formula `noCNF` can have
  different truth values for different names.  This is no longer ordinary SAT;
  it is a language with an external Kleene-evaluation oracle in its semantics.
* Any effective semantics-preserving erasure of that name-sensitive language
  back to ordinary finite CNF would yield the unbounded halting-to-SAT
  reflection already proved impossible.
* Bounded name evaluation can be answer-coded into `yesCNF`/`noCNF`, but the
  bounded evaluator has then already computed the answer before emitting the
  CNF.  The tiny output is not a Cook--Levin witness of the computation.

Thus an opaque compact name does not provide a third ordinary-SAT route.  It is
either ignored, evaluated by the compiler in advance, materialized by a
bounded tableau, or retained as an oracle-bearing extension of the language.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameTowerExternalNameLanguageBarrier

open SATDepthMachine
open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge
open PallLean.Paper93.DeepMath.PathB.NFrameTowerHaltingReflectionNoGo

/-! ## Ordinary CNF versus name-sensitive semantics -/

/-- A compact external program name paired with an ordinary finite CNF. -/
structure ExternallyNamedCNF where
  name : Code
  formula : CNF

/-- Ordinary SAT ignores metadata and evaluates only the finite clauses. -/
def OrdinarySAT (N : ExternallyNamedCNF) : Prop :=
  Satisfiable N.formula

/-- The tempting alternative semantics, allowing truth to consult unbounded
behavior of the external program name. -/
def NameSensitiveSAT (N : ExternallyNamedCNF) : Prop :=
  Satisfiable N.formula ∨ (Code.eval N.name 0).Dom

/-- Under ordinary SAT semantics, changing only the external name is inert. -/
theorem ordinarySAT_name_invariant
    (A B : ExternallyNamedCNF) (hlocal : A.formula = B.formula) :
    OrdinarySAT A ↔ OrdinarySAT B := by
  simp only [OrdinarySAT, hlocal]

/-- Use the fixed unsatisfiable local CNF so that all name-sensitive truth
comes solely from the external program. -/
def haltingOnlyNamedCNF (c : Code) : ExternallyNamedCNF where
  name := c
  formula := noCNF

/-- Ordinary SAT rejects every member of the halting-only named family. -/
theorem haltingOnly_not_ordinarySAT (c : Code) :
    ¬ OrdinarySAT (haltingOnlyNamedCNF c) := by
  simpa [OrdinarySAT, haltingOnlyNamedCNF] using noCNF_not_satisfiable

/-- Name-sensitive truth on the same fixed local CNF is exactly unbounded
Kleene termination. -/
theorem haltingOnly_nameSensitiveSAT_iff (c : Code) :
    NameSensitiveSAT (haltingOnlyNamedCNF c) ↔ (Code.eval c 0).Dom := by
  simp [NameSensitiveSAT, haltingOnlyNamedCNF, noCNF_not_satisfiable]

/-- Two names with different halting behavior give different name-sensitive
truth values despite having literally equal local CNFs. -/
theorem nameSensitiveSAT_not_local
    (halts loops : Code)
    (hhalts : (Code.eval halts 0).Dom)
    (hloops : ¬ (Code.eval loops 0).Dom) :
    (haltingOnlyNamedCNF halts).formula = (haltingOnlyNamedCNF loops).formula ∧
      NameSensitiveSAT (haltingOnlyNamedCNF halts) ∧
      ¬ NameSensitiveSAT (haltingOnlyNamedCNF loops) := by
  exact ⟨rfl,
    (haltingOnly_nameSensitiveSAT_iff halts).mpr hhalts,
    fun h => hloops ((haltingOnly_nameSensitiveSAT_iff loops).mp h)⟩

/-! ## Effective erasure back to ordinary CNF is impossible -/

/-- An alleged effective translation of the name-sensitive halting-only
family back to ordinary finite CNF, together with an effective SAT classifier
for the translated outputs. -/
structure ComputableExternalNameErasure where
  erase : Code → CNF
  satBit : Code → Bool
  satBit_computable : Computable satBit
  satBit_correct : ∀ c : Code,
    satBit c = true ↔ Satisfiable (erase c)
  preserves_semantics : ∀ c : Code,
    Satisfiable (erase c) ↔ NameSensitiveSAT (haltingOnlyNamedCNF c)

/-- Such an erasure is precisely an instance of the forbidden computable
halting-to-SAT reflection. -/
def ComputableExternalNameErasure.toHaltingSATReflection
    (E : ComputableExternalNameErasure) :
    ComputableHaltingSATReflection where
  decode := E.erase
  satBit := E.satBit
  satBit_computable := E.satBit_computable
  satBit_correct := E.satBit_correct
  reflects_halting := by
    intro c
    exact (E.preserves_semantics c).trans
      (haltingOnly_nameSensitiveSAT_iff c)

/-- **External-name erasure no-go.**  An opaque program reference cannot be
compiled away into ordinary finite SAT while preserving its unbounded
name-sensitive meaning. -/
theorem no_computableExternalNameErasure :
    ¬ Nonempty ComputableExternalNameErasure := by
  rintro ⟨E⟩
  exact no_computableHaltingSATReflection
    ⟨E.toHaltingSATReflection⟩

/-! ## Bounded evaluation is finite but answer-coded -/

/-- The bounded truth bit obtained by actually running Mathlib's evaluator for
the supplied fuel before choosing a CNF. -/
def boundedNameBit (fuel : Code → Nat) (c : Code) : Bool :=
  (Code.evaln (fuel c) c 0).isSome

/-- The constant-size answer-coded CNF for bounded name evaluation. -/
def boundedAnswerCodedCNF (fuel : Code → Nat) (c : Code) : CNF :=
  truthCodedCNF (boundedNameBit fuel c)

/-- The answer-coded output reflects the bounded evaluator exactly because the
evaluator's Boolean answer was used to choose `yesCNF` or `noCNF`. -/
theorem boundedAnswerCodedCNF_satisfiable_iff
    (fuel : Code → Nat) (c : Code) :
    Satisfiable (boundedAnswerCodedCNF fuel c) ↔
      boundedNameBit fuel c = true :=
  truthCodedCNF_satisfiable_iff (boundedNameBit fuel c)

/-- This bounded reduction always emits one of the same two fixed formulas;
all dependence on the program and fuel has already been discharged by
`Code.evaln`. -/
theorem boundedAnswerCodedCNF_eq_yes_or_no
    (fuel : Code → Nat) (c : Code) :
    boundedAnswerCodedCNF fuel c = yesCNF ∨
      boundedAnswerCodedCNF fuel c = noCNF := by
  cases h : boundedNameBit fuel c
  · exact Or.inr (by simp [boundedAnswerCodedCNF, truthCodedCNF, h])
  · exact Or.inl (by simp [boundedAnswerCodedCNF, truthCodedCNF, h])

end PallLean.Paper93.DeepMath.PathB.NFrameTowerExternalNameLanguageBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerExternalNameLanguageBarrier.ordinarySAT_name_invariant
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerExternalNameLanguageBarrier.haltingOnly_nameSensitiveSAT_iff
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerExternalNameLanguageBarrier.nameSensitiveSAT_not_local
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerExternalNameLanguageBarrier.no_computableExternalNameErasure
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerExternalNameLanguageBarrier.boundedAnswerCodedCNF_satisfiable_iff
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerExternalNameLanguageBarrier.boundedAnswerCodedCNF_eq_yes_or_no
