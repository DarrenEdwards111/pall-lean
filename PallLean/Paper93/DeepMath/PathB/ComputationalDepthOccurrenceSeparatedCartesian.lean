import Mathlib

/-!
# Occurrence-separated verification gives genuine semantic rectangles

This file formalizes the strongest non-circular semantic-separation mechanism
surviving the research audit.  Two verifier occurrences have disjoint witness
types and are combined only by conjunction.  Their projected port relation is
then exactly the Cartesian product of the two local supports: accepting local
transcripts can be spliced in every cross-combination.

The hypothesis is proof-relevant occurrence separation.  Ordinary Boolean SAT
correctness does not force an unrestricted circuit to expose this structure.
The final example shows why the hypothesis matters: identifying one auxiliary
bit across the occurrences leaves both diagonal points but deletes the crossed
points.
-/

namespace PallLean.Paper93.DeepMath.PathB.OccurrenceSeparatedCartesian

/-- A proof-relevant pair of verifier occurrences with disjoint transcript
namespaces.  The combined verifier contains no cross-occurrence constraint. -/
structure BiTraceVerifier (Row Col RowTrace ColTrace : Type*) where
  leftAccept : Row → RowTrace → Prop
  rightAccept : Col → ColTrace → Prop

namespace BiTraceVerifier

variable {Row Col RowTrace ColTrace : Type*}
    (V : BiTraceVerifier Row Col RowTrace ColTrace)

/-- The visible row support of the left verifier. -/
def rowSupport (r : Row) : Prop := ∃ wr, V.leftAccept r wr

/-- The visible column support of the right verifier. -/
def colSupport (c : Col) : Prop := ∃ wc, V.rightAccept c wc

/-- Acceptance of the occurrence-separated conjunction. -/
def separatedRelation (r : Row) (c : Col) : Prop :=
  ∃ wr wc, V.leftAccept r wr ∧ V.rightAccept c wc

/-- Existential projection of disjoint transcript blocks is exactly the
Cartesian product of their local supports. -/
theorem separatedRelation_iff (r : Row) (c : Col) :
    V.separatedRelation r c ↔ V.rowSupport r ∧ V.colSupport c := by
  constructor
  · rintro ⟨wr, wc, hr, hc⟩
    exact ⟨⟨wr, hr⟩, ⟨wc, hc⟩⟩
  · rintro ⟨⟨wr, hr⟩, ⟨wc, hc⟩⟩
    exact ⟨wr, wc, hr, hc⟩

/-- Constructive four-corner closure: the two missing corners are obtained by
splicing the already accepted local transcripts. -/
theorem four_corner_splice
    {r₀ r₁ : Row} {c₀ c₁ : Col}
    (h00 : V.separatedRelation r₀ c₀)
    (h11 : V.separatedRelation r₁ c₁) :
    V.separatedRelation r₀ c₁ ∧ V.separatedRelation r₁ c₀ := by
  rcases h00 with ⟨wr₀, wc₀, hr₀, hc₀⟩
  rcases h11 with ⟨wr₁, wc₁, hr₁, hc₁⟩
  exact ⟨⟨wr₀, wc₁, hr₀, hc₁⟩, ⟨wr₁, wc₀, hr₁, hc₀⟩⟩

/-- Explicit semantic non-aliasing for two supported values on each port. -/
theorem all_four_combinations
    {r₀ r₁ : Row} {c₀ c₁ : Col}
    (hr₀ : V.rowSupport r₀) (hr₁ : V.rowSupport r₁)
    (hc₀ : V.colSupport c₀) (hc₁ : V.colSupport c₁) :
    V.separatedRelation r₀ c₀ ∧ V.separatedRelation r₀ c₁ ∧
      V.separatedRelation r₁ c₀ ∧ V.separatedRelation r₁ c₁ := by
  simpa [V.separatedRelation_iff] using
    And.intro (And.intro hr₀ hc₀)
      (And.intro (And.intro hr₀ hc₁)
        (And.intro (And.intro hr₁ hc₀) (And.intro hr₁ hc₁)))

end BiTraceVerifier

/-- A one-bit shared auxiliary variable couples the two occurrences. -/
def collidedBitRelation (r c : Bool) : Prop := ∃ shared : Bool, shared = r ∧ shared = c

theorem collidedBitRelation_iff (r c : Bool) :
    collidedBitRelation r c ↔ r = c := by
  constructor
  · rintro ⟨shared, hsr, hsc⟩
    exact hsr.symm.trans hsc
  · intro h
    exact ⟨r, rfl, h⟩

/-- Both diagonal values survive the collision. -/
theorem collidedBit_diagonal :
    collidedBitRelation false false ∧ collidedBitRelation true true := by
  simp [collidedBitRelation]

/-- The crossed values are deleted, so the collided relation is not
Cartesian despite each individual occurrence supporting both bits. -/
theorem collidedBit_missing_crosses :
    ¬ collidedBitRelation false true ∧ ¬ collidedBitRelation true false := by
  simp [collidedBitRelation_iff]

/-- Consequently the four-corner splicing law is false after aliasing. -/
theorem collidedBit_not_four_corner_closed :
    ¬ (∀ r₀ r₁ c₀ c₁,
      collidedBitRelation r₀ c₀ → collidedBitRelation r₁ c₁ →
      collidedBitRelation r₀ c₁ ∧ collidedBitRelation r₁ c₀) := by
  intro h
  have crossed := h false true false true
    collidedBit_diagonal.1 collidedBit_diagonal.2
  exact collidedBit_missing_crosses.1 crossed.1

end PallLean.Paper93.DeepMath.PathB.OccurrenceSeparatedCartesian

#print axioms PallLean.Paper93.DeepMath.PathB.OccurrenceSeparatedCartesian.BiTraceVerifier.separatedRelation_iff
#print axioms PallLean.Paper93.DeepMath.PathB.OccurrenceSeparatedCartesian.BiTraceVerifier.four_corner_splice
#print axioms PallLean.Paper93.DeepMath.PathB.OccurrenceSeparatedCartesian.BiTraceVerifier.all_four_combinations
#print axioms PallLean.Paper93.DeepMath.PathB.OccurrenceSeparatedCartesian.collidedBit_not_four_corner_closed
