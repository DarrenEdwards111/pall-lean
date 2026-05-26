import PallLean.Paper93.DeepMath.PathB.DynamicNFrameLagrangianInvariant

/-!
# Constructive engine form of the dynamic extraction theorem

This file repackages `UniversalDynamicNFrameLagrangianExtraction` as an explicit
constructor object that can be attacked component-by-component.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- A constructive engine for dynamic N-frame/Lagrangian extraction. -/
structure DynamicNFrameLagrangianExtractionEngine
    (enc : ThreeCNFEncoding) where
  lengthForExponent : Nat -> Nat
  length_large : ∀ c : Nat, lengthForExponent c >= 2 ^ 20
  length_log : ∀ c : Nat, 4 * (c + 1) <= Nat.log 2 (lengthForExponent c)
  extract_minor :
    ∀ c : Nat,
      ∀ L : DynamicNFrameLagrangianObserver enc,
        DynamicNFrameLagrangianLiveMinor enc L (lengthForExponent c)

/-- Engine form implies the theorem form. -/
theorem universalDynamicExtraction_of_engine
    (enc : ThreeCNFEncoding)
    (E : DynamicNFrameLagrangianExtractionEngine enc) :
    UniversalDynamicNFrameLagrangianExtraction enc := by
  intro c
  refine ⟨E.lengthForExponent c, E.length_large c, E.length_log c, ?_⟩
  intro L
  exact ⟨E.extract_minor c L⟩

/-- The theorem form yields an engine form by choice. -/
noncomputable def engine_of_universalDynamicExtraction
    (enc : ThreeCNFEncoding)
    (h : UniversalDynamicNFrameLagrangianExtraction enc) :
    DynamicNFrameLagrangianExtractionEngine enc where
  lengthForExponent := fun c => Classical.choose (h c)
  length_large := by
    intro c
    exact (Classical.choose_spec (h c)).1
  length_log := by
    intro c
    exact (Classical.choose_spec (h c)).2.1
  extract_minor := by
    intro c L
    exact Classical.choice ((Classical.choose_spec (h c)).2.2 L)

/-- Equivalence between theorem and engine forms. -/
theorem universalDynamicExtraction_iff_engine
    (enc : ThreeCNFEncoding) :
    UniversalDynamicNFrameLagrangianExtraction enc ↔
      Nonempty (DynamicNFrameLagrangianExtractionEngine enc) := by
  constructor
  · intro h
    exact ⟨engine_of_universalDynamicExtraction enc h⟩
  · intro hE
    rcases hE with ⟨E⟩
    exact universalDynamicExtraction_of_engine enc E

/-! ## Axiom trace -/

#print axioms universalDynamicExtraction_of_engine
#print axioms engine_of_universalDynamicExtraction
#print axioms universalDynamicExtraction_iff_engine

end PallLean.Paper93.DeepMath.PathB
