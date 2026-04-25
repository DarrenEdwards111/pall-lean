import PallLean.Paper93.Direct.PerTypeComposition

/-!
# Per-type spanning to template-collapse bridge at concreteW

This PathB-facing file isolates the exact remaining concrete obligation in the
P-side/template-collapse bridge.

The named row-embedding package
`PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW` is
definitionally the `CookLevinPerTypeSpanning` bundle at
`W := fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau`.  Once that single
term is supplied, the existing per-type spanning bridge closes the
bounded-profile template-collapse lemma, with the concreteW finiteness and
dimension hypotheses discharged by `concreteW_finite` and
`concreteW_finrank_le_three`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open PaperFaithfulSeparation
open SymmetricPowerBound
open TuringMachine (DTM)
open WithinProfileBound

attribute [local instance] Classical.dec

/-- The named concreteW row-embedding obligation is definitionally identical
to the per-type spanning bundle at the canonical concreteW family. -/
theorem concreteW_perTypeSpanning_iff_rowEmbeddings
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4) :
    PallLean.Paper93.Spanning.CookLevinPerTypeSpanning M n hn htb hns
        (fun tau =>
          PallLean.Paper93.Wiring.concreteW n hn4 (Fin.castLEEmb hn4) tau)
      ↔
    PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
      M n hn htb hns hn4 := by
  rfl

/-- A concreteW row-embedding term supplies the concrete per-type spanning
bundle required by `Spanning.cookLevinProfileTemplateCollapseLemmaBoundedProfile_from_perTypeSpanning`. -/
theorem concreteW_perTypeSpanning_of_rowEmbeddings
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    PallLean.Paper93.Spanning.CookLevinPerTypeSpanning M n hn htb hns
      (fun tau =>
        PallLean.Paper93.Wiring.concreteW n hn4 (Fin.castLEEmb hn4) tau) :=
  hRowEmbeddings

/-- ConcreteW per-type spanning closes bounded-profile template collapse,
with all structural `W` assumptions discharged by the concreteW package. -/
theorem cookLevinProfileTemplateCollapseLemmaBoundedProfile_from_concreteW_perTypeSpanning
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hSpan :
      PallLean.Paper93.Spanning.CookLevinPerTypeSpanning M n hn htb hns
        (fun tau =>
          PallLean.Paper93.Wiring.concreteW n hn4 (Fin.castLEEmb hn4) tau)) :
    CookLevinProfileTemplateCollapseLemmaBoundedProfile M n hn htb hns :=
  PallLean.Paper93.Spanning.cookLevinProfileTemplateCollapseLemmaBoundedProfile_from_perTypeSpanning
    M n hn htb hns
    (fun tau =>
      PallLean.Paper93.Wiring.concreteW n hn4 (Fin.castLEEmb hn4) tau)
    (fun tau =>
      PallLean.Paper93.Wiring.concreteW_finite
        n hn4 (Fin.castLEEmb hn4) tau)
    (fun tau =>
      PallLean.Paper93.Wiring.concreteW_finrank_le_three
        n hn4 (Fin.castLEEmb hn4) tau)
    hSpan

/-- The P-side/template-collapse bridge at concreteW reduces to the single
named row-embedding obligation
`Direct.CookLevinPerTypeRowEmbeddings_concreteW`. -/
theorem cookLevinProfileTemplateCollapseLemmaBoundedProfile_from_concreteW_rowEmbeddings
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    CookLevinProfileTemplateCollapseLemmaBoundedProfile M n hn htb hns :=
  cookLevinProfileTemplateCollapseLemmaBoundedProfile_from_concreteW_perTypeSpanning
    M n hn htb hns hn4
    (concreteW_perTypeSpanning_of_rowEmbeddings
      M n hn htb hns hn4 hRowEmbeddings)

/-! ## Axiom audit anchors -/

#print axioms concreteW_perTypeSpanning_iff_rowEmbeddings
#print axioms concreteW_perTypeSpanning_of_rowEmbeddings
#print axioms cookLevinProfileTemplateCollapseLemmaBoundedProfile_from_concreteW_perTypeSpanning
#print axioms cookLevinProfileTemplateCollapseLemmaBoundedProfile_from_concreteW_rowEmbeddings

end PallLean.Paper93.DeepMath.PathB
