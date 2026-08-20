import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultiSwitchingCommonTree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingDnfCount

/-!
# Finite labels for common multi-switching witnesses

A common bad path pays once for its shared branch transcript.  The remaining bookkeeping records,
for each gate, its number of contiguous active runs and, for each of its terms, its multiplicity on
the common path.  All counts lie between zero and the shared depth.  This file gives the exact finite
label space and connects it to the generic injective counting theorem; constructing the canonical
bad-path packing is the next combinatorial obligation.
-/

namespace PallLean.Paper93.DeepMath.PathB.MultiSwitching

open PallLean.Paper93.DeepMath.PathB.SwitchingCounting

/-- Shared boundary bookkeeping: one run count per gate and one term multiplicity per gate/term. -/
abbrev CommonBoundaryLabel (d G m : ℕ) :=
  (Fin G → Fin (d + 1)) × (Fin G → Fin m → Fin (d + 1))

/-- The full finite common witness label: one shared transcript plus polynomial boundary data. -/
abbrev CommonBadPathLabel (d G m : ℕ) :=
  CommonTree.FinitePathLabel d × CommonBoundaryLabel d G m

/-- Exact cardinality of the shared gate/term boundary bookkeeping. -/
theorem card_commonBoundaryLabel (d G m : ℕ) :
    Fintype.card (CommonBoundaryLabel d G m) =
      (d + 1) ^ G * ((d + 1) ^ m) ^ G := by
  simp [CommonBoundaryLabel, Fintype.card_prod]

/-- Exact common-witness label count.  The exponential transcript factor occurs once; all
gate/term identity information is in the displayed fixed-parameter polynomial factors. -/
theorem card_commonBadPathLabel (d G m : ℕ) :
    Fintype.card (CommonBadPathLabel d G m) =
      ((d + 1) * 2 ^ d) * ((d + 1) ^ G * ((d + 1) ^ m) ^ G) := by
  rw [Fintype.card_prod, CommonTree.card_finitePathLabel, card_commonBoundaryLabel]

/-- Assemble the shared transcript and boundary tables without duplicating path bits per gate. -/
def commonBadPathPack {d G m : ℕ}
    (path : CommonTree.PathLabel d)
    (gateRuns : Fin G → Fin (d + 1))
    (termCounts : Fin G → Fin m → Fin (d + 1)) : CommonBadPathLabel d G m :=
  (path.toFinite, (gateRuns, termCounts))

/-- The common packing is injective once its three mathematical components agree. -/
theorem commonBadPathPack_eq_iff {d G m : ℕ}
    {p q : CommonTree.PathLabel d}
    {gr₁ gr₂ : Fin G → Fin (d + 1)}
    {tc₁ tc₂ : Fin G → Fin m → Fin (d + 1)} :
    commonBadPathPack p gr₁ tc₁ = commonBadPathPack q gr₂ tc₂ ↔
      p = q ∧ gr₁ = gr₂ ∧ tc₁ = tc₂ := by
  constructor
  · intro h
    exact ⟨CommonTree.PathLabel.toFinite_injective (congrArg Prod.fst h),
      congrArg (fun z => z.2.1) h, congrArg (fun z => z.2.2) h⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

variable {n : ℕ}

/-- The finite-label count consumed by a genuine common bad-path encoder.  The sole remaining
semantic premise is injectivity of `(endpoint, shared witness label)` on the chosen bad set. -/
theorem commonBadPath_count {d G m : ℕ}
    (endpoint : Restriction n → Restriction n)
    (label : Restriction n → CommonBadPathLabel d G m)
    {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ ∈ Bad, endpoint ρ ∈ Short)
    (hrec : ∀ ρ ∈ Bad, ∀ σ ∈ Bad,
      endpoint ρ = endpoint σ → label ρ = label σ → ρ = σ) :
    Bad.card ≤ Short.card *
      (((d + 1) * 2 ^ d) * ((d + 1) ^ G * ((d + 1) ^ m) ^ G)) := by
  apply card_bad_le_label_card endpoint label
  · exact le_of_eq (card_commonBadPathLabel d G m)
  · exact hmem
  · exact hrec

end PallLean.Paper93.DeepMath.PathB.MultiSwitching

#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.card_commonBadPathLabel
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonBadPathPack_eq_iff
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonBadPath_count
